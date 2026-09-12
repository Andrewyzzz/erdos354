#!/usr/bin/env python3
"""Exact finite checks for the digit-budget propagation / denominator bootstrap.

All pass/fail calculations use integers or fractions.Fraction.  These checks
validate finite identities and finite certificates, not the infinite theorem.
The latter requires the companion proof and the prior finite-event-decay lemma.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, factorial
from pathlib import Path
import hashlib
import json
import random
import time

BITS = ((0,0),(1,0),(0,1),(1,1))


def floor(x: F) -> int:
    return x.numerator // x.denominator


def ceil(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def ceil_log2(n: int) -> int:
    assert n >= 1
    return (n-1).bit_length()


def frac(x: F) -> F:
    return x-floor(x)


def weight(x: F, i: int) -> int:
    return floor(x*(1 << i))


def words(weights: list[int]) -> list[int]:
    s = [0]
    for w in weights:
        s += [v+w for v in s]
    return s


def subset_bits(weights: list[int]) -> int:
    p = 1
    for w in weights:
        if w < 0:
            raise ValueError('Nonnegative weights required')
        p |= p << w
    return p


def run_starts(p: int, length: int) -> int:
    if length < 1:
        raise ValueError('length must be positive')
    out, size = p, 1
    while 2*size <= length:
        out &= out >> size
        size *= 2
    if size < length:
        out &= out >> (length-size)
    return out


def longest_run(p: int) -> tuple[int, int]:
    if not p:
        raise ValueError('empty set')
    lo, hi = 1, p.bit_length()+1
    while lo+1 < hi:
        mid = (lo+hi)//2
        if run_starts(p, mid):
            lo = mid
        else:
            hi = mid
    starts = run_starts(p, lo)
    start = (starts & -starts).bit_length()-1
    return start, start+lo-1


def block_budget(alpha: F, beta: F, n: int, k: int) -> tuple[F,int,int]:
    E = sum((frac((1 << i)*alpha)+frac((1 << i)*beta)
             for i in range(n,n+k)), F(0))
    B = sum(weight(alpha,i+1)-2*weight(alpha,i)+
            weight(beta,i+1)-2*weight(beta,i) for i in range(n,n+k))
    K = sum((weight(alpha,i+1)-2*weight(alpha,i),
             weight(beta,i+1)-2*weight(beta,i)) != (0,0)
            for i in range(n,n+k))
    telescoped = (B-frac((1 << n)*alpha)-frac((1 << n)*beta)
                  +frac((1 << (n+k))*alpha)+frac((1 << (n+k))*beta))
    assert E == telescoped
    assert 0 <= E < B+2 <= 2*K+2
    assert E < 2*k
    return E, B, K


def telescoping_checks() -> dict:
    count = mask_count = 0
    rng = random.Random(3540909)
    # All finite binary fractional words to depth 8, multiple initial scales.
    for a in range(256):
        alpha = F(3)+F(a,256)+F(1,3*256)
        beta = F(2)+F((73*a+19)%256,256)+F(1,5*256)
        for n in range(5):
            for k in range(1,7):
                E, B, K = block_budget(alpha,beta,n,k)
                count += 1
                if n == 0 and k <= 4:
                    wa=[weight(alpha,n+i) for i in range(k)]
                    wb=[weight(beta,n+i) for i in range(k)]
                    aa,bb=words(wa),words(wb)
                    for p,x in enumerate(aa):
                        for q,y in enumerate(bb):
                            err=(1 << n)*(alpha*p+beta*q)-x-y
                            assert 0 <= err <= E
                            mask_count += 1
    for _ in range(300):
        alpha=F(rng.randrange(1,10000),rng.randrange(1,1000))
        beta=F(rng.randrange(1,10000),rng.randrange(1,1000))
        block_budget(alpha,beta,rng.randrange(50),rng.randrange(1,80))
        count += 1
    return {'fractional_error_identity_checks':count,
            'individual_legal_subset_error_checks':mask_count}


def ideal_grid(theta: F, q: int) -> tuple[int,int,list[tuple[int,int,int]]]:
    k=ceil_log2(8*q); K=1 << k
    a,b=theta.numerator,theta.denominator
    t0=ceil((q-1)*theta)
    left=t0*b; right=a*(K-q)+b*(K-1)
    pts=[]
    for p in range(K):
        low=max(0,ceil(F(left-a*p,b)))
        high=min(K-1,(right-a*p)//b)
        pts.extend((a*p+b*t,p,t) for t in range(low,high+1))
    pts.sort()
    assert pts[0][0] == left and pts[-1][0] == right
    assert max(y[0]-x[0] for x,y in zip(pts,pts[1:]))*q <= 3*b
    assert right-left > K*b
    return k,t0,pts


def grid_and_bridge_checks() -> dict:
    grids=bridges=checks=0
    rows=[]
    for q in range(2,8):
        for p in range(q+1,2*q):
            if gcd(p,q) != 1:
                continue
            for sign in (-1,0,1):
                theta=F(p,q)+F(sign,4*q*q)
                assert 1 < theta < 2 and abs(theta-F(p,q)) < F(1,q*q)
                k,t0,pts=ideal_grid(theta,q)
                grids += 1
                beta=F(2)+F(1,7)
                alpha=theta*beta
                # Wait until strict integer interleaving; then find a seed.
                P=1
                found=False
                for n in range(1,10):
                    A,B=weight(alpha,n-1),weight(beta,n-1)
                    P |= P << A; P |= P << B
                    if not (B < A < 2*B):
                        continue
                    low,high=longest_run(P)
                    E,bits,events=block_budget(alpha,beta,n,k)
                    lam=(1 << n)*beta
                    threshold=3*lam/q+E
                    if high-low < threshold:
                        continue
                    aa=words([weight(alpha,n+i) for i in range(k)])
                    bb=words([weight(beta,n+i) for i in range(k)])
                    shifts=sorted(aa[p0]+bb[t0_] for _,p0,t0_ in pts)
                    assert F(max(y-x for x,y in zip(shifts,shifts[1:]))) <= threshold
                    L,U=low+shifts[0],high+shifts[-1]
                    assert U-L > lam*(1 << k)
                    # Independent full integer DP from original weights.
                    Pfull=P
                    for i in range(n,n+k):
                        Pfull |= Pfull << weight(alpha,i)
                        Pfull |= Pfull << weight(beta,i)
                    assert ((Pfull >> L) & ((1 << (U-L+1))-1)).bit_count() == U-L+1
                    assert U-L >= weight(beta,n+k)
                    bridges += 1
                    checks += U-L+1
                    if len(rows)<3:
                        rows.append({'alpha':str(alpha),'beta':str(beta),'n':n,'k':k,
                                     'actual_error_budget':str(E),'old_budget':2*k,
                                     'digit_events_in_block':events,'interval':[L,U]})
                    found=True
                    break
                if not found:
                    raise AssertionError('finite seed search exhausted: not a disproof')
    return {'ideal_grid_checks_with_endpoints':grids,
            'full_integer_propagation_certificates':bridges,
            'represented_integer_positions_checked':checks,'sample_certificates':rows}


def prefix_run_checks() -> dict:
    count=0
    # The combinatorial step from missing positions to longest full interval.
    for M,N in ((3,2),(5,3),(9,6)):
        for n in range(1,6):
            for code in product(BITS,repeat=n):
                A,B=M,N; weights=[]; events=0
                for u,v in code:
                    weights.extend((A,B))
                    A,B=2*A+u,2*B+v
                    events += (u+v)>0
                P=subset_bits(weights); S=sum(weights)
                low,high=longest_run(P); R=high-low
                e=S+1-P.bit_count(); Q=A+B-P.bit_count()
                assert (R+2)*(e+1) >= S+2
                C0=2*(M+N+10)
                den,num=32*N,32*N-1
                assert Q*Q*pow(den,events) <= C0*C0*(1 << (2*n))*pow(num,events)
                # Rational-square version of R+2 >= c0 rho^(-K/2).
                c0=F(M+N,2*(C0+1))
                assert F((R+2)**2)*F(num,den)**events >= c0*c0
                count += 1
    return {'prefix_longest_run_lower_bound_checks':count}


def sqrt2_scaled_examples() -> list[dict]:
    # delta = sum_{j>=2} 2^(-j!), hence delta is a Liouville number.
    delta_lo=sum((F(1,1 << factorial(j)) for j in range(2,5)),F(0))
    delta_hi=delta_lo+F(1,1 << (factorial(5)-1))
    rows=[]
    for N in (3,10,100,1000):
        blo,bhi=F(N)+delta_lo,F(N)+delta_hi
        def b(i):
            lo,hi=floor(blo*(1 << i)),floor(bhi*(1 << i))
            assert lo == hi
            return lo
        def a(i):
            x,y=blo*(1 << i),bhi*(1 << i)
            lo=isqrt(2*x.numerator*x.numerator)//x.denominator
            hi=isqrt(2*y.numerator*y.numerator)//y.denominator
            assert lo == hi
            return lo
        P=1
        for n in range(1,18):
            A,B=a(n-1),b(n-1)
            P |= P << A; P |= P << B
            width=2*B+1
            starts=run_starts(P,width+1)
            if starts and B < A < 2*B:
                L=(starts & -starts).bit_length()-1
                assert ((P>>L)&((1 << (width+1))-1)).bit_count() == width+1
                assert width >= b(n)
                rows.append({'beta':f'{N}+delta (transcendental)',
                             'alpha':'sqrt(2)*beta','prefix_pairs':n,
                             'interval':[L,L+width], 'width':width,
                             'actual_next_b':b(n),
                             'floor_certification':'rational enclosure plus integer square root'})
                break
        else:
            raise AssertionError('finite sample search exhausted, not incompleteness')
    return rows


def factorial_denominator_checks() -> dict:
    # Algebraic inequalities used for the logarithmic-square approximation bound.
    count=0
    for q in range(2,20001):
        j=2
        while (1 << factorial(j)) < 4*q:
            j+=1
        Q=1 << factorial(j)
        Qnext=1 << factorial(j+1)
        assert F(2,Qnext) <= F(1,2*q*Q)
        # Rational inequality j <= log2(4q)+1, verified by exponentiation.
        assert (1 << (j-1)) <= 4*q
        count += 1
    return {'factorial_ratio_denominator_bound_checks':count}


def main() -> None:
    started=time.monotonic()
    result={'status':'Finite exact checks; all infinite quantifiers are proved in the note.',
            'telescoping':telescoping_checks(),
            'grids_and_propagation':grid_and_bridge_checks(),
            'prefix_runs':prefix_run_checks(),
            'arbitrary_scale_sqrt2_samples':sqrt2_scaled_examples(),
            'factorial_ratio':factorial_denominator_checks()}
    prior=Path(__file__).with_name('erdos354_finite_event_decay.py')
    if prior.exists():
        result['prior_verifier_sha256']=hashlib.sha256(prior.read_bytes()).hexdigest()
    result['elapsed_seconds_diagnostic_only']=round(time.monotonic()-started,3)
    out=Path(__file__).with_name('erdos354_digit_budget_bootstrap_results.json')
    out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
