"""Finite checks for the multiplicative-event-gap argument for Erdos #354.

No finite computation establishes the FE/DB inputs or any infinite theorem.
All mathematical assertions use integers or Fraction.  Abstract packing tests
are explicitly separated from actual floor-sequence tests.
"""
from __future__ import annotations
from bisect import bisect_right
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import random
import time

ROOT = Path(__file__).resolve().parent
RNG = random.Random(3540911)


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError('positive integer required')
    return (n-1).bit_length()


def floor_fraction(x: F) -> int:
    return x.numerator // x.denominator


def floor_seq(x: F, T: int) -> list[int]:
    return [(x.numerator << i) // x.denominator for i in range(T+1)]


def events_from(a: list[int], b: list[int]) -> list[int]:
    events = []
    for i in range(1, len(a)):
        u, v = a[i]-2*a[i-1], b[i]-2*b[i-1]
        assert u in (0, 1) and v in (0, 1)
        if u or v:
            events.append(i)
    return events


def choose_exact_levels(T: int, E: int, R: int, n0: int, is_exact) -> list[int]:
    """Pure finite band-packing construction, not an asymptotic claim."""
    x = max(n0+1, 2*E+1)
    b = 2*R+1
    chosen=[]
    while 2*x <= T:
        point=next((i for i in range(x, 2*x+1) if is_exact(i)), None)
        assert point is not None
        chosen.append(point)
        x *= b
    for u, v in zip(chosen, chosen[1:]):
        assert v > R*u
    return chosen


def check_defect_counts() -> dict:
    checked = layers = zeros = informative = 0
    for _ in range(600):
        q = RNG.randint(2, 24)
        p = RNG.randint(q+1, 2*q-1)
        if gcd(p,q) != 1:
            continue
        T = RNG.randint(12, 120)
        # Both coordinates are exact rationals with an independently controlled
        # near-ratio error. They are not asserted to be irrational test points.
        den = 1 << (T+12)
        G = 2*den
        for t in sorted(set([RNG.randint(2,T+8) for _ in range(RNG.randint(0,8))])):
            G += 1 << (T+12-t)
        gamma=F(G,den)
        eps=F(1,q*(1 << (T+3)))
        alpha=p*gamma+eps
        beta=q*gamma
        delta=q*alpha-p*beta
        assert 0 < (1<<T)*delta < 1
        a,b=floor_seq(alpha,T),floor_seq(beta,T)
        events=events_from(a,b)
        h=ceil_log2(p+q+1)
        Ds=[q*x-p*y for x,y in zip(a,b)]
        assert all(abs(d) < (1<<h) for d in Ds)
        E=h*(len(events)+1)
        bad=sum(d!=0 for d in Ds)
        assert bad <= E
        informative += int(E<T)
        event_set=set(events)
        for i in range(T-h+1):
            if all(t not in event_set for t in range(i+1,i+h+1)):
                assert Ds[i]==0
                zeros += 1
        checked+=1
        layers+=len(Ds)
    return dict(configurations=checked, layers=layers,
                verified_exact_starts_after_h_zero_transitions=zeros,
                configurations_where_bad_count_bound_is_below_T=informative)


def check_abstract_packing() -> dict:
    configurations=bands=returns=0
    for _ in range(1000):
        T=RNG.randint(10000,2000000)
        R=RNG.randint(2,7)
        n0=RNG.randint(2,30)
        E=RNG.randint(0,250)
        bad=set(RNG.sample(range(T+1), E))
        events=[1]
        while events[-1] <= T:
            events.append(RNG.randint(events[-1]+1, R*events[-1]))
        chosen=choose_exact_levels(T,E,R,n0,lambda i:i not in bad)
        for u,v in zip(chosen,chosen[1:]):
            event=events[bisect_right(events,u)]
            assert u < event <= R*u < v
            returns+=1
        configurations+=1
        bands+=len(chosen)
    return dict(configurations=configurations, chosen_bands=bands,
                disjoint_event_containing_transitions=returns,
                scope='abstract integer positions; not floor-sequence samples')


def check_actual_returns() -> dict:
    # Rational fixed-ratio negative controls: nu(p,q) need not diverge here.
    configs=checks=selected=0
    examples=[]
    for p,q in [(3,2),(5,4),(7,4),(9,8)]:
        for T in [1024,2048,4096,8192,16384,32768]:
            Z=T+20
            G=2*(1<<Z)
            t=6
            while t<=Z:
                G += 1<<(Z-t)
                t=(3*t+1)//2
            # alpha/beta=p/q; all earlier values are genuine floor values.
            An=p*G; Bn=q*G
            a=[An>>(Z-i) for i in range(T+1)]
            b=[Bn>>(Z-i) for i in range(T+1)]
            events=events_from(a,b)
            h=ceil_log2(p+q+1)
            Ds=[q*x-p*y for x,y in zip(a,b)]
            E=h*(len(events)+1)
            assert sum(d!=0 for d in Ds)<=E
            R=4; n0=32
            for x in range(n0,T//R+1):
                k=bisect_right(events,x)
                assert k<len(events) and events[k]<=R*x
            chosen=choose_exact_levels(T,E,R,n0,lambda i:Ds[i]==0)
            total_cost=0
            for u,v in zip(chosen,chosen[1:]):
                shift=v-u
                U=a[v]-(a[u]<<shift)
                V=b[v]-(b[u]<<shift)
                assert 0<U<(1<<shift) and 0<V<(1<<shift)
                assert q*U==p*V
                c=U//p
                assert U==p*c and V==q*c and c>=1
                actual_cost=(U|V).bit_count()
                counted=bisect_right(events,v)-bisect_right(events,u)
                assert actual_cost==counted
                assert actual_cost>=2  # p!=q, so one joint bit is impossible.
                total_cost+=actual_cost
                checks+=1
            assert total_cost<=len(events)
            selected+=len(chosen)
            configs+=1
            if T==32768:
                examples.append(dict(p=p,q=q,T=T,K_T=len(events),h=h,
                                     bad_layers=sum(d!=0 for d in Ds),
                                     chosen_levels=chosen,return_event_cost=total_cost))
    return dict(configurations=configs, chosen_exact_levels=selected,
                exact_return_identities=checks, examples=examples,
                scope='actual rational floor prefixes; no claim of irrationality')


def check_product_arithmetic() -> dict:
    cases=0
    for _ in range(3000):
        alpha=F(RNG.randint(5,3000),RNG.randint(2,70))
        gamma=F(RNG.randint(1,500),RNG.randint(1,40))
        beta=gamma/alpha
        s=RNG.randint(2,40)
        a=floor_fraction((1<<s)*alpha)
        b=floor_fraction((1<<s)*beta)
        if not (a and b):
            continue
        error=gamma-F(a*b,1<<(2*s))
        assert error>=0
        if error:
            assert error >= F(1,gamma.denominator*(1<<(2*s)))
            cases+=1
    return dict(strict_nonzero_rational_product_separations=cases,
                scope='finite rational-value lattice separation, not Liouville theorem tests')


def check_approx_affine_rounding() -> dict:
    checked=triggered=violations_zero=0
    for _ in range(7000):
        s=RNG.randint(1,10); h=RNG.randint(1,10)
        a=RNG.randint(2,300); b=RNG.randint(2,300)
        # By construction the next h transitions of both columns are zero.
        den=1 << (s+h+5)
        alpha=F(a,1<<s)+F(RNG.randint(0,31),den)
        beta=F(b,1<<s)+F(RNG.randint(0,31),den)
        lam=RNG.randint(-6,6); mu=RNG.randint(-6,6)
        if lam==mu==0:
            continue
        value=lam*alpha+mu*beta
        c=floor_fraction(value+F(1,2))
        if c==0:
            continue
        epsilon=value-c
        bound=(1<<s)*abs(epsilon)+F(abs(lam)+abs(mu),1<<h)
        checked+=1
        if bound<1:
            assert lam*a+mu*b==c*(1<<s)
            d=gcd(a,b)
            odd=d//(d & -d)
            assert c%odd==0
            triggered+=1
    return dict(configurations=checked, strict_rounding_certificates=triggered)


def longest_run(bits: int) -> tuple[int,int]:
    """Return (least start, maximum number of consecutive set bits)."""
    if bits<=0:
        raise ValueError('nonempty subset-sum bitset required')
    powers=[bits]
    width=1
    while True:
        nxt=powers[-1] & (powers[-1]>>width)
        if not nxt:
            break
        powers.append(nxt); width*=2
    mask=powers[-1]; length=1<<(len(powers)-1)
    for k in range(len(powers)-2,-1,-1):
        candidate=mask & (powers[k]>>length)
        if candidate:
            mask=candidate
            length+=1<<k
    start=(mask & -mask).bit_length()-1
    return start,length


def sqrt_bounds(D: int, precision: int) -> tuple[F,F]:
    Q=1<<precision
    a=isqrt(D*Q*Q)
    if a*a==D*Q*Q:
        return F(a,Q),F(a,Q)
    return F(a,Q),F(a+1,Q)


def floors_from_bounds(interval: tuple[F,F], count: int) -> list[int]:
    lo,hi=interval
    out=[]
    for i in range(count+1):
        a,b=floor_fraction((1<<i)*lo),floor_fraction((1<<i)*hi)
        if a!=b:
            raise ArithmeticError(f'Insufficient exact enclosure at level {i}')
        out.append(a)
    return out


def check_irrational_enclosed_examples() -> list[dict]:
    # delta=sum_{j>=3}2^(-j!). Tail after 4! is bounded by 2^(-119).
    dl=F(1,1<<6)+F(1,1<<24)
    du=dl+F(1,1<<119)
    x=(F(33)+dl,F(33)+du)
    product_y=(F(1000)/x[1], F(1000)/x[0])
    root=sqrt_bounds(5000,180)
    sum_y=(root[0]-x[1],root[1]-x[0])
    cases=[('product_1000', x, product_y, 'alpha=33+delta, beta=1000/alpha'),
           ('sum_sqrt5000', sum_y, x, 'alpha=sqrt(5000)-(33+delta), beta=33+delta')]
    reports=[]
    for name,aa,bb,description in cases:
        a,b=floors_from_bounds(aa,22),floors_from_bounds(bb,22)
        assert b[0]<a[0]<2*b[0]
        bits=1; S=0; found=None
        for n in range(1,23):
            for weight in [b[n-1],a[n-1]]:
                bits |= bits<<weight; S+=weight
            start,length=longest_run(bits)
            if length-1>=b[n]:
                end=start+length-1
                fullmask=(1<<length)-1
                assert ((bits>>start)&fullmask)==fullmask
                assert S< a[n]+b[n]
                found=dict(name=name,parameters=description,n=n,A_next=a[n],B_next=b[n],
                           initial_pair=[a[0],b[0]],interval=[start,end],
                           width=length-1,integers_checked=length,
                           finite_sum=S,weight_count=2*n,
                           scope='exact rational enclosures, full integer bitset interval check')
                break
        if found is None:
            raise AssertionError('No finite interval located within implemented test depth')
        reports.append(found)
    return reports


def main() -> None:
    start=time.monotonic()
    results={
      'status':'PASS; finite checks only; infinite conclusions conditional on supplied FE and DB proofs',
      'defect_counts':check_defect_counts(),
      'abstract_packing':check_abstract_packing(),
      'actual_floor_return_packing':check_actual_returns(),
      'product_separation':check_product_arithmetic(),
      'approximate_affine_rounding':check_approx_affine_rounding(),
      'rank3_finite_interval_examples':check_irrational_enclosed_examples(),
      'limitations':[
          'No finite sample proves nu(p_j,q_j) tends to infinity; the compactness proof is required.',
          'No finite sample proves the bounded-ratio-gap hypothesis for an arbitrary infinite parameter.',
          'No limited search over multipliers is presented as an exact minimum for nu(p,q).',
          'The general Erdos #354 conjecture is not proved here.',
          'The new infinite results depend on earlier FE/DB arguments, not just their regression tests.'
      ]
    }
    results['elapsed_seconds']=round(time.monotonic()-start,3)
    results['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in sorted((ROOT/'prior_inputs').glob('*')) if p.is_file()}
    (ROOT/'results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(results,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
