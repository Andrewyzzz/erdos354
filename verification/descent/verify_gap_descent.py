"""Independent finite checks for persistent gap descent (Erdos #354 draft).

The universal proof is in proof.md. A finite homogeneous-linear certificate
proves its template lemma for every q<p<2q. Random/raw tests do not prove the
infinite theorem. All pass/fail checks use integers; no OCR or float tests.
"""
from __future__ import annotations
from itertools import product
from math import gcd
from pathlib import Path
from random import Random
import hashlib
import json

ROOT=Path(__file__).resolve().parent
BITS=((0,0),(0,1),(1,0),(1,1))
FIRST=((1,0),(0,1),(1,1))
SHIFTS=((0,0),(4,0),(0,4),(4,4))

def check(b: bool, text: str='assertion failed') -> None:
    if not b: raise AssertionError(text)

def add(a,b): return a[0]+b[0],a[1]+b[1]
def sub(a,b): return a[0]-b[0],a[1]-b[1]
def nn(a): return a[0]+a[1]>=0 and 2*a[0]+a[1]>=0
def pos(a): return a!=(0,0) and nn(a)
def val(a,p,q): return a[0]*p+a[1]*q

def symbolic_templates():
    records=json.loads((ROOT/'template_certificate.json').read_text())
    check({(tuple(z['first']),tuple(z['second'])) for z in records}==
          set(product(FIRST,BITS)))
    nodes=links=third_checks=0
    recovered=[]
    for rec in records:
        first=tuple(rec['first']); second=tuple(rec['second'])
        terms=[((1,0),first[0]),((0,1),first[1]),
               ((2,0),2*first[0]+second[0]),
               ((0,2),2*first[1]+second[1])]
        sums=[]
        for mask in range(16):
            a=(0,0); c=0
            for j,(v,e) in enumerate(terms):
                if mask>>j&1:a=add(a,v);c+=e
            sums.append((a,c))
        chain=[]
        for item in rec['chain']:
            v0,c0=sums[item['mask0']]; v1,c1=sums[item['mask1']]
            check(c1-c0==1)
            if nn(sub(v0,v1)):lo,hi=v0,add(v1,(1,1))
            else:
                check(nn(sub(v1,v0)));lo,hi=v1,add(v0,(1,1))
            shift=SHIFTS[item['third_mask']]
            lo,hi=add(lo,shift),add(hi,shift)
            check(pos(sub(hi,lo)))
            # Recompute from masks; stored endpoint fields are not trusted.
            check(list(lo)==item['lo'] and list(hi)==item['hi'])
            for third in BITS:
                a3=4*first[0]+2*second[0]+third[0]
                b3=4*first[1]+2*second[1]+third[1]
                tm=item['third_mask']
                e=(a3 if tm&1 else 0)+(b3 if tm&2 else 0)
                check(0<=c0+e<c1+e<=22);third_checks+=1
            chain.append((lo,hi));nodes+=1
        check(nn(sub((1,2),chain[0][0])))
        check(nn(sub(chain[-1][1],(7,6))))
        for (lo,hi),(lo2,hi2) in zip(chain,chain[1:]):
            check(pos(sub(hi,lo2)) and pos(sub(hi2,lo)));links+=1
        recovered.append({'first':first,'second':second,'chain':chain})
    return {'templates':len(records),'nodes':nodes,'strict_links':links,
            'third_digit_checks':third_checks}, recovered

def sum_bits(weights, initial=1):
    out=initial
    for z in weights:
        check(isinstance(z,int) and z>=0)
        out |= out<<z
    return out

def rotate(bits,step,m):
    step%=m
    mask=(1<<m)-1
    return bits if not step else ((bits<<step)&mask)|(bits>>(m-step))

def residues(weights,m):
    check(m>=1)
    mask=(1<<m)-1;r=1
    for x in weights:
        r|=rotate(r,x,m)
        if r==mask:break
    return r

def linear_holes(bits,length):
    h=((1<<length)-1)^bits;run=0
    while h:
        h &= h<<1;run+=1
    return run

def cyclic_holes(bits,m):
    check(bits!=0 and bits.bit_length()<=m)
    h=((1<<m)-1)^bits;run=0
    while h:
        h &= rotate(h,1,m);run+=1
        check(run<m)
    return run

def gap(bits):
    check(bits>0)
    lo=(bits&-bits).bit_length()-1;hi=bits.bit_length()-1
    return linear_holes(bits>>lo,hi-lo+1)+1

def prefix(A,B,n):
    return [x>>(n-i) for i in range(n) for x in (A,B)]

def thresholds(p,q,d,S):
    check(gcd(p,q)==1 and q<p<2*q and 0<=S<d*(p+q))
    f=q*(p-1);k0=2*f+4*(p+q)+64
    K=1<<(k0-1).bit_length();ell=K.bit_length()-1
    trim=S+d*(f+p+q)+22
    check(d*K-2*trim>=64*d-42>=22*d)
    check(k0<=16*p*p)
    left=d*K*(p+2*q)+trim;right=d*K*(7*p+6*q)-trim
    check(right-left-(8*d*K*q+15)>=22*d-15)
    return K,ell,trim,left,right

def new_terms(p,q,d,K,digits):
    a,b=d*K*p,d*K*q;out=[]
    for i,(u,v) in enumerate(digits):
        if i:a,b=2*a+u,2*b+v
        else:a,b=a+u,b+v
        out.extend((a,b))
    return out,a,b

def check_raw(E,S,p,q,d,digits,actual_weights=None):
    """All representation calculations retain the exact old set/weights."""
    K,ell,trim,left,right=thresholds(p,q,d,S)
    mask0=0
    for x in E:mask0|=1<<(x%d)
    H=cyclic_holes(mask0,d);kappa=max(1,H)
    check(1<=kappa<=d)
    check(cyclic_holes(mask0|rotate(mask0,1,d),d)<=kappa-1)
    block=[d*z*(1<<i) for i in range(ell) for z in (p,q)]
    news,a,b=new_terms(p,q,d,K,digits)
    initial=0
    for x in E:initial |= 1<<x
    ss=sum_bits(block+news,initial)
    length=right-left+1
    chunk=(ss>>left)&((1<<length)-1)
    check(linear_holes(chunk,length)<=kappa-1,
          f'mesh failure {(p,q,d,H,digits)}')
    lo=(chunk&-chunk).bit_length()-1;hi=chunk.bit_length()-1
    check(lo<=kappa-1 and length-1-hi<=kappa-1)
    check(gap(chunk)<=kappa)
    check(hi-lo>8*d*K*q+15)
    check(hi-lo>2*b+1)
    return {'positions':length,'H':H,'kappa':kappa,
            'left':left,'right':right,'K':K,'ell':ell,
            'span':hi-lo,'max_gap':gap(chunk),'a_last':a,'b_last':b,
            'weights': (actual_weights+block+news if actual_weights is not None else None)}

def exhaustive_group_erasure():
    erasures=0
    for m in range(1,12):
        for X in range(1,1<<m):
            h=cyclic_holes(X,m)
            check(cyclic_holes(X|rotate(X,1,m),m)==max(0,h-1))
            erasures+=1
    return {'all_nonempty_cyclic_sets':erasures}

def mesh_propagation_tests():
    unions=projections=0
    # All nonempty finite subsets with endpoints 0 and w up to span 11.
    for w in range(1,12):
        for interior in range(1<<(w-1)):
            A=1|(1<<w)|(interior<<1)
            h=gap(A)
            for c in range(1,w+1):
                B=A|(A<<c)
                check(gap(B)<=h)
                check(B.bit_length()-1==w+c)
                unions+=1
            aset=[i for i in range(w+1) if A>>i&1]
            for m in range(1,w+1):
                r=0
                for x in aset:r |= 1<<(x%m)
                check(cyclic_holes(r,m)<=h-1)
                projections+=1
    return {'finite_mesh_union_cases':unions,'mesh_to_modulus_cases':projections}

def raw_abstract_tests():
    rng=Random(3540912);count=positions=nonisolated=0
    slopes=[(3,2),(4,3),(5,3),(5,4),(7,4),(7,5)]
    # E can be any nonempty set. In particular no majority is assumed.
    for _ in range(160):
        p,q=rng.choice(slopes);d=rng.randrange(1,25)
        X={rng.randrange(d)}|{i for i in range(d) if rng.randrange(4)==0}
        E=sorted({r+d*rng.randrange(p+q) for r in X})
        S=max(E)
        for first in FIRST:
            z=check_raw(E,S,p,q,d,(first,rng.choice(BITS),rng.choice(BITS)))
            count+=1;positions+=z['positions'];nonisolated+=z['H']>=2
    return {'arbitrary_old_sets_and_digits':count,'nonisolated_cases':nonisolated,
            'raw_window_positions_checked':positions}

def genuine_tests():
    # Includes empty/sparse, non-majority and genuinely adjacent-hole inputs.
    starts=[(0,12,8),(0,21,14),(4,195,156),(4,159,106),
            (5,471,314),(3,35,28),(3,30,20)]
    rng=Random(35444);count=positions=later=0;reports=[]
    for n,A,B in starts:
        d=gcd(A,B);p,q=A//d,B//d
        old=prefix(A,B,n);bs=sum_bits(old);S=sum(old)
        E=[i for i in range(S+1) if bs>>i&1]
        H=cyclic_holes(residues(old,d),d)
        for first,second,third in product(FIRST,BITS,BITS):
            z=check_raw(E,S,p,q,d,(first,second,third),old)
            count+=1;positions+=z['positions']
            vals=z['weights'];a=z['a_last'];b=z['b_last']
            for depth in range(7):
                u,v=rng.choice(BITS);a,b=2*a+u,2*b+v
                dd=gcd(a,b)
                rr=residues(vals,dd)
                check(cyclic_holes(rr,dd)<=max(0,H-1))
                vals.extend((a,b));later+=1
        reports.append({'n':n,'A':A,'B':B,'d':d,'old_missing_run':H,
                        'old_size':len(E),'old_window':A+B,'templates':48})
    return {'genuine_prefix_digit_templates':count,
            'genuine_window_positions_checked':positions,
            'later_actual_modulus_states':later,'starts':reports}

def sharp_drop_example():
    n,A,B=0,12,8;d=4;p,q=3,2;S=0;E=[0]
    z=check_raw(E,S,p,q,d,((1,1),(1,0),(0,0)),[])
    a,b=2*z['a_last'],2*z['b_last'];e=gcd(a,b)
    rr=residues(z['weights'],e)
    check(e==4100 and cyclic_holes(rr,e)==2 and e-rr.bit_count()==1052)
    return {'old_endpoint':[A,B],'old_modulus':d,'old_holes':3,
            'old_longest_missing_run':3,'ell':z['ell'],
            'first_three_digits':[[1,1],[1,0],[0,0]],
            'new_endpoint_after_next_00':[a,b],'new_modulus':e,
            'new_holes':e-rr.bit_count(),'new_longest_missing_run':2,
            'scope':'Hole count grows, longest run strictly drops. This is a rational finite control, not an irrationality claim.'}

def main():
    symbolic,_=symbolic_templates()
    print('symbolic templates independently checked',flush=True)
    erasure=exhaustive_group_erasure();print('cyclic erosion checked',flush=True)
    meshes=mesh_propagation_tests();print('mesh propagation/projection checked',flush=True)
    abstract=raw_abstract_tests();print('arbitrary old sets checked',flush=True)
    genuine=genuine_tests();print('genuine prefixes and future moduli checked',flush=True)
    sharp=sharp_drop_example()
    out={'status':'Finite verification accompanying an unreviewed complete-proof draft. The infinite conclusion is proved in proof.md, NOT inferred from these finite samples.',
         'symbolic':symbolic,'erosion':erasure,'propagation':meshes,
         'abstract':abstract,'genuine':genuine,'sharpness_control':sharp,
         'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in [Path(__file__),ROOT/'template_certificate.json']}}
    (ROOT/'results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(out,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
