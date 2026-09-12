"""Portable finite symbolic certificate checker.

Adapted from the separately implemented review-reconciliation checker. Reads the
Markdown masks, reconstructs all coefficients, and compares with the certificate.
Does not import the original verifiers or certify the infinite theorem.
"""
from __future__ import annotations
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'proof/PROOF.zh-CN.md'
if not __debug__:
    raise SystemExit('Run without -O: certificate checks use assertions.')
text = SOURCE.read_text(encoding='utf-8')


def plus(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0]+b[0], a[1]+b[1]


def minus(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0]-b[0], a[1]-b[1]


def nonnegative(a: tuple[int, int]) -> bool:
    # p=2x+y, q=x+y, x,y>0. These two coefficients characterize
    # nonnegativity over the closed cone q <= p <= 2q.
    return 2*a[0]+a[1] >= 0 and a[0]+a[1] >= 0


def positive(a: tuple[int, int]) -> bool:
    return a != (0,0) and nonnegative(a)


def masked(mask: int, data: list[tuple[int,int,int]]) -> tuple[tuple[int,int],int]:
    terms=[entry for i,entry in enumerate(data) if (mask >> i) & 1]
    return (sum(v[0] for v in terms),sum(v[1] for v in terms)),sum(v[2] for v in terms)

rows=[]
for line in text.splitlines():
    if not line.startswith('|(') or '`[' not in line:
        continue
    cells=line.split('|')
    first=ast.literal_eval(cells[1].strip())
    second=ast.literal_eval(cells[2].strip())
    chain=ast.literal_eval(cells[3].strip().strip('`'))
    rows.append((first,second,chain))
assert len(rows)==12
nodes=links=third_node_checks=0
for (u1,v1),(u2,v2),chain in rows:
    intervals=[]
    first_four=[(1,0,u1),(0,1,v1),(2,0,2*u1+u2),(0,2,2*v1+v2)]
    for mask0,mask1,mask3 in chain:
        a,c0=masked(mask0,first_four)
        b,c1=masked(mask1,first_four)
        assert c1-c0==1
        shift=((4 if mask3&1 else 0),(4 if mask3&2 else 0))
        a,b=plus(a,shift),plus(b,shift)
        if nonnegative(minus(a,b)):
            lo,hi=a,plus(b,(1,1))
        elif nonnegative(minus(b,a)):
            lo,hi=b,plus(a,(1,1))
        else:
            raise AssertionError('Coefficient order crosses in the cone')
        assert positive(minus(hi,lo))
        intervals.append((lo,hi))
        for u3,v3 in [(0,0),(0,1),(1,0),(1,1)]:
            c3=(4*u1+2*u2+u3 if mask3&1 else 0)+(4*v1+2*v2+v3 if mask3&2 else 0)
            assert 0 <= c0+c3 < c1+c3 <=22
            third_node_checks+=1
        nodes+=1
    assert nonnegative(minus((1,2),intervals[0][0]))
    assert nonnegative(minus(intervals[-1][1],(7,6)))
    for (lo1,hi1),(lo2,hi2) in zip(intervals,intervals[1:]):
        assert positive(minus(hi1,lo2))
        assert positive(minus(hi2,lo1))
        links+=1


# Confirm both Markdown appendices contain exactly the JSON masks.
records=json.loads((ROOT/'certificate/templates.json').read_text(encoding='utf-8'))
expected={(tuple(r['first']),tuple(r['second'])):[(n['mask0'],n['mask1'],n['third_mask']) for n in r['chain']] for r in records}
actual={(a,b):list(map(tuple,c)) for a,b,c in rows}
assert len(expected)==len(actual)==12 and expected==actual
from itertools import product
assert set(actual)==set(product(((1,0),(0,1),(1,1)),((0,0),(0,1),(1,0),(1,1))))
checked=[str(SOURCE.relative_to(ROOT))]
for rel in ['archive/FROZEN_20260912.zh-CN.md','proof/PROOF.md']:
    other=ROOT/rel
    if not other.exists():
        continue
    other_rows={}
    for line in other.read_text(encoding='utf-8').splitlines():
        if line.startswith('|(') and '`[' in line:
            fields=line.split('|')
            key=(tuple(ast.literal_eval(fields[1].strip())),tuple(ast.literal_eval(fields[2].strip())))
            other_rows[key]=list(map(tuple,ast.literal_eval(fields[3].strip().strip('`'))))
    assert other_rows==expected, rel
    checked.append(rel)
print(json.dumps({'status':'PASS: finite symbolic certificate only',
    'templates':len(rows),'nodes':nodes,'strict_overlaps':links,
    'third_digit_instances':third_node_checks,'appendices_checked':checked,
    'certificate_sha256':hashlib.sha256((ROOT/'certificate/templates.json').read_bytes()).hexdigest(),
    'scope':'This is not formal verification of the infinite theorem or FE/DB arguments.'},indent=2))
