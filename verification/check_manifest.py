#!/usr/bin/env python3
"""Verify package bytes, not mathematical correctness. No network or writes."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'MANIFEST.sha256.json').read_text(encoding='utf8'))
errors=[]
for rel, expected in data['files'].items():
    p=(ROOT/rel).resolve()
    if ROOT not in p.parents or not p.is_file():
        errors.append(rel+': missing or invalid path')
    elif hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
        errors.append(rel+': hash mismatch')
if errors:
    raise SystemExit('\n'.join(errors))
print(f'PASS: {len(data["files"])} file hashes match (integrity only).')
