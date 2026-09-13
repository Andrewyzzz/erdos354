"""Check frozen upstream bytes, verbatim definitions and the exact target RHS.

The .txt snapshots are provenance data, never Lean imports. Their upstream
conjecture placeholders are not dependencies. --online additionally checks the
bytes against the pinned public GitHub commit; normal builds work offline.
This syntactic check supplements, not replaces, the kernel-checked bridge.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--online', action='store_true')
args = parser.parse_args()
lock = json.loads((root / 'upstream/lock.json').read_text())
sources = {}
for local, record in lock['files'].items():
    raw = (root / 'upstream' / local).read_bytes()
    if hashlib.sha256(raw).hexdigest() != record['sha256']:
        raise SystemExit(f'Frozen upstream hash mismatch: {local}')
    if args.online:
        url = ('https://raw.githubusercontent.com/google-deepmind/formal-conjectures/'
               + lock['commit'] + '/' + record['path'])
        online = subprocess.check_output(['curl', '-LfsS', url])
        if online != raw:
            raise SystemExit(f'Pinned upstream content mismatch: {local}')
    sources[local] = raw.decode()
    print(f'PASS upstream bytes: {local} sha256={record["sha256"]}')

local = (root / 'Dyadic354/UpstreamDefinitions.lean').read_text()


def block(source, name):
    pattern = r'^(?:noncomputable )?def ' + re.escape(name) + r'(?=\s).*?(?=\n\n|\Z)'
    found = re.findall(pattern, source, re.M | re.S)
    if len(found) != 1:
        raise SystemExit(f'Expected exactly one definition: {name}')
    return found[0].rstrip('\n')


for filename, names in [
    ('354.lean.txt', ['FloorMultiples', 'FloorMultiples.interleave']),
    ('AdditivelyComplete.lean.txt', ['subsetSums', "subseqSums'", 'IsAddComplete',
                                   'IsAddStronglyComplete', "IsAddCompleteNatSeq'"]),
]:
    for name in names:
        if block(sources[filename], name) != block(local, name):
            raise SystemExit(f'Upstream definition was changed: {name}')
        print(f'PASS verbatim definition: {name}')

upstream = re.search(r'theorem erdos_354\.parts\.i : answer\(sorry\) ↔ (.*?) := by',
                     sources['354.lean.txt'], re.S).group(1)
bridge = (root / 'Dyadic354/UpstreamBridge.lean').read_text()
target = re.search(r'def PartITarget : Prop := (.*?)\n\n', bridge, re.S).group(1)
# Qualification is required outside the upstream Erdos354 namespace.
target = target.replace('Erdos354.FloorMultiples', 'FloorMultiples')
if re.sub(r'\s+', ' ', target).strip() != re.sub(r'\s+', ' ', upstream).strip():
    raise SystemExit('PartITarget differs from the pinned upstream positive RHS')
print('PASS exact positive part (i) target, modulo whitespace and namespace qualification.')
print('Upstream toolchain:', sources['lean-toolchain.txt'].strip())
print('Integration mode: exact definition extraction on local Lean; not a full upstream checkout build.')
