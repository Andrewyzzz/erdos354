"""Build the actual default target and reject non-allowlisted transitive axioms.

--fresh recompiles this project's modules in a new directory, reusing the exact
pinned Mathlib dependency cache. It is not a from-source Mathlib rebuild.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(command, cwd, name):
    path = ROOT / 'logs' / (name + '.log')
    start = time.monotonic()
    with path.open('w') as out:
        out.write('COMMAND: ' + json.dumps(command) + '\n')
        out.write('CWD: ' + str(cwd) + '\n')
        out.write('UTC: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
        out.flush()
        proc = subprocess.run(command, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        out.write(f'\nEXIT CODE: {proc.returncode}\nELAPSED SECONDS: {time.monotonic()-start:.3f}\n')
    print(f'{name}: exit {proc.returncode}; {path}', flush=True)
    if proc.returncode:
        print(path.read_text())
        raise SystemExit(proc.returncode)
    return path.read_text()


parser = argparse.ArgumentParser()
parser.add_argument('--fresh', action='store_true')
args = parser.parse_args()
(ROOT / 'logs').mkdir(exist_ok=True)
result_path = ROOT / 'logs' / ('fresh-verification.json' if args.fresh else 'verification.json')
result_path.write_text(json.dumps({'status': 'INCOMPLETE',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}) + '\n')
run(['python3', 'scripts/generate_data.py', '--check'], ROOT, 'data-consistency')
project = ROOT
prefix = ''
if args.fresh:
    fresh = Path(tempfile.mkdtemp(prefix='erdos354-lean-clean-'))
    project = fresh / 'formalization'
    shutil.copytree(ROOT, project, ignore=shutil.ignore_patterns('.lake', 'logs', '__pycache__'))
    (project / '.lake').mkdir()
    (project / '.lake' / 'packages').symlink_to((ROOT / '.lake' / 'packages').resolve(), target_is_directory=True)
    prefix = 'fresh-'
    print(f'Fresh source directory: {project}; only dependency cache reused.', flush=True)
run(['lake', 'build'], project, prefix + 'build')
output = run(['lake', 'env', 'lean', 'Dyadic354/Audit.lean'], project, prefix + 'axioms')
expected = set(re.findall(r'^#print axioms (\S+)', (ROOT / 'Dyadic354/Audit.lean').read_text(), re.M))
declared = set()
for source in sorted((ROOT / 'Dyadic354').glob('*.lean')):
    namespaces = []
    for line in source.read_text().splitlines():
        if match := re.match(r'^namespace ([\w.]+)\s*$', line):
            namespaces.append(match[1])
        elif re.match(r'^end(?:\s+[\w.]+)?\s*$', line):
            if namespaces:
                namespaces.pop()
        elif match := re.match(r'^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)', line):
            declared.add('.'.join(namespaces + [match[1]]))
if declared != expected:
    raise SystemExit(f'Audit inventory mismatch: missing={sorted(declared-expected)}, extra={sorted(expected-declared)}')
records = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
    records[name] = {x.strip() for x in axioms.split(',') if x.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
    records[name] = set()
missing = expected - records.keys()
bad = {k: sorted(v - ALLOWED) for k, v in records.items() if v - ALLOWED}
if missing or bad:
    raise SystemExit(f'Axiom audit failed: missing={sorted(missing)}, disallowed={bad}')
result = {
    'status': 'PASS',
    'scope': 'Finite certificate and three mesh lemmas with iterated propagation; not Erdős 354(i).',
    'fresh_project_build': args.fresh,
    'dependency_cache_reused': True,
    'audited_theorems': len(records),
    'allowed_axioms': sorted(ALLOWED),
    'axioms': {k: sorted(v) for k, v in sorted(records.items())},
    'source_sha256': {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted([*ROOT.glob('*.lean'), *(ROOT / 'Dyadic354').glob('*.lean'),
                         ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json'])
    },
}
result_path.write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS: {len(records)} audited theorems; only allowlisted transitive axioms.', flush=True)
