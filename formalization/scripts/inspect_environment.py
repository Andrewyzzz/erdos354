"""Record actual local versions, frozen mathematical inputs and pinned dependencies."""
import hashlib
import json
from pathlib import Path
import platform
import subprocess

root = Path(__file__).resolve().parents[1]
commands = [
    ['pwd'], ['git', 'status', '--short', '--branch'], ['git', 'rev-parse', 'HEAD'],
    ['lean', '--version'], ['lake', '--version'], ['elan', 'show'],
]
for cmd in commands:
    print('$ ' + ' '.join(cmd), flush=True)
    result = subprocess.run(cmd, cwd=root)
    print('exit:', result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
print('PLATFORM:', platform.platform(), platform.machine())
for rel in ['proof/PROOF.md', 'proof/PROOF.zh-CN.md', 'certificate/templates.json', 'certificate/check_templates.py']:
    print('INPUT SHA256:', rel, hashlib.sha256((root.parent / rel).read_bytes()).hexdigest())
manifest = json.loads((root / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    path = root / '.lake/packages' / package['name']
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
    print('DEPENDENCY:', package['name'], 'locked=', package['rev'], 'actual=', actual, 'tracked_changes=', bool(dirty))
    if actual != package['rev'] or dirty:
        raise SystemExit('Dependency revision mismatch or modified tracked source.')
print('CACHE:', (root / '.lake/packages').resolve())
