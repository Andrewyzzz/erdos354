#!/usr/bin/env python3
"""Stage this package in the exact user-specified repository; push only with --push.

No force push, permission/visibility change, credential handling, or remote deletion.
Differing existing remote files are NOT overwritten. Requires local Git auth.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

SOURCE = Path(__file__).resolve().parents[1]
REPO = 'Andrewyzzz/erdos354'
URL = f'https://github.com/{REPO}.git'


def git(*args: str, cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    p = subprocess.run(['git', *args], cwd=cwd, text=True, capture_output=True)
    if check and p.returncode:
        raise RuntimeError(p.stderr.strip() or p.stdout.strip() or 'Git command failed')
    return p


def normalize(url: str) -> str:
    return url.removesuffix('.git').removesuffix('/').replace('git@github.com:', 'https://github.com/')


def package_files() -> list[Path]:
    manifest = json.loads((SOURCE/'MANIFEST.sha256.json').read_text(encoding='utf-8'))
    paths = []
    for rel, expected in manifest['files'].items():
        src = (SOURCE/rel).resolve()
        if SOURCE not in src.parents or not src.is_file():
            raise RuntimeError(f'Invalid or missing package path: {rel}')
        if hashlib.sha256(src.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'Integrity mismatch: {rel}')
        paths.append(src)
    paths.append(SOURCE/'MANIFEST.sha256.json')
    return paths


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', required=True, type=Path, help='new checkout directory, or this helper\'s already prepared checkout')
    parser.add_argument('--push', action='store_true', help='push the prepared commit (never force)')
    args = parser.parse_args()
    if not shutil.which('git'):
        raise RuntimeError('Git is required. No credentials are provided by this package.')
    files = package_files()
    dst = args.destination.expanduser().resolve()
    if dst == SOURCE or SOURCE in dst.parents or dst in SOURCE.parents:
        raise RuntimeError('Choose a checkout outside the release package.')
    if not dst.exists():
        dst.parent.mkdir(parents=True, exist_ok=True)
        git('clone', URL, str(dst))
    if not (dst/'.git').is_dir():
        raise RuntimeError('Destination must be an ordinary clone of the exact target repository.')
    remote = git('remote', 'get-url', 'origin', cwd=dst).stdout.strip()
    if normalize(remote) != normalize(URL):
        raise RuntimeError(f'Refusing different origin: {remote}')
    if git('status', '--porcelain', cwd=dst).stdout.strip():
        raise RuntimeError('Checkout has uncommitted changes; inspect them before rerunning.')
    conflicts = []
    for src in files:
        rel = src.relative_to(SOURCE)
        target = dst/rel
        if target.is_symlink() or (target.exists() and (not target.is_file() or target.read_bytes() != src.read_bytes())):
            conflicts.append(str(rel))
        # Refuse symlink parents, preventing writes outside the clone.
        parent = target.parent
        while parent != dst:
            if parent.is_symlink():
                conflicts.append(str(rel) + ' (symlink parent)')
                break
            parent = parent.parent
    if conflicts:
        raise RuntimeError('Existing files differ; nothing was overwritten. Reconcile first:\n'+'\n'.join(conflicts))
    for src in files:
        target = dst/src.relative_to(SOURCE)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, target)
    git('add', '--', *[str(p.relative_to(SOURCE)) for p in files], cwd=dst)
    staged = git('diff', '--cached', '--quiet', cwd=dst, check=False)
    if staged.returncode == 1:
        git('commit', '-m', 'Add v0.1.0-candidate: Erdős 354(i) proof and finite certificates', cwd=dst)
    elif staged.returncode != 0:
        raise RuntimeError('Could not inspect the staged diff.')
    sha = git('rev-parse', 'HEAD', cwd=dst).stdout.strip()
    print(f'Prepared checkout: {dst}\nCommit: {sha}')
    if args.push:
        branch = git('symbolic-ref', '--short', 'HEAD', cwd=dst).stdout.strip()
        git('push', '-u', 'origin', f'HEAD:refs/heads/{branch}', cwd=dst)
        print(f'Pushed without force: https://github.com/{REPO}/commit/{sha}')
        print('Verify anonymous public access before linking from the forum.')
    else:
        print('Not pushed. Inspect the commit; rerun with --push to upload.')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        raise SystemExit(1)
