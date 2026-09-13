"""Build the default target and audit every local theorem, including final targets.

--fresh rebuilds this project's sources in a new directory, reusing only the
pinned dependency cache. It is not a from-source rebuild of Lean or Mathlib.
Public logs redact machine-local paths, with the transformation stated explicitly.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time

from audit_checks import ALLOWED, TARGETS, check_output, inventory
from public_logs import NOTICE, redact

ROOT = Path(__file__).resolve().parents[1]
FROZEN_STATEMENTS = '623b20bab06c99013dcbefed752aa80ce29a879930eefc1d069e4944bc5ceb0e'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, name, log_directory):
    path = log_directory / (name + '.log')
    start = time.monotonic()
    raw_lines = []
    cache = (ROOT / '.lake/packages').resolve()

    def public(text):
        return redact(text, ROOT.parent, cache)

    with path.open('w', encoding='utf-8') as out:
        out.write(NOTICE)
        out.write('COMMAND: ' + public(json.dumps(command)) + '\n')
        out.write('CWD: ' + public(str(cwd)) + '\n')
        out.write('UTC: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
        out.flush()
        proc = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, encoding='utf-8',
                                errors='replace')
        for line in proc.stdout:
            raw_lines.append(line)
            out.write(public(line))
            out.flush()
        code = proc.wait()
        out.write(f'\nEXIT CODE: {code}\nELAPSED SECONDS: {time.monotonic()-start:.3f}\n')
    print(f'{name}: exit {code}; {public(str(path))}', flush=True)
    if code:
        print(path.read_text(encoding='utf-8'))
        raise SystemExit(code)
    return ''.join(raw_lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--log-directory', default='logs',
                        help='Output directory, relative to formalization/ unless absolute.')
    args = parser.parse_args()
    log_directory = ROOT / args.log_directory
    log_directory.mkdir(parents=True, exist_ok=True)
    result_path = log_directory / ('fresh-verification.json' if args.fresh else 'verification.json')
    result_path.write_text(json.dumps({
        'status': 'INCOMPLETE',
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }) + '\n')

    if digest(ROOT / 'Dyadic354/Statements.lean') != FROZEN_STATEMENTS:
        raise SystemExit('Frozen mathematical target definitions have changed.')
    lean_sources = sorted([*ROOT.glob('*.lean'), *(ROOT / 'Dyadic354').rglob('*.lean')])
    for source in lean_sources:
        if re.search(r'\b(?:sorry|admit|native_decide|axiom|unsafe|skipKernelTC|implemented_by|extern)\b|\+native',
                     source.read_text()):
            raise SystemExit(f'Forbidden proof mechanism or placeholder: {source.relative_to(ROOT)}')
    expected = inventory(
        [source.read_text() for source in sorted((ROOT / 'Dyadic354').glob('*.lean'))],
        (ROOT / 'Dyadic354/Audit.lean').read_text(),
    )

    run(['python3', 'scripts/generate_data.py', '--check'], ROOT, 'data-consistency', log_directory)
    run(['python3', 'scripts/check_upstream.py'], ROOT, 'upstream-consistency', log_directory)
    run(['python3', 'scripts/inspect_environment.py'], ROOT, 'environment', log_directory)
    project = ROOT
    prefix = ''
    if args.fresh:
        fresh = Path(tempfile.mkdtemp(prefix='erdos354-lean-clean-'))
        project = fresh / 'formalization'
        shutil.copytree(ROOT, project, ignore=shutil.ignore_patterns('.lake', 'logs', '__pycache__'))
        (project / '.lake').mkdir()
        (project / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(),
                                               target_is_directory=True)
        prefix = 'fresh-'
        print('Fresh source directory: $FRESH_PROJECT; only dependency cache reused.', flush=True)
    run(['lake', 'build'], project, prefix + 'build', log_directory)
    output = run(['lake', 'env', 'lean', 'Dyadic354/Audit.lean'], project,
                 prefix + 'axioms', log_directory)
    records = check_output(output, expected)
    git_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                         text=True).strip()
    git_dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'],
                                            cwd=ROOT, text=True).strip())
    run_url = None
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        run_url = (f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/"
                   f"{os.environ['GITHUB_RUN_ID']}")
    result = {
        'status': 'PASS',
        'scope': 'The frozen positive statement of Erdos 354(i) and strong set completeness, '
                 'for all positive real parameters with irrational ratio. No additional '
                 'FE/DB/BG, normalization, long-window, or descent hypotheses. '
                 'Includes the exact extracted-upstream-definition adapter, compiled under '
                 'the pinned Lean 4.27.0 project environment.',
        'completed_targets': sorted(TARGETS),
        'git_commit': git_commit,
        'git_worktree_dirty': git_dirty,
        'ci_run_url': run_url,
        'platform': platform.platform(),
        'fresh_project_build': args.fresh,
        'dependency_cache_reused': True,
        'log_redaction': 'Machine-local paths replaced by symbolic locations; no diagnostic lines removed.',
        'audited_theorems': len(records),
        'allowed_axioms': sorted(ALLOWED),
        'axioms': {name: sorted(value) for name, value in sorted(records.items())},
        'source_sha256': {
            str(path.relative_to(ROOT)): digest(path)
            for path in sorted([
                *lean_sources, ROOT / 'lean-toolchain', ROOT / 'lakefile.toml',
                ROOT / 'lake-manifest.json', *(ROOT / 'upstream').glob('*'),
                *(ROOT / 'scripts').glob('*.py'),
            ])
        },
    }
    result_path.write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: {len(records)} audited theorems; only allowlisted transitive axioms.', flush=True)


if __name__ == '__main__':
    main()
