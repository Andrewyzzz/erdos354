"""Mechanically publish tracked historical logs with machine-local paths redacted."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from public_logs import publish_log, redact


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    cache = (root / 'formalization/.lake/packages').resolve()
    paths = subprocess.check_output(
        ['git', 'ls-files', '-z', 'formalization/logs/*.log'], cwd=root
    ).decode().split('\0')
    record_path = root / 'formalization/logs/redaction.json'
    record = json.loads(record_path.read_text()) if record_path.exists() else {
        'format': 'Machine-local path substitution; diagnostic lines and exit statuses retained.',
        'original_records_commit': '787719cf2b93c321e8022f382591d5590144dd6d',
        'files': {},
    }
    pending = []
    for relative in sorted(filter(None, paths)):
        path = root / relative
        original = path.read_text()
        if redact(original, root, cache) == original:
            continue
        pending.append(relative)
        if args.write:
            public = publish_log(original, root, cache)
            entry = record['files'].setdefault(relative, {
                'original_sha256': hashlib.sha256(original.encode()).hexdigest(),
            })
            entry['public_sha256'] = hashlib.sha256(public.encode()).hexdigest()
            path.write_text(public)
    if args.write:
        record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
        print(f'Published {len(pending)} historical logs; provenance recorded in formalization/logs/redaction.json')
    else:
        if pending:
            raise SystemExit('Machine-local paths remain in: ' + ', '.join(pending))
        for relative, entry in record['files'].items():
            actual = hashlib.sha256((root / relative).read_bytes()).hexdigest()
            if actual != entry['public_sha256']:
                raise SystemExit('Published log hash mismatch: ' + relative)
        print(f'PASS: tracked logs contain no recognized machine-local paths; {len(record["files"])} redaction hashes match')


if __name__ == '__main__':
    main()
