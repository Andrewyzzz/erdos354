"""Run a command, preserving complete stdout/stderr and its actual exit code."""
import datetime
import json
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
name, *command = sys.argv[1:]
log = root / 'logs' / (name + '.log')
log.parent.mkdir(exist_ok=True)
start = time.monotonic()
with log.open('w') as out:
    out.write('COMMAND: ' + json.dumps(command) + '\n')
    out.write('UTC: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
    out.flush()
    result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    out.write(f'\nEXIT CODE: {result.returncode}\nELAPSED SECONDS: {time.monotonic()-start:.3f}\n')
print(log.read_text())
raise SystemExit(result.returncode)
