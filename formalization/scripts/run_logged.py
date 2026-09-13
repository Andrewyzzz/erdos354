"""Run a command, preserving complete stdout/stderr and its actual exit code."""
import datetime
import json
from pathlib import Path
import subprocess
import sys
import time
from public_logs import NOTICE, redact

root = Path(__file__).resolve().parents[1]
name, *command = sys.argv[1:]
log = root / 'logs' / (name + '.log')
log.parent.mkdir(exist_ok=True)
start = time.monotonic()
with log.open('w') as out:
    cache = (root / '.lake/packages').resolve()
    out.write(NOTICE)
    out.write('COMMAND: ' + redact(json.dumps(command), root.parent, cache) + '\n')
    out.write('UTC: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
    out.flush()
    result = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True)
    for line in result.stdout:
        out.write(redact(line, root.parent, cache))
        out.flush()
    code = result.wait()
    out.write(f'\nEXIT CODE: {code}\nELAPSED SECONDS: {time.monotonic()-start:.3f}\n')
print(log.read_text())
raise SystemExit(code)
