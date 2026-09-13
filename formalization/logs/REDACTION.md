# Public log format

We retain the command output, mathematical diagnostics, goal contexts, exit
statuses, timings, and source hashes of the recorded verification runs.
For public distribution, we replace machine-local filesystem paths with
symbolic locations:

| Symbol | Meaning |
|---|---|
| `$REPOSITORY` | The repository checkout |
| `$DEPENDENCY_CACHE` | The pinned local dependency cache |
| `$FRESH_PROJECT` | A fresh formalization source directory |
| `$ELAN_HOME` | The local Elan toolchain directory |
| `$TEMPORARY` | A temporary filesystem location |
| `$LOCAL_PATH` | Another machine-local path |

Changed logs begin with a formatting notice. No diagnostic lines are
removed, and failed compilation iterations remain in the record.
Machine-readable verification reports retain their recorded source hashes.

[redaction.json](redaction.json) lists the before-and-after SHA-256 hashes
of the transformed historical logs. These are formatting changes to
existing records, not new verification runs. The original bytes remain
available in the earlier Git history; this transformation does not rewrite
that history.

New verification runs apply the same path substitutions when writing logs.
The implementation is in [public_logs.py](../scripts/public_logs.py).
To check the tracked historical logs, run from `formalization/`:

```sh
python3 scripts/sanitize_logs.py --check
```
