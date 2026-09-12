# Erdős Problem 354(i) — candidate proof

**Two dyadic floor sequences are claimed to be strongly complete.**

Version: **v0.1.0-candidate** · Package prepared: **12 September 2026**  
Contributors: **Andrew Y and ChatGPT (AI system)** · Human maintainer: **[@Andrewyzzz](https://github.com/Andrewyzzz)**

> **Status:** complete candidate argument, released for independent scrutiny.
> No journal acceptance, independent professional endorsement, or full Lean / proof-assistant
> verification is claimed. A public repository, a forum post, and passing finite checks do not
> by themselves establish that an open problem has been solved.

## Read the proof

**[Full English proof](proof/PROOF.md)** · **[审后完整中文证明](proof/PROOF.zh-CN.md)**

The claimed theorem is that, for all real $\alpha,\beta>0$ with
$\alpha/\beta\notin\mathbb Q$, the ordinary set

$$
\{\lfloor2^n\alpha\rfloor,\lfloor2^n\beta\rfloor:n\ge0\}\setminus\{0\}
$$

remains complete after any finite deletion. Every sufficiently large integer
would therefore be a sum of distinct remaining elements.

This is **part (i), with base fixed at 2**. No claim of priority for part (ii),
which asks for a suitable base in $(1,2)$, is made. The precise mathematical
statement, rather than the problem number alone, defines this submission's scope.

## The two parts of the argument

The proof first constructs an actual finite integer mesh after a long exact-doubling
block and a nonzero binary conversion. Its improved maximum gap propagates through
all subsequent original weights, and bounds missing runs modulo *every future*
endpoint gcd. A bounded nonnegative integer gap measure can therefore descend only
finitely often. An incomplete sequence with infinitely many events would have
bounded ratios between successive event positions.

The other part establishes a finite-event decay estimate (FE), a digit-budget
propagation lemma (DB), and a continued-fraction return-cost contradiction. For an
irrational parameter ratio, these rule out incompleteness under bounded event
ratios. Both arguments use the same normalized parameters and arrival-indexed event
set. They are given in full; FE and DB are not being treated as previously accepted
external theorems.

## Reproduce the checks

Python **3.10 or newer**, standard library only. No package installation or network
access is needed. Do **not** use `python -O` or `PYTHONOPTIMIZE`: historical scripts
use assertions.

```bash
python3 certificate/check_templates.py
python3 verification/run_checks.py --full
```

The first command reconstructs the finite coefficient certificate from subset
masks and checks all ratios $q<p<2q$ by exact cone inequalities. It checks **12
chains, 125 nodes, 113 strict overlaps, and 500 third-digit instances**, including
agreement with the proof appendices.

The second command additionally runs the preserved finite regression suites for
permanent descent, FE, DB, and bounded event ratios. It runs legacy scripts in
temporary directories and writes fresh records to
`verification/local_run.json` and
`verification/local_logs/`.

[The preparation-time full run](verification/release_run.json) records all five checks passing. Its logs are preserved in [`verification/release_logs/`](verification/release_logs/); reruns write separate local files.

**These are not a formal proof of the infinite theorem.** Only the explicitly
finite coefficient lemma is certified by the finite symbolic table. The other
infinite claims depend on the written mathematical arguments. See
[verification scope](verification/README.md).

## Where independent scrutiny is most useful

The key interfaces are Sections 3.2–5 (legal representations, overlapping windows,
and permanent projection to changing moduli), Section 8.1 (different-period boundary
comparison), and Sections 9–11 (finite coefficient windows and infinite quantifiers).

Please report the earliest false statement, a concrete counterexample, or the
precise unproved implication. If no error is found, please state exactly what was
read or checked. [Open a repository issue](https://github.com/Andrewyzzz/erdos354/issues)
with the version, section, and reasoning.

## Files and provenance

| Path | Purpose |
|---|---|
| `proof/PROOF.md` | Complete English rendering with explicit definitions and expanded interfaces |
| `proof/PROOF.zh-CN.md` | Chinese proof with accepted post-review clarifications incorporated |
| `certificate/` | Finite mask table and separately implemented checker |
| `verification/` | Preserved regression code, historical inputs, and fresh run records |
| `review/CHANGES.md` | Review decisions and exact revision scope |
| `archive/FROZEN_20260912.zh-CN.md` | Unmodified frozen candidate proof |
| `release/FORUM_POST.md` | Suggested announcement text; this file is not evidence of an actual forum post |
| `MANIFEST.sha256.json` | File integrity record, not a correctness or priority certificate |

The frozen source SHA-256 is
`582ac11509316f060bfce6ff7afabf11572ea1342bc2c0ebdb0e93d3698edfa8`.
The appendix masks and proof constants are unchanged. The package date is a
preparation date, not a claimed public timestamp. Public availability is recorded
by the actual repository history once uploaded.

## Attribution and disclosure

Andrew Y and ChatGPT are credited for the project; ChatGPT is explicitly an AI
system, not a human researcher. Andrew Y is the responsible human maintainer.
AI contributed substantially to proof development, code, exposition, and critical
checking. Three review reports were supplied during development; this repository
does not represent them as three verified independent professional endorsements.
No institutional endorsement is claimed. See [CREDITS.md](CREDITS.md).

No preprint or journal submission is made by publishing this repository.
No full priority review has been completed. References in the proof are distinguished
from internal lemmas and do not certify this candidate's correctness.
