# Erdős Problem 354(i) — Lean formalization and candidate manuscript

Lean formalization of indexed completeness and strong set completeness for two
dyadic floor sequences, together with the original candidate manuscript.

Original manuscript package: **v0.1.0-candidate** · Prepared: **12 September 2026**

Contributors: **Andrewyzzz and Chatgpt-6 Astra (AI system)** · Human maintainer: **[@Andrewyzzz](https://github.com/Andrewyzzz)**

> **Current status:** the frozen part-(i) and strong-completeness targets have
> passed local Lean verification, including a fresh-directory rebuild and
> transitive axiom audits of all 381 local theorems. This is not a claim of
> external independent checking, community acceptance, or journal publication.
> The original manuscript remains a candidate released for independent scrutiny.

English is the primary language for repository navigation and maintained
documentation. Chinese manuscripts and historical inputs are explicitly marked
with the `.zh-CN.md` suffix and retained for provenance.

## Lean verification

Start with the [formalization README](formalization/README.md),
[verification results](formalization/RESULTS.md), and
[detailed theorem status](formalization/STATUS.md).

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

Both targets cover arbitrary positive real parameters with irrational ratio,
with base fixed at 2. The final theorems have no extra normalization, FE/DB/BG,
permanent-descent, or long-window hypotheses. Their audited dependencies use
only subsets of `propext`, `Classical.choice`, and `Quot.sound`, without `sorry`,
custom axioms, or `native_decide`.

The project pins Lean 4.27.0 and all dependencies. Reproduce it from the repository root:

```sh
cd formalization
lake exe cache get
python3 scripts/verify.py
python3 scripts/verify.py --fresh
```

The fresh build reuses the pinned dependency cache, not this project's compiled
artifacts. No external checker or comparator was run. The adapter to exact
upstream definitions is verified locally, not in a full upstream 4.33.1 checkout;
see [definition provenance and toolchain boundaries](formalization/UPSTREAM.md).
Part (ii) is outside the formalization's scope.

## Read the proof

**[Full English proof](proof/PROOF.md)** · **[Chinese proof](proof/PROOF.zh-CN.md)**

The manuscript files retain their original bytes and candidate-status notices.
Those preparation-time notices predate the Lean work; current formalization
results are recorded separately in [`formalization/`](formalization/README.md).

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

## Reproduce the finite checks

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

**These Python checks are not a formal proof of the infinite theorem.** Only the
explicitly finite coefficient lemma is certified by the finite symbolic table.
They do not establish the infinite claims by sampling. See the
[finite-check scope](verification/README.md); the separate Lean proof and its
recorded audits are described under [Lean verification](#lean-verification).

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
| `formalization/` | Lean proofs, locked dependencies, English documentation, and actual build/axiom-audit logs |
| `proof/PROOF.md` | Complete English rendering with explicit definitions and expanded interfaces |
| `proof/PROOF.zh-CN.md` | Chinese proof with accepted post-review clarifications incorporated |
| `certificate/` | Finite mask table and separately implemented checker |
| `verification/` | Preserved regression code, historical inputs, and fresh run records |
| `review/CHANGES.md` | Review decisions and exact revision scope |
| `archive/FROZEN_20260912.zh-CN.md` | Unmodified frozen candidate proof |
| `release/FORUM_POST.md` | Suggested announcement text; this file is not evidence of an actual forum post |
| `MANIFEST.sha256.json` | Integrity record for the listed package files, including updated documentation hashes; not a correctness or priority certificate |

The frozen source SHA-256 is
`582ac11509316f060bfce6ff7afabf11572ea1342bc2c0ebdb0e93d3698edfa8`.
The appendix masks and proof constants are unchanged. The package date is a
preparation date, not a claimed public timestamp. Public availability is recorded
by the actual repository history once uploaded.

The original package manifest remains available in the Git history at
[`dcdc3c2`](https://github.com/Andrewyzzz/erdos354/blob/dcdc3c255189ab4e0f9bbf9abea2ca0a3758de06/MANIFEST.sha256.json).
The current manifest updates documentation hashes only; mathematical inputs and
historical logs are unchanged. Lean-source and dependency hashes are recorded
separately in [`formalization/logs/verification.json`](formalization/logs/verification.json).

## Attribution and disclosure

Andrewyzzz and Chatgpt-6 Astra are credited for the project; Chatgpt-6 Astra is explicitly an AI
system, not a human researcher. Andrewyzzz is the responsible human maintainer.
AI contributed substantially to proof development, code, exposition, and critical
checking. Three review reports were supplied during development; this repository
does not represent them as three verified independent professional endorsements.
No institutional endorsement is claimed. See [CREDITS.md](CREDITS.md).

No preprint or journal submission is made by publishing this repository.
No full priority review has been completed. References in the proof are distinguished
from internal lemmas and do not certify this candidate's correctness.
