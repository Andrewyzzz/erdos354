# Finite verification: what the Python checks establish

This directory contains finite symbolic and regression checks. The separate Lean
formalization, including the final targets and transitive axiom audits, is in
[`formalization/`](../formalization/README.md); see its
[verification summary](../formalization/RESULTS.md) for the current result.

Use Python 3.10+, standard library only. Do not enable optimized mode, because the
historical verifiers use assertions. The wrapper rejects `-O` and removes
`PYTHONOPTIMIZE` before launching its subprocesses.

```sh
python3 certificate/check_templates.py
python3 verification/run_checks.py --full
```

Run these from the repository root. They do not require internet access, NumPy,
SymPy, Lean, or a private file path.

## Finite symbolic certificate

`certificate/check_templates.py` reconstructs the coefficients of each subset mask
from the six original weights. It checks the full cone `q < p < 2q`, not a grid of
sample ratios. This establishes the finite combinatorial table used in Section 3.
It also checks the frozen, revised Chinese, and English appendices against the same
mask triples.

This Python checker does **not** verify that the problem was formalized correctly,
the FE and DB proofs, or the universal theorem. Those are outside this checker's
scope; the written arguments and the separate Lean proofs remain available for review.

## Regression suites

- `descent/verify_gap_descent.py`: finite mesh, gap erosion, modular projection,
  actual-prefix examples, and the original symbolic checker.
- `legacy/erdos354_finite_event_decay.py`: finite FE identities and estimates.
- `legacy/erdos354_digit_budget_bootstrap.py`: finite digit budgets and propagation
  certificates.
- `legacy/verify_gap_rigidity.py`: finite return and exact-layer checks; it cannot
  test the infinite compactness argument by sampling.

The four scripts are byte-for-byte copies of the frozen versions. The runner copies
them to temporary directories, supplies the original certificate filename, and
creates the nested FE/DB snapshot directory expected by the historical BG hash
listing. This removes the earlier empty-input-hash ambiguity without modifying the
mathematical tests. Results/logs are written to `local_run.json` / `local_logs/`.
The runner treats a timeout or nonzero exit as failure, never as a pass.

`reference/` contains selected **historical** outputs. `inputs/` contains historical
working notes, whose own exploratory qualifications and scope statements remain
unchanged. They are provenance documents, not external published authorities.
The candidate manuscript is in `proof/`; the current Lean proof and its precise
verification boundaries are documented in `formalization/`.

A manifest certifies file identity only. No runtime or number of finite examples
certifies an infinite theorem. Review reports are not votes establishing correctness.
