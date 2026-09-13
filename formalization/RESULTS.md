# Final verification summary

2026-09-13. Local Lean formalization verification: **PASS**.

## Completed mathematical targets

- `Dyadic354.erdos354_part_i : PartI`: for arbitrary positive real α and β with
  irrational ratio and fixed base 2, every sufficiently large integer is a
  legal finite-index sum of the interleaved floor sequences.
- `Dyadic354.erdos354_strong_completeness : StrongCompleteness`: after deleting
  any finite set of values from the original nonzero value set, every sufficiently
  large integer is still a finite sum of distinct remaining values.

Both target definitions are unchanged from their batch 1 frozen versions.
The final theorems have no additional normalization, FE, DB, BG, permanent-descent,
long-window, or event-spacing hypotheses.
See [Main.lean](Dyadic354/Main.lean) for the proofs and
[Statements.lean](Dyadic354/Statements.lean) for the exact target definitions.

## Recorded checks

| Check | Result and record |
|---|---|
| Full default build and complete axiom audit | PASS, 381 theorems; [verification.json](logs/verification.json) |
| Fresh-source-directory rebuild and repeated axiom audit | PASS, 381 theorems; [fresh-verification.json](logs/fresh-verification.json) |
| Source hashes and individual axiom dependencies across both runs | Identical |
| Fresh directory versus delivery sources, scripts, and upstream data | Exit code 0; [comparison log](logs/final-clean-source-match.log) |
| Original release input integrity at the verification revision | All 36 file hashes matched; [integrity log](logs/eighth-batch-input-integrity.log) |
| Pinned upstream provenance and exact target | Online byte comparison and offline definition checks passed; [provenance log](logs/upstream-provenance-online.log) |

Every theorem depends only on a subset of `propext`, `Classical.choice`, and
`Quot.sound`. Compiled sources contain no `sorry`, custom axioms,
`native_decide`, or mechanism that skips kernel checking.
Actual `#print` output and transitive axiom dependencies for the final theorems
are in [axioms.log](logs/axioms.log), with the fresh run in
[fresh-axioms.log](logs/fresh-axioms.log).

## Scope and trust boundaries

- This project remains on Lean 4.27.0 and pinned Mathlib dependencies; no upgrade
  was performed.
- The fresh build does not reuse this project's compiled artifacts, but does
  reuse the pinned dependency cache. Mathlib was not rebuilt from scratch;
  no external independent checker or comparator was run.
- Seven upstream definitions were extracted verbatim. The exact positive
  part-(i) RHS was checked, and Lean proves type equivalence and the corresponding
  conclusions. No upstream placeholder theorem was imported. The entire
  upstream Lean 4.33.1 project was not built.
- Some intermediate proofs use proved alternative implementations rather than
  line-by-line translations of the manuscript; see [STATUS.md](STATUS.md).
- Part (ii), an upstream PR, community acceptance, and journal publication are
  not among the completed results.
- The manuscripts and archive retain their original bytes. On 2026-09-13,
  at the maintainer's explicit request, batches 7 and 8 were pushed and
  `lean-formalization` was fast-forward merged into `main`.
  The verified source commit is
  [59e5957](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e).
  Later English-first documentation edits do not change the verified sources
  or rewrite the historical verification logs.

See [README.md](README.md) for reproduction commands and the module map,
[ENVIRONMENT.md](ENVIRONMENT.md) for environment and dependency records,
and [UPSTREAM.md](UPSTREAM.md) for adapter details.
