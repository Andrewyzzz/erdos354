# Recorded formalization environment

Recorded on 2026-09-13 (Asia/Shanghai). Command logs use UTC.
Environment checks are preserved in `logs/environment.log` (batch 1),
`logs/mesh-environment.log` (batch 2), and
`logs/third-batch-environment.log` through `logs/eighth-batch-environment.log`
for the later batches.

- Host: local macOS 26.5.1, Apple Silicon / arm64.
- Manuscript baseline commit: `dcdc3c255189ab4e0f9bbf9abea2ca0a3758de06`.
- Batch 2 starting point, batch 1 commit: `0f638801c6220866661581e5848eae7db87798a1`.
- Batch 3 starting point, batch 2 commit: `16e0de8ba8dd9f81d2e04d7834ed29ddaca1e7eb`.
- Batch 4 starting point, batch 3 commit: `d685bb3df0cb05190c31b7a92c2c7271f053580d`.
- Batch 5 starting point, batch 4 commit: `e3985208220a96030f454d3ab5e82ac42135a53c`.
- Batch 6 starting point, batch 5 commit: `ea7ad5fd1eb85db223878a6c92f37d77868532ee`.
- Batch 7 starting point, publication record for batches 1–6: `f6c5d2ba8cbca95427ae6aea854d11116f06cd55`.
- Batch 8 starting point, FE/DB/BG commit: `1e6e6d93661dbaa67700ee77097901ea66f276cd`.
- Development branch: `lean-formalization`. The initial worktree was clean;
  all formalization additions were under `formalization/`.
- Actual Lean: `4.27.0`, commit `db93fe1608548721853390a10cd40580fe7d22ae`.
- Actual Lake: `5.0.0-src+db93fe1`, using Lean 4.27.0.
- Mathlib: `a3a10db0e9d66acbebf76c5e6a135066525ac900`, corresponding to `v4.27.0`.
- `lake-manifest.json` pins all nine dependencies. Every actual dependency Git
  HEAD matched its lock, and dependency sources had no tracked modifications.
- Lean 4.32.0 was also installed locally, but this project selects 4.27.0
  through `lean-toolchain`.

Elan once warned that it could not query the latest default stable release.
The project override still explicitly selected 4.27.0, and the build succeeded.
The toolchain was not upgraded.

## Frozen inputs

| File | SHA-256 |
|---|---|
| `proof/PROOF.md` | `8662891ac64f4ed2805a889d087afc7848667b1519192bf368ebdefba30bbdd2` |
| `proof/PROOF.zh-CN.md` | `a424bb9c470e0303bf9529add146911c1b2717375ecb458b4a0cafae450aa618` |
| `certificate/templates.json` | `3293a4fb061ba625ba1f11788dca751920a182d26d60d6298b31a058c065c048` |
| `certificate/check_templates.py` | `862b5ddbb55d134336029977961c4cf0391ff67024f2946b039ca584cab1b98d` |

The handoff's English-manuscript hash `f17d67…` refers to the revision before
the contributor-name change. Only attribution differs from this baseline.
The hashes above record the actual inputs; files with different bytes are not
treated as the same frozen version.

## Cache and build

The local build reuses an existing Mathlib 4.27.0 cache at
`erdos1-reproduction/lean/.lake/packages`. This project's `.lake/packages`
is a local symbolic link excluded by `formalization/.gitignore`.
The absolute path is not stored in the Lake configuration or dependency lock.
A downloaded checkout can restore pinned dependencies with `lake exe cache get`;
the source does not depend on that local path.

The first successful full build is recorded in `logs/certificate-04.log`:
`lake build` exited with code 0 and audited the initial 18 theorems.
Batch 1 ultimately contained 20 theorems. Batches 2–8 added 31, 32, 44, 21, 35,
175, and 23 respectively, bringing the total to 381.

Current acceptance records are `logs/build.log`, `logs/axioms.log`, and
`logs/verification.json`. Final records for earlier batches remain in their
corresponding commits and delivery bundles.

The fresh-directory rebuild is recorded in `logs/fresh-build.log`,
`logs/fresh-axioms.log`, and `logs/fresh-verification.json`.
It recompiles this project's sources while reusing the same-version Mathlib
compiled cache. It is not a rebuild of all Lean/Mathlib, and no external checker
or comparator was run.

## Historical compilation and integrity records

The following records describe the verification revisions, before the later
English-first documentation update. The 36-file checks refer to the original
release package at those revisions. Subsequent navigation/documentation edits
and their manifest updates do not rewrite these historical logs. The frozen
manuscripts, certificate, Lean sources, and dependency locks remain unchanged.

### Batches 1 and 2

Early `basic*.log` and `certificate*.log` files preserve actual compilation and
repair iterations. Initial issues involved unexpanded cone conditions, missing
imports, reserved identifiers, and simplification order; all were resolved.
Historical failures are not the final build status.

`mesh-cyclic-01.log`, `mesh-02.log`, and `mesh-03.log` record batch 2 repairs
for tactic-style checks, numeric-coercion inference, and induction-base type
inference. The mathematical premises and original manuscript were not changed
to bypass failures.

### Batch 3

Iterations are preserved in `coefficient-interval-*`, `representations-*`,
`node-representations-*`, `node-window-*`, `initial-mesh-*`, and
`permanent-mesh-*` logs. Final module builds are `initial-mesh-06.log`
and `permanent-mesh-04.log`; the earlier failures were repaired.
Internal placeholders displayed by Lean for failed goals are not source proofs.
Acceptance uses only the final full build and transitive axiom audit.

`logs/third-batch-input-integrity.log` checked all 36 original package hashes;
all matched. The manuscripts, original JSON, existing target definitions,
toolchain, and dependency locks were unchanged.

### Batch 4

Iterations are in `floor-sequence-*`, `pair-reindex-*`, `exact-block-*`,
`floor-descent-*`, and `block-length-*` logs.
`floor-descent-04.log` records successful actual-floor arrival-indexed permanent
descent; `block-length-02.log` records successful length conditions.
The full build imported every new module and all axiom audits, not just the
old certificate target.

`logs/fourth-batch-input-integrity.log` again passed all 36 original hashes.
The manuscripts, certificate, frozen target definitions, toolchain, and locks
were unchanged. All nine actual dependency HEADs matched their locks, with no
tracked changes. Proved declarations still depended only on subsets of the
three allowed standard axioms.

### Batch 5

Successful module builds are `unit-mesh-01.log`, `low-gap-01.log`,
`event-gaps-01.log`, and `event-infinitude-02.log`.
The real-inequality tactic-selection issue in `event-infinitude-01.log`
was repaired. The final build imported all batch 5 modules and audited every
auxiliary theorem.

`logs/fifth-batch-input-integrity.log` passed all 36 original hashes.
The toolchain, nine dependencies, dependency source state, manuscripts,
certificate, and frozen targets were unchanged.
At this historical stage the results were conditional completeness and
event-ratio bounds under incompleteness, not verification of all of #354(i).

### Batch 6

Iterations are in `prefix-mesh-01.log`, `prefix-bounds-01.log`, and
`fe-counting-*`. Initial indexing/reindexing expansion, Finset API, and strict
style-check issues were repaired. `fe-counting-03.log` records the updated
prefix mesh, actual prefix bounds, and first FE-counting module;
`fe-counting-04.log` adds the final counting-interpretation results.
Full and fresh-directory checks included every new module and all 183 theorems.

`logs/sixth-batch-input-integrity.log` again passed all 36 original hashes.
The toolchain, nine actual dependency commits, frozen targets, and manuscripts
were unchanged. This stage proved uniform gaps and exact finite FE counting,
not yet the FE decay estimate.

## Batch 7: FE/DB/BG

This batch added 29 modules and 175 theorems: FE and FE-R, the DB increment,
actual long windows, uniform exact-return costs, the BG cumulative contradiction,
and finally `BG.normalized_complete`. Its only hypotheses are normalized initial
floor values and an irrational ratio. At this stage it was not yet the original
arbitrary-positive-parameter target or strong set completeness.
No toolchain, dependency lock, frozen target, or manuscript was changed to obtain it.

Successful core-module records include `fe-main-01.log`, `fe-seed-03.log`,
`db-main-05.log`, `bg-returns-03.log`, `bg-windows-02.log`,
`bg-capacity-04.log`, and `bg-final-02.log`.
Historical failure logs retain complete goal contexts. Issues involved coercions,
library interfaces, induction/arithmetic proofs, and strict style checks; all
were repaired. `fe-db-bg-core-audit.log` is an intermediate checkpoint, not
a substitute for the batch's final 358-theorem audit.

`logs/seventh-batch-input-integrity.log` again matched all 36 original hashes.
`logs/seventh-batch-environment.log` confirms Lean 4.27.0, all nine actual
dependency commits, and no tracked dependency-source changes.
Final acceptance uses `verification.json`, `fresh-verification.json`, and their
actual logs. Fresh rebuilding reuses dependencies and is not a from-scratch
Mathlib build or an external-checker run.

## Batch 8: general parameters, strong completeness, and upstream targets

This batch adds 23 theorems: upward-only tail normalization, distinct values,
avoidance of any finite-deletion bound, and set/index representation bridges.
`Main.lean` implements the unchanged `PartI` and `StrongCompleteness`.
`UpstreamBridge.lean` proves the positive target and strong set completeness
in the exact upstream definitions. Every new module is imported by the default
root target; acceptance is not limited to old modules.

Compilation iterations are in `normalization-01.log` and `main-*.log`.
Initial issues involved strict style checks, function arity, rewrite order,
and arithmetic recognition of local abbreviations. They were not repaired by
adding mathematical premises. Provenance checks are in
`upstream-provenance-offline.log` and `upstream-provenance-online.log`.
The first sandbox DNS failure is preserved; the subsequent read-only online
comparison succeeded.

The actual pinned upstream toolchain is Lean 4.33.1. No new toolchain was
installed or selected for this project. Seven definition blocks were extracted
verbatim and compiled in Lean 4.27.0, with exact RHS checks and kernel-proved
type equivalences. This is not a full upstream-checkout build or completed
upstream PR integration. See [UPSTREAM.md](UPSTREAM.md).

`eighth-batch-input-integrity.log` again matched all 36 original package hashes.
`eighth-batch-environment.log` confirms unchanged toolchain, nine actual
dependency commits, and dependency sources.
Full and fresh-source-directory acceptance records for all 381 theorems are
`verification.json` and `fresh-verification.json`; their logs include actual
`#print` output for the final targets and all transitive axiom dependencies.

`logs/final-clean-source-match.log` additionally compares the fresh directory
and delivery worktree's sources, scripts, and upstream data, with exit code 0.
Only build caches, logs, Markdown documentation, and Python caches were excluded.
