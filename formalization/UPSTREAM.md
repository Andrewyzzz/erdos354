# Definition provenance

`Statements.lean` adapts only definitions from google-deepmind/formal-conjectures,
commit `a748dd915c908b21c4d864abf239f61049fa9d96`:

- `FormalConjectures/ErdosProblems/354.lean`: `FloorMultiples`,
  `FloorMultiples.interleave`, and the right-hand side of part (i).
- `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`:
  `subseqSums'`, `IsAddCompleteNatSeq'`, `subsetSums`, `IsAddComplete`,
  and `IsAddStronglyComplete`.

Copyright 2025 The Formal Conjectures Authors. Apache License 2.0; see
`LICENSE.upstream`. This license notice covers the upstream-derived definitions,
not a new license imposed on the manuscript or the rest of the repository.

Local mapping:

| Upstream | Local |
|---|---|
| `FloorMultiples` | `Dyadic354.floorMultiples` |
| `FloorMultiples.interleave` | `Dyadic354.interleave` |
| `k ∈ subseqSums' w` | `Dyadic354.IsSubsetSum w k` |
| `IsAddCompleteNatSeq'` | `Dyadic354.IndexedComplete` |
| `IsAddComplete` | `Dyadic354.SetComplete` |
| `IsAddStronglyComplete` | `Dyadic354.SetStronglyComplete` |

The sequence has values in `ℤ`, uses floor with base exactly 2, and representations
choose a `Finset ℕ`. Two equal values at different indices may both be selected.
The strong target uses a set of values, removes zero, and quantifies over every
finite deleted set. Both frozen local targets are now proved in `Main.lean`.

The upstream `answer(...)` wrapper asks whether the statement holds. `PartI`
records the positive proposition on its right-hand side. No upstream conjecture
theorems or answer wrappers are dependencies of this project.

## Exact extracted-definition adapter

`Dyadic354/UpstreamDefinitions.lean` reproduces seven upstream definition blocks
verbatim under their original names. Only imports and namespace/section scaffolding
are adapted. `Dyadic354/UpstreamBridge.lean` proves definition-level equivalences,
the exact positive part (i) target, and the set-strong-completeness statement in
those types. In particular, the extended upstream quantifiers order their binders
differently from local `PartI`; `partITarget_iff` proves both directions explicitly.

`upstream/lock.json` records the upstream commit, file paths and SHA-256 values.
The `.txt` snapshots preserve the complete source files as provenance data. They
are not Lean imports; the conjecture placeholders in those snapshots do not enter
any proof dependency. All compiled local Lean sources remain placeholder-free.

`scripts/check_upstream.py` checks the frozen hashes, all seven verbatim definition
blocks and the exact positive part (i) RHS, allowing only whitespace and the
necessary `Erdos354.` qualification. The normal verifier runs this offline check.
The additional online check was actually run against the pinned public commit:

```sh
python3 scripts/check_upstream.py --online
```

Successful output: `logs/upstream-provenance-online.log`. An earlier sandbox DNS
failure is preserved in `logs/upstream-provenance.log`; the subsequent authorized
read-only check succeeded. This is an input-provenance check, not a substitute for
the Lean kernel's type-equivalence proofs or the final transitive axiom audit.

## Toolchain boundary

The pinned upstream revision uses Lean/Mathlib **4.33.1**, confirmed from its
`lean-toolchain`. This project remains on the previously locked Lean/Mathlib
**4.27.0**. The adapter is compiled against the exact extracted definitions here;
it is **not** a build of the entire upstream checkout and does not claim binary
compatibility with its compiled modules. A later upstream PR or full-checkout
integration would require a separate toolchain migration/rebuild and review.
Neither is required to prove or compare the frozen mathematical target, and
neither has been performed or published automatically.
