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
finite deleted set. These two targets have not been proved or connected here.

The upstream `answer(...)` wrapper asks whether the statement holds. `PartI`
records the positive proposition on its right-hand side. No upstream conjecture
theorems or answer wrappers are dependencies of this project. A direct adapter
against an installed compatible Formal Conjectures checkout remains a later
integration task; this batch fixes a reviewed local definition mirror.
