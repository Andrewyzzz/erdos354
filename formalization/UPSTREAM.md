# Definition provenance

We compare our target with the definitions in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/tree/a748dd915c908b21c4d864abf239f61049fa9d96),
revision `a748dd915c908b21c4d864abf239f61049fa9d96`.

The relevant sources are:

- `FormalConjectures/ErdosProblems/354.lean`: `FloorMultiples`,
  `FloorMultiples.interleave`, and the positive right-hand side of part (i).
- `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`:
  `subseqSums'`, `IsAddCompleteNatSeq'`, `subsetSums`,
  `IsAddComplete`, and `IsAddStronglyComplete`.

Copyright 2025 The Formal Conjectures Authors.
The upstream-derived definitions retain their Apache License 2.0 notice;
see [LICENSE.upstream](LICENSE.upstream).

## Definition correspondence

| Upstream | Local |
|---|---|
| `FloorMultiples` | `Dyadic354.floorMultiples` |
| `FloorMultiples.interleave` | `Dyadic354.interleave` |
| `k ∈ subseqSums' w` | `Dyadic354.IsSubsetSum w k` |
| `IsAddCompleteNatSeq'` | `Dyadic354.IndexedComplete` |
| `IsAddComplete` | `Dyadic354.SetComplete` |
| `IsAddStronglyComplete` | `Dyadic354.SetStronglyComplete` |

The sequence takes values in `ℤ`. Its representations select a
`Finset ℕ`, so different indices with equal values may both be chosen.
Our strong target uses the nonzero set of values and quantifies over
every finite deletion.

## Extracted-definition adapter

[UpstreamDefinitions.lean](Dyadic354/UpstreamDefinitions.lean) reproduces
seven definition blocks verbatim under their original names, with imports
and namespace/section scaffolding adapted to this project.
[UpstreamBridge.lean](Dyadic354/UpstreamBridge.lean) proves the definition
equivalences and the following conclusions:

```lean
Dyadic354.UpstreamBridge.erdos354_part_i_upstream
Dyadic354.UpstreamBridge.erdos354_strong_upstream
```

In particular, `partITarget_iff` proves equivalence with our frozen
`PartI`, explicitly accounting for the different binder order.
The proof imports definitions only; the upstream conjecture theorem and
its answer wrapper are not dependencies.

We compile this extracted-definition adapter under the project's pinned
Lean 4.27.0 environment. The source revision from which the definitions
were extracted specifies Lean 4.33.1. This records the provenance and
compilation environment of the adapter precisely.

## Reproducible provenance checks

[upstream/lock.json](upstream/lock.json) records the source revision,
paths, and hashes. Full source snapshots are preserved as `.txt` data.
The verifier checks the snapshot hashes, all seven extracted definition
blocks, and the exact positive part-(i) right-hand side. Lean then checks
the type-equivalence proofs and the two conclusion proofs.

The ordinary verification command performs the offline checks.
For an additional byte comparison against the pinned public sources, run
from `formalization/`:

```sh
python3 scripts/check_upstream.py --online
```

The recorded comparison is in
[upstream-provenance-online.log](logs/upstream-provenance-online.log).
