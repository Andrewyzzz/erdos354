# Erdős 354(i): formalized indexed and strong set completeness

The finite template certificate, mesh lemmas, legal representations, permanent
descent, FE, FE-R, DB, BG, upward normalization, and finite-deletion/distinct-value
bridges are complete. Both frozen targets are implemented by proved theorems:

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

For every `α, β > 0` with `Irrational (α / β)`, the first theorem uses distinct
natural-number indices; the second allows deletion of any finite set of values
and uses distinct remaining values. Neither has additional normalization,
FE/DB/BG, or long-window hypotheses. All 381 local theorems have been audited:
their transitive axiom dependencies are subsets of `propext`, `Classical.choice`,
and `Quot.sound`. No placeholders, custom axioms, or native decision procedures
are used.

The adapter to the exact upstream definitions and the positive statement of
part (i) has also compiled and passed the axiom audit; see [UPSTREAM.md](UPSTREAM.md).
This is local Lean verification, not external independent checking or community
acceptance. Part (ii) is outside the scope of this project.

The original manuscripts and archive retain their original bytes and
candidate-status notices. This directory records the current formalization
status. Start with [RESULTS.md](RESULTS.md) for the verification summary,
[STATUS.md](STATUS.md) for exact declarations and implementation boundaries,
and [ENVIRONMENT.md](ENVIRONMENT.md) for the recorded build environment.
English is the primary documentation language; files marked `.zh-CN.md`
elsewhere in the repository are Chinese-language manuscripts or historical inputs.

## Reproduce

From the repository root, which contains the original
`certificate/templates.json`, run:

```sh
cd formalization
lake exe cache get
python3 scripts/verify.py
python3 scripts/verify.py --fresh
```

Skip `lake exe cache get` if the dependency cache is already available. The
toolchain and all dependencies are pinned in `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`; no version update is needed.

By default, `verify.py` builds the root module `Dyadic354`. It imports the frozen
statements, certificate, cyclic gaps, meshes, legal representations, initial mesh,
local permanent descent, actual floor/reindexing/event interfaces, length bounds,
unit-mesh completeness, finite descent, event infinitude, uniform prefix bounds,
the full FE/DB/BG chain, general-parameter normalization, both final theorems,
the upstream adapter, and the axiom audit.

The script reruns `Audit.lean`, checks that every local theorem is listed, and
verifies its actual transitive axiom dependencies. Missing output or an axiom
outside the allowlist causes a nonzero exit. Previous PASS records are cleared
at the start; successful records include SHA-256 hashes of the actual Lean
sources and dependency lockfiles. The verifier also checks prohibited mechanisms
in compiled sources, upstream snapshot hashes, verbatim definition blocks, and
the exact target RHS. Verification scripts and upstream provenance data are
included in the recorded hashes.

`--fresh` creates a new temporary source directory without copying this project's
compiled artifacts, then rebuilds and repeats the audit. It reuses the pinned
Mathlib dependency cache; it is neither a from-scratch Mathlib rebuild nor an
independent compiler check. The temporary directory is retained and its path is
logged for inspection.

## Mathematical scope

### Certificate and mesh foundations

`Certificate.certificate_correct` provides a correct chain for every Boolean
first/second digit type with nonzero first type, and all integers `p, q`
satisfying `0 < q < p < 2*q`. It includes:

- Finite mask support on six positions, each used at most once; mask evaluation
  equals a subset sum of the actual six weights.
- Constants `c` and `c+1` for the two alternative offsets, with `0 ≤ c` and
  `c+1 ≤ 22` for every third digit type.
- Coefficients recomputed from masks, with node endpoints checked to be
  `max` and `min + p + q`.
- Strict node width, strict adjacent overlap in both directions, endpoint
  coverage, and coverage of the integer interval `[p+2*q, 7*p+6*q]`.
- All 12 templates, 125 nodes, and 113 adjacent links, with all four third
  digit types quantified at each node.

The cone result follows from general algebraic lemmas, not enumeration of
`p, q`. The data are checked using `decide +kernel`; the generator only
translates data and is not a trusted source of mathematical correctness.
The JSON `lo/hi` fields are candidate endpoints whose correctness must be
verified by Lean's recomputation from the masks.

The six weights are the algebraic expressions in manuscript §3. Batch 3 proves
their legal, disjoint combination with the old prefix and exact doubling blocks,
constructs an initial finite-subset-sum mesh from the 12 templates, and proves
the original-index map injective. Batch 4 derives the actual blocks and six-weight
identities from the real floor recurrence.

`CyclicGaps.erosion_exact`, `Mesh.translate_union_gap_span`, and
`Mesh.projection_gap` correspond to Lemmas 2.1, 2.2, and 2.3.
For subsequent weights satisfying `0 < c_n` and `c_(n+1) ≤ 2*c_n`,
`Mesh.propagate_iterate` preserves the mesh gap bound at every step and gives
the exact span increment.

The cyclic gap is the least `h` such that every window of length `h+1` is hit.
`missingRun_iff_le_gap` identifies it with the maximum actual missing-run length.
For a finite integer mesh, `gap` is defined directly as the maximum distance
between consecutive points; `meshOn_iff_gap_le` proves equivalence with window
hitting. Modular-gap theorems require positive moduli and include modulus 1.
Empty and singleton integer meshes have gap 0; a singleton has span 0.
Cyclic gaps are defined only for nonempty residue sets; a full set has gap 0.

### Legal representations and permanent descent

Under explicit block identities, nonnegative old weights, and a sum bound,
`InitialMesh.prefix_initial_mesh` constructs a mesh in the original prefix with
gap at most `max(1, old gap)` and span greater than `8dKq+15`.
`PermanentMesh.certificate_permanent_descent` then bounds the prefix gap at every
suitable future modulus by the old gap minus 1, using truncated natural subtraction.
Neither mesh existence nor descent is assumed.

The generic local theorem in batch 3 requires positive future weights,
an adjacent doubling bound, a first-weight bound, and modulus bounds.
Batch 4 derives these conditions from the actual floor recurrence.
`PairReindex.prefixSums_reindex` proves that the future `b,a` order and the
frozen `a,b` order have exactly the same legal subset sums on every complete
paired prefix. `FloorDescent.long_block_descent` instantiates local descent at
the actual moduli `D_t = gcd(a_t,b_t)`.

`BlockLength.next_event_length_descent` says that if
`0 < b_0 < a_0 < 2b_0`, `n < m`, there is no arrival event in `(n,m)`,
`m` is an event, and `m-n ≥ 2n+C`, then
`h_t ≤ max(0,h_n-1)` for every `t ≥ m+3`.
Here `C = (16(M+1)²).toNat`, with `M = a_0`, is deliberately generous, not
claimed optimal. Nodes, actual representations, future reindexing, gcd reduction,
and length estimates are all part of the proof chain.

### Completeness, events, and prefix bounds

`UnitMesh.unit_mesh_half_line` constructs legal finite-index representations of
all sufficiently large integers from an actual unit mesh.
`LowGap.next_event_length_complete` therefore obtains completeness of the frozen
interleaving from a qualifying long block and an old gap at most 1.
Unbounded mesh growth and index legality are proved, not assumed.

`EventGaps.unbounded_qualifying_complete` uses well-founded descent on natural
numbers. Each new starting point is chosen after the previous permanent update
takes effect, so ordinary stepwise gap monotonicity is unnecessary.
It does not borrow an unproved uniform prefix-gap bound or claim to implement the
manuscript's numerical budget of at most `N-1` updates.
Conversely, an incomplete normalized sequence eventually has no qualifying gap,
so consecutive events satisfy `m < 3n+C` and `m ≤ 4n`.

`EventInfinitude.events_unbounded` derives unbounded actual events from the
irrational ratio. `nextEvent` is the least successor; existence and the absence
of intervening events are proved. The explicit hypotheses of
`incomplete_nextEvent_factor_four` are irrationality, normalized floor initial
values, and incompleteness; its conclusion is the eventual factor-four bound.

`PrefixMesh.prefix_gap_bound` bounds all prefix gaps by the first weight,
including the new bridging gap when translated convex hulls are separated.
`PrefixBounds.uniform_cyclic_gap` specializes this to the actual floor sequences:
`h_n ≤ N-1` for `n ≥ 2`. The internal missing-run bound holds for every `n`.
The span condition `S_n ≥ a_n` follows by direct induction from layer 2, without
an unformalized exponential lower bound.

### FE, DB, and BG

`FECounting.values_step` and `deficit_step` prove (8.1).
`Q` and `G` are integer differences; their nonnegativity follows from disjoint
basic copies and actual window bounds. `deficit_eq_holes` and
`growth_eq_newValues` identify the counts of actual missing and new integer values.
All Finsets count distinct sums, not mask multiplicities.
The proof also establishes `B_n = M+N+Σw_i`, `0 < B_n < 3N+2n`, and the
equivalence between a nonzero digit sum and an arrival event.

Batch 7 completes periodic boundaries, changing-period comparison, nonoverlapping
decay, and error accounting. `FE.deficit_exponential_bound` and the actual
contiguous-seed estimate `FER.seed_exponential_bound` use the manuscript's
constants. `DB.digit_propagation` derives the digit-budget increment from legal
finite-coefficient representations. `DBScale.advance_increment` connects it
to the defined and proved first good-denominator crossing.

Long windows, layer heights, and precision are constructed using Dirichlet
approximation and minimality of the crossing. Return cost is proved using a
compact set consisting entirely of rational sparse binary ratios, uniformly
over all common multipliers. `BG.bounded_event_windows_complete` proves the
cumulative contradiction. `BG.normalized_complete` removes the event-window
hypothesis using the proved factor-four successor-event bound.
Its only mathematical hypotheses are
`0 < ⌊β⌋ < ⌊α⌋ < 2⌊β⌋` and `Irrational (α/β)`; FE, DB, BG, and long
plateaux are not additional assumptions.

### General parameters and the final targets

For arbitrary positive real parameters and any integer bound,
`Normalization.above_bound` uses independent nonnegative integer shifts of
the two sequences followed by a common upward shift to construct a normalized
tail above the bound, preserving the irrational ratio.
`SetBridge.normalized_injective` proves that the strictly interlacing tails have
no repeated values. `erdos354_strong_completeness` chooses a bound for the finite
deletion set and obtains genuine set representations from these tails.
`erdos354_part_i` then converts set representations to original-index
representations. Both targets are closed.

This implementation uses proved alternative interfaces; it does not reproduce
every continued-fraction enumeration, explicit minimum popcount, or intermediate
asymptotic constant verbatim. See batches 7 and 8 in [STATUS.md](STATUS.md).
The upstream adapter uses verbatim definitions from pinned sources, not a build
of the entire upstream Lean 4.33.1 project. This project remains pinned to Lean
4.27.0 without an automatic toolchain migration.

## Source map

All Lean paths below are relative to `Dyadic354/`.

| File | Purpose |
|---|---|
| `Statements.lean` | Frozen part-(i) and strong-completeness definitions; explicit-threshold equivalence |
| `Basic.lean` | Finite subset sums and integer-cone lemmas |
| `Certificate.lean` | Generic checker, mask semantics, interval chains, and soundness |
| `CertificateData.lean` | Regenerable original JSON data and concrete certificate theorems |
| `CyclicGaps.lean` | Longest cyclic missing runs, exact erosion, full sets, and modulus 1 |
| `Mesh.lean` | Actual consecutive distances, window equivalence, translation, projection, and iteration |
| `CoefficientInterval.lean` | Bounded Bézout coefficient intervals, reflection, and finite binary support |
| `Representations.lean` | Disjoint representations, doubling blocks, and original-index injectivity |
| `NodeRepresentations.lean` | Actual old representatives, residual bounds, node representations, and window hits |
| `InitialMesh.lean` | Trimmed window chains, constant budgets, and actual initial subset-sum meshes |
| `PermanentMesh.lean` | Legal prefix extension, projection to future moduli, and local descent |
| `FloorSequence.lean` | Floor errors, binary recurrence, preservation of initial separation, and prefix sums |
| `PairReindex.lean` | Future pair swaps, injectivity, paired-prefix invariance, and future-weight bounds |
| `ExactBlock.lean` | Arrival events, zero digits, doubling blocks, the six actual weights, and the next small weight |
| `FloorDescent.lean` | Actual gcd coordinates, prefix residues, and conditional permanent floor-sequence descent |
| `BlockLength.lean` | Polynomial thresholds, floor growth, and sufficient block lengths from initial values |
| `UnitMesh.lean` | Legal unit-mesh extension, unbounded right endpoints, and half-line coverage |
| `LowGap.lean` | Completeness from qualifying long blocks and low gaps |
| `EventGaps.lean` | Well-founded delayed descent and event bounds under incompleteness |
| `EventInfinitude.lean` | Unbounded events from irrationality, least successors, and the eventual factor-four bound |
| `PrefixMesh.lean` | Separated-hull bridge bounds, prefix recurrence, and uniform/internal gap bounds |
| `PrefixBounds.lean` | Actual prefix sums, spans, and the uniform gcd-residue gap bound (1.1) |
| `FECounting.lean` | Four-translate recurrence for distinct sums, B/Q/G, nonnegativity, and actual counts |
| `CyclicBoundary.lean`, `PeriodicWord.lean`, `FEShift.lean` | Periodic missing-value functions, variation, and new sums under shifts |
| `FEMissingRuns.lean`, `IntervalSums.lean`, `PeriodChange.lean`, `EventBoundary.lean` | Missing-run boundary counts, interval sums, changing periods, and nonzero-event boundaries |
| `FERecurrence.lean`, `EventDecay.lean`, `FE.lean` | Nonoverlapping event blocks, potential-function error control, and FE |
| `ContiguousSeed.lean`, `FER.lean` | Actual longest contiguous intervals and FE-R |
| `DBDigits.lean`, `DBPhases.lean`, `DBWindows.lean` | Actual digit budgets, Bézout phases, and legal finite-coefficient windows |
| `DBCover.lean`, `DB.lean` | Contiguous coverage, legal index concatenation, and the DB increment |
| `RationalWindows.lean`, `CubicGrowth.lean`, `DBScale.lean` | Good-rational crossings, cubic-depth contradiction, and actual DB scales |
| `BGSparseCompact.lean`, `BGBinaryRatio.lean`, `BGReturns.lean` | Rational compact sets, binary support, and uniform return-cost divergence |
| `BGExactLayers.lean`, `BGWindowBounds.lean`, `BGWindows.lean` | Nonexact-layer counts, approximation precision, and arbitrarily long sparse windows |
| `BGGeometric.lean`, `BGCapacity.lean`, `BG.lean` | Nonoverlapping return accumulation, window capacity, BG, and normalized completeness |
| `Normalization.lean` | Upward-only shifts, ratio balancing, floor-error control, and avoidance of finite deletion bounds |
| `SetBridge.lean` | Tail injectivity, lower bounds, legal value-set inclusion, and index/set representation bridges |
| `Main.lean` | Final theorems for frozen part (i) and strong set completeness |
| `UpstreamDefinitions.lean`, `UpstreamBridge.lean` | Verbatim upstream definitions, kernel-checked type equivalence, and final target adapters |
| `Audit.lean` | Target-type output and the axiom audit of every completed theorem |

Supporting tools:

| Path | Purpose |
|---|---|
| `scripts/generate_data.py` | Data translation and consistency checks against the JSON |
| `scripts/verify.py` | Build, axiom allowlist, and fresh-directory rebuild |
| `scripts/check_upstream.py`, `upstream/` | Source hashes, definition blocks, and positive-target consistency; snapshots are not Lean imports |

See [UPSTREAM.md](UPSTREAM.md) for definition provenance and licensing.
The published manuscripts and original certificate are unchanged.
