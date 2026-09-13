# Batch 8 status: part (i) and strong completeness

Both frozen targets are proved: #354(i) and the manuscript's strong set
completeness statement, for arbitrary positive real parameters with irrational
ratio. No normalized-initial-value condition or additional FE/DB/BG hypothesis
remains in the final theorems.

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

The first theorem selects summands using a finite set of natural-number indices.
The second deletes any finite set of values and represents every sufficiently
large integer using a finite set of remaining values. Neither indices nor values
are reused illegally. The exact-definition adapter for the positive upstream
statement is also complete: `UpstreamBridge.erdos354_part_i_upstream`.
These are local Lean kernel verification results, not community acceptance,
journal publication, external-checker verification, or a full upstream build.
See [UPSTREAM.md](UPSTREAM.md) for toolchain and adapter boundaries.

The concrete certificate is checked by kernel computation. Generic soundness
then gives coefficient coverage and six-weight subset-sum semantics for every
admissible integer parameter pair. Batch 2 proves Lemmas 2.1–2.3 and connects
longest missing runs, actual consecutive distances, and window formulations.
Batch 3 adds 32 theorems for the finite representation chain (§§3–4) and local
algebraic projection (§5). Batch 4 adds 44 theorems for floor recurrences,
pair reindexing, actual local blocks, gcd coordinates, conditional permanent
descent, and length estimates. Batch 5 adds 21 theorems for low-gap completeness,
well-founded descent, event infinitude, and successor-event ratio bounds.
Batch 6 adds 35 theorems for uniform prefix/internal/modular gaps (§1.1) and
finite counting (§8). Batch 7 adds 175 theorems, connecting FE/DB/BG to actual
normalized completeness. Batch 8 adds 23 theorems for legal tails, distinct
values, finite deletion, and final target adapters.

Finite data use `decide +kernel`. The transitive axiom dependencies of all 381
local theorems are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The final build/audit record is [verification.json](logs/verification.json);
the fresh-directory record is [fresh-verification.json](logs/fresh-verification.json).
Full command output is preserved alongside them.

Batches 1–7 below retain their historical interfaces and completion boundaries.
Statements that work was "not yet complete" describe those earlier stages.
Batch 8 and the final acceptance boundaries describe the current state.

## Batch 1: compiled theorems and manuscript mapping (20)

Names in this table are fully qualified. Every declaration compiled and is
listed in `Audit.lean`.

| Full declaration | Manuscript correspondence | Main dependencies |
|---|---|---|
| `Dyadic354.mem_finiteSubsetSums` | §1: distinct finite subset-sum values | Finset powerset/image |
| `Dyadic354.Linear.eval_add` | §3.3: coefficient-addition semantics | Integer ring arithmetic |
| `Dyadic354.Linear.eval_sub` | §3.3: coefficient-subtraction semantics | Integer ring arithmetic |
| `Dyadic354.Linear.cone_identity` | §3.3: integer-cone change of variables | Integer ring arithmetic |
| `Dyadic354.Linear.nonneg_on_cone` | §3.3: nonnegativity on the closed cone | cone_identity, monotonicity of multiplication |
| `Dyadic354.Linear.positive_on_cone` | §3.3: strict positivity on the open cone | cone_identity, strict monotonicity of multiplication |
| `Dyadic354.indexedComplete_iff` | Original target: an explicit eventual threshold | Filter.eventually_atTop |
| `Dyadic354.Certificate.offset_eq_sum` | §3.2: mask evaluation equals a six-weight subset sum | Distributivity of finite sums |
| `Dyadic354.Certificate.offset_isSubsetSum` | §3.2: finite support on original positions | offset_eq_sum |
| `Dyadic354.Certificate.weights_explicit` | §3: the six actual algebraic weights | Fin 6 cases, integer ring arithmetic |
| `Dyadic354.Certificate.endpoints_sound` | §§3.2–3.3: max/min endpoints | nonneg_on_cone, mask coefficients |
| `Dyadic354.Certificate.node_sound` | §§3.2–3.3: node width, constant difference, and legal alternative representations | endpoints_sound, positive_on_cone, offset_isSubsetSum |
| `Dyadic354.Certificate.interval_chain_covers` | §3.3: interval-chain coverage without monotone endpoints | Natural-number induction, integer order |
| `Dyadic354.Certificate.chain_sound` | §3.3: nodes, two-way overlap, endpoints, and full interval coverage | node_sound, interval_chain_covers |
| `Dyadic354.Certificate.checkCertificate_sound` | §3.3: checker success implies the universal mathematical statement | chain_sound, Boolean-check semantics |
| `Dyadic354.Certificate.certificate_checked` | Appendix A: all 12 input types pass | Original mask data, decide +kernel |
| `Dyadic354.Certificate.certificate_correct` | §3.3 and Appendix A: full certificate for all admissible parameters | checkCertificate_sound, certificate_checked |
| `Dyadic354.Certificate.all_templates_checked` | Appendix A: every listed template passes | Original mask data, decide +kernel |
| `Dyadic354.Certificate.all_templates_correct` | Appendix A: universal meaning of each concrete template | all_templates_checked, chain_sound |
| `Dyadic354.Certificate.certificate_counts` | Appendix A: 12 templates, 125 nodes, 113 links | Original data, decide +kernel |

Each node's constant bounds quantify all four third digit types, covering 500
node/type combinations. The integer parameters `p, q` are those of the
manuscript and are not restricted to a finite test range.

## Batch 2: compiled theorems and manuscript mapping (31)

All declarations compiled and are audited. `CyclicGaps.gap` is natural-valued,
so `h-1` is truncated subtraction, expressing `max(0,h-1)`.

| Full declaration | Manuscript correspondence | Main dependencies |
|---|---|---|
| `Dyadic354.CyclicGaps.gapBound_mono` | Relaxing window length | Window definition |
| `Dyadic354.CyclicGaps.not_missingRun_iff` | Complementarity of missing runs and window hits | Quantifier duality |
| `Dyadic354.CyclicGaps.gapBound_erode_iff` | Lemma 2.1: exact erosion/window-length relation | Integer-window translation |
| `Dyadic354.CyclicGaps.modulus_bound` | Nonempty residue-set gap is less than the modulus | ZMod representatives and bounds |
| `Dyadic354.CyclicGaps.gap_spec` | The least window bound holds | Nat.find_spec, modulus_bound |
| `Dyadic354.CyclicGaps.gap_le_iff` | Numeric gap bound iff window hitting | Nat.find minimality, gapBound_mono |
| `Dyadic354.CyclicGaps.gap_lt_modulus` | Excluding an entirely missing cycle | modulus_bound, gap_le_iff |
| `Dyadic354.CyclicGaps.missingRun_iff_le_gap` | Gap equals the longest actual consecutive missing run | gap_le_iff, not_missingRun_iff |
| `Dyadic354.CyclicGaps.erode_nonempty` | Erosion preserves nonemptiness | Finset union |
| `Dyadic354.CyclicGaps.lift_erode` | Residue erosion agrees with the periodic integer lift | ZMod addition/subtraction, Finset image |
| `Dyadic354.CyclicGaps.erosion_exact` | Lemma 2.1: h(X∪(X+1))=h(X)-1 | gapBound_erode_iff, gap minimality |
| `Dyadic354.CyclicGaps.gap_eq_zero_iff_full` | Gap is zero iff the set is full | ZMod representatives, gap_spec |
| `Dyadic354.CyclicGaps.gap_modulus_one` | Modulus-1 boundary case | gap_lt_modulus |
| `Dyadic354.Mesh.gap_le_iff` | Bound on maximum actual consecutive distance | Finset.sup |
| `Dyadic354.Mesh.gap_empty` | Empty integer mesh has gap 0 | Empty finite supremum |
| `Dyadic354.Mesh.gap_singleton` | Singleton integer mesh has gap 0 | No consecutive pair |
| `Dyadic354.Mesh.encloses_min_max` | Convex-hull endpoints bound all elements | Finset.min'/max' |
| `Dyadic354.Mesh.span_of_encloses` | Actual span equals endpoint difference | Minimum and maximum |
| `Dyadic354.Mesh.span_singleton` | Singleton span is 0 | Finset.min'/max' |
| `Dyadic354.Mesh.meshOn_gap_le` | Window hitting bounds actual consecutive distances | Consecutive, window hitting |
| `Dyadic354.Mesh.meshOn_of_gap_le` | Actual consecutive-distance bound implies window hitting | Finite-set predecessor/successor |
| `Dyadic354.Mesh.meshOn_iff_gap_le` | Window and manuscript gap formulations are equivalent | Both directions above; k>0 |
| `Dyadic354.Mesh.gap_positive_of_encloses` | Positive span forces positive gap | Successor of the first hull point |
| `Dyadic354.Mesh.meshOn_translate_union` | Translation preserves window bounds when hulls overlap or touch | Original/translated hull cases |
| `Dyadic354.Mesh.translate_union_nonempty` | Translated union is nonempty | Finset union |
| `Dyadic354.Mesh.translate_union_gap_span` | Lemma 2.2: gap does not increase; span increases by c | Window equivalence, translated hulls, endpoint uniqueness |
| `Dyadic354.Mesh.residues_nonempty` | Nonempty mesh has nonempty modular image | Finset.image |
| `Dyadic354.Mesh.projection_window_bound` | Every modular window is hit by the integer mesh | ZMod representatives, mesh windows, including wraparound |
| `Dyadic354.Mesh.projection_gap` | Lemma 2.3: span≥m>0 implies h(W mod m)≤k-1 | projection_window_bound, gap_le_iff |
| `Dyadic354.Mesh.extend_nonempty` | Each future-weight extension is nonempty | Recursive union |
| `Dyadic354.Mesh.propagate_iterate` | Corollary of Lemma 2.2: preserved gap bound and exact cumulative span | translate_union_gap_span, natural-number induction |

Modular gaps are defined only for nonempty `Finset (ZMod d)` with `NeZero d`.
The proofs cover full sets, zero-length missing runs, and modulus 1.
Empty and singleton integer meshes have gap 0; singleton span is 0.
The translation theorem uses the manuscript condition `span(W) ≥ c > 0`;
the needed `k > 0` is derived, not added as a hypothesis.
Projection likewise derives positive gap from `span(W) ≥ m > 0` and does not
identify groups with different moduli.

## Batch 3: compiled theorems and manuscript mapping (32)

Names below omit `Dyadic354.`. All auxiliary theorems are audited, not just
terminal conclusions. Exact parameters and types are in `logs/axioms.log`
and the corresponding Lean sources.

| Declaration | Manuscript correspondence |
|---|---|
| `CoefficientInterval.lower_interval` | §3.1: reduce Bézout coefficients modulo the other parameter to obtain bounded x, y |
| `CoefficientInterval.bounded_interval` | §3.1: reflection covers all of [F,(p+q)(K-1)-F] |
| `CoefficientInterval.binary_sum_exists` | Every natural number below 2^ℓ is a sum of distinct binary positions |
| `Representations.subsetSum_disjSum` | Legal subset-sum concatenation on disjoint index types |
| `Representations.subsetSum_embed` | Injective embedding into a specified index set preserves non-repetition |
| `Representations.binary_scaled` | Integer-scaled binary coefficients realized on Fin ℓ positions |
| `Representations.block_interval` | §3.1: two doubling blocks realize the coefficient interval |
| `Representations.position_injective` | Old prefix, two doubling blocks, and six weights use pairwise disjoint original indices |
| `Representations.position_lt` | Every original index is below 2(n+ℓ+3) |
| `Representations.packed_weights_match` | Explicit block and six-weight identities match the local model |
| `Representations.packed_to_prefix` | Local representations become finite-index sums in the original prefix |
| `Representations.prefix_block_offset` | §3.2: legal concatenation of old prefix, doubling blocks, and six-weight offset |
| `NodeRepresentations.residual_bounds` | §3.2: residual coefficient bounds from actual old representatives and constant 22 |
| `NodeRepresentations.old_sum_bounds` | Each subset sum of nonnegative old weights lies in [0,Σold] |
| `NodeRepresentations.mask_representation` | §3.2: a mask realizes its residue in the trimmed node interval |
| `NodeRepresentations.node_representation` | §3.2: each checked node realizes two classes of old residues |
| `NodeRepresentations.oldResidues_nonempty` | Old prefix residues contain the empty-sum residue |
| `NodeRepresentations.lift_oldResidues_iff` | Residue membership iff an actual old representative and divisibility condition exist |
| `NodeRepresentations.node_window` | §3.2: every k-window in an eroded node hits an actual subset sum |
| `InitialMesh.margin_budget` | (4.1): dK-2B ≥ 64d-42 ≥ 22d, including d=1 |
| `InitialMesh.trimmed_chain_covers` | §4: trimmed-chain coverage without monotone endpoints |
| `InitialMesh.chain_windows` | §4: every k-window in the global interval hits an actual subset sum |
| `InitialMesh.mesh_from_windows` | (4.2): actual finite mesh, endpoint losses, and span bound |
| `InitialMesh.span_budget` | (4.3): span is strictly greater than 8dKq+15 |
| `InitialMesh.certificate_initial_mesh` | Actual subset-sum mesh from the 12 original templates and local block conditions |
| `InitialMesh.prefix_initial_mesh` | Every initial-mesh point is a legal finite-index sum in the original prefix |
| `PermanentMesh.prefix_nonempty` | Every original prefix contains the empty sum |
| `PermanentMesh.extend_step_subset` | Appending one new index does not collide with old support |
| `PermanentMesh.extend_subset_prefix` | Every propagated mesh remains in the actual prefix subset sums |
| `PermanentMesh.gap_of_subset` | Enlarging a nonempty residue set cannot increase its cyclic gap |
| `PermanentMesh.permanent_projection` | Legal initial mesh and future-weight bounds imply prefix-gap bounds at all suitable future moduli |
| `PermanentMesh.certificate_permanent_descent` | Actual templates, explicit local blocks, and future-weight bounds imply all suitable future gaps are at most the old gap minus 1 |

### Batch 3 local interfaces

`certificate_initial_mesh` assumes a positive integer modulus `d`,
`0 < q < p < 2q`, `IsCoprime p q`, nonnegative old weights with sum
less than `d(p+q)`, `K = 2^ℓ ≥ K_*`, and a nonzero first digit type.
`IsCoprime` is Mathlib's standard integer Bézout definition.
Coefficients are not restricted to finite enumeration.
The mesh is built from finite subset sums of these weights, not supplied as an
abstract residue mesh or an existence assumption.

`prefix_initial_mesh` explicitly maps positions to the old prefix `[0,2n)`,
doubling-block indices `2n+2i` / `2n+2i+1`, and six-weight indices
`2n+2ℓ+j`. This map is proved injective. Its agreement with the supplied
sequence `v` is expressed by two block identities and six weight identities.
Batch 3 did not derive these local assumptions from real floors, events, and gcds;
batch 4 supplies that interface.

`certificate_permanent_descent` proves mesh existence and gap descent internally.
It still explicitly requires positive future weights, an adjacent doubling bound,
first future weight at most `8dKq+15`, and each selected new modulus at most
the current future weight. It quantifies all such extensions and moduli.
At this stage it was only the local algebraic version of §5, not a
formalization of every statement in §§2–6.

The propagation order is `b_r,a_r,b_(r+1),a_(r+1),…`, whereas the frozen target
uses `a_r,b_r,a_(r+1),b_(r+1),…`. Batch 4 resolves this through explicit index
swaps, complete-paired-prefix sum invariance, and the floor recurrence, without
changing the frozen target.

## Batch 4: compiled theorems and manuscript mapping (44)

Names omit `Dyadic354.`; every auxiliary theorem is audited.

| Declaration | Manuscript correspondence |
|---|---|
| `FloorSequence.correction_bounds` | §1: actual floor errors lie in the integer interval [0,1] |
| `FloorSequence.digit_bit` | Boolean digit evaluation equals the actual correction |
| `FloorSequence.recurrence` | a_(n+1)=2a_n+u_n, proved rather than assumed |
| `FloorSequence.next_bounds` | The next term lies between twice the current term and twice it plus 1 |
| `FloorSequence.normalized_bounds` | Normalized initial bounds 0<b_n<a_n<2b_n persist at all layers |
| `FloorSequence.prefix_deficit` | Exact identity for a current term minus the old one-sequence prefix sum |
| `FloorSequence.prefix_sum_lt` | Positive initial value makes the old prefix sum strictly less than the current term |
| `FloorSequence.interleave_even` | Frozen interleaving selects the first sequence at even positions |
| `FloorSequence.interleave_odd` | Frozen interleaving selects the second sequence at odd positions |
| `FloorSequence.paired_prefix_sum` | A complete paired-prefix sum equals the sum of the two sequence prefixes |
| `FloorSequence.paired_prefix_lt` | §§1, 3: actual S_n<a_n+b_n |
| `PairReindex.swapAfter_before` | Original indices before the update layer remain unchanged |
| `PairReindex.swapAfter_even` | Swap even positions after the update layer |
| `PairReindex.swapAfter_odd` | Swap odd positions after the update layer |
| `PairReindex.index_cases` | Even/odd decomposition of natural-number indices |
| `PairReindex.swapAfter_involutive` | Applying the pair swap twice is the identity |
| `PairReindex.swapAfter_injective` | No collisions or repeated original indices |
| `PairReindex.swapAfter_lt_iff` | Every complete paired-prefix index range is preserved |
| `PairReindex.prefixSums_reindex_subset` | One inclusion between legal subset-sum sets before and after reindexing |
| `PairReindex.prefixSums_reindex` | Equality of all subset-sum values on every complete paired prefix |
| `PairReindex.sortedTail_even` | Even positions of the future enumeration contain b terms |
| `PairReindex.sortedTail_odd` | Odd positions of the future enumeration contain a terms |
| `PairReindex.sortedTail_positive` | Normalized floor initial values imply positive future weights |
| `PairReindex.sortedTail_doubling` | The floor recurrence gives the future adjacent doubling bound |
| `ExactBlock.no_events_zero_digits` | No arrival events implies zero corresponding departure digits |
| `ExactBlock.exact_block` | ℓ−1 zero transitions give ℓ exact doubling weights |
| `ExactBlock.after_exact_block` | The ℓth transition arrives at n+ℓ, making the one-step offset explicit |
| `ExactBlock.interleave_block` | Two actual doubling-block identities for the frozen interleaving |
| `ExactBlock.three_pairs` | Three actual consecutive pairs equal the certificate's six-weight vector |
| `ExactBlock.six_after_exact_block` | Zero-transition blocks imply the certificate's actual six-weight inputs |
| `ExactBlock.next_small_weight_bound` | Actual error bounds imply b_(n+ℓ+3)≤8dKq+15 |
| `FloorDescent.fin_prefix_iff` | Legal representations on Fin(2n) and natural-number prefixes are equivalent |
| `FloorDescent.oldResidues_prefix` | Certificate old residues equal the actual interleaved prefix's modular image |
| `FloorDescent.modulus_positive` | A positive b term makes the actual gcd positive |
| `FloorDescent.gcd_coordinates` | Actual gcd reduction gives a=dp, b=dq, 0<q<p<2q, and Bézout coprimality |
| `FloorDescent.interleave_positive` | Every original weight in the normalized frozen interleaving is positive |
| `FloorDescent.long_block_descent` | §5: an actual long zero block and terminal event trigger permanent descent |
| `FloorDescent.next_event_descent` | Arrival-indexed form: terminal event at m, update effective from m+3 |
| `BlockLength.threshold_le_square` | §5: K_*≤16p² |
| `BlockLength.floor_upper` | a_n<(M+1)2^n |
| `BlockLength.coordinate_upper` | Actual reduced coordinate 0<p≤a_n<(M+1)2^n |
| `BlockLength.growthConstant_bound` | An explicit constant depending only on initial M controls 16(M+1)² |
| `BlockLength.threshold_of_length` | Block length ℓ≥2n+C implies the certificate threshold 2^ℓ≥K_* |
| `BlockLength.next_event_length_descent` | Actual event-free interval length implies permanent descent from m+3 |

### Batch 4 terminal result and hypotheses

For the actual sequences `a_i=⌊2^i α⌋`, `b_i=⌊2^i β⌋`,
`BlockLength.next_event_length_descent` assumes:

1. Initial values satisfy `0 < b_0 < a_0 < 2b_0`. Legal normalization of arbitrary
   positive real parameters was not yet proved at this stage.
2. `n < m`, there is no arrival event in the open interval `(n,m)`, and
   `m` is an event.
3. `m-n ≥ 2n+C`, where `C = (16(a_0+1)²).toNat`.

For every `t ≥ m+3`, the actual prefix gap at the actual gcd modulus satisfies
`h_t ≤ h_n-1`, with truncated natural subtraction.
Here `D_t = gcd(a_t,b_t)`, not an arbitrary substitute modulus.
Prefixes use finite sets of natural-number indices in the frozen interleaving.
The old-sum bound, coprimality, six-weight inputs, future positivity, doubling
bound, and first-weight bound are all derived inside the proof chain.
The chain includes the original 12-template kernel-checked certificate.

The generous constant `C` is not optimized to logarithmic order. It depends only
on the initial first floor value `M`, not future digits, events, or moduli.
This conditional result does not require irrationality and by itself does not
prove the original problem. At the end of batch 4, low-gap completeness,
event infinitude, finite descent, and FE/DB/BG were still unfinished.

## Batch 5: compiled theorems and manuscript mapping (21)

Names omit `Dyadic354.`; all declarations are included in the transitive axiom audit.

| Declaration | Manuscript correspondence |
|---|---|
| `PairReindex.isSubsetSum_reindex_iff` | Future pair swaps preserve all legal finite-index sums |
| `PairReindex.indexedComplete_reindex_iff` | Indexed completeness is invariant under reindexing |
| `FloorDescent.long_block_mesh` | Extract the actual long-block mesh for both descent and completeness |
| `UnitMesh.mem_extend` | Original mesh points remain in every future extension |
| `UnitMesh.add_sum_mem_extend` | Selecting all new indices gives a legal lower bound on right-endpoint growth |
| `UnitMesh.positive_sum_ge_length` | A prefix sum of positive integer future weights is at least its length |
| `UnitMesh.unit_mesh_half_line` | §5: actual unit mesh and legal extensions cover a half-line from a fixed left endpoint |
| `UnitMesh.unit_mesh_complete` | Half-line coverage implies the frozen IndexedComplete definition |
| `LowGap.long_block_complete` | §5: an actual long block, certificate threshold, and old gap≤1 imply completeness |
| `LowGap.next_event_length_complete` | Arrival-indexed, explicit-block-length version of the same result |
| `EventGaps.eventually_not_of_eventual_descent` | §6: delayed permanent strict descent excludes unbounded qualifying starts |
| `EventGaps.incomplete_eventually_no_qualifying` | An incomplete normalized sequence eventually has no qualifying long intervals |
| `EventGaps.unbounded_qualifying_complete` | Unbounded qualifying long intervals imply actual indexed completeness |
| `EventGaps.incomplete_event_step_bound` | Under incompleteness, consecutive actual events eventually satisfy m<3n+C |
| `EventGaps.incomplete_event_factor_four` | §6: consecutive actual events eventually satisfy m≤4n |
| `EventInfinitude.zero_tail_dyadic` | Eventually zero floor errors force a dyadic-rational parameter |
| `EventInfinitude.no_events_tail_digits` | No tail arrival events implies zero corresponding digits in both sequences |
| `EventInfinitude.events_unbounded` | §1: an irrational ratio guarantees an actual event beyond every layer |
| `EventInfinitude.nextEvent_spec` | The least successor is an actual event strictly after the given layer |
| `EventInfinitude.no_event_before_next` | No event lies between the given layer and its least successor |
| `EventInfinitude.incomplete_nextEvent_factor_four` | The actual successor supplied by irrationality eventually satisfies nextEvent(n)≤4n |

### Batch 5 conclusions, hypotheses, and boundaries

1. A unit mesh genuinely implies completeness. `unit_mesh_half_line` starts from
   a finite mesh in an original prefix, with gap at most 1, enough span to attach
   the first future term, and positive integer future weights satisfying the
   adjacent doubling bound. It constructs legal extensions and proves their
   right endpoints unbounded; neither an unbounded mesh nor a half-line is
   assumed. `LowGap.next_event_length_complete` derives these conditions from
   actual floors and returns to the frozen interleaving via proved reindexing.
   A gap bound of 1 alone is not sufficient: a qualifying block and normalized
   initial values are also required.
2. Finite descent needs no stepwise transition monotonicity.
   `eventually_not_of_eventual_descent` uses strong induction on the natural
   gap, choosing each later qualifying start after the previous update becomes
   permanent. It therefore does not borrow the then-unproved uniform
   `h_n ≤ N-1` bound or claim to formalize the manuscript's budget of at most
   `N-1` updates. It is an alternative well-founded proof of §6's qualitative result.
3. Irrationality guarantees actual events. If both digit tails vanish, floor
   inequalities and unbounded powers of 2 give `α = a_N/2^N` and
   `β = b_N/2^N`, contradicting the irrational ratio.
   `events_unbounded` does not require normalization or positive parameters.
   The actual least successor has proved existence, strict lateness, and no
   intervening events.
4. The combined result at this stage assumes `Irrational (α/β)`,
   `0 < b_0 < a_0 < 2b_0`, and incompleteness. It gives an `N` such that
   `nextEvent(n) ≤ 4n` for every `n ≥ N`, without placeholder FE/DB/BG,
   descent, or event-existence hypotheses. Incompleteness is an explicit
   contradiction assumption, but the contradiction was not yet obtained.
   The sharper `m < 3n+C` is also proved; the real-ratio `limsup ≤ 3`
   statement was not separately formalized.

This connects milestone 3's qualitative permanent-descent/event-ratio result,
not every statement in §§2–6 verbatim. The cumulative FE/DB/BG contradiction
was still the main unfinished component at this historical stage.

## Batch 6: compiled theorems and manuscript mapping (35)

Names omit `Dyadic354.`; every auxiliary theorem is audited.

| Declaration | Manuscript correspondence |
|---|---|
| `PrefixMesh.translate_union_mesh` | §1.1: translated hulls may be separated; explicitly bound the new bridging gap |
| `PrefixMesh.prefix_zero` | The empty prefix has exactly the distinct-sum set {0} |
| `PrefixMesh.prefix_step` | Exact subset-sum set equality after appending one original index, not just inclusion |
| `PrefixMesh.prefix_encloses` | A nonnegative-weight prefix has actual endpoints 0 and its total sum |
| `PrefixMesh.prefix_span` | Actual prefix span equals the weight sum |
| `PrefixMesh.next_weight_bound` | Adjacent doubling implies c_n≤Σ_(i<n)c_i+c_0 |
| `PrefixMesh.prefix_gap_bound` | §1.1: all prefix gaps of positive integer weights with the doubling bound are at most the first weight |
| `PrefixMesh.internal_run_bound` | Consecutive missing intervals inside the actual hull have length at most the gap bound minus 1 |
| `PrefixBounds.total_eq` | Frozen interleaved total equals the layerwise total of the two sequences |
| `PrefixBounds.total_step` | S_(n+1)=S_n+L_n |
| `PrefixBounds.actual_prefix_encloses` | Actual floor-prefix endpoints are 0 and S_n |
| `PrefixBounds.actual_prefix_span` | Actual floor-prefix span equals S_n |
| `PrefixBounds.actual_prefix_gap` | §1.1: proved pair reindexing gives original prefix gap≤N |
| `PrefixBounds.total_ge_first` | S_n≥a_n for n≥2, by direct induction |
| `PrefixBounds.uniform_cyclic_gap` | (1.1): actual gcd-modular prefix gap h_n≤N−1 for n≥2 |
| `PrefixBounds.internal_missing_run_bound` | §8: every actual prefix has internal missing-run length≤N−1 in [0,S_n] |
| `FECounting.translate_translate` | Successive translations add their offsets |
| `FECounting.values_step` | P_(n+1)=P_n∪(P_n+a_n)∪(P_n+b_n)∪(P_n+L_n) |
| `FECounting.period_step` | L_(n+1)=2L_n+w_n |
| `FECounting.digitSum_bounds` | Actual two-sequence digit sum satisfies 0≤w_n≤2 |
| `FECounting.digitSum_event_iff` | w_n≠0 iff n+1 is an actual arrival event |
| `FECounting.total_lt_period` | Positive initial floors imply S_n<L_n |
| `FECounting.basic_copies_subset` | Both basic copies lie in the next actual prefix |
| `FECounting.basic_copies_disjoint` | P_n and P_n+L_n are disjoint |
| `FECounting.card_translate` | Translation preserves the number of distinct integer values |
| `FECounting.growth_nonneg` | G_n≥0 follows from disjoint basic copies, not truncated subtraction |
| `FECounting.values_subset_period` | All of P_n lies in the actual integer window [0,L_n) |
| `FECounting.deficit_nonneg` | Distinct-sum count is at most window length, so Q_n≥0 |
| `FECounting.padding_step` | B_(n+1)=B_n+w_n |
| `FECounting.padding_identity` | B_n=M+N+Σ_(i<n)w_i |
| `FECounting.padding_bound` | §8: 0<B_n<3N+2n |
| `FECounting.deficit_step` | (8.1): Q_(n+1)=2Q_n+w_n−G_n |
| `FECounting.deficit_zero` | Initial deficit Q_0=M+N−1 |
| `FECounting.deficit_eq_holes` | Q_n is exactly the number of actual missing integer positions in [0,L_n) |
| `FECounting.growth_eq_newValues` | G_n is exactly the number of new integer values outside the two basic copies |

### Batch 6 historical interfaces and unfinished work

- Uniform-gap results require normalized integer initial values
  `0 < b_0 < a_0 < 2b_0`, not irrationality, events, or long blocks.
  `actual_prefix_gap` and internal missing-run bounds hold for all `n`;
  `uniform_cyclic_gap` projects the span to the actual gcd and needs `n ≥ 2`.
  Ordinary integer gaps and cyclic modular gaps are kept distinct.
- The proof of `S_n ≥ a_n` checks layer 2 and inducts using the floor recurrence.
  It does not reproduce the manuscript's stronger exponential lower bound;
  the required span result is independently proved, not assumed.
- `values` is the set of distinct integer sums of finite subsets of original
  indices. Finset unions deduplicate overlapping sums in the four translates.
  Only the two basic copies are proved disjoint, not all four.
- B, Q, and G are integer differences with proved nonnegativity.
  The counting equivalences connect Q and G to actual missing window positions
  and newly added values.
- Batch 6 completed only FE's counting foundations, not its decay theorem.
  Periodic missing-function boundary variation J, missing-run counting (8.2),
  shift bounds (8.3), changing-period comparison (8.4), nonzero-event boundaries
  (8.5), nonoverlapping two-step decay, and accumulated error accounting remained.

All FE obligations listed above were completed in batch 7; they are not current blockers.

## Batch 7: compiled theorems and manuscript mapping (175)

This batch added 29 Lean modules. All auxiliary theorems are listed in
`Audit.lean`. The table highlights core interfaces. The cumulative audit
contained 358 theorems at this stage; the current `logs/axioms.log` includes
all 381, their individual axiom dependencies, and actual `#print` output
for core declarations.

| Core declaration, omitting `Dyadic354.` | Proved content |
|---|---|
| `FEMissingRuns.actual_holes_boundary_bound` | (8.2): actual internal missing-run bounds control Q and the unit boundary |
| `FEShift.variation_le_new_values` | (8.3): actual new sums control the old sequence's shift boundary |
| `PeriodChange.actual_changing_period_bound` | (8.4): comparison of different-period functions with explicit terminal padding |
| `EventBoundary.actual_nonzero_boundary` | (8.5): unit-boundary estimate for every nonzero digit type |
| `FERecurrence.potential_two_step`, `EventDecay.block_bound` | Decay over nonoverlapping event blocks and accumulated error accounting |
| `FE.deficit_exponential_bound` | FE: Q_n ≤ C₀ 2^n exp(-a K_n), with manuscript constants C₀=2(M+N+10), a=1/(64N) |
| `FER.seed_exponential_bound` | FE-R: the longest actual contiguous integer interval satisfies c₀ exp(a K_n) ≤ R_n+2, with the manuscript's c₀ |
| `DBDigits.error_lt_budget`, `suffix_approximation` | (9.1): actual suffix-error budget and legal finite representations using distinct indices |
| `DBCover.propagated_interval`, `DB.interval_complete` | Finite-coefficient windows concatenate with old prefixes to give a sufficiently wide actual interval and completeness |
| `DB.digit_propagation` | DB increment for all coprime rational approximations at the required scale, not finite parameter tests |
| `RationalWindows.before_crossing` | Dirichlet approximation and first-crossing minimality construct the preceding precise small-denominator approximation |
| `DBScale.advance_increment` | With the actual denominator crossing defined, K_f(n) ≥ K_n+(c₀/2)exp(aK_n)-3 for every n≥1 |
| `CubicGrowth.no_eventual_cubic_advance` | Exponential event increments cannot eventually fit within cubic depth growth |
| `BGWindows.arbitrarily_large_windows` | Incompleteness constructs arbitrarily long windows satisfying precision, h²≤4T, layerwise errors, and logarithmic event sparsity simultaneously |
| `BGExactLayers.nonexact_count` | (11.2): at most hK_T+h nonexact layers, including the final h layers |
| `BGSparseCompact.irrational_separation` | Ratios using bounded joint binary support belong to an all-rational compact set, separated from a fixed irrational |
| `BGReturns.return_cost_unbounded` | Uniform return-cost divergence needed for (11.3), without bounding the common multiplier or gcd |
| `BGGeometric.cost_bound`, `BGCapacity.eventual_capacity` | Enough nonoverlapping exact returns fit in one window, with total event cost exceeding its budget |
| `BG.bounded_event_windows_complete` | BG: eventual bounded-ratio event windows and an irrational ratio imply normalized completeness |
| `BG.normalized_complete` | The proved factor-four successor-event bound removes the event-window hypothesis |

### Implementation differences and acceptance boundaries

1. FE error summation uses the potential `z_n+9(n+1)/2^n` and induction over
   nonoverlapping blocks. Final FE and FE-R constants match the manuscript;
   the error budget is not assumed.
2. DB directly constructs representations of each target integer, without an
   unproved claim about movement of order statistics. Original-prefix and suffix
   index supports are proved disjoint. Equal sum values do not mean reusing an index.
3. §§10–11 use all good rationals satisfying `|θ-r| < 1/den(r)²`.
   The proof establishes finiteness at bounded denominators, arbitrarily large
   good denominators for irrationals, existence of the first crossing, and the
   required precision of the previous small-denominator approximation.
   Constructed long windows satisfy all later conditions; BG is not supplied with
   an extra window hypothesis. The numbered continued-fraction denominators
   `q_j` and literal statement (10.2) are not formalized here and are not missing
   dependencies of this implementation. The generic `DB.digit_propagation`
   interface also applies to convergents satisfying its approximation conditions.
4. Return cost uses actual binary support and an all-rational compact set,
   without separately defining `min_c popcount((cp) OR (cq))`.
   The conclusion quantifies all exact returns and all common multipliers.
5. The cumulative contradiction takes `K_T/k+1` returns, with eventual seed
   length below `T^(3/4)`, geometric growth at most `T^(1/8)`, and the remaining
   `T^(1/8)` absorbing constants. It proves the same BG conclusion without
   reproducing the manuscript's `T^(2/3)` or its particular return-count bound.
6. Both manuscripts, the certificate, frozen `Statements.lean`, toolchain, and
   dependency locks were unchanged. Compiled sources contain no `sorry`,
   custom axioms, or `native_decide`; the transitive axiom audit is the
   acceptance criterion.

## Batch 8: compiled theorems and manuscript mapping (23)

Five modules were added: `Normalization.lean`, `SetBridge.lean`, `Main.lean`,
`UpstreamDefinitions.lean`, and `UpstreamBridge.lean`.
Names below omit `Dyadic354.`; all theorems and auxiliary lemmas are audited.

| Declaration | Manuscript correspondence |
|---|---|
| `Normalization.term_shift` | Multiplying upward by 2^u gives exactly the original term at n+u |
| `Normalization.shifted_irrational` | Independent upward shifts preserve the irrational ratio |
| `Normalization.balance_larger`, `balance` | Adjacent powers-of-two bounds and irrationality excluding endpoints give a strict ratio using only nonnegative shifts |
| `Normalization.common_shift`, `above_bound` | Overcome floor errors and put every retained normalized-tail term above any specified integer bound |
| `SetBridge.normalized_sorted_strictMono`, `normalized_injective` | Strict interlacing gives injective values even though the original a,b enumeration is not monotone |
| `SetBridge.normalized_lower_bound` | Every retained term is at least the first smaller term |
| `SetBridge.indexed_to_set` | Convert finite-index representations of an injective sequence into finite sets of distinct values |
| `SetBridge.setComplete_mono`, `set_to_indexed` | Monotonicity of set completeness and conversion of set representations to legal original indices |
| `SetBridge.shifted_range_subset` | Independently shifted sequences really are tails of the original sequences |
| `erdos354_strong_completeness` | For every finite deletion set, choose a normalized tail above its bound and apply the complete proof chain |
| `erdos354_part_i` | Frozen #354(i) for all positive real parameters, with no extra premises |
| `UpstreamBridge.floorMultiples_eq`, `interleave_eq` | Equalities between the original sequences and exact upstream definitions |
| `UpstreamBridge.indexedComplete_iff`, `setComplete_iff`, `strongComplete_iff` | Equivalences for representations and finite-deletion quantifiers in upstream definitions |
| `UpstreamBridge.partITarget_iff` | Bidirectional equivalence of upstream extended-quantifier order and frozen PartI |
| `UpstreamBridge.erdos354_part_i_upstream`, `erdos354_strong_upstream` | Both final conclusions in the exact upstream-definition types |

### Upstream and toolchain boundaries

The pinned upstream revision uses Lean/Mathlib 4.33.1. This project remains on
4.27.0 without an upgrade. Seven upstream definition blocks are extracted
verbatim; the positive target RHS only adds necessary namespace qualification.
Snapshot hashes, definition blocks, and target text are checked automatically,
and the pinned public sources were also compared byte-for-byte online.
Beyond these syntax checks, Lean proves definition and target-type equivalences;
the final adapter theorems pass the same axiom audit.

Complete upstream files containing conjecture placeholders are stored only as
`.txt` provenance data and are not Lean imports. No full upstream 4.33.1 build
or upstream PR has been performed or claimed.

## Completion of the frozen targets

- `Dyadic354.PartI`: arbitrary positive real α and β, irrational ratio, fixed
  base 2, eventual coverage by finite-index sums of the floor interleaving.
- `Dyadic354.StrongCompleteness`: set completeness after deleting any finite
  set of values.

Both remain unchanged `Prop` definitions, realized by the two proved theorems
in `Main.lean`. The targets were not weakened, nor completed using additional
typeclasses, placeholders, or hypotheses that supply the conclusion.

## Acceptance boundaries and optional follow-up

1. Both frozen mathematical targets are complete, with no remaining mathematical
   hypotheses awaiting proof. Part (ii) is outside this task.
2. Fresh rebuilding reuses only the pinned dependency cache, not this project's
   compiled artifacts. Mathlib was not rebuilt from scratch, and no independent
   checker or comparator was run. These remain possible additional checks.
3. Full-upstream integration, toolchain migration, and an upstream PR are separate
   integration tasks and were not performed.
4. The implementation uses proved rational-approximation windows and compact
   return-cost interfaces. Literal coverage of every manuscript statement could
   additionally include §6's `N-1` update budget, `limsup ≤ 3`, the numbered
   continued-fraction version of (10.2), and explicit minimum popcount.
   None is a missing dependency of the final `PartI` or `StrongCompleteness`.

There are no remaining compilation blockers for this batch. Historical failure
and repair logs are retained; failures were not bypassed by adding
conclusion-supplying hypotheses. Any later mathematical gap should still be
reported separately: a successful build is not a substitute for proving a target.

## Publication status

### Current publication: all frozen targets

On 2026-09-13, at the maintainer's explicit request, the committed batch 7 and 8
results were pushed to GitHub, and `lean-formalization` was fast-forward merged
into [main](https://github.com/Andrewyzzz/erdos354/tree/main).
The final verified source commit is
[59e5957ac8bf28623318cebec6c67b1a672ad49e](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e).

It contains part (i), strong completeness, the exact-upstream-definition adapter,
and build, transitive-axiom-audit, and fresh-rebuild records for 381 theorems.
The subsequent publication-record update changed no verified source or dependency.
No force push, GitHub Release, upstream PR, or forum post was made.
The manuscripts, archive, and certificate retain their original bytes and
candidate/community-status notices. Later English-first navigation and
documentation updates are separate from the frozen mathematical inputs.

### Historical publication: batches 1–6

Batches 1–6 were developed locally on `lean-formalization`, without automatic
pushes during development. On 2026-09-13, at the maintainer's explicit request,
the six verified batches were pushed to
[lean-formalization](https://github.com/Andrewyzzz/erdos354/tree/lean-formalization),
with verified source commit `04c0593bba303281787f2bccc5450a3e879dcfd6`.

That push included sources, locked dependencies, status documents, and actual
build/axiom-audit logs. The manuscripts and certificate were unchanged.
At that time there was no merge to `main`, Release, or forum post.
The public result was staged formalization progress, not a completed proof
of all of #354(i).

The batch 7 FE/DB/BG commit is `1e6e6d93661dbaa67700ee77097901ea66f276cd`.
Batches 7 and 8 were initially local only; they are now pushed and merged as
recorded under "Current publication" above.
