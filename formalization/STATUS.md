# Theorem map

We prove both frozen targets for arbitrary positive real parameters with
irrational ratio. The formalization comprises 381 audited local theorems.
The exact declarations and their transitive axiom output are enumerated in
[Audit.lean](Dyadic354/Audit.lean); [RESULTS.md](RESULTS.md) records the builds.

## Final results

| Declaration | Conclusion |
|---|---|
| `Dyadic354.erdos354_part_i` | `PartI`: eventual finite-index representability for the interleaved dyadic floor sequences |
| `Dyadic354.erdos354_strong_completeness` | `StrongCompleteness`: eventual distinct-value representability after any finite deletion |
| `Dyadic354.UpstreamBridge.erdos354_part_i_upstream` | Positive part-(i) target in the exact extracted upstream definitions |
| `Dyadic354.UpstreamBridge.erdos354_strong_upstream` | Strong completeness in the extracted upstream set definitions |

The targets are defined in [Statements.lean](Dyadic354/Statements.lean)
and proved in [Main.lean](Dyadic354/Main.lean). The upstream conclusions
are in [UpstreamBridge.lean](Dyadic354/UpstreamBridge.lean).
No FE/DB/BG, normalized-initial-value, long-window, or permanent-descent
assumption is added to the final statements.

## Principal declarations

All names below have the prefix `Dyadic354.`. Section references are to
the [formalization-aligned English manuscript](../proof/FORMALIZED_PROOF.md).

| Sections | Declaration | Mathematical content |
|---|---|---|
| §1 | `Normalization.above_bound` | Upward dyadic tail shifts, normalized initial values, and avoidance of any prescribed integer bound |
| §1 | `SetBridge.normalized_injective` | Injectivity of the normalized interleaving |
| §1 | `PrefixBounds.uniform_cyclic_gap` | Uniform modular missing-run bound for actual floor prefixes |
| §2 | `CyclicGaps.erosion_exact` | Exact erosion of missing runs by a one-step translate |
| §2 | `Mesh.translate_union_gap_span` | Mesh propagation under an admissible translate |
| §2 | `Mesh.projection_gap` | Projection to every positive modulus bounded by the span |
| §3 | `Certificate.checkCertificate_sound` | Checker acceptance implies universal coefficient-chain semantics |
| §3 | `Certificate.certificate_correct` | The twelve mask chains give the required coverage for every admissible integer pair |
| §4 | `InitialMesh.prefix_initial_mesh` | A mesh of legal original-index subset sums with sufficient span |
| §5 | `PermanentMesh.certificate_permanent_descent` | Permanent gap control for every admissible future continuation |
| §5 | `FloorDescent.long_block_descent` | Descent at the actual floor-sequence gcd moduli |
| §5 | `BlockLength.next_event_length_descent` | An explicit event-gap length sufficient for permanent descent |
| §6 | `EventGaps.unbounded_qualifying_complete` | Completeness from unbounded qualifying blocks by well-founded descent |
| §6 | `EventInfinitude.events_unbounded` | Infinitely many actual binary events from irrationality |
| §6 | `EventInfinitude.incomplete_nextEvent_factor_four` | Eventual factor-four successor-event bound under incompleteness |
| §7 | `SetBridge.indexed_to_set` | Indexed completeness of an injective sequence implies completeness of its value set |
| §7 | `SetBridge.set_to_indexed` | Set completeness implies the corresponding indexed statement |
| §8 | `FECounting.deficit_step` | Exact deficit recurrence on actual finite subset-sum sets |
| §8.1 | `PeriodChange.actual_changing_period_bound` | Comparison of missing words with different periods |
| §8.1 | `EventBoundary.actual_nonzero_boundary` | Unit-boundary estimate for every nonzero digit type |
| §8.2 | `FE.deficit_exponential_bound` | FE with the stated constants |
| §8.3 | `FER.seed_exponential_bound` | Exponential lower bound on the largest represented interval |
| §9 | `DBCover.propagated_interval` | Legal finite-index interval coverage using an old seed and a disjoint suffix |
| §9 | `DB.digit_propagation` | The digit-budget increment |
| §10.1 | `DBScale.arbitrarily_large_advance` | Arbitrarily large advances beyond the cubic bound |
| §10.2 | `BGWindows.arbitrarily_large_windows` | Simultaneous rational precision, small height, and logarithmic event count |
| §11.1 | `BGExactLayers.nonexact_count` | At most `H*K_T + H` nonexact layers |
| §11.2 | `BGReturns.return_cost_unbounded` | Uniform event cost of a nontrivial exact return near an irrational ratio |
| §11.3 | `BGCapacity.eventual_capacity` | Enough geometrically separated layers within each sufficiently large window |
| §11.3 | `BG.bounded_event_windows_complete` | Completeness under bounded event spacing and irrationality |
| §11.3 | `BG.normalized_complete` | Completeness for normalized parameters with irrational ratio |

## Mathematical correspondence

The current English manuscript incorporates the following choices made
in the formal proof. The original manuscript remains a fixed source for
comparison.

| Interface | Formalized argument |
|---|---|
| Prefix span, §1.1 | Direct induction from layer 2 proves `S_n ≥ a_n`. |
| Block length, §5 | We use the explicit sufficient constant `C_M = 16(M+1)^2`. |
| Event spacing, §6 | Well-founded descent gives eventual absence of qualifying gaps and a factor-four bound. |
| FE error budget, §8.2 | The potential `V_n = Q_n/2^n + 9(n+1)/2^n` absorbs the two-step errors. |
| DB interval coverage, §9 | Each target integer is represented directly by an old interval value and a legal, disjoint suffix sum. |
| Rational windows, §10 | Least denominator crossings among all good rational approximants replace continued-fraction numbering. |
| Return cost, §11.2 | Compact sets of ratios of bounded sparse dyadic sums give a uniform neighbourhood exclusion. |
| BG capacity, §11.3 | The bound `x ≤ T^(3/4)`, combined with `B^r ≤ B*T^(1/8)`, fits the required disjoint returns inside the window. |

These are proved implementations of the displayed arguments. The final
statement definitions and the original coefficient data are unchanged.

## Certificate semantics

The certificate has twelve chains, 125 nodes, and 113 adjacent links.
For every node, all four third-digit types are quantified, giving 500
node/type instances. The coefficients and constants are recomputed from
the masks. Soundness proves legal six-position subset sums, constants
differing by one, positive widths, two-sided overlaps, and endpoint coverage.

Writing `p = 2x+y` and `q = x+y` with `x,y > 0` connects the finite
coefficient inequalities to the entire open cone. Kernel evaluation checks
the concrete data; generic theorems prove their universal meaning.

## Verification

Every listed declaration is included in the default build and the complete
axiom audit. All 381 transitive axiom sets are subsets of
`{propext, Classical.choice, Quot.sound}`.
The [build records](RESULTS.md) include both an ordinary local build and
a fresh-source rebuild with pinned dependencies.
