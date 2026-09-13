import Dyadic354.Statements
import Dyadic354.CertificateData
import Dyadic354.Mesh
import Dyadic354.PermanentMesh
import Dyadic354.BlockLength
import Dyadic354.EventInfinitude
import Dyadic354.FECounting
import Dyadic354.DB
import Dyadic354.BGReturns
import Dyadic354.RationalWindows
import Dyadic354.BG
import Dyadic354.UpstreamBridge

#print Dyadic354.PartI
#print Dyadic354.StrongCompleteness
#print Dyadic354.IndexedComplete
#print Dyadic354.SetStronglyComplete
#print Dyadic354.interleave
#print Dyadic354.floorMultiples
#print Dyadic354.dyadicValueSet
#print Dyadic354.SetComplete
#print Dyadic354.IsSubsetSum
#print Dyadic354.Certificate.MathematicallyCorrect
#print Dyadic354.Certificate.ChainMeaning
#print Dyadic354.Certificate.NodeMeaning
#check Dyadic354.Certificate.certificate_correct
#check Dyadic354.Certificate.all_templates_correct
#check Dyadic354.Certificate.weights_explicit

#print Dyadic354.CyclicGaps.MissingRun
#print Dyadic354.CyclicGaps.gap
#print Dyadic354.Mesh.Consecutive
#print Dyadic354.Mesh.gap
#print Dyadic354.Mesh.span
#print Dyadic354.Mesh.MeshOn
#check Dyadic354.CyclicGaps.erosion_exact
#check Dyadic354.Mesh.translate_union_gap_span
#check Dyadic354.Mesh.projection_gap
#check Dyadic354.Mesh.propagate_iterate

#print Dyadic354.Representations.PackedIndex
#print Dyadic354.Representations.position
#print Dyadic354.Representations.packedWeights
#print Dyadic354.InitialMesh.threshold
#check Dyadic354.CoefficientInterval.bounded_interval
#check Dyadic354.Representations.block_interval
#check Dyadic354.NodeRepresentations.node_representation
#check Dyadic354.NodeRepresentations.node_window
#check Dyadic354.InitialMesh.certificate_initial_mesh
#check Dyadic354.InitialMesh.prefix_initial_mesh
#check Dyadic354.PermanentMesh.permanent_projection
#check Dyadic354.PermanentMesh.certificate_permanent_descent

#print Dyadic354.FloorSequence.correction
#print Dyadic354.FloorSequence.bit
#print Dyadic354.ExactBlock.IsEvent
#print Dyadic354.PairReindex.swapAfter
#print Dyadic354.FloorDescent.modulus
#print Dyadic354.FloorDescent.pCoord
#print Dyadic354.FloorDescent.qCoord
#print Dyadic354.FloorDescent.gapAt
#print Dyadic354.BlockLength.growthConstant
#check Dyadic354.FloorSequence.recurrence
#check Dyadic354.FloorSequence.normalized_bounds
#check Dyadic354.FloorSequence.prefix_deficit
#check Dyadic354.PairReindex.prefixSums_reindex
#check Dyadic354.ExactBlock.six_after_exact_block
#check Dyadic354.FloorDescent.long_block_descent
#check Dyadic354.FloorDescent.next_event_descent
#check Dyadic354.BlockLength.threshold_of_length
#check Dyadic354.BlockLength.next_event_length_descent

#print Dyadic354.EventGaps.QualifyingGap
#print Dyadic354.EventInfinitude.nextEvent
#check Dyadic354.UnitMesh.unit_mesh_half_line
#check Dyadic354.UnitMesh.unit_mesh_complete
#check Dyadic354.LowGap.next_event_length_complete
#check Dyadic354.EventGaps.eventually_not_of_eventual_descent
#check Dyadic354.EventGaps.unbounded_qualifying_complete
#check Dyadic354.EventGaps.incomplete_event_step_bound
#check Dyadic354.EventGaps.incomplete_event_factor_four
#check Dyadic354.EventInfinitude.zero_tail_dyadic
#check Dyadic354.EventInfinitude.events_unbounded
#check Dyadic354.EventInfinitude.incomplete_nextEvent_factor_four

#print Dyadic354.PrefixBounds.total
#print Dyadic354.PrefixBounds.period
#print Dyadic354.FECounting.values
#print Dyadic354.FECounting.digitSum
#print Dyadic354.FECounting.padding
#print Dyadic354.FECounting.deficit
#print Dyadic354.FECounting.growth
#print Dyadic354.FECounting.holes
#print Dyadic354.FECounting.newValues
#check Dyadic354.PrefixMesh.prefix_gap_bound
#check Dyadic354.PrefixBounds.total_ge_first
#check Dyadic354.PrefixBounds.uniform_cyclic_gap
#check Dyadic354.PrefixBounds.internal_missing_run_bound
#check Dyadic354.FECounting.values_step
#check Dyadic354.FECounting.basic_copies_disjoint
#check Dyadic354.FECounting.growth_nonneg
#check Dyadic354.FECounting.deficit_step
#check Dyadic354.FECounting.padding_identity
#check Dyadic354.FECounting.padding_bound
#check Dyadic354.FECounting.deficit_eq_holes
#check Dyadic354.FECounting.growth_eq_newValues

#print axioms Dyadic354.mem_finiteSubsetSums
#print axioms Dyadic354.Linear.eval_add
#print axioms Dyadic354.Linear.eval_sub
#print axioms Dyadic354.Linear.cone_identity
#print axioms Dyadic354.Linear.nonneg_on_cone
#print axioms Dyadic354.Linear.positive_on_cone
#print axioms Dyadic354.indexedComplete_iff
#print axioms Dyadic354.Certificate.offset_eq_sum
#print axioms Dyadic354.Certificate.offset_isSubsetSum
#print axioms Dyadic354.Certificate.weights_explicit
#print axioms Dyadic354.Certificate.endpoints_sound
#print axioms Dyadic354.Certificate.node_sound
#print axioms Dyadic354.Certificate.interval_chain_covers
#print axioms Dyadic354.Certificate.chain_sound
#print axioms Dyadic354.Certificate.checkCertificate_sound
#print axioms Dyadic354.Certificate.certificate_checked
#print axioms Dyadic354.Certificate.certificate_correct
#print axioms Dyadic354.Certificate.all_templates_checked
#print axioms Dyadic354.Certificate.all_templates_correct
#print axioms Dyadic354.Certificate.certificate_counts

#print axioms Dyadic354.CyclicGaps.gapBound_mono
#print axioms Dyadic354.CyclicGaps.not_missingRun_iff
#print axioms Dyadic354.CyclicGaps.gapBound_erode_iff
#print axioms Dyadic354.CyclicGaps.modulus_bound
#print axioms Dyadic354.CyclicGaps.gap_spec
#print axioms Dyadic354.CyclicGaps.gap_le_iff
#print axioms Dyadic354.CyclicGaps.gap_lt_modulus
#print axioms Dyadic354.CyclicGaps.missingRun_iff_le_gap
#print axioms Dyadic354.CyclicGaps.erode_nonempty
#print axioms Dyadic354.CyclicGaps.lift_erode
#print axioms Dyadic354.CyclicGaps.erosion_exact
#print axioms Dyadic354.CyclicGaps.gap_eq_zero_iff_full
#print axioms Dyadic354.CyclicGaps.gap_modulus_one
#print axioms Dyadic354.Mesh.gap_le_iff
#print axioms Dyadic354.Mesh.gap_empty
#print axioms Dyadic354.Mesh.gap_singleton
#print axioms Dyadic354.Mesh.encloses_min_max
#print axioms Dyadic354.Mesh.span_of_encloses
#print axioms Dyadic354.Mesh.span_singleton
#print axioms Dyadic354.Mesh.meshOn_gap_le
#print axioms Dyadic354.Mesh.meshOn_of_gap_le
#print axioms Dyadic354.Mesh.meshOn_iff_gap_le
#print axioms Dyadic354.Mesh.gap_positive_of_encloses
#print axioms Dyadic354.Mesh.meshOn_translate_union
#print axioms Dyadic354.Mesh.translate_union_nonempty
#print axioms Dyadic354.Mesh.translate_union_gap_span
#print axioms Dyadic354.Mesh.residues_nonempty
#print axioms Dyadic354.Mesh.projection_window_bound
#print axioms Dyadic354.Mesh.projection_gap
#print axioms Dyadic354.Mesh.extend_nonempty
#print axioms Dyadic354.Mesh.propagate_iterate

#print axioms Dyadic354.CoefficientInterval.lower_interval
#print axioms Dyadic354.CoefficientInterval.bounded_interval
#print axioms Dyadic354.CoefficientInterval.binary_sum_exists
#print axioms Dyadic354.Representations.subsetSum_disjSum
#print axioms Dyadic354.Representations.subsetSum_embed
#print axioms Dyadic354.Representations.binary_scaled
#print axioms Dyadic354.Representations.block_interval
#print axioms Dyadic354.Representations.position_injective
#print axioms Dyadic354.Representations.position_lt
#print axioms Dyadic354.Representations.packed_weights_match
#print axioms Dyadic354.Representations.packed_to_prefix
#print axioms Dyadic354.Representations.prefix_block_offset
#print axioms Dyadic354.NodeRepresentations.residual_bounds
#print axioms Dyadic354.NodeRepresentations.old_sum_bounds
#print axioms Dyadic354.NodeRepresentations.mask_representation
#print axioms Dyadic354.NodeRepresentations.node_representation
#print axioms Dyadic354.NodeRepresentations.oldResidues_nonempty
#print axioms Dyadic354.NodeRepresentations.lift_oldResidues_iff
#print axioms Dyadic354.NodeRepresentations.node_window
#print axioms Dyadic354.InitialMesh.margin_budget
#print axioms Dyadic354.InitialMesh.trimmed_chain_covers
#print axioms Dyadic354.InitialMesh.chain_windows
#print axioms Dyadic354.InitialMesh.mesh_from_windows
#print axioms Dyadic354.InitialMesh.span_budget
#print axioms Dyadic354.InitialMesh.certificate_initial_mesh
#print axioms Dyadic354.InitialMesh.prefix_initial_mesh
#print axioms Dyadic354.PermanentMesh.prefix_nonempty
#print axioms Dyadic354.PermanentMesh.extend_step_subset
#print axioms Dyadic354.PermanentMesh.extend_subset_prefix
#print axioms Dyadic354.PermanentMesh.gap_of_subset
#print axioms Dyadic354.PermanentMesh.permanent_projection
#print axioms Dyadic354.PermanentMesh.certificate_permanent_descent

#print axioms Dyadic354.FloorSequence.correction_bounds
#print axioms Dyadic354.FloorSequence.digit_bit
#print axioms Dyadic354.FloorSequence.recurrence
#print axioms Dyadic354.FloorSequence.next_bounds
#print axioms Dyadic354.FloorSequence.normalized_bounds
#print axioms Dyadic354.FloorSequence.prefix_deficit
#print axioms Dyadic354.FloorSequence.prefix_sum_lt
#print axioms Dyadic354.FloorSequence.interleave_even
#print axioms Dyadic354.FloorSequence.interleave_odd
#print axioms Dyadic354.FloorSequence.paired_prefix_sum
#print axioms Dyadic354.FloorSequence.paired_prefix_lt
#print axioms Dyadic354.PairReindex.swapAfter_before
#print axioms Dyadic354.PairReindex.swapAfter_even
#print axioms Dyadic354.PairReindex.swapAfter_odd
#print axioms Dyadic354.PairReindex.index_cases
#print axioms Dyadic354.PairReindex.swapAfter_involutive
#print axioms Dyadic354.PairReindex.swapAfter_injective
#print axioms Dyadic354.PairReindex.swapAfter_lt_iff
#print axioms Dyadic354.PairReindex.prefixSums_reindex_subset
#print axioms Dyadic354.PairReindex.prefixSums_reindex
#print axioms Dyadic354.PairReindex.sortedTail_even
#print axioms Dyadic354.PairReindex.sortedTail_odd
#print axioms Dyadic354.PairReindex.sortedTail_positive
#print axioms Dyadic354.PairReindex.sortedTail_doubling
#print axioms Dyadic354.ExactBlock.no_events_zero_digits
#print axioms Dyadic354.ExactBlock.exact_block
#print axioms Dyadic354.ExactBlock.after_exact_block
#print axioms Dyadic354.ExactBlock.interleave_block
#print axioms Dyadic354.ExactBlock.three_pairs
#print axioms Dyadic354.ExactBlock.six_after_exact_block
#print axioms Dyadic354.ExactBlock.next_small_weight_bound
#print axioms Dyadic354.FloorDescent.fin_prefix_iff
#print axioms Dyadic354.FloorDescent.oldResidues_prefix
#print axioms Dyadic354.FloorDescent.modulus_positive
#print axioms Dyadic354.FloorDescent.gcd_coordinates
#print axioms Dyadic354.FloorDescent.interleave_positive
#print axioms Dyadic354.FloorDescent.long_block_descent
#print axioms Dyadic354.FloorDescent.next_event_descent
#print axioms Dyadic354.BlockLength.threshold_le_square
#print axioms Dyadic354.BlockLength.floor_upper
#print axioms Dyadic354.BlockLength.coordinate_upper
#print axioms Dyadic354.BlockLength.growthConstant_bound
#print axioms Dyadic354.BlockLength.threshold_of_length
#print axioms Dyadic354.BlockLength.next_event_length_descent

#print axioms Dyadic354.PairReindex.isSubsetSum_reindex_iff
#print axioms Dyadic354.PairReindex.indexedComplete_reindex_iff
#print axioms Dyadic354.FloorDescent.long_block_mesh
#print axioms Dyadic354.UnitMesh.mem_extend
#print axioms Dyadic354.UnitMesh.add_sum_mem_extend
#print axioms Dyadic354.UnitMesh.positive_sum_ge_length
#print axioms Dyadic354.UnitMesh.unit_mesh_half_line
#print axioms Dyadic354.UnitMesh.unit_mesh_complete
#print axioms Dyadic354.LowGap.long_block_complete
#print axioms Dyadic354.LowGap.next_event_length_complete
#print axioms Dyadic354.EventGaps.eventually_not_of_eventual_descent
#print axioms Dyadic354.EventGaps.incomplete_eventually_no_qualifying
#print axioms Dyadic354.EventGaps.unbounded_qualifying_complete
#print axioms Dyadic354.EventGaps.incomplete_event_step_bound
#print axioms Dyadic354.EventGaps.incomplete_event_factor_four
#print axioms Dyadic354.EventInfinitude.zero_tail_dyadic
#print axioms Dyadic354.EventInfinitude.no_events_tail_digits
#print axioms Dyadic354.EventInfinitude.events_unbounded
#print axioms Dyadic354.EventInfinitude.nextEvent_spec
#print axioms Dyadic354.EventInfinitude.no_event_before_next
#print axioms Dyadic354.EventInfinitude.incomplete_nextEvent_factor_four

#print axioms Dyadic354.PrefixMesh.translate_union_mesh
#print axioms Dyadic354.PrefixMesh.prefix_zero
#print axioms Dyadic354.PrefixMesh.prefix_step
#print axioms Dyadic354.PrefixMesh.prefix_encloses
#print axioms Dyadic354.PrefixMesh.prefix_span
#print axioms Dyadic354.PrefixMesh.next_weight_bound
#print axioms Dyadic354.PrefixMesh.prefix_gap_bound
#print axioms Dyadic354.PrefixMesh.internal_run_bound
#print axioms Dyadic354.PrefixBounds.total_eq
#print axioms Dyadic354.PrefixBounds.total_step
#print axioms Dyadic354.PrefixBounds.actual_prefix_encloses
#print axioms Dyadic354.PrefixBounds.actual_prefix_span
#print axioms Dyadic354.PrefixBounds.actual_prefix_gap
#print axioms Dyadic354.PrefixBounds.total_ge_first
#print axioms Dyadic354.PrefixBounds.uniform_cyclic_gap
#print axioms Dyadic354.PrefixBounds.internal_missing_run_bound
#print axioms Dyadic354.FECounting.translate_translate
#print axioms Dyadic354.FECounting.values_step
#print axioms Dyadic354.FECounting.period_step
#print axioms Dyadic354.FECounting.digitSum_bounds
#print axioms Dyadic354.FECounting.digitSum_event_iff
#print axioms Dyadic354.FECounting.total_lt_period
#print axioms Dyadic354.FECounting.basic_copies_subset
#print axioms Dyadic354.FECounting.basic_copies_disjoint
#print axioms Dyadic354.FECounting.card_translate
#print axioms Dyadic354.FECounting.growth_nonneg
#print axioms Dyadic354.FECounting.deficit_nonneg
#print axioms Dyadic354.FECounting.padding_step
#print axioms Dyadic354.FECounting.padding_identity
#print axioms Dyadic354.FECounting.padding_bound
#print axioms Dyadic354.FECounting.deficit_step
#print axioms Dyadic354.FECounting.deficit_zero
#print axioms Dyadic354.FECounting.values_subset_period
#print axioms Dyadic354.FECounting.deficit_eq_holes
#print axioms Dyadic354.FECounting.growth_eq_newValues

#check Dyadic354.FE.deficit_exponential_bound
#check Dyadic354.FER.seed_exponential_bound
#check Dyadic354.DB.digit_propagation
#check Dyadic354.BGExactLayers.nonexact_count
#check Dyadic354.BGReturns.return_cost_unbounded

#print axioms Dyadic354.BGBinaryRatio.normalize_power
#print axioms Dyadic354.BGBinaryRatio.ratio_mem
#print axioms Dyadic354.BGExactLayers.delta_error_bound
#print axioms Dyadic354.BGExactLayers.quiet_scaling
#print axioms Dyadic354.BGExactLayers.exact_of_quiet
#print axioms Dyadic354.BGExactLayers.nonexact_sees_event
#print axioms Dyadic354.BGExactLayers.window_count_bound
#print axioms Dyadic354.BGExactLayers.nonexact_count
#print axioms Dyadic354.BGReturns.word_step
#print axioms Dyadic354.BGReturns.word_polynomial
#print axioms Dyadic354.BGReturns.support_card
#print axioms Dyadic354.BGReturns.support_polynomials
#print axioms Dyadic354.BGReturns.exact_word_relation
#print axioms Dyadic354.BGReturns.return_ratio_mem
#print axioms Dyadic354.BGReturns.return_cost_unbounded
#print axioms Dyadic354.BGSparseCompact.atoms_compact
#print axioms Dyadic354.BGSparseCompact.atom_rational
#print axioms Dyadic354.BGSparseCompact.sums_compact
#print axioms Dyadic354.BGSparseCompact.sum_rational
#print axioms Dyadic354.BGSparseCompact.zero_mem_sums
#print axioms Dyadic354.BGSparseCompact.sums_mono
#print axioms Dyadic354.BGSparseCompact.finset_sum_mem
#print axioms Dyadic354.BGSparseCompact.ratios_compact
#print axioms Dyadic354.BGSparseCompact.ratio_rational
#print axioms Dyadic354.BGSparseCompact.irrational_not_mem_ratios
#print axioms Dyadic354.BGSparseCompact.irrational_separation
#print axioms Dyadic354.BGSparseCompact.eventually_not_bounded
#print axioms Dyadic354.ContiguousSeed.interval_width_le
#print axioms Dyadic354.ContiguousSeed.width_attained
#print axioms Dyadic354.ContiguousSeed.next_hole
#print axioms Dyadic354.ContiguousSeed.represented_card_bound
#print axioms Dyadic354.ContiguousSeed.width_count_bound
#print axioms Dyadic354.CyclicBoundary.sum_shift
#print axioms Dyadic354.CyclicBoundary.variation_nonneg
#print axioms Dyadic354.CyclicBoundary.variation_zero
#print axioms Dyadic354.CyclicBoundary.variation_neg
#print axioms Dyadic354.CyclicBoundary.variation_add_le
#print axioms Dyadic354.CyclicBoundary.missing_bounds
#print axioms Dyadic354.CyclicBoundary.variation_missing
#print axioms Dyadic354.CyclicBoundary.variation_double
#print axioms Dyadic354.CyclicBoundary.variation_shift
#print axioms Dyadic354.CyclicBoundary.variation_boundary_le
#print axioms Dyadic354.DB.interval_complete
#print axioms Dyadic354.DB.incomplete_seed_lt_error
#print axioms Dyadic354.DB.incomplete_seed_budget
#print axioms Dyadic354.DB.digit_propagation
#print axioms Dyadic354.DBCover.real_normalization
#print axioms Dyadic354.DBCover.coefficient_approximation
#print axioms Dyadic354.DBCover.propagated_interval
#print axioms Dyadic354.DBDigits.residual_bounds
#print axioms Dyadic354.DBDigits.residual_step
#print axioms Dyadic354.DBDigits.residual_telescope
#print axioms Dyadic354.DBDigits.digit_budget
#print axioms Dyadic354.DBDigits.error_nonneg
#print axioms Dyadic354.DBDigits.error_lt_budget
#print axioms Dyadic354.DBDigits.error_le_length
#print axioms Dyadic354.DBDigits.column_suffix
#print axioms Dyadic354.DBDigits.subset_error_bound
#print axioms Dyadic354.DBDigits.suffix_legality
#print axioms Dyadic354.DBDigits.suffix_approximation
#print axioms Dyadic354.DBDigits.prefix_suffix_add
#print axioms Dyadic354.DBPhases.residue_lift
#print axioms Dyadic354.DBPhases.phase_after
#print axioms Dyadic354.DBWindows.start_bounds
#print axioms Dyadic354.DBWindows.window_after
#print axioms Dyadic354.DBWindows.global_after
#print axioms Dyadic354.DBWindows.span_large
#print axioms Dyadic354.DBWindows.endpoints_legal
#print axioms Dyadic354.DBWindows.global_at_or_after
#print axioms Dyadic354.EventBoundary.segment_variation_le
#print axioms Dyadic354.EventBoundary.compare_segment
#print axioms Dyadic354.EventBoundary.add_shift_cancel
#print axioms Dyadic354.EventBoundary.first_digit_one
#print axioms Dyadic354.EventBoundary.second_digit_one
#print axioms Dyadic354.EventBoundary.actual_nonzero_boundary
#print axioms Dyadic354.EventDecay.block_bound
#print axioms Dyadic354.EventDecay.power_le_exp
#print axioms Dyadic354.FE.potential_zero
#print axioms Dyadic354.FE.normalized_power_bound
#print axioms Dyadic354.FE.rate_positive
#print axioms Dyadic354.FE.constant_positive
#print axioms Dyadic354.FE.deficit_exponential_bound
#print axioms Dyadic354.FEMissingRuns.successor_after_hole
#print axioms Dyadic354.FEMissingRuns.internal_holes_card
#print axioms Dyadic354.FEMissingRuns.holes_split_bound
#print axioms Dyadic354.FEMissingRuns.holes_boundary_bound
#print axioms Dyadic354.FEMissingRuns.actual_holes_boundary_bound
#print axioms Dyadic354.FER.term_lower
#print axioms Dyadic354.FER.total_lower
#print axioms Dyadic354.FER.exp_count_le_pow
#print axioms Dyadic354.FER.seed_constant_positive
#print axioms Dyadic354.FER.seed_exponential_bound
#print axioms Dyadic354.FER.seed_interval_exists
#print axioms Dyadic354.FERecurrence.eventCount_card
#print axioms Dyadic354.FERecurrence.eventCount_step
#print axioms Dyadic354.FERecurrence.eventCount_step_bounds
#print axioms Dyadic354.FERecurrence.eventCount_mono
#print axioms Dyadic354.FERecurrence.eventCount_le
#print axioms Dyadic354.FERecurrence.eventCount_unbounded
#print axioms Dyadic354.FERecurrence.initial_second_ge_two
#print axioms Dyadic354.FERecurrence.two_step_scaled
#print axioms Dyadic354.FERecurrence.normalized_nonneg
#print axioms Dyadic354.FERecurrence.normalized_zero_step
#print axioms Dyadic354.FERecurrence.rho_bounds
#print axioms Dyadic354.FERecurrence.sigma_bounds
#print axioms Dyadic354.FERecurrence.normalized_step
#print axioms Dyadic354.FERecurrence.normalized_two_step
#print axioms Dyadic354.FERecurrence.potential_nonneg
#print axioms Dyadic354.FERecurrence.normalized_le_potential
#print axioms Dyadic354.FERecurrence.potential_zero_step
#print axioms Dyadic354.FERecurrence.potential_two_step
#print axioms Dyadic354.FERecurrence.normalized_step_le_potential
#print axioms Dyadic354.FEShift.exits_le_new_values
#print axioms Dyadic354.FEShift.variation_le_new_values
#print axioms Dyadic354.FEShift.length_cast
#print axioms Dyadic354.FEShift.length_positive
#print axioms Dyadic354.FEShift.boundary_eq_cyclic
#print axioms Dyadic354.FEShift.boundary_a_le
#print axioms Dyadic354.FEShift.boundary_b_eq_a
#print axioms Dyadic354.FEShift.boundary_double_a_le
#print axioms Dyadic354.IntervalSums.split
#print axioms Dyadic354.IntervalSums.mono
#print axioms Dyadic354.IntervalSums.sum_period_start
#print axioms Dyadic354.IntervalSums.interval_le_period
#print axioms Dyadic354.IntervalSums.two_arcs_cover
#print axioms Dyadic354.IntervalSums.replace_variation
#print axioms Dyadic354.PeriodChange.basic_word
#print axioms Dyadic354.PeriodChange.missing_difference
#print axioms Dyadic354.PeriodChange.sum_indicator_le_card
#print axioms Dyadic354.PeriodChange.changing_period_bound
#print axioms Dyadic354.PeriodChange.actual_changing_period_bound
#print axioms Dyadic354.PeriodicWord.cast_injective
#print axioms Dyadic354.PeriodicWord.cast_mem_iff
#print axioms Dyadic354.PeriodicWord.word_on_period
#print axioms Dyadic354.PeriodicWord.word_add_period
#print axioms Dyadic354.PeriodicWord.word_sub_period
#print axioms Dyadic354.PeriodicWord.word_bounds
#print axioms Dyadic354.PeriodicWord.sum_period
#print axioms Dyadic354.PeriodicWord.variation_eq_sum
#print axioms Dyadic354.PeriodicWord.word_periodic
#print axioms Dyadic354.RationalWindows.cast_mul_den
#print axioms Dyadic354.RationalWindows.good_distance_lt_one
#print axioms Dyadic354.RationalWindows.bounded_good_finite
#print axioms Dyadic354.RationalWindows.good_den_unbounded
#print axioms Dyadic354.RationalWindows.crossing_exists
#print axioms Dyadic354.RationalWindows.crossing_spec
#print axioms Dyadic354.RationalWindows.crossingRat_spec
#print axioms Dyadic354.RationalWindows.crossing_minimal
#print axioms Dyadic354.RationalWindows.before_crossing

#print Dyadic354.FE.deficit_exponential_bound
#print Dyadic354.FER.seed_exponential_bound
#print Dyadic354.DB.digit_propagation
#print Dyadic354.DBScale.advance_increment
#print Dyadic354.BGWindows.arbitrarily_large_windows
#print Dyadic354.BGReturns.return_cost_unbounded
#print Dyadic354.BG.bounded_event_windows_complete
#print Dyadic354.BG.normalized_complete

#print axioms Dyadic354.BGCapacity.logarithmic_bound
#print axioms Dyadic354.BGCapacity.seed_size_eventually
#print axioms Dyadic354.BGCapacity.event_power_bound
#print axioms Dyadic354.BGCapacity.eventual_capacity
#print axioms Dyadic354.BGGeometric.exact_in_interval
#print axioms Dyadic354.BGGeometric.cost_bound
#print axioms Dyadic354.BGWindowBounds.height_bound
#print axioms Dyadic354.BGWindowBounds.precision_to_delta
#print axioms Dyadic354.BGWindowBounds.crossing_close
#print axioms Dyadic354.BGWindows.inverse_scale_small
#print axioms Dyadic354.BGWindows.arbitrarily_large_windows
#print axioms Dyadic354.DBScale.block_sufficient
#print axioms Dyadic354.DBScale.matching_bounds
#print axioms Dyadic354.DBScale.block_matching_bound
#print axioms Dyadic354.DBScale.threshold_bounds
#print axioms Dyadic354.DBScale.threshold_ge_two
#print axioms Dyadic354.DBScale.advance_increment
#print axioms Dyadic354.DBScale.matching_exp_bound
#print axioms Dyadic354.DBScale.arbitrarily_large_advance
#print axioms Dyadic354.DBScale.large_advance_matching
#print axioms Dyadic354.CubicGrowth.no_eventual_quartic
#print axioms Dyadic354.CubicGrowth.exponential_eventually_dominates
#print axioms Dyadic354.CubicGrowth.no_eventual_cubic_advance
#print axioms Dyadic354.BG.support_nonempty_of_event
#print axioms Dyadic354.BG.bounded_event_windows_complete
#print axioms Dyadic354.BG.normalized_complete

#print Dyadic354.erdos354_strong_completeness
#print Dyadic354.erdos354_part_i
#print Dyadic354.UpstreamBridge.PartITarget
#print Dyadic354.UpstreamBridge.erdos354_part_i_upstream
#print Dyadic354.UpstreamBridge.erdos354_strong_upstream

#print axioms Dyadic354.Normalization.term_shift
#print axioms Dyadic354.Normalization.shifted_irrational
#print axioms Dyadic354.Normalization.balance_larger
#print axioms Dyadic354.Normalization.balance
#print axioms Dyadic354.Normalization.common_shift
#print axioms Dyadic354.Normalization.above_bound
#print axioms Dyadic354.SetBridge.normalized_sorted_strictMono
#print axioms Dyadic354.SetBridge.normalized_injective
#print axioms Dyadic354.SetBridge.normalized_lower_bound
#print axioms Dyadic354.SetBridge.indexed_to_set
#print axioms Dyadic354.SetBridge.setComplete_mono
#print axioms Dyadic354.SetBridge.set_to_indexed
#print axioms Dyadic354.SetBridge.shifted_range_subset
#print axioms Dyadic354.erdos354_strong_completeness
#print axioms Dyadic354.erdos354_part_i
#print axioms Dyadic354.UpstreamBridge.floorMultiples_eq
#print axioms Dyadic354.UpstreamBridge.interleave_eq
#print axioms Dyadic354.UpstreamBridge.indexedComplete_iff
#print axioms Dyadic354.UpstreamBridge.setComplete_iff
#print axioms Dyadic354.UpstreamBridge.strongComplete_iff
#print axioms Dyadic354.UpstreamBridge.partITarget_iff
#print axioms Dyadic354.UpstreamBridge.erdos354_part_i_upstream
#print axioms Dyadic354.UpstreamBridge.erdos354_strong_upstream
