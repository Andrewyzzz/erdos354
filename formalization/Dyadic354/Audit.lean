import Dyadic354.Statements
import Dyadic354.CertificateData
import Dyadic354.Mesh
import Dyadic354.PermanentMesh
import Dyadic354.BlockLength
import Dyadic354.EventInfinitude

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
