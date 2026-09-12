import Dyadic354.Statements
import Dyadic354.CertificateData
import Dyadic354.Mesh
import Dyadic354.PermanentMesh

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
