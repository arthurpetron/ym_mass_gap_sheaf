/-
# Both exact cancellations on the SAME original shifted-probe numerator

The outer sum removes separating selected supports. Each retained
coefficient expands into covered replica labels with the original full
heat weights and signed four-moment term. The inner sum removes thin
odd cuts in either replica. Empty odd cuts remain allowed; no positivity
or response lower bound is inferred for the retained signed terms.
-/

import YMGap.Continuum.BF4ExactSlabCoveredPairExpansion
import YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabCoveredPairExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_insert_smul (blocks : Nat) (p a : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul p (polySmul c a)) ≈ c * quaternionHaar blocks (polyMul p a) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c p a))
    (quaternionHaar_polySmul _ _ _)

theorem connected_smul (blocks : Nat) (p q a b : RatPoly) (c d : Q') :
    (connected blocks p q).value (polySmul c a) (polySmul d b) ≈
      (c*d)*(connected blocks p q).value a b :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul (haar_insert_smul blocks (polyMul p q) a c) (haar_insert_smul blocks polyOne b d))
    (Q'.neg_eqv_congr _ _ (qmul (haar_insert_smul blocks p a c) (haar_insert_smul blocks q b d))))
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (.neg (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))))
      (.mul (.mul (.var 0) (.var 1))
        (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 4) (.var 5))))) (by decide)
      (fun i => if i = 0 then c else if i = 1 then d
        else if i = 2 then quaternionHaar blocks (polyMul (polyMul p q) a)
        else if i = 3 then quaternionHaar blocks (polyMul polyOne b)
        else if i = 4 then quaternionHaar blocks (polyMul p a)
        else quaternionHaar blocks (polyMul q b)))

theorem original_pair_pin (w : Q') (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (connected (N margin) (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))).value
      (weightedIntegrand w K (responseExtent margin) pair.1)
      (weightedIntegrand w K (responseExtent margin) pair.2) ≈ weightedPairTerm w K margin pair :=
  connected_smul _ _ _ _ _ _ _

theorem coefficient_covered (w : Q') (K margin : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈
      listQSum (weightedPairTerm w K margin) (labels K ids) :=
  Q'.eqv_trans _ _ _ (connectedCoefficient_original w K (responseExtent margin) _ _ ids hn hi)
    (listQSum_congr_on _ _ _ (fun pair _ => original_pair_pin w K margin pair))

theorem coefficient_cut_filtered (w : Q') (K margin time : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈
      listQSum (weightedPairTerm w K margin) ((labels K ids).filter (pairKeep margin time)) :=
  Q'.eqv_trans _ _ _ (coefficient_covered w K margin ids hn hi) (weighted_sum_filter w K margin time _)

theorem selected_nodup {A : Type} : ∀ {xs ys : List A}, xs.Nodup → ys ∈ selections xs → ys.Nodup
  | [], ys, _, hm => by
    have he := List.mem_singleton.mp hm
    subst ys
    exact List.nodup_nil
  | head::xs, ys, hn, hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact selected_nodup (List.nodup_cons.mp hn).2 hm
    · obtain ⟨zs,hz,he⟩ := List.mem_map.mp hm
      subst ys
      exact List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (selected_mem hz head h),
        selected_nodup (List.nodup_cons.mp hn).2 hz⟩

theorem lower_link_local (margin : Nat) : LinkLocal (responseExtent margin)
    (edgesOf (sliceFace margin 0)) (lower (enlarge margin shiftedProbe)) := by
  rw [lower_shifted_probe_pin]
  exact (face_scalar_local _ _).character 1

theorem upper_link_local (margin : Nat) : LinkLocal (responseExtent margin)
    (edgesOf (sliceFace margin 3)) (upper (enlarge margin shiftedProbe)) := by
  rw [upper_shifted_probe_pin]
  exact (face_scalar_local _ _).character 1

/-- Complete original action; connected supports and odd cuts are filtered together. -/
theorem original_numerator_joint_filter (w : Q') (K margin time : Nat) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
      listQSum (fun ids => listQSum (weightedPairTerm w K margin)
        ((labels K ids).filter (pairKeep margin time)))
        (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
          (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin))) :=
  Q'.eqv_trans _ _ _ (connectedNumerator_filtered w K (responseExtent margin) _ _ _ _
    (lower_supported _) (upper_supported _) (lower_link_local margin) (upper_link_local margin) _)
    (listQSum_congr_on _ _ _ (fun ids hm => coefficient_cut_filtered w K margin time ids
      (selected_nodup (CayleyParentInj.range_nodup _) (List.mem_filter.mp hm).1)
      (fun id hi => selected_mem (List.mem_filter.mp hm).1 id hi)))

end YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.connected_smul
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.original_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.coefficient_covered
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.coefficient_cut_filtered
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.selected_nodup
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.lower_link_local
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.upper_link_local
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion.original_numerator_joint_filter
