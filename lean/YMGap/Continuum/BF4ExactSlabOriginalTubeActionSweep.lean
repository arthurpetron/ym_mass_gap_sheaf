/-
# The original ordered tube heat sub-action under one common sweep

The physical-index support is the existing tubeIds, not a replacement
enumeration. A proved face permutation identifies its full heat action
with twelve tube factors. Both original probes, the partition and both
means are swept together. Every cutoff spin is retained in literalChain.
-/

import YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
import YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
import YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction

namespace YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem tubeIds_faces_perm (margin : Nat) :
    ((tubeIds margin).map (slabPlaquetteAt (responseExtent margin))).Perm (tubeSides margin) := by
  have hn := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt (responseExtent margin)) _
    (tubeIds_nodup margin) (by
      intro i hi j hj he
      have h := congrArg (fun f => (boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf f) he
      dsimp only at h
      rw [idxOf_slabPlaquetteAt ((tubeIds_mem_iff margin i).mp hi).1,
        idxOf_slabPlaquetteAt ((tubeIds_mem_iff margin j).mp hj).1] at h
      exact h)
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _ hn (tubeSides_nodup margin)
  intro face
  constructor
  · intro hf
    obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
    exact ((tubeIds_mem_iff margin id).mp hi).2
  · intro hf
    have hp := tubeSides_physical margin face hf
    have he := face_lookup hp
    exact List.mem_map.mpr ⟨_,(tubeIds_mem_iff margin _).mpr
      ⟨List.mem_range.mpr (List.idxOf_lt_length_of_mem hp),he.symm ▸ hf⟩,he⟩

theorem tubeIds_length (margin : Nat) : (tubeIds margin).length = 12 := by
  have h := (tubeIds_faces_perm margin).length_eq
  rw [List.length_map,tubeSides_length] at h
  exact h

def tubeAction (w : Q') (K margin : Nat) : List FaceFactor :=
  (tubeSides margin).map (fun face => (face,heatWeights w K))

theorem tubeAction_physical (w : Q') (K margin : Nat) : ∀ f, f ∈ tubeAction w K margin →
    f.1 ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  intro f hf
  obtain ⟨face,hface,rfl⟩ := List.mem_map.mp hf
  exact tubeSides_physical margin face hface

private theorem finiteSum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by simp only [List.map_cons,finitePolySum,finiteSum_map f g xs]

theorem selected_action_zero (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    sweptProduct extent 0 (ids.map (fun id => (slabPlaquetteAt extent id,heatWeights w K))) =
      polynomialProduct (faceHeatPolynomial w K extent) ids
  | [] => rfl
  | id::ids => by
    change polyMul _ (sweptProduct extent 0 (ids.map _)) = polyMul _ (polynomialProduct _ ids)
    rw [selected_action_zero w K extent ids]
    congr 1
    simp only [factor,heatWeights,finiteSum_map,sweptCharacter,if_neg (not_swept_zero _)]
    rfl

theorem tube_action_zero (w : Q') (K margin : Nat) :
    RatPolyCoeffEqv (sweptProduct (responseExtent margin) 0 (tubeAction w K margin))
      (polynomialProduct (faceHeatPolynomial w K (responseExtent margin)) (tubeIds margin)) := by
  have h := polynomialProduct_perm (factor (sweptCharacter (responseExtent margin) 0))
    ((tubeIds_faces_perm margin).map (fun face => (face,heatWeights w K)))
  rw [List.map_map] at h
  change RatPolyCoeffEqv (sweptProduct (responseExtent margin) 0
    ((tubeIds margin).map (fun id => (slabPlaquetteAt (responseExtent margin) id,heatWeights w K))))
    (sweptProduct (responseExtent margin) 0 (tubeAction w K margin)) at h
  rw [selected_action_zero] at h
  exact h.symm

theorem tube_action_swept (w : Q') (K margin : Nat) :
    sweptProduct (responseExtent margin) (margin+3) (tubeAction w K margin) =
      literalChain margin w K polyOne := by
  unfold tubeAction
  rw [← side_faces_pin margin,List.map_map]
  unfold sweptProduct product polynomialProduct
  rw [List.foldr_map]
  rfl

def endpointFactors (margin : Nat) (time : Fin 4) : List FaceFactor := [(sliceFace margin time.val,[(1,1)])]

private theorem singleton_factor (chars : Z4Plaq → Nat → RatPoly) (face : Z4Plaq) :
    RatPolyCoeffEqv (product chars [(face,[(1,1)])]) (chars face 1) :=
  (((RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)).mul (RatPolyCoeffEqv.refl polyOne)).trans
    (RatPolyCoeffEqv.mul_one _)

theorem endpoint_swept (margin cut : Nat) (time : Fin 4) :
    RatPolyCoeffEqv (sweptProduct (responseExtent margin) cut (endpointFactors margin time))
      (literalSlice margin time) := by
  have h := singleton_factor (sweptCharacter (responseExtent margin) cut) (sliceFace margin time.val)
  have hp : sweptCharacter (responseExtent margin) cut (sliceFace margin time.val) 1 = literalSlice margin time :=
    if_neg (slice_not_swept margin time.val cut)
  rw [hp] at h
  exact h

theorem endpoint_physical (margin : Nat) (time : Fin 4) : ∀ f, f ∈ endpointFactors margin time →
    f.1 ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  intro f hf
  have he := List.mem_singleton.mp hf
  subst f
  exact slice_physical margin time

/-- Full original tube sub-action, including its partition and both means. -/
theorem original_tube_connected_sweep (w : Q') (K margin : Nat) :
    BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator w K (responseExtent margin) (tubeIds margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
      connectedNumerator (boundaryCompleteSlabLinks (responseExtent margin)).length
        (literalSlice margin 0) (literalSlice margin 3) (literalChain margin w K polyOne) := by
  refine Q'.eqv_trans _ _ _ (original_connected_pin w K (responseExtent margin) (tubeIds margin) _ _) ?_
  rw [lower_shifted_probe_pin,upper_shifted_probe_pin]
  refine Q'.eqv_trans _ _ _ (connected_coeff_congr _ (endpoint_swept margin 0 0).symm
    (endpoint_swept margin 0 3).symm (tube_action_zero w K margin).symm) ?_
  refine Q'.eqv_trans _ _ _ (sweep_connected (responseExtent margin) (margin+3)
    (endpointFactors margin 0) (endpointFactors margin 3) (tubeAction w K margin)
    (endpoint_physical margin 0) (endpoint_physical margin 3) (tubeAction_physical w K margin)) ?_
  rw [tube_action_swept]
  exact connected_coeff_congr _ (endpoint_swept margin (margin+3) 0)
    (endpoint_swept margin (margin+3) 3) (RatPolyCoeffEqv.refl _)

end YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep

#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tubeIds_faces_perm
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tubeIds_length
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tubeAction
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tubeAction_physical
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.selected_action_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tube_action_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.tube_action_swept
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.endpointFactors
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.endpoint_swept
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.endpoint_physical
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep.original_tube_connected_sweep
