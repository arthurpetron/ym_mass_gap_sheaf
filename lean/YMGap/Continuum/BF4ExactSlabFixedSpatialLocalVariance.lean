/-
# Volume-independent nontriviality for recentered original plaquette probes

The local six-face comparison applies to the literal selected chain. First
and second moments use the same finiteValue and partition. Passing their
joint cutoff/time diagonal gives a variance floor starRatio(w), independent
of spatial width, face position, cutoff and boundary depth. The existing
centering stream realizes it as the norm of an actual completed vector.

Spatially recentered faces therefore retain this positive floor in every
larger box. No comparison or convergence of the different boxes' states is
asserted. The bound depends on nome and is a nontriviality estimate, NOT a
volume-uniform transfer gap or a continuum/physical-mass estimate.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit zero physicalTime_zero)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width)

local notation "x" => faceSpan width p hp
local notation "J" => jointPairing hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width

attribute [local irreducible] chartScalar jointPairing chartJointLimit

/-- The same explicit floor works at every width, depth and cutoff stage. -/
theorem chart_variance_floor (stage t : Nat) :
    starRatio w ≤ chartScalar hw0 hw1 width stage 0 x x t +
      -(chartScalar hw0 hw1 width stage 0 x (unit width) t *
        chartScalar hw0 hw1 width stage 0 x (unit width) t) := by
  let E := adjacentEvenExtent (width+t)
  let f := timeShiftPlaquette ((width+1)+t) p
  have hf : f ∈ boundaryCompleteSlabPlaquettes E :=
    spatialFaces_shift_physical
      (by dsimp [E, adjacentEvenExtent, centralExtent]; omega)
      (by dsimp [E, adjacentEvenExtent, centralExtent]; omega) hp
  have hl : (f.1, (dirsOf f.2).1) ∈ edgesOf f := List.mem_cons_self
  have h := BF4ExactSlabSelectedStarVariance.finiteValue_variance_floor hw0 hw1 E
    (chainIds E width (width+1) (t+t)) (fun _ hi => chainIds_physical hi)
    (chainIds_nodup _ _ _ _) hf _ hl stage
  have hm := chartScalar_mean_finiteValue hw0 hw1 width p hp stage t
  have hs := chartScalar_square_finiteValue hw0 hw1 width p hp stage t
  have he := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.mul_eqv_congr_left _ _ _ hm)))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv he)

private theorem rational_variance_converges {a b : Nat → Q'} {C D : CReal}
    (ha : ConvergesTo (fun k => ofQ' (a k)) C)
    (hb : ConvergesTo (fun k => ofQ' (b k)) D) :
    ConvergesTo (fun k => ofQ' (a k + -(b k*b k))) (sub C (mul D D)) := by
  have h : ConvergesTo
      (fun k => add (ofQ' (a k)) (neg (mul (ofQ' (b k)) (ofQ' (b k)))))
      (sub C (mul D D)) :=
    TrigAddCReal.convergesTo_add ha (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hb hb))
  apply TrigAddCReal.convergesTo_congr_seq (s := fun k =>
    add (ofQ' (a k)) (neg (mul (ofQ' (b k)) (ofQ' (b k))))) _ h
  intro k
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

theorem face_variance_converges :
    ConvergesTo (fun k => ofQ'
      (chartScalar hw0 hw1 width k 0 x x k +
        -(chartScalar hw0 hw1 width k 0 x (unit width) k *
          chartScalar hw0 hw1 width k 0 x (unit width) k)))
      (sub (J x x) (mul (J x (unit width)) (J x (unit width)))) := by
  apply rational_variance_converges
  · exact ArctanTrigConvergesProof.convergesTo_of_equiv
      (chartJoint_diagonal_converges hw0 hw1 width 0 x x (Nat.le_refl 0) (Nat.le_refl 0))
      (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x x (Nat.le_refl 0) (Nat.le_refl 0)))
  · exact ArctanTrigConvergesProof.convergesTo_of_equiv
      (chartJoint_diagonal_converges hw0 hw1 width 0 x (unit width) (Nat.le_refl 0) (Nat.le_refl 0))
      (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x (unit width) (Nat.le_refl 0) (Nat.le_refl 0)))

/-- Both regulator limits have been taken; the lower bound still names only w. -/
theorem face_joint_variance_floor :
    leEv (ofQ' (starRatio w)) (jointCenteredMoment hw0 hw1 width 0 x x) := by
  have h := leEv_of_convergesTo_le
    (CReal.convergesTo_const (ofQ' (starRatio w)))
    (face_variance_converges hw0 hw1 width p hp)
    (fun k => leEv_ofQ'_of_approx_ge (fun _ => chart_variance_floor hw0 hw1 width p hp k k))
  have he : Equiv (sub (J x x) (mul (J x (unit width)) (J x (unit width))))
      (jointCenteredMoment hw0 hw1 width 0 x x) := by
    unfold jointCenteredMoment
    rw [physicalTime_zero]
    exact Equiv_add (Equiv.refl _) (neg_congr
      (TrigSignedAdd.mul_congr_right (jointPairing_symm hw0 hw1 width x (unit width))))
  exact leEv_trans h (leEv_of_equiv he)

/-- The already constructed centering stream, with its explicit modulus. -/
def faceExcitation : UnitComplement hw0 hw1 width :=
  ⟨centeredVector hw0 hw1 width x, centeredVector_orthogonal hw0 hw1 width x⟩

theorem faceExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (B (faceExcitation hw0 hw1 width p hp).val (faceExcitation hw0 hw1 width p hp).val) := by
  change RCle _ (B (centeredVector hw0 hw1 width x) (centeredVector hw0 hw1 width x))
  rw [centeredVector_pairing]
  exact face_joint_variance_floor hw0 hw1 width p hp

theorem faceExcitation_ne_zero :
    (faceExcitation hw0 hw1 width p hp).val ≠ jointEmbedSpan hw0 hw1 width (zero width) := by
  intro hz
  have h := faceExcitation_norm_floor hw0 hw1 width p hp
  rw [hz, jointCompletedZero_norm] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

theorem faceExcitation_correlator_pin (n : Nat) :
    B (faceExcitation hw0 hw1 width p hp).val
      (jointCompletedTime hw0 hw1 width n (faceExcitation hw0 hw1 width p hp).val) =
      Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width n x x) :=
  centeredVector_time_pairing hw0 hw1 width n x x

theorem recenter_faceSpan (margin : Nat) :
    recenter margin x = faceSpan (paddedWidth width margin) (shiftFace (margin+1) 0 p)
      (shiftFace_spatial (by unfold paddedWidth; omega) hp) := Subtype.ext rfl

/-- A family of actual original completed excitations, one per recentered box. -/
def bulkExcitation (margin : Nat) : UnitComplement hw0 hw1 (paddedWidth width margin) :=
  ⟨centeredVector hw0 hw1 (paddedWidth width margin) (recenter margin x),
    centeredVector_orthogonal hw0 hw1 (paddedWidth width margin) (recenter margin x)⟩

/-- Uniform in the requested spatial margin, without identifying different
boxes' Hilbert carriers or asserting a spatial limit. -/
theorem bulkExcitation_norm_floor (margin : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (completedInner hw0 hw1 (paddedWidth width margin)
        (bulkExcitation hw0 hw1 width p hp margin).val
        (bulkExcitation hw0 hw1 width p hp margin).val) := by
  change RCle _ (completedInner hw0 hw1 (paddedWidth width margin)
    (centeredVector hw0 hw1 (paddedWidth width margin) (recenter margin x))
    (centeredVector hw0 hw1 (paddedWidth width margin) (recenter margin x)))
  rw [recenter_faceSpan]
  exact faceExcitation_norm_floor hw0 hw1 _ _ _

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.chart_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.face_variance_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.face_joint_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.faceExcitation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.faceExcitation_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.faceExcitation_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.faceExcitation_correlator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.recenter_faceSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.bulkExcitation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance.bulkExcitation_norm_floor
