/-
# All-nome time control on the EXISTING completed plaquette excitation

The exact Wilson/joint-pairing pin puts the literal increment estimate on
the already constructed nonzero unit-complement vector. For an active
plaquette, its completed correlation loss is nonnegative and at most
`192*n*(1-w)`. Strict spatial padding supplies activity uniformly in width.

The original fixed-width JointCompletion, completedInner, jointCompletedTime
and faceExcitation are unchanged. Their known positive time-zero norm floor
is not enough to make the resulting positive-time lower bound positive.
This proves neither continuum survival nor physical-time calibration.
-/
import YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion

namespace YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner (completedInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (source_edges_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin

attribute [local irreducible] completedInner timeIncrement

private theorem half_double (a : CReal) :
    Equiv (mul (ofQ' HalfPow.half) (mul (ofQ' 2) a)) a :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 2 (a.approx k)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a.approx k) (by decide : (HalfPow.half*2).eqv 1))
        (Q'.one_mul_eqv _)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (faceExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "loop" => plaquetteLoop face hf

/-- The SAME existing centered completed vector and its actual time map.
This equality identifies only its scalar loss, not two whole carriers. -/
theorem completed_loss_pin (n : Nat) :
    RCsub (B v v) (B v (T n v)) =
      RCscale HalfPow.half (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop n)) := by
  have h0 := faceExcitation_correlator_pin hw0 hw1 width face hf 0
  simp only [jointCompletedTime_zero] at h0
  rw [h0, faceExcitation_correlator_pin]
  apply Quotient.sound
  exact (half_double _).symm.trans
    (Pivot2.mul_congr_right (timeIncrement_centered_pin hw0 hw1 width face hf n).symm)

/-- Nonnegative loss is proved for this actual excitation at every lag;
it is not an assumed spectral representation or one-step positivity law. -/
theorem completed_loss_nonnegative (n : Nat) :
    RCle RCzero (RCsub (B v v) (B v (T n v))) := by
  rw [completed_loss_pin]
  have h := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half)
    (show RCle (Quotient.mk crealSetoid (ofQ' 0))
      (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop n)) from
      timeIncrement_nonnegative hw0 hw1 loop n)
  simpa only [show Quotient.mk crealSetoid (ofQ' 0) = RCzero from rfl,
    RCscale_RCzero] using h

/-- Only the literal four-link source enters the factor 192. Nome remains
explicit; this is not a nome-uniform positive response or mass bound. -/
theorem completed_loss_nome_bound
    (hactive : ∀ e, e ∈ (loop).edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (n : Nat) :
    RCle (RCsub (B v v) (B v (T n v)))
      (Quotient.mk crealSetoid (ofQ' (192 * Q'.ofNat n * (1 + -w)))) := by
  rw [completed_loss_pin]
  have h := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half)
    (show RCle (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop n))
      (Quotient.mk crealSetoid (ofQ'
        (Q'.ofNat n * (24 * (Q'.ofNat 4 * Q'.ofNat 4) * (1 + -w))))) from
      timeIncrement_nome_bound hw0 hw1 loop hactive n)
  refine RCle_trans h ?_
  apply leEv_of_equiv
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 2)
        (.mul (.var 0) (.mul (.mul (.const 24) (.mul (.const 4) (.const 4))) (.var 1))))
      (.mul (.mul (.mul (.var 2) (.const 384)) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => Q'.ofNat n | 1 => 1 + -w | _ => HalfPow.half))
    (Q'.mul_eqv_congr_right _ _ (1 + -w)
      (Q'.mul_eqv_congr_right _ _ (Q'.ofNat n) (by decide : (HalfPow.half*384).eqv 192)))

/-- Every fixed base plaquette has this bound on the existing centered
excitation at every strictly larger width. No cross-width state equality. -/
theorem padded_completed_loss_nome_bound {base : Nat} (hwidth : base < width)
    (hfbase : face ∈ spatialFaces base) (n : Nat) :
    RCle (RCsub (B v v) (B v (T n v)))
      (Quotient.mk crealSetoid (ofQ' (192 * Q'.ofNat n * (1 + -w)))) := by
  apply completed_loss_nome_bound hw0 hw1 width face hf ?_ n
  intro e he
  exact source_edges_active_after_padding hwidth (plaquetteLoop face hfbase) e he

end YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement

#print axioms YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement.completed_loss_pin
#print axioms YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement.completed_loss_nonnegative
#print axioms YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement.completed_loss_nome_bound
#print axioms YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement.padded_completed_loss_nome_bound
