/-
# Signed lower bound for the original conditional residual pair

The reference projections are orthogonal only for the detached background.
Their proved common ranges and two signed form errors give a lower bound
for the ACTUAL original conditional projections, on every completed vector.
The coefficient depends on the nome, not extent or the late heat cutoff.
This is a conditional-link dynamics estimate, not an OS time-transfer gap.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity
import YMGap.Continuum.BF4ExactSlabTwoLinkReferenceEnergy
import YMGap.Continuum.BF4ExactSlabTwoLinkFormError

namespace YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
open YMGap.Continuum.BF4ExactSlabTwoLinkReferenceEnergy
open YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity
open YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants
open YMGap.Continuum.BF4ExactSlabTwoLinkFormError
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_comm_eqv (A.approx n) (B.approx n)))

/-- The explicit coefficient `(U-L)/(2L)`, with no volume or cutoff input. -/
def pairCoefficient {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  RCSignedPairBudget.coefficient (width w) (twoLinkLower w)
    (twoLinkLower_positive hd)

theorem pairCoefficient_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) : (0 : Q') ≤ pairCoefficient hd :=
  RCSignedPairBudget.coefficient_nonnegative _ _ _ (width_nonnegative hw0 hd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)
  (hl : left ∈ boundaryCompleteSlabLinks extent)
  (hr : right ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "B0" => twoLinkBackgroundData (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent left right
local notation "J" => toBackground hw0 hw1 hsmall hd K extent hK left right

include hsmall in
/-- Every pair of physical-link conditional residuals on the ORIGINAL
completion obeys this signed lower bound. No centering, locality, distinctness,
or assumed conditional-angle estimate is required. -/
theorem conditional_residual_pair_lower (x : GNSCompletionSpace F) :
    let u := (F).cSub x (conditionalProjection hw0 hw1 K extent hK left hl x);
    let v := (F).cSub x (conditionalProjection hw0 hw1 K extent hK right hr x);
    RCle (RCneg (RCscale (pairCoefficient hd)
      (RCadd ((F).cinnerCompl u u) ((F).cinnerCompl v v))))
      ((F).cinnerCompl u v) := by
  let i : PairLink extent left right := ⟨left, hl, List.mem_cons_self⟩
  let j : PairLink extent left right :=
    ⟨right, hr, List.mem_cons_of_mem left List.mem_cons_self⟩
  let Qi := reference hw0 hw1 hsmall hd K extent hK left right
    left hl i.property.2
  let Qj := reference hw0 hw1 hsmall hd K extent hK left right
    right hr j.property.2
  let u := (F).cSub x (conditionalProjection hw0 hw1 K extent hK left hl x)
  let v := (F).cSub x (conditionalProjection hw0 hw1 K extent hK right hr x)
  let ei := (F).cSub x (Qi x)
  let ej := (F).cSub x (Qj x)
  let t := (F).cSub v (Qi v)
  let q := Qj ei
  let N := fun a => (B0).cinnerCompl (J a) (J a)
  let S := RCadd (N u) (N v)
  let E := RCadd ((F).cinnerCompl u u) ((F).cinnerCompl v v)
  let err := formError hw0 hw1 hsmall hd K extent hK left right
  have he0 : RCnonneg ((B0).cinnerCompl (J ei) (J ej)) :=
    remainder_pair_nonnegative hw0 hw1 hsmall hd K extent hK left right i j x
  have ht : RCle (N t) (N v) :=
    remainder_background_norm hw0 hw1 hsmall hd K extent hK left right i v
  have hei : RCle (N ei) (N u) := by
    have h := remainder_background_norm hw0 hw1 hsmall hd K extent hK left right i u
    change RCle (N ((F).cSub u (Qi u))) (N u) at h
    have hid := reference_residual_conditional hw0 hw1 hsmall hd K extent hK
      left right left hl i.property.2 x
    change (F).cSub u (Qi u) = ei at hid
    rw [hid] at h
    exact h
  have hq : RCle (N q) (N u) := RCle_trans
    (reference_background_norm hw0 hw1 hsmall hd K extent hK left right
      right hr j.property.2 ei) hei
  have hdq : (0 : Q') ≤ RCSignedPairBudget.quarter (width w) :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg (width_nonnegative hw0 hd))
  have ha : RCle (RCneg (RCscale (RCSignedPairBudget.quarter (width w)) S))
      (err u t) := by
    have hs := RCadd_le_add (RCle_refl (N u)) ht
    exact RCle_trans (RCSignedPairBudget.neg_mono (RCscale_mono hdq hs))
      (formError_bounds hw0 hw1 hsmall hd K extent hK left right u t).1
  have hb : RCle (err v q)
      (RCscale (RCSignedPairBudget.quarter (width w)) S) := by
    have hs := RCadd_le_add (RCle_refl (N v)) hq
    rw [add_comm (N v) (N u)] at hs
    exact RCle_trans (formError_bounds hw0 hw1 hsmall hd K extent hK left right v q).2
      (RCscale_mono hdq hs)
  have hE : RCle (RCscale (twoLinkLower w) S) E := by
    change RCle (RCscale (twoLinkLower w) (RCadd (N u) (N v))) E
    rw [RCscale_RCadd]
    exact RCadd_le_add
      (completed_form_bounds hw0 hw1 hsmall hd K extent hK left right u).1
      (completed_form_bounds hw0 hw1 hsmall hd K extent hK left right v).1
  have hid : (F).cinnerCompl u v =
      RCadd (RCscale (midpoint w) ((B0).cinnerCompl (J ei) (J ej)))
        (RCsub (err u t) (err v q)) :=
    two_error_identity hw0 hw1 hsmall hd K extent hK left right hl hr
      i.property.2 j.property.2 (midpoint w) x
  exact RCSignedPairBudget.signed_pair_lower
    (twoLinkLower w) (width w) (midpoint w) (twoLinkLower_positive hd)
    (width_nonnegative hw0 hd) (midpoint_nonnegative hw0 hd)
    _ _ _ S E _ he0 ha hb hE hid

#print axioms pairCoefficient
#print axioms pairCoefficient_nonnegative
#print axioms conditional_residual_pair_lower

end YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
