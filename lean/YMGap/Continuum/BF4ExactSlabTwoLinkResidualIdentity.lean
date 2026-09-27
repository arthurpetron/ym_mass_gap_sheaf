/-
# Exact two-error decomposition for original neighboring residuals

The reference coordinate maps are orthogonal only for the retained two-link
background. This file uses their proved same-range identities with the actual
conditional projections to split one original mixed residual pairing into a
background mixed residual and two signed form-comparison errors. No error
estimate or conditional angle is inferred here.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
import YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => A.approx n)))

private theorem rc_sub_add_cancel (a b : RC) :
    RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem rc_sub_sub_cancel (a b c : RC) :
    RCsub (RCsub a b) (RCsub c b) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 2) (.neg (.var 1)))))
      (.add (.var 0) (.neg (.var 2)))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem rc_error_identity (c : Q') (a b d : RC) :
    a = RCadd (RCscale c b)
      (RCsub (RCsub a (RCscale c (RCadd b d)))
        (RCsub RCzero (RCscale c d))) := by
  refine Quotient.inductionOn₃ a b d ?_
  intro A B E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.var 0)
      (.add (.mul (.var 3) (.var 1))
        (.add
          (.add (.var 0)
            (.neg (.mul (.var 3) (.add (.var 1) (.var 2)))))
          (.neg (.add (.const 0)
            (.neg (.mul (.var 3) (.var 2)))))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n
           | 2 => E.approx n | _ => c)))

private theorem inner_sub_right (D : GNSData)
    (a b c : GNSCompletionSpace D) :
    D.cinnerCompl a (D.cSub b c) =
      RCsub (D.cinnerCompl a b) (D.cinnerCompl a c) := by
  rw [D.cinnerCompl_comm a (D.cSub b c), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm b a, D.cinnerCompl_comm c a]

private theorem vector_sub_sub_cancel (D : GNSData)
    (a b c : GNSCompletionSpace D) :
    D.cSub (D.cSub a b) (D.cSub c b) = D.cSub a c := by
  apply eq_of_pairings_equal
  intro z
  simp only [D.cinnerCompl_cSub_left, rc_sub_sub_cancel]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (left right : Z4Link)
  (hl : left ∈ boundaryCompleteSlabLinks extent)
  (hr : right ∈ boundaryCompleteSlabLinks extent)
  (hlpair : left ∈ [left,right])
  (hrpair : right ∈ [left,right])

local notation "F" => fullData hw0 hw1 K extent hK
local notation "B0" => twoLinkBackgroundData (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent left right
local notation "J" => toBackground hw0 hw1 hsmall hd K extent hK left right
local notation "Pl" => conditionalProjection hw0 hw1 K extent hK left hl
local notation "Pr" => conditionalProjection hw0 hw1 K extent hK right hr
local notation "Ql" => reference hw0 hw1 hsmall hd K extent hK left right left hl hlpair
local notation "Qr" => reference hw0 hw1 hsmall hd K extent hK left right right hr hrpair

/-- Applying the reference residual after its corresponding ACTUAL conditional
residual returns the reference residual of the original vector. This is a
same-carrier vector identity, not an assertion of F-self-adjointness of Q. -/
theorem reference_residual_conditional (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hpair : link ∈ [left,right]) (x : GNSCompletionSpace F) :
    (F).cSub
      ((F).cSub x (conditionalProjection hw0 hw1 K extent hK link hlink x))
      (reference hw0 hw1 hsmall hd K extent hK left right link hlink hpair
        ((F).cSub x (conditionalProjection hw0 hw1 K extent hK link hlink x))) =
      (F).cSub x
        (reference hw0 hw1 hsmall hd K extent hK left right link hlink hpair x) := by
  rw [reference_sub, reference_conditional]
  exact vector_sub_sub_cancel F x
    (conditionalProjection hw0 hw1 K extent hK link hlink x)
    (reference hw0 hw1 hsmall hd K extent hK left right link hlink hpair x)

private theorem original_residual_reference_orthogonal (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hpair : link ∈ [left,right]) (x y : GNSCompletionSpace F) :
    (F).cinnerCompl
      ((F).cSub x (conditionalProjection hw0 hw1 K extent hK link hlink x))
      (reference hw0 hw1 hsmall hd K extent hK left right link hlink hpair y) =
      RCzero := by
  rw [(F).cinnerCompl_cSub_left]
  have hfix := conditional_reference hw0 hw1 hsmall hd K extent hK left right
    link hlink hpair y
  have hsa := conditionalProjection_selfAdjoint hw0 hw1 K extent hK
    link hlink x
    (reference hw0 hw1 hsmall hd K extent hK left right link hlink hpair y)
  rw [hfix] at hsa
  rw [hsa, rc_sub_self]

/-- The two-error decomposition is exact on the ORIGINAL completed action.
The scalar c is arbitrary; this identity alone bounds neither error. -/
theorem two_error_identity (c : Q') (x : GNSCompletionSpace F) :
    let u := (F).cSub x (Pl x);
    let v := (F).cSub x (Pr x);
    let ei := (F).cSub x (Ql x);
    let ej := (F).cSub x (Qr x);
    let err := fun a b => RCsub ((F).cinnerCompl a b)
      (RCscale c ((B0).cinnerCompl (J a) (J b)));
    (F).cinnerCompl u v =
      RCadd (RCscale c ((B0).cinnerCompl (J ei) (J ej)))
        (RCsub (err u ((F).cSub v (Ql v))) (err v (Qr ei))) := by
  dsimp only
  let u := (F).cSub x (Pl x)
  let v := (F).cSub x (Pr x)
  let ei := (F).cSub x (Ql x)
  let ej := (F).cSub x (Qr x)
  let t := (F).cSub v (Ql v)
  let q := Qr ei
  let A := (F).cinnerCompl u v
  let B := (B0).cinnerCompl (J ei) (J ej)
  let C := (B0).cinnerCompl (J u) (J t)
  let D := (B0).cinnerCompl (J v) (J q)
  have hf1 : (F).cinnerCompl u t = A := by
    change (F).cinnerCompl u ((F).cSub v (Ql v)) = (F).cinnerCompl u v
    rw [inner_sub_right, original_residual_reference_orthogonal hw0 hw1
      hsmall hd K extent hK left right left hl hlpair x v]
    refine Quotient.inductionOn ((F).cinnerCompl u v) ?_
    intro Z
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.const 0))) (.var 0)
        (by decide) (fun _ => Z.approx n)))
  have hf2 : (F).cinnerCompl v q = RCzero := by
    change (F).cinnerCompl ((F).cSub x (Pr x)) (Qr ei) = RCzero
    exact original_residual_reference_orthogonal hw0 hw1 hsmall hd K extent hK
      left right right hr hrpair x ei
  have hb1 : C = (B0).cinnerCompl (J ei) (J v) := by
    change (B0).cinnerCompl (J u) (J ((F).cSub v (Ql v))) = _
    rw [toBackground_sub hw0 hw1 hsmall hd K extent hK left right v (Ql v), inner_sub_right]
    rw [← reference_background_adjoint hw0 hw1 hsmall hd K extent hK
      left right left hl hlpair u v]
    rw [← (B0).cinnerCompl_cSub_left,
      ← toBackground_sub hw0 hw1 hsmall hd K extent hK left right u (Ql u)]
    exact congrArg (fun z => (B0).cinnerCompl (J z) (J v))
      (reference_residual_conditional hw0 hw1 hsmall hd K extent hK
        left right left hl hlpair x)
  have hb2 : B = RCsub ((B0).cinnerCompl (J ei) (J v)) D := by
    change (B0).cinnerCompl (J ei) (J ej) = _
    have he := reference_residual_conditional hw0 hw1 hsmall hd K extent hK
      left right right hr hrpair x
    change (F).cSub v (Qr v) = ej at he
    rw [← he, toBackground_sub hw0 hw1 hsmall hd K extent hK left right v (Qr v), inner_sub_right]
    rw [← reference_background_adjoint hw0 hw1 hsmall hd K extent hK
      left right right hr hrpair ei v]
    rw [(B0).cinnerCompl_comm (J (Qr ei)) (J v)]
  have hb : C = RCadd B D := by
    rw [hb1, hb2, rc_sub_add_cancel]
  change A = RCadd (RCscale c B)
    (RCsub (RCsub ((F).cinnerCompl u t) (RCscale c C))
      (RCsub ((F).cinnerCompl v q) (RCscale c D)))
  rw [hf1, hf2, hb]
  exact rc_error_identity c A B D

end YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity

#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity.reference_residual_conditional
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkResidualIdentity.two_error_identity
