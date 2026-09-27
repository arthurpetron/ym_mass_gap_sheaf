/-
# Completed two-link signed form error

The exact signed comparison is divided by four at its proved rational
midpoint. This is a same-original-completion perturbation bound, not a
conditional angle or spatial gap.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison
import YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4ExactSlabTwoLinkFormError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem scale_neg (s : Q') (a : RC) :
    RCscale s (RCneg a) = RCneg (RCscale s a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => s | _ => A.approx n)))

private theorem scale_sub (s : Q') (a b : RC) :
    RCscale s (RCsub a b) =
      RCsub (RCscale s a) (RCscale s b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.var 2))))
      (by decide)
      (fun | 0 => s | 1 => A.approx n | _ => B.approx n)))

private theorem quarter_four (a : RC) :
    RCscale (HalfPow.half * HalfPow.half) (RCscale 4 a) = a := by
  rw [RCscale_RCscale,
    scale_congr (by decide : Q'.eqv ((HalfPow.half * HalfPow.half) * 4) 1) a,
    RCscale_one]

private theorem quarter_twice_midpoint (w : Q') (a : RC) :
    RCscale (HalfPow.half * HalfPow.half)
      (RCscale (2 * (twoLinkLower w + twoLinkUpper w)) a) =
      RCscale (midpoint w) a := by
  rw [RCscale_RCscale]
  apply scale_congr
  unfold midpoint
  have hh : Q'.eqv ((HalfPow.half * HalfPow.half) * 2) HalfPow.half := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (HalfPow.half * HalfPow.half) 2 (twoLinkLower w + twoLinkUpper w)))
    (Q'.mul_eqv_congr_right _ _ _ hh)

private theorem quarter_width (d : Q') (a : RC) :
    RCscale (HalfPow.half * HalfPow.half) (RCscale d a) =
      RCscale (HalfPow.half * (HalfPow.half * d)) a := by
  rw [RCscale_RCscale]
  exact scale_congr (Q'.mul_assoc_eqv HalfPow.half HalfPow.half d) a

private theorem quarter_middle (w : Q') (a b : RC) :
    RCscale (HalfPow.half * HalfPow.half)
      (RCsub (RCscale 4 a)
        (RCscale (2 * (twoLinkLower w + twoLinkUpper w)) b)) =
      RCsub a (RCscale (midpoint w) b) := by
  rw [scale_sub, quarter_four, quarter_twice_midpoint]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "B0" => twoLinkBackgroundData (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent left right
local notation "J" => toBackground hw0 hw1 hsmall hd K extent hK left right

/-- Signed difference between the original mixed form and the arithmetic
midpoint multiple of the detached-background mixed form. -/
def formError (a b : GNSCompletionSpace F) : RC :=
  RCsub ((F).cinnerCompl a b)
    (RCscale (midpoint w) ((B0).cinnerCompl (J a) (J b)))

/-- Both signs of the same completed mixed-form error are controlled by one
quarter of the two-link comparison width times the two background norms. -/
theorem formError_bounds (a b : GNSCompletionSpace F) :
    let S := RCadd ((B0).cinnerCompl (J a) (J a))
      ((B0).cinnerCompl (J b) (J b));
    RCle (RCneg (RCscale
      (HalfPow.half * (HalfPow.half * width w)) S))
      (formError hw0 hw1 hsmall hd K extent hK left right a b) ∧
    RCle (formError hw0 hw1 hsmall hd K extent hK left right a b)
      (RCscale (HalfPow.half * (HalfPow.half * width w)) S) := by
  let S := RCadd ((B0).cinnerCompl (J a) (J a))
    ((B0).cinnerCompl (J b) (J b))
  let A := (F).cinnerCompl a b
  let B := (B0).cinnerCompl (J a) (J b)
  have h := completed_signed_pair (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall (Q'.le_of_lt hd) hw0 hw1 hd K extent hK left right a b
  change RCle (RCneg (RCscale (width w) S))
      (RCsub (RCscale 4 A)
        (RCscale (2 * (twoLinkLower w + twoLinkUpper w)) B)) ∧
    RCle (RCsub (RCscale 4 A)
        (RCscale (2 * (twoLinkLower w + twoLinkUpper w)) B))
      (RCscale (width w) S) at h
  have hq : (0 : Q') ≤ HalfPow.half * HalfPow.half :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg HalfPow.half_nonneg
  have hlo := RCscale_mono hq h.1
  have hhi := RCscale_mono hq h.2
  rw [scale_neg, quarter_width, quarter_middle] at hlo
  rw [quarter_middle, quarter_width] at hhi
  exact ⟨hlo, hhi⟩

end YMGap.Continuum.BF4ExactSlabTwoLinkFormError

#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkFormError.formError
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkFormError.formError_bounds
