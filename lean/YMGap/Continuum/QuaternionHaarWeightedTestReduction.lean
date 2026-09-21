/-
# Computed removal of one direction from a weighted polynomial test

For the SAME certified Haar weight W, subtract the rational multiple
<F,h>_W / <h,h>_W of h when its squared norm is positive, and subtract
zero otherwise. This is a total finite construction, including null h.
Its exact Pythagorean identity proves that the new test norm never increases.

The consumer is a signed pairing already known to annihilate h. No
conditional expectation with a changed weight, limiting projection, or
uniform analytic estimate is assumed.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.QuaternionHaarWeightedTestReduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- Exact rational coefficient, with a decidable zero/negative-norm fallback. -/
def reductionCoefficient (b c : Q') : Q' :=
  if hc : (0 : Q') < c then b * Q'.recipPos c hc else 0

private theorem coefficient_normal (b c : Q') :
    reductionCoefficient b c * (reductionCoefficient b c * c) ≈
      reductionCoefficient b c * b := by
  by_cases hc : (0 : Q') < c
  · simp only [reductionCoefficient, dif_pos hc]
    have h : (b * Q'.recipPos c hc) * c ≈ b :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
          (fun | 0 => b | 1 => Q'.recipPos c hc | _ => c))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv c hc))
          (Q'.mul_one_eqv b))
    exact Q'.mul_eqv_congr_left _ _ _ h
  · simp only [reductionCoefficient, dif_neg hc]
    exact Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _)
      (Q'.eqv_symm (Q'.zero_mul_eqv _))

/-- Subtract the computed multiple; all polynomial coordinates are retained. -/
def reducedTest (blocks : Nat) (W F h : RatPoly) : RatPoly :=
  polyAdd F (polySmul
    (-reductionCoefficient (weightedPair blocks W F h) (weightedPair blocks W h h)) h)

theorem reducedTest_supported {blocks : Nat} (W : RatPoly) {F h : RatPoly}
    (hF : SupportedQuaternionBlocks blocks F) (hh : SupportedQuaternionBlocks blocks h) :
    SupportedQuaternionBlocks blocks (reducedTest blocks W F h) := by
  apply supported_add hF
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hh s hs

/-- Exact energy accounting, including the null-direction branch. -/
theorem reducedTest_pythagoras (blocks : Nat) (W F h : RatPoly)
    (H : Certificate blocks W)
    (hF : SupportedQuaternionBlocks blocks F) (hh : SupportedQuaternionBlocks blocks h) :
    let t := reductionCoefficient (weightedPair blocks W F h) (weightedPair blocks W h h)
    weightedPair blocks W (reducedTest blocks W F h) (reducedTest blocks W F h) +
        (t*t)*weightedPair blocks W h h ≈ weightedPair blocks W F F := by
  let D := weightedGNSData blocks W H
  let x : D.V := ⟨F, hF⟩
  let y : D.V := ⟨h, hh⟩
  let t := reductionCoefficient (weightedPair blocks W F h) (weightedPair blocks W h h)
  let z : D.V := ⟨reducedTest blocks W F h, reducedTest_supported W hF hh⟩
  have hz : D.veq (D.add (D.smul 1 x) (D.smul (-t) y)) z :=
    (RatPolyCoeffEqv.one_smul F).add (RatPolyCoeffEqv.refl _)
  have hex : D.B z z ≈
      D.B x x + -((2 : Q')*(t*D.B x y)) + (t*t)*D.B y y :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (D.B_diag_congr hz))
      (Q'.eqv_trans _ _ _ (D.diag_expand 1 (-t) x y)
        (poly_identity_of_normal_eq
          (.add
            (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
              (.mul (.const 1) (.mul (.neg (.var 3)) (.var 1))))
            (.add (.mul (.neg (.var 3)) (.mul (.const 1) (.var 1)))
              (.mul (.neg (.var 3)) (.mul (.neg (.var 3)) (.var 2)))))
          (.add (.add (.var 0) (.neg (.mul (.const 2) (.mul (.var 3) (.var 1)))))
            (.mul (.mul (.var 3) (.var 3)) (.var 2))) (by decide)
          (fun | 0 => D.B x x | 1 => D.B x y | 2 => D.B y y | _ => t)))
  have hn : (t*t)*D.B y y ≈ t*D.B x y :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (coefficient_normal (D.B x y) (D.B y y))
  have hsum := Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ hex (Q'.add_eqv_congr_left _ _ _ hn)) hn
  exact Q'.eqv_trans _ _ _ hsum
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.mul (.const 2) (.var 1)))) (.var 1)) (.var 1))
      (.var 0) (by decide) (fun | 0 => D.B x x | _ => t*D.B x y))

/-- The computed test has no greater SAME-weight squared norm. -/
theorem reducedTest_norm_le (blocks : Nat) (W F h : RatPoly)
    (H : Certificate blocks W)
    (hF : SupportedQuaternionBlocks blocks F) (hh : SupportedQuaternionBlocks blocks h) :
    weightedPair blocks W (reducedTest blocks W F h) (reducedTest blocks W F h) ≤
      weightedPair blocks W F F := by
  let t := reductionCoefficient (weightedPair blocks W F h) (weightedPair blocks W h h)
  have hc : (0 : Q') ≤ weightedPair blocks W h h := H.square_insertion_nonnegative h hh
  have hgain : (0 : Q') ≤ (t*t)*weightedPair blocks W h h :=
    Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg t) hc
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hgain)
    (Q'.le_of_eqv (reducedTest_pythagoras blocks W F h H hF hh))

#print axioms reductionCoefficient
#print axioms reducedTest
#print axioms reducedTest_supported
#print axioms reducedTest_pythagoras
#print axioms reducedTest_norm_le

end YMGap.Continuum.QuaternionHaarWeightedTestReduction
