/-
# Outer-order-zero edge of the coupled height recurrence

At outer contraction order zero the factorial Hahn row is the constant row
one.  Its adjacent height difference therefore vanishes without constructing
the nonexistent order-minus-one shifted channel.  This supplies the missing
edge branch of the coupled propagation mechanism.  The smallest physical
three-channel block is also discharged exactly by cancelling its positive
normalization factor.
-/

import YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence
open YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The finite outer factorial sum at contraction order zero is exactly one. -/
theorem outerOrderZero_factorialCarrier_eq_one
    (m n i h : Nat) : transvectFactorialCoeff m n 0 i h ≈ 1 :=
  transvectFactorialCoeff_zero m n i h

/-- Consequently the order-zero outer row has zero adjacent height
difference on every pair of coordinates. -/
theorem outerOrderZero_adjacentDifference_zero
    (m n i h : Nat) :
    (transvectFactorialCoeff m n 0 (i + 1) (h - 1) +
      -(transvectFactorialCoeff m n 0 i h)) ≈ 0 := by
  refine Q'.eqv_trans _ ((1 : Q') + -1) _
    (Q'.add_eqv_congr'
      (outerOrderZero_factorialCarrier_eq_one m n (i + 1) (h - 1))
      (Q'.neg_eqv_congr _ _
        (outerOrderZero_factorialCarrier_eq_one m n i h))) ?_
  exact Q'.add_neg_self_eqv 1

/-- On inner support, an order-zero right-shell carrier is just its inner Hahn
entry; the outer finite sum contributes the unit factor. -/
theorem rightShellFactorialCoefficient_outerOrderZero
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hr : q.r = 0) (i j l : Nat) (hinner : q.p ≤ j + l) :
    rightShellFactorialCoefficient q i j l ≈
      hahnEntry b c (j + l) q.p j := by
  unfold rightShellFactorialCoefficient
  rw [if_pos hinner, hr]
  refine Q'.eqv_trans _
    (hahnEntry b c (j + l) q.p j * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (outerOrderZero_factorialCarrier_eq_one
        a q.intermediate i (j + l - q.p))) ?_
  exact Q'.mul_one_eqv _

/-- The order-zero shell carrier is independent of the first source
coordinate. -/
theorem rightShellFactorialCoefficient_outerOrderZero_i_invariant
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hr : q.r = 0) (i i' j l : Nat) (hinner : q.p ≤ j + l) :
    rightShellFactorialCoefficient q i j l ≈
      rightShellFactorialCoefficient q i' j l :=
  Q'.eqv_trans _ _ _
    (rightShellFactorialCoefficient_outerOrderZero q hr i j l hinner)
    (Q'.eqv_symm
      (rightShellFactorialCoefficient_outerOrderZero q hr i' j l hinner))

/-- At order zero the coupled recurrence moves one step toward height one
without any lower-label vanishing premise: its pivot is literally zero. -/
theorem coupledOuterHeight_step_order_zero
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n i h : Nat) (him : i < m) (hh : 0 < h) (hhn : h ≤ n) :
    R m n 0 i h ≈ R m n 0 (i + 1) (h - 1) := by
  have hdiff := hR m n 0 i h (by omega) (by omega) him hh hhn
  have hrhs :
      Q'.ofNat (0 * (m + n - 0 + 1)) *
          R (m - 1) (n - 1) (0 - 1) i (h - 1) ≈ 0 := by
    simpa only [Nat.zero_mul, Nat.zero_sub] using
      (QPoly.q_zero_mul (R (m - 1) (n - 1) 0 i (h - 1)))
  exact Q'.eqv_symm (q_eqv_of_sub_zero
    (Q'.eqv_trans _ _ _ hdiff hrhs))

/-- All positive order-zero heights propagate to height one without a shifted
channel. -/
theorem coupledOuterHeight_order_zero_eqv_height_one
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n i h : Nat) (hishell : i + h ≤ m)
    (hh : 0 < h) (hhn : h ≤ n) :
    R m n 0 i h ≈ R m n 0 (i + h - 1) 1 := by
  induction h generalizing i with
  | zero => omega
  | succ h hInd =>
      by_cases hzero : h = 0
      · subst h
        simpa using Q'.eqv_refl (R m n 0 i 1)
      · have hhpos : 0 < h := by omega
        have hstep := coupledOuterHeight_step_order_zero R hR
          m n i (h + 1) (by omega) (by omega) (by omega)
        have htail := hInd (i + 1) (by omega) hhpos (by omega)
        have hidx : (i + 1) + h - 1 = i + (h + 1) - 1 := by omega
        rw [hidx] at htail
        exact Q'.eqv_trans _ _ _ hstep htail

/-- Height one therefore closes the complete order-zero edge. -/
theorem coupledOuterHeight_order_zero_of_height_one
    (R : Nat → Nat → Nat → Nat → Nat → Q')
    (hR : CoupledOuterHeightDifference R)
    (m n i h : Nat) (hishell : i + h ≤ m)
    (hh : 0 < h) (hhn : h ≤ n)
    (hheightOne : ∀ u, R m n 0 u 1 ≈ 0) :
    R m n 0 i h ≈ 0 :=
  Q'.eqv_trans _ _ _
    (coupledOuterHeight_order_zero_eqv_height_one
      R hR m n i h hishell hh hhn)
    (hheightOne (i + h - 1))

private def scaleThreeLHS : PolyExpr :=
  .mul (.var 0)
    (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5)))
      (.mul (.var 3) (.var 6)))

private def scaleThreeRHS : PolyExpr :=
  .add (.add (.mul (.mul (.var 0) (.var 1)) (.var 4))
    (.mul (.mul (.var 0) (.var 2)) (.var 5)))
    (.mul (.mul (.var 0) (.var 3)) (.var 6))

private theorem scaleThree_normal :
    normalize scaleThreeLHS = normalize scaleThreeRHS := by
  decide

private theorem scale_three_carriers
    (K L D U M C P : Q') :
    K * (L * M + D * C + U * P) ≈
      (K * L) * M + (K * D) * C + (K * U) * P := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then K else if r = 1 then L else if r = 2 then D else
    if r = 3 then U else if r = 4 then M else if r = 5 then C else P
  have h := poly_identity_of_normal_eq scaleThreeLHS scaleThreeRHS
    scaleThree_normal ρ
  simpa [scaleThreeLHS, scaleThreeRHS, RingNormaliser.eval, ρ] using h

/-- Exact closed coefficients of the smallest block after clearing its
positive normalization three. -/
private theorem correctionFence_scaled_coefficients :
    Q'.ofNat 3 * omegaCorrectionLowerCoefficient 2 2 2 2 1 ≈ Q'.ofNat 2 ∧
    Q'.ofNat 3 * omegaCorrectionDiagonalCoefficient 2 2 2 2 1 ≈
      -(Q'.ofNat 3) ∧
    Q'.ofNat 3 * omegaCorrectionUpperCoefficient 2 2 2 2 1 ≈ Q'.ofNat 4 := by
  decide

/-- **Upper-order-zero Omega edge.**  The smallest physical block, whose
upper adjacent channel has outer order zero, satisfies the unscaled exact
three-carrier correction identity throughout its physical coordinate box. -/
theorem correctionFence_upperOrderZero_omega
    (i j l s : Nat) (hi : i < 3) (hj : j < 3)
    (hl : l < 3) (hs : s < 3) :
    OmegaCorrectionThreeCarrierAt correctionFenceLower
      correctionFenceMiddle correctionFenceUpper i j l s := by
  let M := triRight 2 2 2 2 correctionFenceLower.intermediate
    (mono i) (mono j) (mono l) s
  let C := triRight 2 2 2 2 correctionFenceMiddle.intermediate
    (mono i) (mono j) (mono l) s
  let P := triRight 2 2 2 2 correctionFenceUpper.intermediate
    (mono i) (mono j) (mono l) s
  let L := omegaCorrectionLowerCoefficient 2 2 2 2 1
  let D := omegaCorrectionDiagonalCoefficient 2 2 2 2 1
  let U := omegaCorrectionUpperCoefficient 2 2 2 2 1
  have hscaled := correctionFence_three_channel_identity
    i hi j hj l hl s hs
  have hcoeff := correctionFence_scaled_coefficients
  have hcarriers :
      (Q'.ofNat 3 * L) * M + (Q'.ofNat 3 * D) * C +
          (Q'.ofNat 3 * U) * P ≈
        Q'.ofNat 2 * M + -(Q'.ofNat 3 * C) + Q'.ofNat 4 * P := by
    refine Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ M hcoeff.1)
        (Q'.eqv_trans _ ((-(Q'.ofNat 3)) * C) _
          (Q'.mul_eqv_congr_right _ _ C hcoeff.2.1) ?_))
      (Q'.mul_eqv_congr_right _ _ P hcoeff.2.2)
    exact Q'.neg_mul_eqv (Q'.ofNat 3) C
  have hnormal :
      Q'.ofNat 3 * (L * M + D * C + U * P) ≈
        Q'.ofNat 2 * M + -(Q'.ofNat 3 * C) + Q'.ofNat 4 * P :=
    Q'.eqv_trans _ _ _
      (scale_three_carriers (Q'.ofNat 3) L D U M C P) hcarriers
  unfold OmegaCorrectionThreeCarrierAt
  apply Q'.mul_left_cancel_of_pos (by decide : (0 : Q') < Q'.ofNat 3)
  simpa only [M, C, P, L, D, U, correctionFenceMiddle] using
    Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm hnormal)

/-- The new edge theorem extends the previously packaged positive-coordinate
bases at the concrete measure-six block where the strict outer shift fails. -/
theorem correctionFence_mutualMeasureBase :
    rightLabelMeasure 2 2 2 = 6 ∧ correctionFenceUpper.r = 0 ∧
    PositiveCorrectionBaseRegimes correctionFenceLower
      correctionFenceMiddle correctionFenceUpper ∧
    ∀ i j l s, i < 3 → j < 3 → l < 3 → s < 3 →
      OmegaCorrectionThreeCarrierAt correctionFenceLower
        correctionFenceMiddle correctionFenceUpper i j l s := by
  refine ⟨rfl, rfl, positiveCorrectionBaseRegimes _ _ _, ?_⟩
  intro i j l s hi hj hl hs
  exact correctionFence_upperOrderZero_omega i j l s hi hj hl hs

end YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge

#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.outerOrderZero_factorialCarrier_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.outerOrderZero_adjacentDifference_zero
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.rightShellFactorialCoefficient_outerOrderZero
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.coupledOuterHeight_step_order_zero
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.coupledOuterHeight_order_zero_eqv_height_one
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.coupledOuterHeight_order_zero_of_height_one
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.correctionFence_upperOrderZero_omega
#print axioms YMGap.Continuum.SU2OrderedRacahOuterOrderZeroEdge.correctionFence_mutualMeasureBase
