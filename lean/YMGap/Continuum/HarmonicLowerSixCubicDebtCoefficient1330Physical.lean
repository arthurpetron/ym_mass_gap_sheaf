/-
# Physical bridge for the sharp cubic-debt coefficient certificate

This file transports the recentered degree-ten polynomial certificate to the
literal constructive-rational coefficient occurring in the lower-six moment
payment.  Every denominator is cleared by a proved positive multiplier.
-/

import YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Polynomial
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassComparison

namespace YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Physical

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Polynomial
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem physical_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "physical_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               physical_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private def coefficientAEnvironment (A : Q') (index : Nat) : Q' :=
  if index = 0 then A else 0

private theorem eval_congr_of_environment
    {rho sigma : Nat → Q'} (henv : ∀ i, rho i ≈ sigma i) :
    ∀ expression : RingNormaliser.PolyExpr,
      RingNormaliser.eval rho expression ≈
        RingNormaliser.eval sigma expression
  | .const _ => Q'.eqv_refl _
  | .var i => henv i
  | .add a b =>
      Q'.add_eqv_congr'
        (eval_congr_of_environment henv a)
        (eval_congr_of_environment henv b)
  | .mul a b =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (eval_congr_of_environment henv a))
        (Q'.mul_eqv_congr_left _ _ _
          (eval_congr_of_environment henv b))
  | .neg a =>
      Q'.neg_eqv_congr _ _ (eval_congr_of_environment henv a)
  | .pow a n =>
      RingNormaliser.qpow_eqv_congr
        (eval_congr_of_environment henv a) n

private theorem shifted_eval_eqv_unshifted
    (X A : Q') (hA : Q'.ofInt 1332 + X ≈ A) :
    RingNormaliser.eval (cubicDebt1330Environment X)
        pCubicDebtCoefficient1330 ≈
      RingNormaliser.eval (coefficientAEnvironment A)
        (pCubicDebtCoefficientClearedAt (.var 0)) := by
  let A0 := Q'.ofInt 1332 + X
  have hsyntactic :
      RingNormaliser.eval (cubicDebt1330Environment X)
          pCubicDebtCoefficient1330 =
        RingNormaliser.eval (coefficientAEnvironment A0)
          (pCubicDebtCoefficientClearedAt (.var 0)) := by
    simp [pCubicDebtCoefficient1330,
      pCubicDebtCoefficientClearedAt,
      cubicDebt1330Environment, coefficientAEnvironment,
      A0, RingNormaliser.eval]
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.eqv_of_eq hsyntactic) ?_
  apply eval_congr_of_environment
  intro i
  unfold coefficientAEnvironment
  by_cases hi : i = 0
  · subst i
    simp only [if_pos]
    exact hA
  · simp only [if_neg hi]
    exact Q'.eqv_refl 0

/-- The exact degree-ten cleared inequality at every `k >= 1330`. -/
theorem cubicDebtCoefficient_cleared_1330
    {k : Nat} (hk : 1330 ≤ k) :
    let A : Q' := Q'.ofNat (k + 2)
    let E : Q' := Q'.ofNat (k + 3)
    let r : Q' := Q'.ofNat 2 * RingNormaliser.qpow A 2 + -(1 : Q')
    Q'.ofNat 40320 *
        (A *
          ((Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1) *
            RingNormaliser.qpow r 3)) ≤
      Q'.ofNat 2916 *
        (RingNormaliser.qpow (A + -(1 : Q')) 6 *
          RingNormaliser.qpow E 4) := by
  let X : Q' := Q'.ofNat (k - 1330)
  let A : Q' := Q'.ofNat (k + 2)
  let E : Q' := Q'.ofNat (k + 3)
  let E0 : Q' := A + 1
  let r : Q' := Q'.ofNat 2 * RingNormaliser.qpow A 2 + -(1 : Q')
  have hX0 : (0 : Q') ≤ X := by
    dsimp only [X]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hpoly := pCubicDebtCoefficient1330_eval_nonnegative X hX0
  have hAnat : Q'.ofNat 1332 + X ≈ A := by
    dsimp only [X, A]
    refine Q'.eqv_trans _ (Q'.ofNat (1332 + (k - 1330))) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.ofNat_add_eqv 1332 (k - 1330))
    · have hnat : 1332 + (k - 1330) = k + 2 := by omega
      rw [hnat]
      exact Q'.eqv_refl _
  have hA : Q'.ofInt 1332 + X ≈ A := by
    exact Q'.eqv_trans _ (Q'.ofNat 1332 + X) _
      (Q'.add_eqv_congr_right _ _ _ (by decide)) hAnat
  have hshift := shifted_eval_eqv_unshifted X A hA
  have hnonnegative :
      (0 : Q') ≤
        RingNormaliser.eval (coefficientAEnvironment A)
          (pCubicDebtCoefficientClearedAt (.var 0)) :=
    Q'.le_trans' _ _ _ hpoly (Q'.le_of_eqv hshift)
  have hdiff :
      (0 : Q') ≤
        (Q'.ofNat 2916 *
            (RingNormaliser.qpow (A + -(1 : Q')) 6 *
              RingNormaliser.qpow E0 4)) +
          -(Q'.ofNat 40320 *
            (A *
              ((Q'.ofNat 12 * RingNormaliser.qpow E0 2 + 1) *
                RingNormaliser.qpow r 3))) := by
    simpa [pCubicDebtCoefficientClearedAt,
      coefficientAEnvironment, RingNormaliser.eval, E0, r] using hnonnegative
  have hraw := Q'.le_of_sub_nonneg hdiff
  have hE : E0 ≈ E := by
    dsimp only [E0, A, E]
    exact Q'.eqv_symm (Q'.ofNat_add_eqv (k + 2) 1)
  have hE2 := RingNormaliser.qpow_eqv_congr hE 2
  have hE4 := RingNormaliser.qpow_eqv_congr hE 4
  have hleft :
      Q'.ofNat 40320 *
          (A *
            ((Q'.ofNat 12 * RingNormaliser.qpow E0 2 + 1) *
              RingNormaliser.qpow r 3)) ≈
        Q'.ofNat 40320 *
          (A *
            ((Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1) *
              RingNormaliser.qpow r 3)) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hE2))))
  have hright :
      Q'.ofNat 2916 *
          (RingNormaliser.qpow (A + -(1 : Q')) 6 *
            RingNormaliser.qpow E0 4) ≈
        Q'.ofNat 2916 *
          (RingNormaliser.qpow (A + -(1 : Q')) 6 *
            RingNormaliser.qpow E 4) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hE4)
  dsimp only [A, E, r] at hleft hright hraw ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright))

private theorem ofNat_mul_unit_eqv_one (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem rnqpow_mul_base (a b : Q') : ∀ n,
    RingNormaliser.qpow (a * b) n ≈
      RingNormaliser.qpow a n * RingNormaliser.qpow b n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show RingNormaliser.qpow (a * b) n * (a * b) ≈
        (RingNormaliser.qpow a n * a) * (RingNormaliser.qpow b n * b)
      refine Q'.eqv_trans _
        ((RingNormaliser.qpow a n * RingNormaliser.qpow b n) * (a * b)) _
        (Q'.mul_eqv_congr_right _ _ _ (rnqpow_mul_base a b n)) ?_
      physical_ring

private theorem rnqpow_pos (a : Q') (ha : (0 : Q') < a) : ∀ n,
    (0 : Q') < RingNormaliser.qpow a n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n + 1 => Q'.mul_pos (rnqpow_pos a ha n) ha

private theorem ofNat_sub_one_eqv (n : Nat) (hn : 1 ≤ n) :
    Q'.ofNat (n - 1) ≈ Q'.ofNat n + -(1 : Q') := by
  change (Int.ofNat (n - 1)) * 1 =
    (Int.ofNat n * 1 + (-1) * 1) * 1
  simp
  omega

private theorem profile_cleared (k : Nat) :
    let E := Q'.ofNat (k + 3)
    RingNormaliser.qpow E 2 *
        (E * lowerSixDirichletProfile (k + 1)) ≈
      Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1 := by
  let E := Q'.ofNat (k + 3)
  let u := harmU (k + 1)
  have hEu : E * u ≈ (1 : Q') := by
    dsimp only [E, u]
    unfold harmU
    simpa only [show k + 1 + 2 = k + 3 by omega] using
      ofNat_mul_unit_eqv_one (k + 3) (by omega)
  have hraw :
      RingNormaliser.qpow E 2 *
          (E * lowerSixDirichletProfile (k + 1)) ≈
        (E * u) *
          (Q'.ofNat 12 * RingNormaliser.qpow E 2 +
            (E * u) * (E * u)) := by
    unfold lowerSixDirichletProfile
    dsimp only [u]
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    physical_ring
  refine Q'.eqv_trans _ _ _ hraw ?_
  have hsquare : (E * u) * (E * u) ≈ (1 : Q') * 1 :=
    Q'.eqv_trans _ ((1 : Q') * (E * u)) _
      (Q'.mul_eqv_congr_right _ _ _ hEu)
      (Q'.mul_eqv_congr_left _ _ _ hEu)
  have hinner :
      Q'.ofNat 12 * RingNormaliser.qpow E 2 + (E * u) * (E * u) ≈
        Q'.ofNat 12 * RingNormaliser.qpow E 2 + (1 : Q') * 1 :=
    Q'.add_eqv_congr_left _ _ _ hsquare
  refine Q'.eqv_trans _
    ((1 : Q') *
      (Q'.ofNat 12 * RingNormaliser.qpow E 2 + (E * u) * (E * u))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hEu
  refine Q'.eqv_trans _
    ((1 : Q') *
      (Q'.ofNat 12 * RingNormaliser.qpow E 2 + (1 : Q') * 1)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hinner
  · physical_ring

private theorem driftExcess_cleared (k : Nat) :
    let d := Q'.ofNat (driftDen k)
    RingNormaliser.qpow d 2 * lowerSixDriftExcess k ≈
      Q'.ofNat 2 * d + 1 := by
  let d := Q'.ofNat (driftDen k)
  let u := unit (driftDen k) (driftDen_pos k)
  have hdu : d * u ≈ (1 : Q') := by
    dsimp only [d, u]
    exact ofNat_mul_unit_eqv_one _ (driftDen_pos k)
  have hraw :
      RingNormaliser.qpow d 2 * lowerSixDriftExcess k ≈
        (d * u) * (Q'.ofNat 2 * d + d * u) := by
    unfold lowerSixDriftExcess
    dsimp only [u]
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    physical_ring
  refine Q'.eqv_trans _ _ _ hraw ?_
  have hinner : Q'.ofNat 2 * d + d * u ≈
      Q'.ofNat 2 * d + 1 := Q'.add_eqv_congr_left _ _ _ hdu
  refine Q'.eqv_trans _
    ((1 : Q') * (Q'.ofNat 2 * d + d * u)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hdu
  refine Q'.eqv_trans _
    ((1 : Q') * (Q'.ofNat 2 * d + 1)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hinner
  · exact Q'.one_mul_eqv _

private theorem driftCube_cleared (k : Nat) :
    let d := Q'.ofNat (driftDen k)
    RingNormaliser.qpow d 6 *
        RingNormaliser.qpow (lowerSixDriftExcess k) 3 ≈
      RingNormaliser.qpow (Q'.ofNat 2 * d + 1) 3 := by
  let d := Q'.ofNat (driftDen k)
  let e := lowerSixDriftExcess k
  have hde : RingNormaliser.qpow d 2 * e ≈
      Q'.ofNat 2 * d + 1 := by
    dsimp only [d, e]
    exact driftExcess_cleared k
  have hd6 : RingNormaliser.qpow d 6 ≈
      RingNormaliser.qpow (RingNormaliser.qpow d 2) 3 := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    physical_ring
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (RingNormaliser.qpow d 2) 3 *
      RingNormaliser.qpow e 3) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hd6
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (RingNormaliser.qpow d 2 * e) 3) _
    (Q'.eqv_symm (rnqpow_mul_base _ _ 3)) ?_
  exact RingNormaliser.qpow_eqv_congr hde 3

private theorem harmonicDriftDen_factor (k : Nat) :
    let A := Q'.ofNat (k + 2)
    let E := Q'.ofNat (k + 3)
    (A + -(1 : Q')) * E ≈ Q'.ofNat (driftDen k) := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  have hminus : A + -(1 : Q') ≈ Q'.ofNat (k + 1) := by
    dsimp only [A]
    exact Q'.eqv_symm (by
      simpa only [show k + 2 - 1 = k + 1 by omega] using
        ofNat_sub_one_eqv (k + 2) (by omega))
  have hmul : Q'.ofNat (k + 1) * E ≈
      Q'.ofNat ((k + 1) * (k + 3)) := by
    dsimp only [E]
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hminus) ?_
  refine Q'.eqv_trans _ _ _ hmul ?_
  have hnat : (k + 1) * (k + 3) = driftDen k := by
    unfold driftDen
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [hnat]
  exact Q'.eqv_refl _

private theorem certificateRight_cleared (k : Nat) :
    let A := Q'.ofNat (k + 2)
    let E := Q'.ofNat (k + 3)
    let d := Q'.ofNat (driftDen k)
    RingNormaliser.qpow E 2 *
        (RingNormaliser.qpow (A + -(1 : Q')) 6 *
          RingNormaliser.qpow E 4) ≈
      RingNormaliser.qpow d 6 := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  let d := Q'.ofNat (driftDen k)
  have hfactor : (A + -(1 : Q')) * E ≈ d := by
    dsimp only [A, E, d]
    exact harmonicDriftDen_factor k
  have hE6 : RingNormaliser.qpow E 6 ≈
      RingNormaliser.qpow E 2 * RingNormaliser.qpow E 4 := by
    simpa only using RingNormaliser.qpow_add E 2 4
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (A + -(1 : Q')) 6 *
      (RingNormaliser.qpow E 2 * RingNormaliser.qpow E 4)) _ ?_ ?_
  · physical_ring
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (A + -(1 : Q')) 6 *
      RingNormaliser.qpow E 6) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hE6)
  refine Q'.eqv_trans _
    (RingNormaliser.qpow ((A + -(1 : Q')) * E) 6) _
    (Q'.eqv_symm (rnqpow_mul_base _ _ 6)) ?_
  exact RingNormaliser.qpow_eqv_congr hfactor 6

private theorem certificateDriftBase_eqv (k : Nat) :
    let A := Q'.ofNat (k + 2)
    let d := Q'.ofNat (driftDen k)
    Q'.ofNat 2 * RingNormaliser.qpow A 2 + -(1 : Q') ≈
      Q'.ofNat 2 * d + 1 := by
  let A := Q'.ofNat (k + 2)
  let d := Q'.ofNat (driftDen k)
  have hA2 : RingNormaliser.qpow A 2 ≈ d + 1 := by
    have hsquare : RingNormaliser.qpow A 2 ≈
        Q'.ofNat ((k + 2) * (k + 2)) := by
      refine Q'.eqv_trans _ (A * A) _ ?_ ?_
      · simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
        physical_ring
      · dsimp only [A]
        exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)
    have hnat : driftDen k + 1 = (k + 2) * (k + 2) := by
      unfold driftDen
      have hpos : 0 < (k + 2) * (k + 2) := by positivity
      omega
    refine Q'.eqv_trans _ _ _ hsquare ?_
    refine Q'.eqv_trans _ (Q'.ofNat (driftDen k + 1)) _ ?_ ?_
    · rw [hnat]
      exact Q'.eqv_refl _
    · dsimp only [d]
      exact Q'.ofNat_add_eqv _ _
  refine Q'.eqv_trans _
    (Q'.ofNat 2 * (d + 1) + -(1 : Q')) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hA2)
  · physical_ring

/-- The literal physical moment coefficient is valid uniformly from the
sharp polynomial threshold `k = 1330`. -/
theorem lowerSixCubicDebt_momentCoefficient_le_massCoefficient_1330
    {k : Nat} (hk : 1330 ≤ k) :
    Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)) ≤
      Q'.ofNat 2916 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  let d := Q'.ofNat (driftDen k)
  let e := lowerSixDriftExcess k
  let S := lowerSixPrefixCubicDebtScalar k
  let profileFactor := Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1
  let driftBase := Q'.ofNat 2 * d + 1
  let Cleft := Q'.ofNat 40320 *
    (A * (profileFactor * RingNormaliser.qpow driftBase 3))
  let Cright := Q'.ofNat 2916 *
    (RingNormaliser.qpow (A + -(1 : Q')) 6 *
      RingNormaliser.qpow E 4)
  have hcertRaw := cubicDebtCoefficient_cleared_1330 hk
  have hdriftBase := certificateDriftBase_eqv k
  have hcert : Cleft ≤ Cright := by
    change Q'.ofNat 40320 *
      (A * (profileFactor * RingNormaliser.qpow driftBase 3)) ≤ Cright
    change Q'.ofNat 40320 *
      (A * ((Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1) *
        RingNormaliser.qpow
          (Q'.ofNat 2 * RingNormaliser.qpow A 2 + -(1 : Q')) 3)) ≤
        Cright at hcertRaw
    have hp := RingNormaliser.qpow_eqv_congr hdriftBase 3
    have hleft :
        Q'.ofNat 40320 *
          (A * ((Q'.ofNat 12 * RingNormaliser.qpow E 2 + 1) *
            RingNormaliser.qpow
              (Q'.ofNat 2 * RingNormaliser.qpow A 2 + -(1 : Q')) 3)) ≈
          Q'.ofNat 40320 *
            (A * (profileFactor * RingNormaliser.qpow driftBase 3)) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hp))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hcertRaw
  have hscale0 : (0 : Q') ≤ RingNormaliser.qpow A 3 *
      RingNormaliser.qpow E 2 := by
    exact Q'.mul_nonneg _ _
      (Q'.le_of_lt (rnqpow_pos A (Q'.ofNat_succ_pos (k + 1)) 3))
      (Q'.le_of_lt (rnqpow_pos E (Q'.ofNat_succ_pos (k + 2)) 2))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (RingNormaliser.qpow A 3 * RingNormaliser.qpow E 2)
    hcert hscale0
  have hprofile := profile_cleared k
  change RingNormaliser.qpow E 2 *
      (E * lowerSixDirichletProfile (k + 1)) ≈ profileFactor at hprofile
  have hdrift := driftCube_cleared k
  change RingNormaliser.qpow d 6 * RingNormaliser.qpow e 3 ≈
      RingNormaliser.qpow driftBase 3 at hdrift
  have hrightClear := certificateRight_cleared k
  change RingNormaliser.qpow E 2 *
      (RingNormaliser.qpow (A + -(1 : Q')) 6 *
        RingNormaliser.qpow E 4) ≈ RingNormaliser.qpow d 6 at hrightClear
  have hleftEqv :
      RingNormaliser.qpow d 6 *
          (Q'.ofNat 40320 *
            (RingNormaliser.qpow A 4 *
              (S * RingNormaliser.qpow E 4))) ≈
        (RingNormaliser.qpow A 3 * RingNormaliser.qpow E 2) * Cleft := by
    unfold S lowerSixPrefixCubicDebtScalar
    change RingNormaliser.qpow d 6 *
        (Q'.ofNat 40320 *
          (RingNormaliser.qpow A 4 *
            (((E * lowerSixDirichletProfile (k + 1)) *
              (e * (e * e))) * RingNormaliser.qpow E 4))) ≈ _
    have he3 : e * (e * e) ≈ RingNormaliser.qpow e 3 := by
      simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
      physical_ring
    refine Q'.eqv_trans _
      (RingNormaliser.qpow d 6 *
        (Q'.ofNat 40320 *
          (RingNormaliser.qpow A 4 *
            (((E * lowerSixDirichletProfile (k + 1)) *
              RingNormaliser.qpow e 3) * RingNormaliser.qpow E 4)))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_left _ _ _ he3))))
    refine Q'.eqv_trans _
      ((RingNormaliser.qpow A 3 * RingNormaliser.qpow E 2) *
        (Q'.ofNat 40320 *
          (A *
            ((RingNormaliser.qpow E 2 *
                (E * lowerSixDirichletProfile (k + 1))) *
              (RingNormaliser.qpow d 6 * RingNormaliser.qpow e 3))))) _ ?_ ?_
    · simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
      physical_ring
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hprofile)
          |> fun h1 => Q'.eqv_trans _ _ _ h1
            (Q'.mul_eqv_congr_left _ _ _ hdrift)))
  have hrightEqv :
      (RingNormaliser.qpow A 3 * RingNormaliser.qpow E 2) * Cright ≈
        RingNormaliser.qpow d 6 *
          (Q'.ofNat 2916 * RingNormaliser.qpow A 3) := by
    unfold Cright
    refine Q'.eqv_trans _
      (Q'.ofNat 2916 * RingNormaliser.qpow A 3 *
        (RingNormaliser.qpow E 2 *
          (RingNormaliser.qpow (A + -(1 : Q')) 6 *
            RingNormaliser.qpow E 4))) _ ?_ ?_
    · physical_ring
    refine Q'.eqv_trans _
      ((Q'.ofNat 2916 * RingNormaliser.qpow A 3) *
        RingNormaliser.qpow d 6) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hrightClear
    · exact Q'.mul_comm_eqv _ _
  have hcleared :
      RingNormaliser.qpow d 6 *
          (Q'.ofNat 40320 *
            (RingNormaliser.qpow A 4 *
              (S * RingNormaliser.qpow E 4))) ≤
        RingNormaliser.qpow d 6 *
          (Q'.ofNat 2916 * RingNormaliser.qpow A 3) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftEqv)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrightEqv))
  have hdpos : (0 : Q') < RingNormaliser.qpow d 6 :=
    rnqpow_pos d (Q'.ofNat_succ_pos (driftDen k - 1)) 6
  have hout := Q'.le_of_mul_le_mul_left hcleared hdpos
  dsimp only [A, E, d, S] at hout ⊢
  exact hout

/-
private theorem target_order_from_cleared
    {k : Nat} (hk : 1330 ≤ k) :
    Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)) ≤
      Q'.ofNat 2916 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 := by
  have hcert := cubicDebtCoefficient_cleared_1330 hk
  change
    Q'.ofNat 40320 *
        (Q'.ofNat (k + 2) *
          ((Q'.ofNat 12 * RingNormaliser.qpow (Q'.ofNat (k + 3)) 2 + 1) *
            RingNormaliser.qpow
              (Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 +
                -(1 : Q')) 3)) ≤
      Q'.ofNat 2916 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2) + -(1 : Q')) 6 *
          RingNormaliser.qpow (Q'.ofNat (k + 3)) 4) at hcert
  change
    (Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4))).num *
      ((Q'.ofNat 2916 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 3).den : Int) ≤
    (Q'.ofNat 2916 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 3).num *
      ((Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4))).den : Int)
  unfold lowerSixPrefixCubicDebtScalar lowerSixDirichletProfile
    lowerSixDriftExcess harmU unit driftDen at ⊢
  change
    (Q'.ofNat 40320 *
        (Q'.ofNat (k + 2) *
          ((Q'.ofNat 12 * RingNormaliser.qpow (Q'.ofNat (k + 3)) 2 + 1) *
            RingNormaliser.qpow
              (Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 +
                -(1 : Q')) 3))).num *
      ((Q'.ofNat 2916 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2) + -(1 : Q')) 6 *
          RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)).den : Int) ≤
    (Q'.ofNat 2916 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2) + -(1 : Q')) 6 *
          RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)).num *
      ((Q'.ofNat 40320 *
        (Q'.ofNat (k + 2) *
          ((Q'.ofNat 12 * RingNormaliser.qpow (Q'.ofNat (k + 3)) 2 + 1) *
            RingNormaliser.qpow
              (Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 +
                -(1 : Q')) 3))).den : Int) at hcert
  simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero,
    Q'.mul_num_cast, Q'.mul_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.neg_den, physical_neg_num_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mkPos_num,
    Q'.mkPos_den,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one, Int.one_mul, Int.neg_one_mul, Int.mul_neg,
    Int.neg_mul, Int.add_mul, Int.mul_add] at ⊢ hcert
  have hscale : (0 : Int) ≤
      Int.ofNat ((k + 2) * (k + 2) * (k + 2) *
        ((k + 3) * (k + 3) * (k + 3) * (k + 3))) :=
    Int.natCast_nonneg _
  have hscaled := Int.mul_le_mul_of_nonneg_left hcert hscale
  exact hscaled

/-- The literal physical moment coefficient is valid uniformly from the
sharp polynomial threshold `k = 1330`. -/
theorem lowerSixCubicDebt_momentCoefficient_le_massCoefficient_1330
    {k : Nat} (hk : 1330 ≤ k) :
    Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)) ≤
      Q'.ofNat 2916 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 :=
  target_order_from_cleared hk

-/

#print axioms cubicDebtCoefficient_cleared_1330
#print axioms lowerSixCubicDebt_momentCoefficient_le_massCoefficient_1330

end YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Physical
