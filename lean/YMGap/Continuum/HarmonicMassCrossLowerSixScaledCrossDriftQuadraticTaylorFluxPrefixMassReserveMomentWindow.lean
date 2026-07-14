/-
Large-scale closure of the reciprocal-Bernoulli quarter window.

The eighth-moment summation theorem keeps its smallness hypothesis explicit.
Here that hypothesis is discharged on the actual theta prefix from a purely
integer square-root bound.  The deliberately round threshold `k ≥ 8189`
leaves a finite bootstrap interval while keeping the proof division-free.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentWindow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem window_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "window_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               window_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pSeparationL : PE :=
  let u : PE := .var 0
  .add (.const 1)
    (.neg (.mul (.add (.const 1) (.neg u))
      (.add (.const 1) (.neg u))))

private def pSeparationR : PE :=
  let u : PE := .var 0
  .mul u (.add (.const 2) (.neg u))

private theorem pSeparation_normal :
    RingNormaliser.normalize pSeparationL =
      RingNormaliser.normalize pSeparationR := by decide

private theorem nat_le_of_square_le_square {a b : Nat}
    (hsq : a * a ≤ b * b) : a ≤ b := by
  rcases Nat.le_total a b with hab | hba
  · exact hab
  · rcases Nat.eq_or_lt_of_le hba with heq | hlt
    · exact Nat.le_of_eq heq.symm
    · by_cases hb : b = 0
      · subst b
        have ha0 : 0 < a := by omega
        have haa0 : 0 < a * a := Nat.mul_pos ha0 ha0
        omega
      · have hb0 : 0 < b := Nat.pos_of_ne_zero hb
        have ha0 : 0 < a := Nat.lt_trans hb0 hlt
        have h1 : b * b < a * b :=
          Nat.mul_lt_mul_of_pos_right hlt hb0
        have h2 : a * b < a * a :=
          Nat.mul_lt_mul_of_pos_left hlt ha0
        omega

/-- At the large-scale analytic threshold, the largest odd exponent in the
theta prefix is at most one eighth of the harmonic denominator. -/
theorem eight_odd_thetaWindowRight_le_harmonicDen
    {k : Nat} (hk : 8189 ≤ k) :
    8 * (2 * thetaWindowRight k + 1) ≤ k + 3 := by
  let D := k + 3
  let c := thetaWindowCenter k
  have hD : 8192 ≤ D := by
    dsimp only [D]
    omega
  have hc9 : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (by omega)
  have hcsq : c * c ≤ 2 * D := by
    have hraw : c * c ≤ thetaWindowLength k := by
      dsimp only [c, thetaWindowCenter]
      exact ChebOrthoMidpointEst.isqrt_sq_le _
    have hlength : thetaWindowLength k ≤ 2 * D := by
      dsimp only [D]
      unfold thetaWindowLength
      omega
    exact Nat.le_trans hraw hlength
  have hscaled := Nat.mul_le_mul_left 4096 hcsq
  have h64sq : (64 * c) * (64 * c) ≤ D * D := by
    have hfirst : (64 * c) * (64 * c) ≤ 8192 * D := by
      calc
        (64 * c) * (64 * c) = 4096 * (c * c) := by ac_rfl
        _ ≤ 4096 * (2 * D) := hscaled
        _ = 8192 * D := by omega
    have hsecond : 8192 * D ≤ D * D :=
      Nat.mul_le_mul_right D hD
    exact Nat.le_trans hfirst hsecond
  have h64c : 64 * c ≤ D := nat_le_of_square_le_square h64sq
  have hR : thetaWindowRight k ≤ 2 * c := by
    have hquarter := Nat.div_le_self c 4
    unfold thetaWindowRight
    dsimp only [c] at hquarter ⊢
    omega
  dsimp only [D] at h64c
  omega

private theorem harmonicDen_mul_nextU_eqv_one (k : Nat) :
    Q'.ofNat (k + 3) * harmU (k + 1) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem nextGaussianSeparation_eqv_u_twoSub
    (k : Nat) :
    lowerSixNextGaussianSeparation k ≈
      harmU (k + 1) * (Q'.ofNat 2 + -harmU (k + 1)) := by
  unfold lowerSixNextGaussianSeparation lowerSixNextGaussianBase
    harmW ReciprocalBernoulliUpper.oneSub
  simpa [pSeparationL, pSeparationR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSeparationL pSeparationR pSeparation_normal
      (fun _ => harmU (k + 1)))

private theorem mode_nextGaussianSeparation_le_quarter
    {k n : Nat} (hmode : 8 * (2 * n + 1) ≤ k + 3) :
    Q'.ofNat (2 * n + 1) * lowerSixNextGaussianSeparation k ≤
      oneFourth := by
  let D := Q'.ofNat (k + 3)
  let M := Q'.ofNat (2 * n + 1)
  let u := harmU (k + 1)
  let S := lowerSixNextGaussianSeparation k
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact harmU_nonneg _
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hM0 : (0 : Q') ≤ M := by
    dsimp only [M]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hcast : Q'.ofNat (8 * (2 * n + 1)) ≤ Q'.ofNat (k + 3) :=
    CReal.ofNat_le_ofNat hmode
  have hmulU := Q'.mul_le_mul_of_nonneg_right _ _ u hcast hu0
  have h8mu : (Q'.ofNat 8 * M) * u ≤ (1 : Q') := by
    have hleft : Q'.ofNat (8 * (2 * n + 1)) * u ≈
        (Q'.ofNat 8 * M) * u := by
      dsimp only [M]
      exact Q'.mul_eqv_congr_right _ _ _
        (HeatKernelRGStep.ofNat_mul_eqv 8 (2 * n + 1))
    have hright : D * u ≈ (1 : Q') := by
      dsimp only [D, u]
      exact harmonicDen_mul_nextU_eqv_one k
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hmulU (Q'.le_of_eqv hright))
  have htwoSub : Q'.ofNat 2 + -u ≤ Q'.ofNat 2 := by
    have hneg : -u ≤ (0 : Q') := by
      have hstep : (0 : Q') + -u ≤ u + -u :=
        Q'.add_le_add_right 0 u (-u) hu0
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (QPoly.q_zero_add_eqv (-u)))
        (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_neg_self_eqv u)))
    have hadd := Q'.add_le_add_left (Q'.ofNat 2) _ _ hneg
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv (Q'.ofNat 2)))
  have huMul := Q'.mul_le_mul_of_nonneg_left _ _ u htwoSub hu0
  have hS : S ≤ u * Q'.ofNat 2 := by
    dsimp only [S]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (nextGaussianSeparation_eqv_u_twoSub k)) huMul
  have hMS := Q'.mul_le_mul_of_nonneg_left _ _ M hS hM0
  have hquarter0 : (0 : Q') ≤ oneFourth := by
    unfold oneFourth
    decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ oneFourth h8mu hquarter0
  have hMUquarter : M * (u * Q'.ofNat 2) ≤ oneFourth := by
    have hleft : M * (u * Q'.ofNat 2) ≈
        oneFourth * ((Q'.ofNat 8 * M) * u) := by
      unfold oneFourth
      window_ring
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_one_eqv _)))
  dsimp only [M, S] at hMS ⊢
  exact Q'.le_trans' _ _ _ hMS hMUquarter

/-- The actual finite theta prefix satisfies the quarter-window hypothesis on
every scale `k ≥ 8189`. -/
theorem lowerSixNextGaussianQuarterWindow_large
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixNextGaussianQuarterWindow k (thetaWindowRight k) := by
  intro j hj
  apply mode_nextGaussianSeparation_le_quarter
  have hmax := eight_odd_thetaWindowRight_le_harmonicDen hk
  have hjR : j + 1 ≤ thetaWindowRight k := by omega
  have hodd : 2 * (j + 1) + 1 ≤ 2 * thetaWindowRight k + 1 := by omega
  have hscaled : 8 * (2 * (j + 1) + 1) ≤
      8 * (2 * thetaWindowRight k + 1) := Nat.mul_le_mul_left 8 hodd
  exact Nat.le_trans hscaled hmax

#print axioms eight_odd_thetaWindowRight_le_harmonicDen
#print axioms lowerSixNextGaussianQuarterWindow_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentWindow
