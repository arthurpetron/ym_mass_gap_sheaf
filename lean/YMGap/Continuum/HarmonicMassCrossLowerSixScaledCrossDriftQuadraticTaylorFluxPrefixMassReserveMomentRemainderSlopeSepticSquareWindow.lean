/-
Physical-window square bounds for the seventh-order root-slope model.

The exact root slope lies in `[-1,1]` on the left square-root prefix.  The
generic sign-agnostic perturbation lemmas therefore provide the old-square
upper bound and next-square lower bound required by the finite-Hermite
carrier, while the flux square is monotone directly from `T6 <= S`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquare
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareWindow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquare
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pNatPredL : PE :=
  .add (.var 0) (.neg (.add (.var 0) (.const 1)))

private def pNatPredR : PE := .neg (.const 1)

private theorem pNatPred_normal :
    RingNormaliser.normalize pNatPredL =
      RingNormaliser.normalize pNatPredR := by decide

private theorem ofNat_sub_succ_eqv_neg_one (n : Nat) :
    Q'.ofNat n + -Q'.ofNat (n + 1) ≈ -(1 : Q') := by
  let N := Q'.ofNat n
  let A := Q'.ofNat (n + 1)
  have hA : A ≈ N + (1 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hreplace : N + -A ≈ N + -(N + (1 : Q')) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hA)
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pNatPredL pNatPredR pNatPred_normal
    (fun _ => N)
  exact Q'.eqv_trans _ _ _ hreplace hpoly

private def pBernoulliSlopeL : PE :=
  let A : PE := .var 0
  let M : PE := .var 1
  let u : PE := .var 2
  .add
    (.add A (.neg (.const 1)))
    (.neg (.mul A (.add (.const 1) (.neg (.mul M u)))))

private def pBernoulliSlopeR : PE :=
  let A : PE := .var 0
  let M : PE := .var 1
  let u : PE := .var 2
  .add (.neg (.const 1)) (.mul (.mul A M) u)

private theorem pBernoulliSlope_normal :
    RingNormaliser.normalize pBernoulliSlopeL =
      RingNormaliser.normalize pBernoulliSlopeR := by decide

private theorem bernoulli_slope_algebra (A M u : Q') :
    (A + -(1 : Q')) + -(A * ((1 : Q') + -(M * u))) ≈
      -(1 : Q') + (A * M) * u := by
  simpa [pBernoulliSlopeL, pBernoulliSlopeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pBernoulliSlopeL pBernoulliSlopeR pBernoulliSlope_normal
      (fun | 0 => A | 1 => M | _ => u))

private theorem root_linear_numerator_le_two_den
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (n + 1) * (2 * n + 1) ≤ 2 * (k + 2) := by
  let c := thetaWindowCenter k
  let D := k + 2
  let A := n + 1
  let m := 2 * n + 1
  have hc9 : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (by omega)
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have h2A : 2 * A ≤ c + 2 := by
    dsimp only [A]
    omega
  have hm : m ≤ c + 1 := by
    dsimp only [m]
    omega
  have hprod : (2 * A) * m ≤ (c + 2) * (c + 1) :=
    Nat.mul_le_mul h2A hm
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h6c : 6 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 6 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have h3c : 3 * c ≤ D := by omega
  have hright : (c + 2) * (c + 1) ≤ 4 * D := by
    have hexpand : (c + 2) * (c + 1) = c * c + 3 * c + 2 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    rw [hexpand]
    omega
  have htwice : 2 * (A * m) ≤ 2 * (2 * D) := by
    calc
      2 * (A * m) = (2 * A) * m := by ac_rfl
      _ ≤ (c + 2) * (c + 1) := hprod
      _ ≤ 4 * D := hright
      _ = 2 * (2 * D) := by ac_rfl
  have hcancel : A * m ≤ 2 * D :=
    Nat.le_of_mul_le_mul_left htwice (by decide)
  simpa only [A, m, D] using hcancel

private theorem root_linear_fraction_le_two
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1)) * harmU k ≤
      Q'.ofNat 2 := by
  have hnat := root_linear_numerator_le_two_den hk hn
  unfold harmU unit
  show
    ((Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1)) *
      Q'.mkPos 1 (k + 2) (by omega)).num *
        ((Q'.ofNat 2).den : Int) ≤
      (Q'.ofNat 2).num *
        (((Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1)) *
          Q'.mkPos 1 (k + 2) (by omega)).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  exact_mod_cast hnat

/-- Every harmonic adjacent-root slope is at least `-1`. -/
theorem lowerSixThetaRootSlope_ge_neg_one (k n : Nat) :
    -(1 : Q') ≤ thetaRootSlope k n := by
  let q := qpow (harmW k) (2 * n + 1)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  have hq1 : q ≤ (1 : Q') :=
    HeatKernelGap.qpow_le_one (harmW_nonneg k) (harmW_le_one k) _
  have hmul : A * q ≤ A * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ A hq1
      (HeatKernelRGStep.zero_le_ofNat _)
  have hright : A * (1 : Q') ≈ A := Q'.mul_one_eqv A
  have hAq : A * q ≤ A :=
    Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright)
  have hneg : -A ≤ -(A * q) := Q'.neg_le_neg hAq
  have hadd := Q'.add_le_add_left N (-A) (-(A * q)) hneg
  have hconst : N + -A ≈ -(1 : Q') := by
    dsimp only [N, A]
    exact ofNat_sub_succ_eqv_neg_one n
  unfold thetaRootSlope
  dsimp only [q, A, N] at hadd hconst ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconst) hadd

/-- On the physical left prefix, the adjacent-root slope is at most `1`. -/
theorem lowerSixThetaRootSlope_le_one_large
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    thetaRootSlope k n ≤ (1 : Q') := by
  let q := qpow (harmW k) (2 * n + 1)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  let M := Q'.ofNat (2 * n + 1)
  let u := harmU k
  let L := (1 : Q') + -(M * u)
  have hbern0 := MovingCutoff.qpow_ge_bernoulli
    (harmW_nonneg k) (harmW_le_one k) (2 * n + 1)
  have hcomp : (1 : Q') - harmW k ≈ u := by
    unfold harmW ReciprocalBernoulliUpper.oneSub
    dsimp only [u]
    have h : (1 : Q') + -((1 : Q') + -harmU k) ≈ harmU k := by
      let rho : Nat → Q' := fun _ => harmU k
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
        (.var 0) (by decide) rho
    exact h
  have hL : (1 : Q') - Q'.ofNat (2 * n + 1) *
      ((1 : Q') - harmW k) ≈ L := by
    dsimp only [L, M]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hcomp))
  have hbern : L ≤ q :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) hbern0
  have hmul : A * L ≤ A * q :=
    Q'.mul_le_mul_of_nonneg_left _ _ A hbern
      (HeatKernelRGStep.zero_le_ofNat _)
  have hneg : -(A * q) ≤ -(A * L) := Q'.neg_le_neg hmul
  have hslope := Q'.add_le_add_left N (-(A * q)) (-(A * L)) hneg
  have hN : N ≈ A + -(1 : Q') := by
    have hbase := ofNat_sub_succ_eqv_neg_one n
    let e := N + -A
    have hsum : A + e ≈ N := by
      dsimp only [e]
      let rho : Nat → Q' := fun | 0 => A | _ => N
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
        (.var 1) (by decide) rho
    have he : e ≈ -(1 : Q') := by
      dsimp only [e, N, A]
      exact hbase
    exact Q'.eqv_trans _ (A + e) _
      (Q'.eqv_symm hsum) (Q'.add_eqv_congr_left _ _ _ he)
  have hrewrite : N + -(A * L) ≈
      -(1 : Q') + (A * M) * u := by
    exact Q'.eqv_trans _ ((A + -(1 : Q')) + -(A * L)) _
      (Q'.add_eqv_congr_right _ _ _ hN)
      (by
        dsimp only [L]
        exact bernoulli_slope_algebra A M u)
  have hfrac : (A * M) * u ≤ Q'.ofNat 2 := by
    dsimp only [A, M, u]
    exact root_linear_fraction_le_two hk hn
  have hadd := Q'.add_le_add_left (-(1 : Q')) _ _ hfrac
  have htarget : -(1 : Q') + Q'.ofNat 2 ≈ (1 : Q') := by decide
  unfold thetaRootSlope
  dsimp only [q, A, N, M, u, L] at hslope hrewrite ⊢
  exact Q'.le_trans' _ _ _ hslope
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv htarget)))

private theorem thetaWindowLeft_mono_step (k : Nat) :
    thetaWindowLeft k ≤ thetaWindowLeft (k + 1) := by
  have h := thetaWindowCenter_mono_step k
  unfold thetaWindowLeft
  omega

private theorem invDenCube_le_one (k : Nat) :
    Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
        (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) ≤
      (1 : Q') := by
  let T : Q' := Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
    (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
  change T ≤ (1 : Q')
  change T.num * ((1 : Q').den : Int) ≤
    (1 : Q').num * (T.den : Int)
  dsimp only [T]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d]
  simp only [Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have hD : 1 ≤ k + 2 := by omega
  have hcube : 1 ≤ (k + 2) * ((k + 2) * (k + 2)) :=
    Nat.mul_le_mul hD (Nat.mul_le_mul hD hD)
  exact_mod_cast hcube

/-- Old-slope square upper bound on the physical prefix. -/
theorem lowerSixThetaRootSlope_square_le_Taylor6_square_add_three_invCube
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    thetaRootSlope k n * thetaRootSlope k n ≤
      rootSlopeTaylor6 (harmU k) n * rootSlopeTaylor6 (harmU k) n +
        Q'.ofNat 3 *
          Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
            (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) := by
  exact square_le_model_square_add_three_error
    (lowerSixThetaRootSlopeTaylor6_le k n)
    (lowerSixThetaRootSlope_le_Taylor6_add_invDenCube_large hk hn)
    (lowerSixThetaRootSlope_le_one_large hk hn)
    (invDenCube_le_one k)

/-- Next-slope square lower bound on the same physical prefix. -/
theorem lowerSixTaylor6Next_square_sub_four_invCube_le_ThetaRootSlope_square
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    rootSlopeTaylor6 (harmU (k + 1)) n *
          rootSlopeTaylor6 (harmU (k + 1)) n +
        -(Q'.ofNat 4 *
          Q'.mkPos 1 ((k + 3) * ((k + 3) * (k + 3)))
            (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))) ≤
      thetaRootSlope (k + 1) n * thetaRootSlope (k + 1) n := by
  have hnnext : n ≤ thetaWindowLeft (k + 1) :=
    Nat.le_trans hn (thetaWindowLeft_mono_step k)
  exact model_square_sub_four_error_le_square
    (lowerSixThetaRootSlope_ge_neg_one (k + 1) n)
    (lowerSixThetaRootSlopeTaylor6_le (k + 1) n)
    (lowerSixThetaRootSlope_le_Taylor6_add_invDenCube_large
      (k := k + 1) (n := n) (by omega) hnnext)
    (invDenCube_le_one (k + 1))

/-- The old flux square is bounded above by the square induced by the lower
Taylor slope model. -/
theorem lowerSixOldFluxSlope_square_le_Taylor6Flux_square
    (k n : Nat) :
    (Q'.ofNat n + -thetaRootSlope k n) *
        (Q'.ofNat n + -thetaRootSlope k n) ≤
      (Q'.ofNat n + -rootSlopeTaylor6 (harmU k) n) *
        (Q'.ofNat n + -rootSlopeTaylor6 (harmU k) n) := by
  let S := thetaRootSlope k n
  let T := rootSlopeTaylor6 (harmU k) n
  let N := Q'.ofNat n
  have hmodel := lowerSixThetaRootSlopeTaylor6_le k n
  have hneg := Q'.neg_le_neg hmodel
  have hdiff : N + -S ≤ N + -T := Q'.add_le_add_left N _ _ hneg
  have hleft0 : (0 : Q') ≤ N + -S := by
    let A := Q'.ofNat (n + 1)
    let q := qpow (harmW k) (2 * n + 1)
    have hq0 := qpow_nonneg (harmW k) (harmW_nonneg k) (2 * n + 1)
    have hprod := Q'.mul_nonneg A q (HeatKernelRGStep.zero_le_ofNat _) hq0
    have heq : N + -S ≈ A * q := by
      dsimp only [N, S, A, q]
      unfold thetaRootSlope
      let rho : Nat → Q' := fun
        | 0 => Q'.ofNat n | 1 => Q'.ofNat (n + 1)
        | _ => qpow (harmW k) (2 * n + 1)
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0)
          (.neg (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))))
        (.mul (.var 1) (.var 2)) (by decide) rho
    exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv heq)
  have hright0 : (0 : Q') ≤ N + -T :=
    Q'.le_trans' _ _ _ hleft0 hdiff
  dsimp only [N, S, T] at hdiff hleft0 hright0 ⊢
  exact Q'.mul_le_mul_of_nonneg hdiff hdiff hright0 hleft0

#print axioms lowerSixThetaRootSlope_ge_neg_one
#print axioms lowerSixThetaRootSlope_le_one_large
#print axioms lowerSixThetaRootSlope_square_le_Taylor6_square_add_three_invCube
#print axioms lowerSixTaylor6Next_square_sub_four_invCube_le_ThetaRootSlope_square
#print axioms lowerSixOldFluxSlope_square_le_Taylor6Flux_square

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareWindow
