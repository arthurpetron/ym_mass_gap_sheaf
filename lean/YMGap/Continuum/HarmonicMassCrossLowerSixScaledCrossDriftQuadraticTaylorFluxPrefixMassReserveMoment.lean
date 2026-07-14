/-
Exact scale bounds for paying the cubic Taylor debt from the Hermite mass.

The mass-reserve regrouping leaves a single Gaussian factorial-moment
estimate.  This file records the coefficient and harmonic-scale bounds used
to reduce that estimate to a dimensionless finite Gaussian moment.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem moment_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "moment_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               moment_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Exact closed form for the subtraction-free quadratic Pascal coefficient. -/
theorem lowerSixQuadraticCoeff_double (m : Nat) :
    2 * lowerSixQuadraticCoeff m = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [lowerSixQuadraticCoeff]
      cases m with
      | zero => rfl
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          calc
            2 * (lowerSixQuadraticCoeff (n + 1) + (n + 1)) =
                2 * lowerSixQuadraticCoeff (n + 1) + 2 * (n + 1) :=
              Nat.mul_add _ _ _
            _ = (n + 1) * n + 2 * (n + 1) := by rw [ih]
            _ = (n + 2) * (n + 1) := by
              simp only [Nat.add_mul, Nat.mul_add]
              omega

/-- Exact closed form for the cubic Pascal coefficient. -/
theorem cubicCoeff_six (m : Nat) :
    6 * cubicCoeff m = m * (m - 1) * (m - 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [cubicCoeff]
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => rfl
          | succ n =>
              have hsubq : n + 2 - 1 = n + 1 := by omega
              have hq : 2 * lowerSixQuadraticCoeff (n + 2) =
                  (n + 2) * (n + 1) := by
                simpa only [hsubq] using
                  lowerSixQuadraticCoeff_double (n + 2)
              have hi0 : n + 1 + 1 = n + 2 := by omega
              have hi1 : n + 1 + 1 - 1 = n + 1 := by omega
              have hi2 : n + 1 + 1 - 2 = n := by omega
              have ih' : 6 * cubicCoeff (n + 2) =
                  (n + 2) * (n + 1) * n := by
                simpa only [hi0, hi1, hi2] using ih
              simp only [Nat.add_sub_cancel] at ⊢
              calc
                6 * (cubicCoeff (n + 2) + lowerSixQuadraticCoeff (n + 2)) =
                    6 * cubicCoeff (n + 2) +
                      6 * lowerSixQuadraticCoeff (n + 2) :=
                  Nat.mul_add _ _ _
                _ = ((n + 2) * (n + 1) * n) +
                      3 * (2 * lowerSixQuadraticCoeff (n + 2)) := by
                  rw [ih']
                  omega
                _ = ((n + 2) * (n + 1) * n) +
                      3 * ((n + 2) * (n + 1)) := by rw [hq]
                _ = ((n + 2) * (n + 1)) * n +
                      ((n + 2) * (n + 1)) * 3 := by ac_rfl
                _ = ((n + 2) * (n + 1)) * (n + 3) := by
                  exact (Nat.mul_add _ _ _).symm
                _ = (n + 3) * (n + 2) * (n + 1) := by
                  ac_rfl

/-- The cubic Pascal coefficient is at most one sixth of the exponent cube,
in a division-free form. -/
theorem six_cubicCoeff_le_cube (m : Nat) :
    6 * cubicCoeff m ≤ m * m * m := by
  rw [cubicCoeff_six]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.le_refl m) (Nat.sub_le m 1))
    (Nat.sub_le m 2)

private theorem ofNat_mul_unit_eqv_one_local (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem four_mul_unit_le_one_local
    (n : Nat) (hn : 4 ≤ n) :
    Q'.ofNat 4 * unit n (by omega) ≤ (1 : Q') := by
  unfold unit
  show (Q'.ofNat 4 * Q'.mkPos 1 n (by omega)).num *
      ((1 : Q').den : Int) ≤
    (1 : Q').num *
      ((Q'.ofNat 4 * Q'.mkPos 1 n (by omega)).den : Int)
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d]
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  exact_mod_cast hn

private theorem scaled_drift_excess_algebra (d u : Q') :
    (d + 1) * ((u + u) + u * u) ≈
      ((d * u + d * u) + ((d * u) * u + (u + u))) + u * u := by
  moment_ring

private theorem four_units_algebra (u : Q') :
    ((u + u) + u) + u ≈ Q'.ofNat 4 * u := by
  have h4 : (((1 : Q') + 1) + (1 + 1)) ≈ Q'.ofNat 4 := by decide
  refine Q'.eqv_trans _ ((((1 : Q') + 1) + (1 + 1)) * u) _ ?_ ?_
  · moment_ring
  · exact Q'.mul_eqv_congr_right _ _ u h4

/-- At every campaign scale, the cube-generating drift excess costs at most
three inverse square units after multiplication by the harmonic square. -/
theorem lowerSixDriftExcess_scaled_le_three
    {k : Nat} (hk : 1 ≤ k) :
    Q'.ofNat ((k + 2) * (k + 2)) * lowerSixDriftExcess k ≤
      Q'.ofNat 3 := by
  let d : Nat := driftDen k
  let u : Q' := unit d (driftDen_pos k)
  have hsquare : 9 ≤ (k + 2) * (k + 2) :=
    Nat.mul_le_mul (by omega : 3 ≤ k + 2) (by omega : 3 ≤ k + 2)
  have hd4 : 4 ≤ d := by
    dsimp only [d]
    unfold driftDen
    omega
  have hscale : (k + 2) * (k + 2) = d + 1 := by
    dsimp only [d]
    unfold driftDen
    omega
  have hdu : Q'.ofNat d * u ≈ (1 : Q') := by
    dsimp only [u]
    exact ofNat_mul_unit_eqv_one_local d (driftDen_pos k)
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact unit_nonneg d (driftDen_pos k)
  have h4u : Q'.ofNat 4 * u ≤ (1 : Q') := by
    dsimp only [u]
    exact four_mul_unit_le_one_local d hd4
  have hu1 : u ≤ (1 : Q') := by
    have h1four : (1 : Q') ≤ Q'.ofNat 4 := by decide
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ u h1four hu0
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv u))) hmul)
      h4u
  have huu : u * u ≤ u := by
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _ u hu1 hu0
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv u))
  have hsmall : ((u + u) + u) + u * u ≤ (1 : Q') := by
    have hadd := Q'.add_le_add_left ((u + u) + u) _ _ huu
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (four_units_algebra u)) h4u)
  have hexpand :
      (Q'.ofNat d + 1) * ((u + u) + u * u) ≈
        ((1 : Q') + 1) + (((u + u) + u) + u * u) := by
    refine Q'.eqv_trans _
      (((Q'.ofNat d * u + Q'.ofNat d * u) +
          ((Q'.ofNat d * u) * u + (u + u))) + u * u) _
      (scaled_drift_excess_algebra (Q'.ofNat d) u) ?_
    refine Q'.eqv_trans _
      ((((1 : Q') + 1) + ((1 : Q') * u + (u + u))) + u * u) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' hdu hdu)
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_right _ _ u hdu)
            (Q'.eqv_refl _)))
        (Q'.eqv_refl _)
    · moment_ring
  have hle : (Q'.ofNat d + 1) * ((u + u) + u * u) ≤
      Q'.ofNat 3 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left ((1 : Q') + 1) _ _ hsmall)
        (by decide))
  rw [hscale]
  unfold lowerSixDriftExcess
  change Q'.ofNat (d + 1) * ((u + u) + u * u) ≤ Q'.ofNat 3
  have hcast : Q'.ofNat (d + 1) ≈ Q'.ofNat d + 1 := by
    refine Q'.eqv_trans _ (Q'.ofNat d + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv d 1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ ((u + u) + u * u) hcast))
    hle

/-- The denominator-scaled next profile is bounded by the integer thirteen:
the exact leading contribution is twelve and the remaining square is at most
one. -/
theorem lowerSixDirichletProfile_scaled_le_thirteen (k : Nat) :
    Q'.ofNat (k + 3) * lowerSixDirichletProfile (k + 1) ≤
      Q'.ofNat 13 := by
  let u := harmU (k + 1)
  have hdu : Q'.ofNat (k + 3) * u ≈ (1 : Q') := by
    have h := ofNat_mul_unit_eqv_one_local (k + 3) (by omega)
    dsimp only [u]
    unfold harmU
    simpa only [show k + 1 + 2 = k + 3 by omega] using h
  have hu0 : (0 : Q') ≤ u := harmU_nonneg (k + 1)
  have huu : u * u ≤ (1 : Q') := by
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmU_le_one (k + 1)) (harmU_le_one (k + 1)) (by decide) hu0
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hinner : Q'.ofNat 12 + u * u ≤ Q'.ofNat 13 := by
    have h := Q'.add_le_add_left (Q'.ofNat 12) _ _ huu
    exact Q'.le_trans' _ _ _ h (by decide)
  have heq : Q'.ofNat (k + 3) * lowerSixDirichletProfile (k + 1) ≈
      Q'.ofNat 12 + u * u := by
    unfold lowerSixDirichletProfile
    dsimp only [u]
    refine Q'.eqv_trans _
      ((Q'.ofNat (k + 3) * harmU (k + 1)) *
        (Q'.ofNat 12 + harmU (k + 1) * harmU (k + 1))) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((1 : Q') *
        (Q'.ofNat 12 + harmU (k + 1) * harmU (k + 1))) _
      (Q'.mul_eqv_congr_right _ _ _ hdu) ?_
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hinner

/-- The next-scale Gaussian factorial-moment cell left after exact
cancellation of the old weight against the drift factor. -/
def lowerSixPrefixCubicMomentCell (k j : Nat) : Q' :=
  let n := j + 1
  (Q'.ofNat (cubicCoeff (n * n)) * Q'.ofNat (n * n)) *
    lowerSixModeWeight (k + 1) n

def lowerSixPrefixCubicMomentSum (k : Nat) : Q' :=
  finSum (lowerSixPrefixCubicMomentCell k) (thetaWindowRight k)

/-- Exact scalar multiplying the next-scale cubic moment. -/
def lowerSixPrefixCubicDebtScalar (k : Nat) : Q' :=
  (Q'.ofNat (k + 3) * lowerSixDirichletProfile (k + 1)) *
    (lowerSixDriftExcess k *
      (lowerSixDriftExcess k * lowerSixDriftExcess k))

theorem prefixCubicDebtCell_eqv_scalar_moment (k j : Nat) :
    prefixCubicDebtCell k j ≈
      lowerSixPrefixCubicDebtScalar k *
        lowerSixPrefixCubicMomentCell k j := by
  let n := j + 1
  let W := lowerSixModeWeight k n
  let F := lowerSixWeightDriftFactor k n
  let W1 := lowerSixModeWeight (k + 1) n
  let C := Q'.ofNat (cubicCoeff (n * n))
  let N := Q'.ofNat (n * n)
  let D := Q'.ofNat (k + 3)
  let P := lowerSixDirichletProfile (k + 1)
  let e := lowerSixDriftExcess k
  let S := (D * P) * (e * (e * e))
  have hstep : W * F ≈ W1 :=
    Q'.eqv_symm (lowerSixModeWeight_step_eqv k n)
  refine Q'.eqv_trans _ (S * ((C * N) * (W * F))) _ ?_ ?_
  · unfold prefixCubicDebtCell cubicUpper carrierDebt
      lowerSixAbelWeight
    dsimp only [n, W, F, W1, C, N, D, P, e, S]
    ring_qeqv
  · unfold lowerSixPrefixCubicDebtScalar lowerSixPrefixCubicMomentCell
    dsimp only [n, W, F, W1, C, N, D, P, e, S]
    exact Q'.mul_eqv_congr_left S _ _
      (Q'.mul_eqv_congr_left (C * N) _ _ hstep)

theorem lowerSixPrefixCubicMomentCell_nonnegative (k j : Nat) :
    (0 : Q') ≤ lowerSixPrefixCubicMomentCell k j := by
  unfold lowerSixPrefixCubicMomentCell
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _))
    (lowerSixModeWeight_nonnegative (k + 1) (j + 1))

theorem lowerSixPrefixCubicMomentSum_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixPrefixCubicMomentSum k := by
  unfold lowerSixPrefixCubicMomentSum
  induction thetaWindowRight k with
  | zero => exact Q'.le_refl' 0
  | succ N ih =>
      exact Q'.zero_le_add _ _ ih
        (lowerSixPrefixCubicMomentCell_nonnegative k N)

/-- Exact factorization of the complete cubic debt into its harmonic scalar
and one finite next-scale Gaussian factorial moment. -/
theorem prefixCubicDebtSum_eqv_scalar_moment (k : Nat) :
    prefixCubicDebtSum k ≈
      lowerSixPrefixCubicDebtScalar k * lowerSixPrefixCubicMomentSum k := by
  unfold prefixCubicDebtSum lowerSixPrefixCubicMomentSum
  refine Q'.eqv_trans _
    (finSum
      (fun j => lowerSixPrefixCubicDebtScalar k *
        lowerSixPrefixCubicMomentCell k j)
      (thetaWindowRight k)) _ ?_ ?_
  · exact finSum_eqv_congr _ _
      (fun j => prefixCubicDebtCell_eqv_scalar_moment k j) _
  · exact Q'.eqv_symm
      (const_mul_finSum (lowerSixPrefixCubicMomentCell k)
        (lowerSixPrefixCubicDebtScalar k) (thetaWindowRight k))

#print axioms lowerSixQuadraticCoeff_double
#print axioms cubicCoeff_six
#print axioms six_cubicCoeff_le_cube
#print axioms lowerSixDriftExcess_scaled_le_three
#print axioms lowerSixDirichletProfile_scaled_le_thirteen
#print axioms prefixCubicDebtCell_eqv_scalar_moment
#print axioms lowerSixPrefixCubicMomentSum_nonnegative
#print axioms prefixCubicDebtSum_eqv_scalar_moment

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
