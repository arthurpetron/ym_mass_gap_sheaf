/-
Cancellation-preserving slope normal form for the finite-Hermite remainder.

Multiplication by `(n+1)^2` eliminates the root-power denominator.  The
squared-weight flux step then becomes the square of `n - thetaRootSlope`,
leaving a polynomial in the old and next adjacent-root slopes.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Weight-free remainder bracket: the mass term is removed from the
mass-plus-remainder net bracket. -/
def lowerSixHermiteRemainderNetBracket (k n : Nat) : Q' :=
  lowerSixHermiteNetBracket k n +
    -(Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3)

/-- Exact cleared polynomial in the old and next adjacent-root slopes. -/
def lowerSixHermiteRemainderSlopePolynomial
    (k n : Nat) (S0 S1 : Q') : Q' :=
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  let N2 := Q'.ofNat (n * n)
  let C :=
    Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
        (Q'.ofNat 4 * (S1 * S1) +
          -(lowerSixDirichletProfile (k + 1) * N2)) +
      -(D *
        (Q'.ofNat 4 * (S0 * S0) +
          -(lowerSixDirichletProfile k * N2)))
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  (A * A) *
      (Q'.ofNat 48 * RingNormaliser.qpow D 4 * C +
        J n +
        -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) +
    -(((N + -S0) * (N + -S0)) * J (n + 1))

private abbrev PE := RingNormaliser.PolyExpr

private def pSlopePowerL : PE :=
  .mul (.var 0) (.var 1)

private def pSlopePowerR : PE :=
  .add (.var 2)
    (.neg (.add (.var 2) (.neg (.mul (.var 0) (.var 1)))))

private theorem pSlopePower_normal :
    RingNormaliser.normalize pSlopePowerL =
      RingNormaliser.normalize pSlopePowerR := by decide

private theorem slope_power_algebra (A q N S : Q')
    (hS : S ≈ N + -(A * q)) :
    A * q ≈ N + -S := by
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pSlopePowerL pSlopePowerR pSlopePower_normal
    (fun | 0 => A | 1 => q | 2 => N | _ => S)
  exact Q'.eqv_trans _ _ _ hpoly
    (Q'.add_eqv_congr_left N _ _
      (Q'.eqv_symm (Q'.neg_eqv_congr _ _ hS)))

private def pBracketClearL : PE :=
  let A : PE := .var 0
  let X : PE := .var 1
  let q : PE := .var 2
  let Jp : PE := .var 3
  let Jn : PE := .var 4
  let M : PE := .var 5
  .mul (.mul A A)
    (.add
      (.add X (.neg (.add (.mul (.mul q q) Jp) (.neg Jn))))
      (.neg M))

private def pBracketClearR : PE :=
  let A : PE := .var 0
  let X : PE := .var 1
  let q : PE := .var 2
  let Jp : PE := .var 3
  let Jn : PE := .var 4
  let M : PE := .var 5
  .add
    (.mul (.mul A A) (.add (.add X Jn) (.neg M)))
    (.neg (.mul (.mul (.mul A q) (.mul A q)) Jp))

private theorem pBracketClear_normal :
    RingNormaliser.normalize pBracketClearL =
      RingNormaliser.normalize pBracketClearR := by decide

private theorem bracket_clear_algebra
    (A X q Jp Jn M : Q') :
    (A * A) * (X + -((q * q) * Jp + -Jn) + -M) ≈
      (A * A) * (X + Jn + -M) +
        -(((A * q) * (A * q)) * Jp) := by
  simpa [pBracketClearL, pBracketClearR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pBracketClearL pBracketClearR pBracketClear_normal
      (fun | 0 => A | 1 => X | 2 => q | 3 => Jp | 4 => Jn | _ => M))

private def pExtractRemainderL : PE := .var 0

private def pExtractRemainderR : PE :=
  .add (.add (.var 1) (.var 0)) (.neg (.var 1))

private theorem pExtractRemainder_normal :
    RingNormaliser.normalize pExtractRemainderL =
      RingNormaliser.normalize pExtractRemainderR := by decide

private theorem extract_remainder_algebra (R M : Q') :
    R ≈ (M + R) + -M := by
  simpa [pExtractRemainderL, pExtractRemainderR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pExtractRemainderL pExtractRemainderR pExtractRemainder_normal
      (fun | 0 => R | _ => M))

private def pExtractFactorL : PE :=
  .add (.mul (.var 0) (.var 1))
    (.neg (.mul (.var 0) (.var 2)))

private def pExtractFactorR : PE :=
  .mul (.var 0) (.add (.var 1) (.neg (.var 2)))

private theorem pExtractFactor_normal :
    RingNormaliser.normalize pExtractFactorL =
      RingNormaliser.normalize pExtractFactorR := by decide

private theorem extract_factor_algebra (W B M : Q') :
    W * B + -(W * M) ≈ W * (B + -M) := by
  simpa [pExtractFactorL, pExtractFactorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pExtractFactorL pExtractFactorR pExtractFactor_normal
      (fun | 0 => W | 1 => B | _ => M))

private theorem lowerSixQuadraticTaylorCarrier_slope_eqv
    (k n : Nat) :
    let D := Q'.ofNat (k + 2)
    let N2 := Q'.ofNat (n * n)
    let S0 := thetaRootSlope k n
    let S1 := thetaRootSlope (k + 1) n
    lowerSixQuadraticTaylorCarrier k n ≈
      Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
          (Q'.ofNat 4 * (S1 * S1) +
            -(lowerSixDirichletProfile (k + 1) * N2)) +
        -(D *
          (Q'.ofNat 4 * (S0 * S0) +
            -(lowerSixDirichletProfile k * N2))) := by
  unfold lowerSixQuadraticTaylorCarrier lowerSixModeCarrier
  exact Q'.eqv_refl _

private theorem old_root_power_eqv (k n : Nat) :
    let A := Q'.ofNat (n + 1)
    let N := Q'.ofNat n
    let q := qpow (harmW k) (2 * n + 1)
    A * q ≈ N + -thetaRootSlope k n := by
  intro A N q
  have hS : thetaRootSlope k n ≈ N + -(A * q) := by
    unfold thetaRootSlope
    exact Q'.eqv_refl _
  exact slope_power_algebra A q N (thetaRootSlope k n) hS

/-- Exact polynomial normal form for the cleared remainder bracket. -/
theorem lowerSixHermiteRemainderNetBracket_slopePolynomial (k n : Nat) :
    let A := Q'.ofNat (n + 1)
    (A * A) * lowerSixHermiteRemainderNetBracket k n ≈
      lowerSixHermiteRemainderSlopePolynomial k n
        (thetaRootSlope k n) (thetaRootSlope (k + 1) n) := by
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  let q := qpow (harmW k) (2 * n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let C := lowerSixQuadraticTaylorCarrier k n
  let X := Q'.ofNat 48 * RingNormaliser.qpow D 4 * C
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  let M := Q'.ofNat 6 * RingNormaliser.qpow D 3
  have hstep : step ≈ q * q := by
    dsimp only [step, q]
    exact qpow_mul_self (harmW k) (2 * n + 1)
  have hreplaceStep :
      (A * A) * (X + -(step * J (n + 1) + -J n) + -M) ≈
        (A * A) * (X + -((q * q) * J (n + 1) + -J n) + -M) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_right _ _ _ hstep)))))
  have hclear := bracket_clear_algebra A X q (J (n + 1)) (J n) M
  have hAq := old_root_power_eqv k n
  have hsquare : (A * q) * (A * q) ≈
      (N + -thetaRootSlope k n) * (N + -thetaRootSlope k n) :=
    Q'.eqv_trans _
      ((N + -thetaRootSlope k n) * (A * q)) _
      (Q'.mul_eqv_congr_right _ _ _ hAq)
      (Q'.mul_eqv_congr_left _ _ _ hAq)
  have hreplaceSlope :
      (A * A) * (X + J n + -M) +
          -(((A * q) * (A * q)) * J (n + 1)) ≈
        (A * A) * (X + J n + -M) +
          -(((N + -thetaRootSlope k n) *
            (N + -thetaRootSlope k n)) * J (n + 1)) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ hsquare))
  have hcarrier := lowerSixQuadraticTaylorCarrier_slope_eqv k n
  have hX : X ≈
      Q'.ofNat 48 * RingNormaliser.qpow D 4 *
        (Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
            (Q'.ofNat 4 *
                (thetaRootSlope (k + 1) n * thetaRootSlope (k + 1) n) +
              -(lowerSixDirichletProfile (k + 1) * Q'.ofNat (n * n))) +
          -(D *
            (Q'.ofNat 4 * (thetaRootSlope k n * thetaRootSlope k n) +
              -(lowerSixDirichletProfile k * Q'.ofNat (n * n))))) :=
    Q'.mul_eqv_congr_left _ _ _ hcarrier
  unfold lowerSixHermiteRemainderNetBracket lowerSixHermiteNetBracket
    lowerSixHermiteRemainderSlopePolynomial
  dsimp only [D, A, N, q, step, C, X, J, M] at hreplaceStep hclear hreplaceSlope hX ⊢
  exact Q'.eqv_trans _ _ _ hreplaceStep
    (Q'.eqv_trans _ _ _ hclear
      (Q'.eqv_trans _ _ _ hreplaceSlope
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_eqv_congr_right _ _ _ hX))))))

/-- Exact removal of the positive old Gaussian weight from the finite-Hermite
remainder itself. -/
theorem lowerSixDiscreteHermiteRemainder_eqv_weight_mul_netBracket
    (k n : Nat) :
    lowerSixDiscreteHermiteRemainder k n ≈
      lowerSixModeWeight k n * lowerSixHermiteRemainderNetBracket k n := by
  let R := lowerSixDiscreteHermiteRemainder k n
  let Mass := lowerSixDiscreteHermiteMassNumerator k n
  let W := lowerSixModeWeight k n
  let B := lowerSixHermiteNetBracket k n
  let M := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hsum : Mass + R ≈ W * B := by
    dsimp only [Mass, R, W, B]
    exact lowerSixMass_add_remainder_eqv_weight_mul_netBracket k n
  have hmass : Mass ≈ W * M := by
    dsimp only [Mass, W, M]
    unfold lowerSixDiscreteHermiteMassNumerator
    exact Q'.mul_comm_eqv _ _
  have hreplace : (Mass + R) + -Mass ≈ W * B + -(W * M) :=
    Q'.add_eqv_congr'
      hsum (Q'.neg_eqv_congr _ _ hmass)
  change R ≈ W * (B + -M)
  exact Q'.eqv_trans _ _ _
    (extract_remainder_algebra _ _)
    (Q'.eqv_trans _ _ _ hreplace (extract_factor_algebra _ _ _))

/-- A nonnegative cleared slope polynomial implies a nonnegative actual
finite-Hermite remainder. -/
theorem lowerSixDiscreteHermiteRemainder_nonnegative_of_slopePolynomial
    {k n : Nat}
    (hpoly : (0 : Q') ≤ lowerSixHermiteRemainderSlopePolynomial k n
      (thetaRootSlope k n) (thetaRootSlope (k + 1) n)) :
    (0 : Q') ≤ lowerSixDiscreteHermiteRemainder k n := by
  let A := Q'.ofNat (n + 1)
  let B := lowerSixHermiteRemainderNetBracket k n
  let P := lowerSixHermiteRemainderSlopePolynomial k n
    (thetaRootSlope k n) (thetaRootSlope (k + 1) n)
  have hnorm : (A * A) * B ≈ P := by
    dsimp only [A, B, P]
    exact lowerSixHermiteRemainderNetBracket_slopePolynomial k n
  have hcleared : (0 : Q') ≤ (A * A) * B :=
    Q'.le_trans' _ _ _ hpoly (Q'.ge_of_eqv hnorm)
  have hApos : (0 : Q') < A := by
    dsimp only [A]
    exact Q'.ofNat_succ_pos n
  have hA2pos : (0 : Q') < A * A := Q'.mul_pos hApos hApos
  have hB : (0 : Q') ≤ B := Q'.nonneg_of_mul_pos hA2pos hcleared
  have hwpos : (0 : Q') < lowerSixModeWeight k n := by
    unfold lowerSixModeWeight
    exact BondMovingScaledNorm.qpow_pos
      (Q'.mul_pos
        (HarmonicFusedSchurObstruction.harmW_pos k)
        (HarmonicFusedSchurObstruction.harmW_pos k)) (n * n)
  have hprod : (0 : Q') ≤ lowerSixModeWeight k n * B :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hwpos) hB
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (lowerSixDiscreteHermiteRemainder_eqv_weight_mul_netBracket k n)))

#print axioms lowerSixHermiteRemainderNetBracket_slopePolynomial
#print axioms lowerSixDiscreteHermiteRemainder_eqv_weight_mul_netBracket
#print axioms lowerSixDiscreteHermiteRemainder_nonnegative_of_slopePolynomial

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier
