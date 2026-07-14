/-
Exact sign certificate for the second lower-six Hermite flux.

The flux has one positive monomial.  A sum-of-squares identity absorbs it
uniformly on the nonnegative quadrant, so both the weight-free flux and its
Gaussian-weighted numerator are nonpositive.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux

namespace YMGap.Continuum.HarmonicLowerSixSecondFluxSign

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

/-- Integral odd polynomial selected by the second Hermite-flux identity. -/
def lowerSixHermiteSecondFluxPoly (D N : Q') : Q' :=
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let N3 := RingNormaliser.qpow N 3
  let N5 := RingNormaliser.qpow N 5
  let N7 := RingNormaliser.qpow N 7
  let N9 := RingNormaliser.qpow N 9
  (((-(Q'.ofNat 15750 * N * D4) +
      -(Q'.ofNat 45560 * N3 * D3)) +
      Q'.ofNat 10976 * N5 * D2) +
      -(Q'.ofNat 30848 * N7 * D)) +
      -(Q'.ofNat 4608 * N9)

private def pAbsorptionCoreL : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .mul (.const 4)
    (.add
      (.add
        (.mul (.const 45560) (.pow D 2))
        (.mul (.const 30848) (.pow N 4)))
      (.neg (.mul (.const 10976) (.mul (.pow N 2) D))))

private def pAbsorptionCoreR : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  let X : PE := .add (.mul (.const 2) (.pow N 2)) (.neg D)
  .add
    (.add
      (.mul (.const 10976) (.mul X X))
      (.mul (.const 79488) (.pow N 4)))
    (.mul (.const 171264) (.pow D 2))

private theorem pAbsorptionCore_normal :
    RingNormaliser.normalize pAbsorptionCoreL =
      RingNormaliser.normalize pAbsorptionCoreR := by decide

private theorem absorptionCore_algebra (D N : Q') :
    Q'.ofNat 4 *
        ((Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
          Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
          -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))) ≈
      (Q'.ofNat 10976 *
          ((Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D) *
            (Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D)) +
        Q'.ofNat 79488 * RingNormaliser.qpow N 4) +
        Q'.ofNat 171264 * RingNormaliser.qpow D 2 := by
  simpa only [pAbsorptionCoreL, pAbsorptionCoreR,
    RingNormaliser.eval,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 10976 = Q'.ofNat 10976 from rfl,
    show Q'.ofInt 30848 = Q'.ofNat 30848 from rfl,
    show Q'.ofInt 45560 = Q'.ofNat 45560 from rfl,
    show Q'.ofInt 79488 = Q'.ofNat 79488 from rfl,
    show Q'.ofInt 171264 = Q'.ofNat 171264 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      pAbsorptionCoreL pAbsorptionCoreR pAbsorptionCore_normal
      (fun | 0 => D | _ => N))

private theorem absorptionCore_nonnegative
    {D N : Q'} (hD : (0 : Q') ≤ D) (hN : (0 : Q') ≤ N) :
    (0 : Q') ≤
      (Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
        Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
        -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D)) := by
  let X := Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D
  let B :=
    (Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
      Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
      -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))
  have hD2 : (0 : Q') ≤ RingNormaliser.qpow D 2 :=
    ringQpow_nonnegative hD 2
  have hN4 : (0 : Q') ≤ RingNormaliser.qpow N 4 :=
    ringQpow_nonnegative hN 4
  have hX2 : (0 : Q') ≤ X * X :=
    SumOfSquares.q_mul_self_nonneg X
  have hcert : (0 : Q') ≤
      (Q'.ofNat 10976 * (X * X) +
        Q'.ofNat 79488 * RingNormaliser.qpow N 4) +
        Q'.ofNat 171264 * RingNormaliser.qpow D 2 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hX2)
        (Q'.mul_nonneg _ _ (by decide) hN4))
      (Q'.mul_nonneg _ _ (by decide) hD2)
  have hscaled : (0 : Q') ≤ Q'.ofNat 4 * B := by
    dsimp only [X, B] at hcert ⊢
    exact Q'.le_trans' _ _ _ hcert
      (Q'.le_of_eqv (Q'.eqv_symm (absorptionCore_algebra D N)))
  have hzero : Q'.ofNat 4 * (0 : Q') ≤ Q'.ofNat 4 * B :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 4))) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

private def pAbsorptionL : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .add
    (.add
      (.mul (.const 45560) (.mul (.pow N 3) (.pow D 3)))
      (.mul (.const 30848) (.mul (.pow N 7) D)))
    (.neg (.mul (.const 10976) (.mul (.pow N 5) (.pow D 2))))

private def pAbsorptionR : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .mul (.mul (.pow N 3) D)
    (.add
      (.add
        (.mul (.const 45560) (.pow D 2))
        (.mul (.const 30848) (.pow N 4)))
      (.neg (.mul (.const 10976) (.mul (.pow N 2) D))))

private theorem pAbsorption_normal :
    RingNormaliser.normalize pAbsorptionL =
      RingNormaliser.normalize pAbsorptionR := by decide

private theorem absorption_algebra (D N : Q') :
    (Q'.ofNat 45560 *
          (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3) +
        Q'.ofNat 30848 * (RingNormaliser.qpow N 7 * D)) +
        -(Q'.ofNat 10976 *
          (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2)) ≈
      (RingNormaliser.qpow N 3 * D) *
        ((Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
          Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
          -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))) := by
  simpa only [pAbsorptionL, pAbsorptionR, RingNormaliser.eval,
    show Q'.ofInt 10976 = Q'.ofNat 10976 from rfl,
    show Q'.ofInt 30848 = Q'.ofNat 30848 from rfl,
    show Q'.ofInt 45560 = Q'.ofNat 45560 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      pAbsorptionL pAbsorptionR pAbsorption_normal
      (fun | 0 => D | _ => N))

/-- The second Hermite flux is nonpositive on the nonnegative quadrant. -/
theorem lowerSixHermiteSecondFluxPoly_nonpositive
    {D N : Q'} (hD : (0 : Q') ≤ D) (hN : (0 : Q') ≤ N) :
    lowerSixHermiteSecondFluxPoly D N ≤ (0 : Q') := by
  let A :=
    (Q'.ofNat 45560 *
          (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3) +
        Q'.ofNat 30848 * (RingNormaliser.qpow N 7 * D)) +
        -(Q'.ofNat 10976 *
          (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2))
  have hfactor : (0 : Q') ≤ RingNormaliser.qpow N 3 * D :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hN 3) hD
  have hcore := absorptionCore_nonnegative hD hN
  have hA : (0 : Q') ≤ A := by
    dsimp only [A]
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hfactor hcore)
      (Q'.le_of_eqv (Q'.eqv_symm (absorption_algebra D N)))
  have hfirst : (0 : Q') ≤
      Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 := by
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hN)
      (ringQpow_nonnegative hD 4)
  have hlast : (0 : Q') ≤
      Q'.ofNat 4608 * RingNormaliser.qpow N 9 :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hN 9)
  have hsum : (0 : Q') ≤
      (Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 + A) +
        Q'.ofNat 4608 * RingNormaliser.qpow N 9 := by
    exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hfirst hA) hlast
  have hid : lowerSixHermiteSecondFluxPoly D N ≈
      -((Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 + A) +
        Q'.ofNat 4608 * RingNormaliser.qpow N 9) := by
    unfold lowerSixHermiteSecondFluxPoly
    dsimp only [A]
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.nonpos_neg_of_nonneg hsum)

def lowerSixHermiteSecondFluxNumerator (k n : Nat) : Q' :=
  lowerSixModeWeight k n *
    lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2)) (Q'.ofNat n)

theorem lowerSixHermiteSecondFluxNumerator_nonpositive (k n : Nat) :
    lowerSixHermiteSecondFluxNumerator k n ≤ (0 : Q') := by
  have hW : (0 : Q') ≤ lowerSixModeWeight k n := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hK := lowerSixHermiteSecondFluxPoly_nonpositive
    (D := Q'.ofNat (k + 2)) (N := Q'.ofNat n)
    (HeatKernelRGStep.zero_le_ofNat _)
    (HeatKernelRGStep.zero_le_ofNat _)
  unfold lowerSixHermiteSecondFluxNumerator
  exact Q'.mul_nonpos_of_nonneg_nonpos hW hK

#print axioms lowerSixHermiteSecondFluxPoly_nonpositive
#print axioms lowerSixHermiteSecondFluxNumerator_nonpositive

end YMGap.Continuum.HarmonicLowerSixSecondFluxSign
