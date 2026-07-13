/-
Composition of the even/odd endpoint certificates with the exact raw
endpoints and the antiderivative telescope.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddShift

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointSubstitution
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointEvenShift
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddSubstitution
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddShift

local infix:50 " ≈ " => Q'.eqv

/-- The even raw endpoint is nonnegative throughout its square-root band. -/
theorem thetaCubicEvenRawEndpoint_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 9) :
    (0 : Q') ≤ thetaCubicEvenRawEndpoint
      (Q'.ofNat 2 * ((M + 5) * (M + 5)) + r) (M + 5) := by
  have hsub := thetaCubicEvenRaw_centered (M + 5) r
  have hshift := thetaCubicEvenCentered_eq_certificate M r
  have hcert := thetaCubicEvenEndpointCertificate_nonnegative hM hr hrTop
  have htotal := Q'.eqv_trans _ _ _ hsub hshift
  exact Q'.le_trans' _ _ _ hcert (Q'.ge_of_eqv htotal)

/-- The odd raw endpoint is nonnegative throughout its square-root band. -/
theorem thetaCubicOddRawEndpoint_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 11) :
    (0 : Q') ≤ thetaCubicOddRawEndpoint
      (Q'.ofNat 2 * ((M + 5) * ((M + 5) + 1)) + r) (M + 5) := by
  have hsub := thetaCubicOddRaw_centered (M + 5) r
  have hshift := thetaCubicOddCentered_eq_certificate M r
  have hcert := thetaCubicOddEndpointCertificate_nonnegative hM hr hrTop
  have htotal := Q'.eqv_trans _ _ _ hsub hshift
  exact Q'.le_trans' _ _ _ hcert (Q'.ge_of_eqv htotal)

/-- Nonnegativity of the exact even primitive endpoint. -/
theorem thetaCubicEvenPrimitiveEndpoint_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 9) :
    let m := M + 5
    let D := Q'.ofNat 2 * (m * m) + r
    (0 : Q') ≤ thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 1) +
      -thetaCubicCellAntiderivative D m := by
  dsimp only
  have heq := thetaCubicEvenEndpoint_eq_raw
    (Q'.ofNat 2 * ((M + 5) * (M + 5)) + r) (M + 5)
  have hraw := thetaCubicEvenRawEndpoint_nonnegative hM hr hrTop
  exact Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv heq)

/-- Nonnegativity of the exact odd primitive endpoint. -/
theorem thetaCubicOddPrimitiveEndpoint_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 11) :
    let m := M + 5
    let D := Q'.ofNat 2 * (m * (m + 1)) + r
    (0 : Q') ≤ thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 2) +
      -thetaCubicCellAntiderivative D m := by
  dsimp only
  have heq := thetaCubicOddEndpoint_eq_raw
    (Q'.ofNat 2 * ((M + 5) * ((M + 5) + 1)) + r) (M + 5)
  have hraw := thetaCubicOddRawEndpoint_nonnegative hM hr hrTop
  exact Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv heq)

/-- Positive scaling can be cancelled from the telescoped cleared block. -/
theorem thetaCubicClearedBlock_nonnegative_of_endpoint
    {D X : Q'} {count : Nat}
    (hendpoint : (0 : Q') ≤
      thetaCubicCellAntiderivative D (X + Q'.ofNat count) +
        -thetaCubicCellAntiderivative D X) :
    (0 : Q') ≤ thetaCubicClearedBlock D X count := by
  have htel := thetaCubicClearedBlock_telescope D X count
  have hscaled : (0 : Q') ≤
      Q'.ofNat 210 * thetaCubicClearedBlock D X count :=
    Q'.le_trans' _ _ _ hendpoint (Q'.ge_of_eqv htel)
  have hzero : Q'.ofNat 210 * (0 : Q') ≤
      Q'.ofNat 210 * thetaCubicClearedBlock D X count :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _)) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b

private def pEvenTopL : PE :=
  padd (padd (.var 0) (pc 5)) (padd (.var 0) (pc 6))
private def pEvenTopR : PE :=
  padd (pmul (pc 2) (padd (.var 0) (pc 5))) (pc 1)
private def pOddTopL : PE :=
  padd (padd (.var 0) (pc 5)) (padd (.var 0) (pc 7))
private def pOddTopR : PE :=
  padd (pmul (pc 2) (padd (.var 0) (pc 5))) (pc 2)

private theorem pEvenTop_normal : RingNormaliser.normalize pEvenTopL =
    RingNormaliser.normalize pEvenTopR := by decide
private theorem pOddTop_normal : RingNormaliser.normalize pOddTopL =
    RingNormaliser.normalize pOddTopR := by decide

private theorem even_top_identity (M : Nat) :
    (Q'.ofNat M + 5) + Q'.ofNat (M + 6) ≈
      Q'.ofNat 2 * (Q'.ofNat M + 5) + 1 := by
  have hcount : Q'.ofNat (M + 6) ≈ Q'.ofNat M + Q'.ofNat 6 :=
    Q'.ofNat_add_eqv M 6
  have hreplace := Q'.add_eqv_congr_left (Q'.ofNat M + 5) _ _ hcount
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pEvenTopL pEvenTopR pEvenTop_normal (fun _ => Q'.ofNat M)
  refine Q'.eqv_trans _ _ _ hreplace ?_
  simpa [pEvenTopL, pEvenTopR, pc, padd, pmul,
    RingNormaliser.eval] using hpoly

private theorem odd_top_identity (M : Nat) :
    (Q'.ofNat M + 5) + Q'.ofNat (M + 7) ≈
      Q'.ofNat 2 * (Q'.ofNat M + 5) + 2 := by
  have hcount : Q'.ofNat (M + 7) ≈ Q'.ofNat M + Q'.ofNat 7 :=
    Q'.ofNat_add_eqv M 7
  have hreplace := Q'.add_eqv_congr_left (Q'.ofNat M + 5) _ _ hcount
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pOddTopL pOddTopR pOddTop_normal (fun _ => Q'.ofNat M)
  refine Q'.eqv_trans _ _ _ hreplace ?_
  simpa [pOddTopL, pOddTopR, pc, padd, pmul,
    RingNormaliser.eval] using hpoly

/-- The entire cleared even-center window block is nonnegative. -/
theorem thetaCubicEvenClearedBlock_nonnegative {M : Nat} {r : Q'}
    (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * Q'.ofNat M + 9) :
    let m := Q'.ofNat M + 5
    let D := Q'.ofNat 2 * (m * m) + r
    (0 : Q') ≤ thetaCubicClearedBlock D m (M + 6) := by
  dsimp only
  have hM : (0 : Q') ≤ Q'.ofNat M :=
    YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat M
  have hend := thetaCubicEvenPrimitiveEndpoint_nonnegative hM hr hrTop
  have htop := thetaCubicCellAntiderivative_eqv_congr
    (Q'.eqv_refl (Q'.ofNat 2 *
      ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) + r))
    (even_top_identity M)
  have hconverted : (0 : Q') ≤
      thetaCubicCellAntiderivative
          (Q'.ofNat 2 * ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) + r)
          ((Q'.ofNat M + 5) + Q'.ofNat (M + 6)) +
        -thetaCubicCellAntiderivative
          (Q'.ofNat 2 * ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) + r)
          (Q'.ofNat M + 5) := by
    exact Q'.le_trans' _ _ _ hend
      (Q'.ge_of_eqv
        (Q'.add_eqv_congr_right _ _ _ htop))
  exact thetaCubicClearedBlock_nonnegative_of_endpoint hconverted

/-- The entire cleared odd-center window block is nonnegative. -/
theorem thetaCubicOddClearedBlock_nonnegative {M : Nat} {r : Q'}
    (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * Q'.ofNat M + 11) :
    let m := Q'.ofNat M + 5
    let D := Q'.ofNat 2 * (m * (m + 1)) + r
    (0 : Q') ≤ thetaCubicClearedBlock D m (M + 7) := by
  dsimp only
  have hM : (0 : Q') ≤ Q'.ofNat M :=
    YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat M
  have hend := thetaCubicOddPrimitiveEndpoint_nonnegative hM hr hrTop
  have htop := thetaCubicCellAntiderivative_eqv_congr
    (Q'.eqv_refl (Q'.ofNat 2 *
      ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) + r))
    (odd_top_identity M)
  have hconverted : (0 : Q') ≤
      thetaCubicCellAntiderivative
          (Q'.ofNat 2 *
            ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) + r)
          ((Q'.ofNat M + 5) + Q'.ofNat (M + 7)) +
        -thetaCubicCellAntiderivative
          (Q'.ofNat 2 *
            ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) + r)
          (Q'.ofNat M + 5) := by
    exact Q'.le_trans' _ _ _ hend
      (Q'.ge_of_eqv
        (Q'.add_eqv_congr_right _ _ _ htop))
  exact thetaCubicClearedBlock_nonnegative_of_endpoint hconverted

#print axioms thetaCubicEvenRawEndpoint_nonnegative
#print axioms thetaCubicOddRawEndpoint_nonnegative
#print axioms thetaCubicEvenPrimitiveEndpoint_nonnegative
#print axioms thetaCubicOddPrimitiveEndpoint_nonnegative
#print axioms thetaCubicClearedBlock_nonnegative_of_endpoint
#print axioms thetaCubicEvenClearedBlock_nonnegative
#print axioms thetaCubicOddClearedBlock_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointClosure
