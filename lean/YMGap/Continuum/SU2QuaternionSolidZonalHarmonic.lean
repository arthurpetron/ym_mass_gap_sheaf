/-
# Selected-head harmonicity of every solid SU(2) zonal character

The finite quaternion computations are split by orientation and then consumed
by one orientation-independent Euler--Laplacian recurrence.  Polynomial
equality is coefficient-sensitive, so every unintegrated BF4 coordinate is
retained throughout.
-/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonic

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111

local infix:50 " ≈ " => Q'.eqv

/-- All 16 plaquette orientations share the two finite differential
certificates. -/
theorem exposedDifferentialCertificate
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    ExposedDifferentialCertificate reverse0 reverse1 reverse2 reverse3 := by
  cases reverse0 <;> cases reverse1 <;>
    cases reverse2 <;> cases reverse3
  · exact certificate0000
  · exact certificate0001
  · exact certificate0010
  · exact certificate0011
  · exact certificate0100
  · exact certificate0101
  · exact certificate0110
  · exact certificate0111
  · exact certificate1000
  · exact certificate1001
  · exact certificate1010
  · exact certificate1011
  · exact certificate1100
  · exact certificate1101
  · exact certificate1110
  · exact certificate1111

theorem laplacian_exposedScalar_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
      polyZero :=
  (exposedDifferentialCertificate
    reverse0 reverse1 reverse2 reverse3).laplacianScalar

theorem gradient_exposedScalar_self
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
      retainedThreeRadiusProduct :=
  (exposedDifferentialCertificate
    reverse0 reverse1 reverse2 reverse3).gradientSelf

theorem laplacian_fourRadius :
    RatPolyCoeffEqv
      (headLaplacian fourQuaternionRadiusProduct)
      (polySmul 8 retainedThreeRadiusProduct) :=
  SU2QuaternionSolidZonalHarmonicBase.laplacian_fourRadius

theorem gradient_exposedScalar_fourRadius
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        fourQuaternionRadiusProduct)
      (polySmul 2
        (polyMul retainedThreeRadiusProduct
          (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)) :=
  SU2QuaternionSolidZonalHarmonicBase.gradient_exposedScalar_fourRadius
    reverse0 reverse1 reverse2 reverse3

private theorem laplacian_twice_exposedScalar_mul
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (polynomial target : RatPoly)
    (hpolynomial : RatPolyCoeffEqv
      (headLaplacian polynomial) polyZero)
    (hdirectional : RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        polynomial)
      target) :
    RatPolyCoeffEqv
      (headLaplacian
        (polyMul
          (polySmul 2
            (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
          polynomial))
      (polySmul 4 target) := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  have hscalar : RatPolyCoeffEqv
      (headLaplacian (polySmul 2 scalar)) polyZero :=
    RatPolyCoeffEqv.trans
      (headLaplacian_smul 2 scalar)
      (RatPolyCoeffEqv.trans
        ((laplacian_exposedScalar_zero
          reverse0 reverse1 reverse2 reverse3).smul 2)
        (RatPolyCoeffEqv.smul_zero 2))
  have hfirst : RatPolyCoeffEqv
      (polyMul (headLaplacian (polySmul 2 scalar)) polynomial)
      polyZero :=
    RatPolyCoeffEqv.trans
      (hscalar.mul_right polynomial)
      (RatPolyCoeffEqv.mul_zero_left polynomial)
  have hinner : RatPolyCoeffEqv
      (headGradientDot (polySmul 2 scalar) polynomial)
      (polySmul 2 target) :=
    RatPolyCoeffEqv.trans
      (headGradientDot_smul_left 2 scalar polynomial)
      (hdirectional.smul 2)
  have hcross : RatPolyCoeffEqv
      (polySmul 2
        (headGradientDot (polySmul 2 scalar) polynomial))
      (polySmul 4 target) :=
    RatPolyCoeffEqv.trans (hinner.smul 2)
      (twice_twice_smul target)
  have hthird : RatPolyCoeffEqv
      (polyMul (polySmul 2 scalar) (headLaplacian polynomial))
      polyZero :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left (polySmul 2 scalar) hpolynomial)
      (RatPolyCoeffEqv.mul_zero_right (polySmul 2 scalar))
  have hparts := RatPolyCoeffEqv.add hfirst
    (RatPolyCoeffEqv.add hcross hthird)
  have hcollapse : RatPolyCoeffEqv
      (polyAdd polyZero
        (polyAdd (polySmul 4 target) polyZero))
      (polySmul 4 target) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.zero_add _)
      (RatPolyCoeffEqv.add_zero _)
  exact RatPolyCoeffEqv.trans
    (headLaplacian_mul (polySmul 2 scalar) polynomial)
    (RatPolyCoeffEqv.trans hparts hcollapse)

private theorem laplacian_fourRadius_mul
    (degree : Nat) (polynomial : RatPoly)
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial)
    (hpolynomial : RatPolyCoeffEqv
      (headLaplacian polynomial) polyZero) :
    RatPolyCoeffEqv
      (headLaplacian
        (polyMul fourQuaternionRadiusProduct polynomial))
      (polySmul (4 * Q'.ofNat (degree + 2))
        (polyMul retainedThreeRadiusProduct polynomial)) := by
  let common := polyMul retainedThreeRadiusProduct polynomial
  have hfirst : RatPolyCoeffEqv
      (polyMul (headLaplacian fourQuaternionRadiusProduct) polynomial)
      (polySmul 8 common) :=
    RatPolyCoeffEqv.trans
      (laplacian_fourRadius.mul_right polynomial)
      (RatPolyCoeffEqv.polyMul_smul_left
        8 retainedThreeRadiusProduct polynomial)
  have hgradient : RatPolyCoeffEqv
      (headGradientDot fourQuaternionRadiusProduct polynomial)
      (polySmul (2 * Q'.ofNat degree) common) :=
    RatPolyCoeffEqv.trans
      (headGradientDot_comm fourQuaternionRadiusProduct polynomial)
      (headGradientDot_fourRadius_of_blockDegree
        degree polynomial hdegree)
  have hcross : RatPolyCoeffEqv
      (polySmul 2
        (headGradientDot fourQuaternionRadiusProduct polynomial))
      (polySmul (4 * Q'.ofNat degree) common) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.trans
        (hgradient.smul 2)
        (RatPolyCoeffEqv.smul_assoc
          2 (2 * Q'.ofNat degree) common))
      (RatPolyCoeffEqv.smul_coefficient
        (two_mul_two_mul_eqv (Q'.ofNat degree)) common)
  have hthird : RatPolyCoeffEqv
      (polyMul fourQuaternionRadiusProduct
        (headLaplacian polynomial))
      polyZero :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left
        fourQuaternionRadiusProduct hpolynomial)
      (RatPolyCoeffEqv.mul_zero_right fourQuaternionRadiusProduct)
  have hparts := RatPolyCoeffEqv.add hfirst
    (RatPolyCoeffEqv.add hcross hthird)
  have hcombine : RatPolyCoeffEqv
      (polyAdd (polySmul 8 common)
        (polyAdd (polySmul (4 * Q'.ofNat degree) common) polyZero))
      (polySmul (4 * Q'.ofNat (degree + 2)) common) := by
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (RatPolyCoeffEqv.add_zero _)) ?_
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add_smul_same
        8 (4 * Q'.ofNat degree) common) ?_
    exact RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (four_mul_ofNat_add_two_eqv degree)) common
  exact RatPolyCoeffEqv.trans
    (headLaplacian_mul fourQuaternionRadiusProduct polynomial)
    (RatPolyCoeffEqv.trans hparts hcombine)

private theorem directional_twice_exposedScalar_mul
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (polynomial target : RatPoly)
    (hdirectional : RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        polynomial)
      target) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        (polyMul
          (polySmul 2
            (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
          polynomial))
      (polyAdd
        (polySmul 2
          (polyMul retainedThreeRadiusProduct polynomial))
        (polySmul 2
          (polyMul
            (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
            target))) := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  have hfirst : RatPolyCoeffEqv
      (polyMul (headGradientDot scalar (polySmul 2 scalar)) polynomial)
      (polySmul 2
        (polyMul retainedThreeRadiusProduct polynomial)) :=
    RatPolyCoeffEqv.trans
      ((RatPolyCoeffEqv.trans
        (headGradientDot_smul_right 2 scalar scalar)
        ((gradient_exposedScalar_self
          reverse0 reverse1 reverse2 reverse3).smul 2)).mul_right
            polynomial)
      (RatPolyCoeffEqv.polyMul_smul_left
        2 retainedThreeRadiusProduct polynomial)
  have hsecond : RatPolyCoeffEqv
      (polyMul (polySmul 2 scalar)
        (headGradientDot scalar polynomial))
      (polySmul 2 (polyMul scalar target)) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul
        (RatPolyCoeffEqv.refl (polySmul 2 scalar)) hdirectional)
      (RatPolyCoeffEqv.polyMul_smul_left 2 scalar target)
  exact RatPolyCoeffEqv.trans
    (headGradientDot_mul_right scalar (polySmul 2 scalar) polynomial)
    (RatPolyCoeffEqv.add hfirst hsecond)

private theorem directional_fourRadius_mul
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (polynomial target : RatPoly)
    (hdirectional : RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        polynomial)
      target) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        (polyMul fourQuaternionRadiusProduct polynomial))
      (polyAdd
        (polySmul 2
          (polyMul
            (polyMul retainedThreeRadiusProduct
              (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
            polynomial))
        (polyMul fourQuaternionRadiusProduct target)) := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  have hfirst : RatPolyCoeffEqv
      (polyMul (headGradientDot scalar fourQuaternionRadiusProduct)
        polynomial)
      (polySmul 2
        (polyMul
          (polyMul retainedThreeRadiusProduct scalar) polynomial)) :=
    RatPolyCoeffEqv.trans
      ((gradient_exposedScalar_fourRadius
        reverse0 reverse1 reverse2 reverse3).mul_right polynomial)
      (RatPolyCoeffEqv.polyMul_smul_left
        2 (polyMul retainedThreeRadiusProduct scalar) polynomial)
  have hsecond : RatPolyCoeffEqv
      (polyMul fourQuaternionRadiusProduct
        (headGradientDot scalar polynomial))
      (polyMul fourQuaternionRadiusProduct target) :=
    RatPolyCoeffEqv.mul_left fourQuaternionRadiusProduct hdirectional
  exact RatPolyCoeffEqv.trans
    (headGradientDot_mul_right
      scalar fourQuaternionRadiusProduct polynomial)
    (RatPolyCoeffEqv.add hfirst hsecond)

/-- The preceding solid zonal mode, with a constructive zero at spin zero. -/
def exposedPreviousZonal
    (reverse0 reverse1 reverse2 reverse3 : Bool) : Nat → RatPoly
  | 0 => polyZero
  | spin + 1 =>
      exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 spin

/-- Closed directional target, valid uniformly even at spin zero because the
preceding mode is defined there to be zero. -/
def exposedDirectionalTarget
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) : RatPoly :=
  polySmul (Q'.ofNat (spin + 1))
    (polyMul retainedThreeRadiusProduct
      (exposedPreviousZonal
        reverse0 reverse1 reverse2 reverse3 spin))

private theorem exposedZonal_next_recurrence
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    RatPolyCoeffEqv
      (exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 (spin + 1))
      (polyAdd
        (polyMul
          (polySmul 2
            (exposedFourWord
              reverse0 reverse1 reverse2 reverse3).scalar)
          (exposedSolidZonalCharacter
            reverse0 reverse1 reverse2 reverse3 spin))
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct
            (exposedPreviousZonal
              reverse0 reverse1 reverse2 reverse3 spin)))) := by
  cases spin with
  | zero =>
      apply RatPolyCoeffEqv.of_canon_termwise
      cases reverse0 <;> cases reverse1 <;>
        cases reverse2 <;> cases reverse3 <;> decide
  | succ spin =>
      exact RatPolyCoeffEqv.refl _

private theorem minus_one_mul_eqv_neg (value : Q') :
    (-1 : Q') * value ≈ -value :=
  Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv 1 value)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv value))

private theorem directional_scalar_rearrange
    (coefficient x y w : Q') :
    (2 * x + (2 * (coefficient + 1)) * y) +
        (-1) * (2 * y + coefficient * w) ≈
      2 * x + coefficient * (2 * y + (-1) * w) := by
  let A := 2 * x
  let B := (2 * coefficient) * y
  let C := 2 * y
  let D := coefficient * w
  have hcoefficient :
      (2 * (coefficient + 1)) * y ≈ B + C := by
    refine Q'.eqv_trans _
      ((2 * coefficient + 2 * 1) * y) _
      (Q'.mul_eqv_congr_right _ _ y
        (Q'.mul_add_eqv 2 coefficient 1)) ?_
    refine Q'.eqv_trans _
      ((2 * coefficient) * y + (2 * 1) * y) _
      (Q'.add_mul_eqv (2 * coefficient) (2 * 1) y) ?_
    exact Q'.add_eqv_congr_left B _ C
      (Q'.mul_eqv_congr_right (2 * 1) 2 y
        (Q'.mul_one_eqv 2))
  have hnegative :
      (-1) * (C + D) ≈ (-C) + (-D) :=
    Q'.eqv_trans _ _ _
      (minus_one_mul_eqv_neg (C + D))
      (Q'.neg_add_eqv C D)
  refine Q'.eqv_trans _
    ((A + (B + C)) + ((-C) + (-D))) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left A _ _ hcoefficient)
      hnegative) ?_
  refine Q'.eqv_trans _
    (((A + B) + C) + ((-C) + (-D))) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv A B C))) ?_
  refine Q'.eqv_trans _
    ((A + B) + (C + ((-C) + (-D)))) _
    (Q'.add_assoc_eqv (A + B) C ((-C) + (-D))) ?_
  refine Q'.eqv_trans _
    ((A + B) + ((C + (-C)) + (-D))) _
    (Q'.add_eqv_congr_left (A + B) _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv C (-C) (-D)))) ?_
  refine Q'.eqv_trans _
    ((A + B) + (0 + (-D))) _
    (Q'.add_eqv_congr_left (A + B) _ _
      (Q'.add_eqv_congr_right _ _ (-D)
        (Q'.add_neg_self_eqv C))) ?_
  refine Q'.eqv_trans _
    ((A + B) + (-D)) _
    (Q'.add_eqv_congr_left (A + B) _ _
      (QPoly.q_zero_add_eqv (-D))) ?_
  refine Q'.eqv_trans _
    (A + (B + (-D))) _
    (Q'.add_assoc_eqv A B (-D)) ?_
  have hleftTarget : coefficient * (2 * y) ≈ B := by
    refine Q'.eqv_trans _
      ((coefficient * 2) * y) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv coefficient 2 y)) ?_
    exact Q'.mul_eqv_congr_right
      (coefficient * 2) (2 * coefficient) y
      (Q'.mul_comm_eqv coefficient 2)
  have hrightTarget :
      coefficient * ((-1) * w) ≈ -D := by
    refine Q'.eqv_trans _
      (coefficient * (-w)) _
      (Q'.mul_eqv_congr_left coefficient _ _
        (minus_one_mul_eqv_neg w)) ?_
    exact Q'.mul_neg_eqv coefficient w
  have htarget :
      coefficient * (2 * y + (-1) * w) ≈ B + (-D) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv coefficient (2 * y) ((-1) * w))
      (Q'.add_eqv_congr' hleftTarget hrightTarget)
  exact Q'.add_eqv_congr_left A _ _ (Q'.eqv_symm htarget)

private theorem two_plus_coefficient_mul
    (coefficient x : Q') :
    2 * x + coefficient * x ≈ (coefficient + 2) * x :=
  Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (2 * x) (coefficient * x))
    (Q'.eqv_symm (Q'.add_mul_eqv coefficient 2 x))

/-- Pure coefficient-quotient algebra behind the directional recurrence. -/
private theorem directional_recombine
    (coefficient : Q') (X Y W : RatPoly)
    (hrecurrence : RatPolyCoeffEqv X
      (polyAdd (polySmul 2 Y) (polySmul (-1) W))) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd
          (polySmul 2 X)
          (polySmul (2 * (coefficient + 1)) Y))
        (polySmul (-1)
          (polyAdd
            (polySmul 2 Y)
            (polySmul coefficient W))))
      (polySmul (coefficient + 2) X) := by
  intro weight
  let x := ratWeightedSum weight X
  let y := ratWeightedSum weight Y
  let w := ratWeightedSum weight W
  have hxyw : x ≈ 2 * y + (-1) * w := by
    refine Q'.eqv_trans _
      (ratWeightedSum weight
        (polyAdd (polySmul 2 Y) (polySmul (-1) W))) _
      (hrecurrence weight) ?_
    refine Q'.eqv_trans _
      (ratWeightedSum weight (polySmul 2 Y) +
        ratWeightedSum weight (polySmul (-1) W)) _
      (ratWeightedSum_add weight _ _) ?_
    exact Q'.add_eqv_congr'
      (ratWeightedSum_smul weight 2 Y)
      (ratWeightedSum_smul weight (-1) W)
  have hfirst :
      ratWeightedSum weight
          (polyAdd (polySmul 2 X)
            (polySmul (2 * (coefficient + 1)) Y)) ≈
        2 * x + (2 * (coefficient + 1)) * y :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_smul weight 2 X)
        (ratWeightedSum_smul weight
          (2 * (coefficient + 1)) Y))
  have hinner :
      ratWeightedSum weight
          (polyAdd (polySmul 2 Y)
            (polySmul coefficient W)) ≈
        2 * y + coefficient * w :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_smul weight 2 Y)
        (ratWeightedSum_smul weight coefficient W))
  have hnegative :
      ratWeightedSum weight
          (polySmul (-1)
            (polyAdd (polySmul 2 Y)
              (polySmul coefficient W))) ≈
        (-1) * (2 * y + coefficient * w) :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_smul weight (-1) _)
      (Q'.mul_eqv_congr_left (-1) _ _ hinner)
  refine Q'.eqv_trans _
    ((2 * x + (2 * (coefficient + 1)) * y) +
      (-1) * (2 * y + coefficient * w)) _
    (Q'.eqv_trans _ _ _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr' hfirst hnegative)) ?_
  refine Q'.eqv_trans _
    (2 * x + coefficient * (2 * y + (-1) * w)) _ ?_ ?_
  · exact directional_scalar_rearrange coefficient x y w
  refine Q'.eqv_trans _
    (2 * x + coefficient * x) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left coefficient _ _
        (Q'.eqv_symm hxyw))) ?_
  refine Q'.eqv_trans _
    ((coefficient + 2) * x) _ ?_ ?_
  · exact two_plus_coefficient_mul coefficient x
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight (coefficient + 2) X)

private theorem polyMul_swap_first_two
    (first second third : RatPoly) :
    RatPolyCoeffEqv
      (polyMul first (polyMul second third))
      (polyMul second (polyMul first third)) :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.mul_assoc first second third))
    (RatPolyCoeffEqv.trans
      ((RatPolyCoeffEqv.mul_comm first second).mul_right third)
      (RatPolyCoeffEqv.mul_assoc second first third))

structure ExposedZonalDifferentialAt
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (spin : Nat) : Prop where
  harmonic : RatPolyCoeffEqv
    (headLaplacian
      (exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 spin))
    polyZero
  directional : RatPolyCoeffEqv
    (headGradientDot
      (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
      (exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 spin))
    (exposedDirectionalTarget
      reverse0 reverse1 reverse2 reverse3 spin)

private theorem exposedZonalDifferential_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 0 := by
  constructor
  · cases reverse0 <;> cases reverse1 <;>
      cases reverse2 <;> cases reverse3 <;>
      apply RatPolyCoeffEqv.of_canon_termwise <;> decide
  · cases reverse0 <;> cases reverse1 <;>
      cases reverse2 <;> cases reverse3 <;>
      apply RatPolyCoeffEqv.of_canon_termwise <;> decide

private theorem exposedZonalDifferential_one
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 1 := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  constructor
  · change RatPolyCoeffEqv
      (headLaplacian (polySmul 2 scalar)) polyZero
    exact RatPolyCoeffEqv.trans
      (headLaplacian_smul 2 scalar)
      (RatPolyCoeffEqv.trans
        ((laplacian_exposedScalar_zero
          reverse0 reverse1 reverse2 reverse3).smul 2)
        (RatPolyCoeffEqv.smul_zero 2))
  · change RatPolyCoeffEqv
      (headGradientDot scalar (polySmul 2 scalar))
      (polySmul 2
        (polyMul retainedThreeRadiusProduct polyOne))
    refine RatPolyCoeffEqv.trans
      (headGradientDot_smul_right 2 scalar scalar) ?_
    refine RatPolyCoeffEqv.trans
      ((gradient_exposedScalar_self
        reverse0 reverse1 reverse2 reverse3).smul 2) ?_
    apply RatPolyCoeffEqv.of_canon_termwise
    decide

private theorem exposedZonalHarmonic_step
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat)
    (hspin : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 spin)
    (hnext : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 (spin + 1)) :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 (spin + 2)))
      polyZero := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  let current := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 spin
  let next := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 (spin + 1)
  let common := polyMul retainedThreeRadiusProduct current
  let cancellation := polySmul (4 * Q'.ofNat (spin + 2)) common
  have hleftRaw := laplacian_twice_exposedScalar_mul
    reverse0 reverse1 reverse2 reverse3 next
      (exposedDirectionalTarget
        reverse0 reverse1 reverse2 reverse3 (spin + 1))
      hnext.harmonic hnext.directional
  have hleft : RatPolyCoeffEqv
      (headLaplacian (polyMul (polySmul 2 scalar) next))
      cancellation := by
    refine RatPolyCoeffEqv.trans hleftRaw ?_
    change RatPolyCoeffEqv
      (polySmul 4
        (polySmul (Q'.ofNat (spin + 2)) common))
      cancellation
    exact RatPolyCoeffEqv.smul_assoc
      4 (Q'.ofNat (spin + 2)) common
  have hright : RatPolyCoeffEqv
      (headLaplacian
        (polyMul fourQuaternionRadiusProduct current))
      cancellation := by
    exact laplacian_fourRadius_mul spin current
      (exposedSolidZonalCharacter_blockDegree
        reverse0 reverse1 reverse2 reverse3 0 (by omega) spin)
      hspin.harmonic
  have hnegative : RatPolyCoeffEqv
      (headLaplacian
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct current)))
      (polySmul (-1) cancellation) :=
    RatPolyCoeffEqv.trans
      (headLaplacian_smul (-1)
        (polyMul fourQuaternionRadiusProduct current))
      (hright.smul (-1))
  change RatPolyCoeffEqv
    (headLaplacian
      (polyAdd
        (polyMul (polySmul 2 scalar) next)
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct current))))
    polyZero
  exact RatPolyCoeffEqv.trans
    (headLaplacian_add
      (polyMul (polySmul 2 scalar) next)
      (polySmul (-1)
        (polyMul fourQuaternionRadiusProduct current)))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add hleft hnegative)
      (RatPolyCoeffEqv.add_neg_smul cancellation))

private theorem exposedZonalDirectional_step
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat)
    (hspin : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 spin)
    (hnext : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 (spin + 1)) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 (spin + 2)))
      (exposedDirectionalTarget
        reverse0 reverse1 reverse2 reverse3 (spin + 2)) := by
  let scalar :=
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  let previous := exposedPreviousZonal
    reverse0 reverse1 reverse2 reverse3 spin
  let current := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 spin
  let next := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 (spin + 1)
  let coefficient := Q'.ofNat (spin + 1)
  let X := polyMul retainedThreeRadiusProduct next
  let Y := polyMul retainedThreeRadiusProduct
    (polyMul scalar current)
  let W := polyMul retainedThreeRadiusProduct
    (polyMul fourQuaternionRadiusProduct previous)
  have hcoefficient :
      Q'.ofNat (spin + 2) ≈ coefficient + 1 := by
    have hnat : spin + 2 = (spin + 1) + 1 := by omega
    rw [hnat]
    exact Q'.ofNat_add_eqv (spin + 1) 1
  have hfinalCoefficient :
      coefficient + 2 ≈ Q'.ofNat (spin + 3) :=
    Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv coefficient 2)
      (two_add_ofNat_succ_eqv spin)
  have hrecurrence : RatPolyCoeffEqv X
      (polyAdd (polySmul 2 Y) (polySmul (-1) W)) := by
    let first := polyMul (polySmul 2 scalar) current
    let second := polySmul (-1)
      (polyMul fourQuaternionRadiusProduct previous)
    have hraw := RatPolyCoeffEqv.mul_left retainedThreeRadiusProduct
      (exposedZonal_next_recurrence
        reverse0 reverse1 reverse2 reverse3 spin)
    have hfirst : RatPolyCoeffEqv
        (polyMul retainedThreeRadiusProduct first)
        (polySmul 2 Y) :=
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_left retainedThreeRadiusProduct
          (RatPolyCoeffEqv.polyMul_smul_left 2 scalar current))
        (RatPolyCoeffEqv.polyMul_smul_right 2
          retainedThreeRadiusProduct (polyMul scalar current))
    have hsecond : RatPolyCoeffEqv
        (polyMul retainedThreeRadiusProduct second)
        (polySmul (-1) W) :=
      RatPolyCoeffEqv.polyMul_smul_right (-1)
        retainedThreeRadiusProduct
        (polyMul fourQuaternionRadiusProduct previous)
    exact RatPolyCoeffEqv.trans hraw
      (RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_add_right
          retainedThreeRadiusProduct first second)
        (RatPolyCoeffEqv.add hfirst hsecond))
  have hleftRaw := directional_twice_exposedScalar_mul
    reverse0 reverse1 reverse2 reverse3 next
      (exposedDirectionalTarget
        reverse0 reverse1 reverse2 reverse3 (spin + 1))
      hnext.directional
  have hleftSecond : RatPolyCoeffEqv
      (polySmul 2
        (polyMul scalar
          (exposedDirectionalTarget
            reverse0 reverse1 reverse2 reverse3 (spin + 1))))
      (polySmul (2 * (coefficient + 1)) Y) := by
    change RatPolyCoeffEqv
      (polySmul 2
        (polyMul scalar
          (polySmul (Q'.ofNat (spin + 2))
            (polyMul retainedThreeRadiusProduct current))))
      (polySmul (2 * (coefficient + 1)) Y)
    refine RatPolyCoeffEqv.trans
      ((RatPolyCoeffEqv.polyMul_smul_right
        (Q'.ofNat (spin + 2)) scalar
        (polyMul retainedThreeRadiusProduct current)).smul 2) ?_
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.smul_assoc 2
        (Q'.ofNat (spin + 2))
        (polyMul scalar
          (polyMul retainedThreeRadiusProduct current))) ?_
    refine RatPolyCoeffEqv.trans
      ((polyMul_swap_first_two scalar
        retainedThreeRadiusProduct current).smul
          (2 * Q'.ofNat (spin + 2))) ?_
    exact RatPolyCoeffEqv.smul_coefficient
      (Q'.mul_eqv_congr_left 2 _ _ hcoefficient) Y
  have hleft : RatPolyCoeffEqv
      (headGradientDot scalar
        (polyMul (polySmul 2 scalar) next))
      (polyAdd
        (polySmul 2 X)
        (polySmul (2 * (coefficient + 1)) Y)) :=
    RatPolyCoeffEqv.trans hleftRaw
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) hleftSecond)
  have hrightRaw := directional_fourRadius_mul
    reverse0 reverse1 reverse2 reverse3 current
      (exposedDirectionalTarget
        reverse0 reverse1 reverse2 reverse3 spin)
      hspin.directional
  have hrightFirst : RatPolyCoeffEqv
      (polySmul 2
        (polyMul
          (polyMul retainedThreeRadiusProduct scalar) current))
      (polySmul 2 Y) :=
    (RatPolyCoeffEqv.mul_assoc
      retainedThreeRadiusProduct scalar current).smul 2
  have hrightSecond : RatPolyCoeffEqv
      (polyMul fourQuaternionRadiusProduct
        (exposedDirectionalTarget
          reverse0 reverse1 reverse2 reverse3 spin))
      (polySmul coefficient W) := by
    change RatPolyCoeffEqv
      (polyMul fourQuaternionRadiusProduct
        (polySmul coefficient
          (polyMul retainedThreeRadiusProduct previous)))
      (polySmul coefficient W)
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.polyMul_smul_right coefficient
        fourQuaternionRadiusProduct
        (polyMul retainedThreeRadiusProduct previous)) ?_
    exact (polyMul_swap_first_two fourQuaternionRadiusProduct
      retainedThreeRadiusProduct previous).smul coefficient
  have hright : RatPolyCoeffEqv
      (headGradientDot scalar
        (polyMul fourQuaternionRadiusProduct current))
      (polyAdd
        (polySmul 2 Y)
        (polySmul coefficient W)) :=
    RatPolyCoeffEqv.trans hrightRaw
      (RatPolyCoeffEqv.add hrightFirst hrightSecond)
  have hnegative : RatPolyCoeffEqv
      (headGradientDot scalar
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct current)))
      (polySmul (-1)
        (polyAdd
          (polySmul 2 Y)
          (polySmul coefficient W))) :=
    RatPolyCoeffEqv.trans
      (headGradientDot_smul_right (-1) scalar
        (polyMul fourQuaternionRadiusProduct current))
      (hright.smul (-1))
  have hcombined : RatPolyCoeffEqv
      (headGradientDot scalar
        (polyAdd
          (polyMul (polySmul 2 scalar) next)
          (polySmul (-1)
            (polyMul fourQuaternionRadiusProduct current))))
      (polyAdd
        (polyAdd
          (polySmul 2 X)
          (polySmul (2 * (coefficient + 1)) Y))
        (polySmul (-1)
          (polyAdd
            (polySmul 2 Y)
            (polySmul coefficient W)))) :=
    RatPolyCoeffEqv.trans
      (headGradientDot_add_right scalar
        (polyMul (polySmul 2 scalar) next)
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct current)))
      (RatPolyCoeffEqv.add hleft hnegative)
  change RatPolyCoeffEqv
    (headGradientDot scalar
      (polyAdd
        (polyMul (polySmul 2 scalar) next)
        (polySmul (-1)
          (polyMul fourQuaternionRadiusProduct current))))
    (polySmul (Q'.ofNat (spin + 3)) X)
  exact RatPolyCoeffEqv.trans hcombined
    (RatPolyCoeffEqv.trans
      (directional_recombine coefficient X Y W hrecurrence)
      (RatPolyCoeffEqv.smul_coefficient hfinalCoefficient X))

private theorem exposedZonalDifferential_step
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat)
    (hspin : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 spin)
    (hnext : ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 (spin + 1)) :
    ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 (spin + 2) :=
  ⟨exposedZonalHarmonic_step
      reverse0 reverse1 reverse2 reverse3 spin hspin hnext,
    exposedZonalDirectional_step
      reverse0 reverse1 reverse2 reverse3 spin hspin hnext⟩

private theorem exposedZonalDifferential_pair
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    ∀ spin,
      ExposedZonalDifferentialAt
          reverse0 reverse1 reverse2 reverse3 spin ∧
        ExposedZonalDifferentialAt
          reverse0 reverse1 reverse2 reverse3 (spin + 1)
  | 0 =>
      ⟨exposedZonalDifferential_zero
          reverse0 reverse1 reverse2 reverse3,
        exposedZonalDifferential_one
          reverse0 reverse1 reverse2 reverse3⟩
  | spin + 1 => by
      have previous := exposedZonalDifferential_pair
        reverse0 reverse1 reverse2 reverse3 spin
      exact ⟨previous.2,
        exposedZonalDifferential_step
          reverse0 reverse1 reverse2 reverse3 spin
          previous.1 previous.2⟩

theorem exposedZonalDifferential_all
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    ExposedZonalDifferentialAt
      reverse0 reverse1 reverse2 reverse3 spin :=
  (exposedZonalDifferential_pair
    reverse0 reverse1 reverse2 reverse3 spin).1

/-- The selected-link Euclidean Laplacian annihilates every all-spin solid
zonal BF4 wavefunction, with all 115 non-selected blocks retained. -/
theorem laplacian_exposedSolidZonalCharacter_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 spin))
      polyZero :=
  (exposedZonalDifferential_all
    reverse0 reverse1 reverse2 reverse3 spin).harmonic

/-- Explicit `Δ_U Z_j(A U B) = 0` spelling of the all-spin theorem.  The
four booleans record the orientations of the four factors surrounding the
selected quaternion `U`; every other quaternion remains in the coefficients
of the resulting rational polynomial. -/
theorem laplacian_U_solidZonal_AUB_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 spin))
      polyZero :=
  laplacian_exposedSolidZonalCharacter_zero
    reverse0 reverse1 reverse2 reverse3 spin

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonic

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonic.laplacian_exposedScalar_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonic.gradient_exposedScalar_self
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonic.gradient_exposedScalar_fourRadius
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonic.laplacian_exposedSolidZonalCharacter_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonic.laplacian_U_solidZonal_AUB_zero
