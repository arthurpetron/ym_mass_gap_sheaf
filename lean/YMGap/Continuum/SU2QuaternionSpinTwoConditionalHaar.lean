/-
# The first even-spin conditional Haar identity

This file closes the quadratic (`twice-spin = 2`) instance of the exposed
link calculation on the literal 116-block carrier.  The selected quaternion
is block zero; three further blocks form the other plaquette edges; all other
112 blocks occur only through an arbitrary multiplier.

The key point is coefficient retention.  Integrating the selected block in
`4 scalar(A U B C)^2 - 1` produces the tail polynomial
`|A|^2 |B|^2 |C|^2 - 1`, rather than zero before the remaining sphere
relations are imposed.  The three radius factors then disappear under the
tail Haar functional.  Thus every one of the other 115 blocks remains an
arbitrary polynomial coefficient throughout the proof.
-/

import YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter
import YMGap.Continuum.BF4CompactActionSphereShift

namespace YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift

local infix:50 " ≈ " => Q'.eqv

/-- Apply one of the two plaquette orientations to a coordinate quaternion. -/
def orientedCoordinateQuaternion
    (block : Nat) (reverse : Bool) : PolyQuaternion :=
  if reverse then
    PolyQuaternion.conj (PolyQuaternion.coordinateVariable block)
  else
    PolyQuaternion.coordinateVariable block

/-- Orientation reversal changes signs but not polynomial block degree. -/
theorem orientedCoordinateQuaternion_blockDegree
    (source block : Nat) (reverse : Bool) :
    HasPolyQuaternionBlockDegree block
      (if block = source then 1 else 0)
      (orientedCoordinateQuaternion source reverse) := by
  cases reverse with
  | false =>
      exact hasPolyQuaternionBlockDegree_coordinateVariable source block
  | true =>
      exact
        (hasPolyQuaternionBlockDegree_coordinateVariable source block).conj

/-- A four-edge plaquette word with the exposed link in block zero. -/
def exposedFourWord
    (reverse0 reverse1 reverse2 reverse3 : Bool) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (orientedCoordinateQuaternion 0 reverse0)
        (orientedCoordinateQuaternion 1 reverse1))
      (orientedCoordinateQuaternion 2 reverse2))
    (orientedCoordinateQuaternion 3 reverse3)

/-- The ordinary quadratic character of the oriented four-edge word. -/
def exposedSpinTwoCharacter
    (reverse0 reverse1 reverse2 reverse3 : Bool) : RatPoly :=
  characterPolynomial
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar 2

/-- The all-spin homogeneous zonal character attached to the same four-edge
word. -/
def exposedSolidZonalCharacter
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (spin : Nat) : RatPoly :=
  solidZonalCharacterPolynomial
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
    fourQuaternionRadiusProduct spin

/-- Every oriented four-edge scalar is linear in each of its four quaternion
blocks. -/
theorem exposedFourWord_scalar_blockDegree
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (block : Nat) (hblock : block < 4) :
    HasQuaternionBlockDegree block 1
      (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar := by
  have hcases : block = 0 ∨ block = 1 ∨ block = 2 ∨ block = 3 := by
    omega
  have hword :=
    (((orientedCoordinateQuaternion_blockDegree 0 block reverse0).mul
      (orientedCoordinateQuaternion_blockDegree 1 block reverse1)).mul
      (orientedCoordinateQuaternion_blockDegree 2 block reverse2)).mul
      (orientedCoordinateQuaternion_blockDegree 3 block reverse3)
  rcases hcases with h | h | h | h <;> subst block
  all_goals
    exact
      (HasPolyQuaternionBlockDegree.relabel (by decide) hword).scalar

/-- The four-radius product is quadratic in each of the four word blocks. -/
theorem fourQuaternionRadiusProduct_blockDegree
    (block : Nat) (hblock : block < 4) :
    HasQuaternionBlockDegree block 2 fourQuaternionRadiusProduct := by
  have hcases : block = 0 ∨ block = 1 ∨ block = 2 ∨ block = 3 := by
    omega
  have hradius :=
    (hasQuaternionBlockDegree_radius 0 block).mul
      ((hasQuaternionBlockDegree_radius 1 block).mul
        ((hasQuaternionBlockDegree_radius 2 block).mul
          (hasQuaternionBlockDegree_radius 3 block)))
  rcases hcases with h | h | h | h <;> subst block
  all_goals
    exact HasQuaternionBlockDegree.relabel (by decide) hradius

/-- Consequently every solid zonal mode has its representation degree in
each of the four plaquette quaternions. -/
theorem exposedSolidZonalCharacter_blockDegree
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (block : Nat) (hblock : block < 4) (spin : Nat) :
    HasQuaternionBlockDegree block spin
      (exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 spin) := by
  exact solidZonalCharacterPolynomial_blockDegree
    (exposedFourWord_scalar_blockDegree
      reverse0 reverse1 reverse2 reverse3 block hblock)
    (fourQuaternionRadiusProduct_blockDegree block hblock)
    spin

/-- The solid and ordinary exposed characters agree in the full arbitrary-
insertion 116-block Haar quotient, uniformly in spin. -/
theorem exposedSolidZonalCharacter_eq_character_116
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    QuaternionHaarCarrierEqv 116
      (exposedSolidZonalCharacter
        reverse0 reverse1 reverse2 reverse3 spin)
      (characterPolynomial
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar spin) :=
  solidZonalCharacterPolynomial_eq_character_116 _ spin

/-- The squared norm of the other three plaquette factors, after deleting
the selected head block. -/
def tailThreeRadiusProduct : RatPoly :=
  polyMul (quaternionRadiusPolynomial 0)
    (polyMul (quaternionRadiusPolynomial 1)
      (quaternionRadiusPolynomial 2))

/-- The conditional spin-two integral before the tail sphere equations. -/
def centeredTailThreeRadiusProduct : RatPoly :=
  polyAdd tailThreeRadiusProduct (polySmul (-1) polyOne)

/-- **Coefficient-retaining quadratic conditional identity.**  Integrating
the selected quaternion gives `|A|^2 |B|^2 |C|^2 - 1`.  Rational
canonicalization checks the polynomial identity without integrating a single
tail block. -/
theorem exposedSpinTwoCharacter_partial_canon
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    RatPolyTermwiseEqv
      (canonRat
        (partialHaarHead
          (exposedSpinTwoCharacter
            reverse0 reverse1 reverse2 reverse3)))
      (canonRat centeredTailThreeRadiusProduct) := by
  cases reverse0 <;> cases reverse1 <;>
    cases reverse2 <;> cases reverse3 <;> decide

/-- Canonical equality transports through an arbitrary Haar multiplier. -/
private theorem quaternionHaar_mul_eq_of_canonRat_eq
    (blocks : Nat) (left right multiplier : RatPoly)
    (hcanon : RatPolyTermwiseEqv (canonRat left) (canonRat right)) :
    quaternionHaar blocks (polyMul left multiplier) ≈
      quaternionHaar blocks (polyMul right multiplier) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul (canonRat left) multiplier)) _
    (Q'.eqv_symm
      (quaternionHaar_canonRat_mul blocks left multiplier)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul multiplier (canonRat left))) _
    (quaternionHaar_polyMul_comm blocks _ _) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul multiplier (canonRat right))) _
    (quaternionHaar_polyMul_termwise_eqv blocks multiplier hcanon) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul (canonRat right) multiplier)) _
    (quaternionHaar_polyMul_comm blocks _ _) ?_
  exact quaternionHaar_canonRat_mul blocks right multiplier

/-- The three tail radius factors are Haar units even against an arbitrary
polynomial in all 115 retained blocks. -/
private theorem quaternionHaar_tailThreeRadiusProduct_mul
    (multiplier : RatPoly) :
    quaternionHaar 115
        (polyMul tailThreeRadiusProduct multiplier) ≈
      quaternionHaar 115 multiplier := by
  refine Q'.eqv_trans _
    (quaternionHaar 115
      (polyMul multiplier tailThreeRadiusProduct)) _
    (quaternionHaar_polyMul_comm 115 _ _) ?_
  unfold tailThreeRadiusProduct
  refine Q'.eqv_trans _
    (quaternionHaar 115
      (polyMul
        (polyMul
          (polyMul multiplier (quaternionRadiusPolynomial 0))
          (quaternionRadiusPolynomial 1))
        (quaternionRadiusPolynomial 2))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (quaternionHaar 115
        (polyMul
          (polyMul multiplier (quaternionRadiusPolynomial 0))
          (polyMul (quaternionRadiusPolynomial 1)
            (quaternionRadiusPolynomial 2)))) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc 115 _ _ _)) ?_
    exact Q'.eqv_symm
      (quaternionHaar_polyMul_assoc 115 _ _ _)
  · refine Q'.eqv_trans _
      (quaternionHaar 115
        (polyMul
          (polyMul multiplier (quaternionRadiusPolynomial 0))
          (quaternionRadiusPolynomial 1))) _
      (quaternionHaar_mul_radius 115 2 (by omega) _) ?_
    refine Q'.eqv_trans _
      (quaternionHaar 115
        (polyMul multiplier (quaternionRadiusPolynomial 0))) _
      (quaternionHaar_mul_radius 115 1 (by omega) _) ?_
    exact quaternionHaar_mul_radius 115 0 (by omega) multiplier

/-- The conditional radius defect vanishes after the tail Haar functional. -/
private theorem quaternionHaar_centeredTailThreeRadiusProduct_mul_zero
    (multiplier : RatPoly) :
    quaternionHaar 115
        (polyMul centeredTailThreeRadiusProduct multiplier) ≈ 0 := by
  refine Q'.eqv_trans _
    (quaternionHaar 115
      (polyMul multiplier centeredTailThreeRadiusProduct)) _
    (quaternionHaar_polyMul_comm 115 _ _) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 115
        (polyMul multiplier tailThreeRadiusProduct) +
      quaternionHaar 115
        (polyMul multiplier (polySmul (-1) polyOne))) _ ?_ ?_
  · exact quaternionHaar_polyMul_add_right
      115 multiplier tailThreeRadiusProduct (polySmul (-1) polyOne)
  · refine Q'.eqv_trans _
      (quaternionHaar 115 multiplier +
        (-1) * quaternionHaar 115 (polyMul multiplier polyOne)) _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_comm 115 _ _)
          (quaternionHaar_tailThreeRadiusProduct_mul multiplier))
        (quaternionHaar_polyMul_smul_right
          115 (-1) multiplier polyOne)) ?_
    refine Q'.eqv_trans _
      (quaternionHaar 115 multiplier +
        (-1) * quaternionHaar 115 multiplier) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (-1) _ _
          (quaternionHaar_polyMul_one_right 115 multiplier))) ?_
    refine Q'.eqv_trans _
      (quaternionHaar 115 multiplier +
        -(quaternionHaar 115 multiplier)) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _
          (-(1 * quaternionHaar 115 multiplier)) _
          (Q'.neg_mul_eqv 1 (quaternionHaar 115 multiplier))
          (Q'.neg_eqv_congr _ _
            (Q'.one_mul_eqv (quaternionHaar 115 multiplier))))) ?_
    exact Q'.add_neg_self_eqv _

/-- **Quadratic conditional Peter--Weyl identity on 116 blocks.**  The other
115 blocks are retained as arbitrary polynomial coefficients. -/
theorem exposedSpinTwoCharacter116_mul_headIndependent_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (multiplier : RatPoly)
    (hindependent : HeadQuaternionIndependent multiplier) :
    quaternionHaar 116
        (polyMul
          (exposedSpinTwoCharacter
            reverse0 reverse1 reverse2 reverse3)
          multiplier) ≈ 0 := by
  refine Q'.eqv_trans _
    (quaternionHaar 115
      (polyMul
        (partialHaarHead
          (exposedSpinTwoCharacter
            reverse0 reverse1 reverse2 reverse3))
        (dropHeadPolynomial multiplier))) _
    (quaternionHaar_polyMul_headIndependent 115 _ _ hindependent) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 115
      (polyMul centeredTailThreeRadiusProduct
        (dropHeadPolynomial multiplier))) _
    (quaternionHaar_mul_eq_of_canonRat_eq
      115 _ centeredTailThreeRadiusProduct _
      (exposedSpinTwoCharacter_partial_canon
        reverse0 reverse1 reverse2 reverse3)) ?_
  exact quaternionHaar_centeredTailThreeRadiusProduct_mul_zero _

end YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

#print axioms YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar.exposedSpinTwoCharacter_partial_canon
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar.exposedSolidZonalCharacter_blockDegree
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar.exposedSolidZonalCharacter_eq_character_116
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar.exposedSpinTwoCharacter116_mul_headIndependent_zero
