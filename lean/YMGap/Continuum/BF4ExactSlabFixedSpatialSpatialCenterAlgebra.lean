/-
# Literal rational centering for the actual spatial limiting form

The existing centerApprox is unchanged: subtract a rational multiple of
the original physical unit from the original signed presentation. Recentring
commutes with this literal operation. Its exact mixed, diagonal and distance
identities pass through the proved spatial limits of the SAME joint forms.
Thus no pure scalar polynomial algebra is reproved, and no limit-null vector
is asserted null in a finite box.

The resulting distance is exactly the square of the change of coefficient.
These are spatial-form identities under the displayed small-nome guards,
not a new carrier, a metric-completeness assertion or a continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenterAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (differenceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra (centerApprox)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance (recenter_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Recentring changes the original words, but not their rational centering. -/
theorem recenter_centerApprox {base : Nat} (r : Nat) (x : PhysicalSpan base) (q : Q') :
    recenter r (centerApprox x q) = centerApprox (recenter r x) q := by
  unfold centerApprox
  rw [recenter_difference, recenter_smul, recenter_unit]

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb
local notation "u" => unit base

attribute [local irreducible] spatialPairing

theorem centerApprox_pairing_left (x y : PhysicalSpan base) (q : Q') :
    Equiv (P (centerApprox x q) y) (sub (P x y) (mul (ofQ' q) (P u y))) :=
  (spatialPairing_difference_left hw0 hw1 base hsmall hd hs hb x (smulSpan q u) y).trans
    (sub_congr (Equiv.refl _)
      (spatialPairing_smul_left hw0 hw1 base hsmall hd hs hb q u y))

theorem centerApprox_pairing_right (x y : PhysicalSpan base) (q : Q') :
    Equiv (P x (centerApprox y q)) (sub (P x y) (mul (ofQ' q) (P x u))) :=
  (spatialPairing_difference_right hw0 hw1 base hsmall hd hs hb x y (smulSpan q u)).trans
    (sub_congr (Equiv.refl _)
      (spatialPairing_smul_right hw0 hw1 base hsmall hd hs hb q x u))

/-- The remaining unit coefficient is the actual spatial mean error. -/
theorem centerApprox_unit (x : PhysicalSpan base) (q : Q') :
    Equiv (P (centerApprox x q) u) (sub (P x u) (ofQ' q)) :=
  (centerApprox_pairing_left hw0 hw1 base hsmall hd hs hb x u q).trans
    (sub_congr (Equiv.refl _)
      ((TrigSignedAdd.mul_congr_right (spatialPairing_unit_unit hw0 hw1 base hsmall hd hs hb)).trans
        (CRealAlg.cmul_cone (ofQ' q))))

/-- Exact mixed centering with both signed rational coefficients retained. -/
theorem centerApprox_pairing (x y : PhysicalSpan base) (q r : Q') :
    Equiv (P (centerApprox x q) (centerApprox y r))
      (sub (sub (P x y) (mul (ofQ' q) (P u y)))
        (sub (mul (ofQ' r) (P x u)) (ofQ' (q*r)))) :=
  Equiv_of_limit_of_equal
    (fun margin => by
      simpa only [recenter_centerApprox, recenter_unit] using
        BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_pairing
          hw0 hw1 (paddedWidth base margin) (recenter margin x) (recenter margin y) q r)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (centerApprox x q) (centerApprox y r))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add
        (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)
        (TrigAddCReal.convergesTo_neg (convergesTo_const_mul (ofQ' q)
          (spatialPairing_converges hw0 hw1 base hsmall hd hs hb u y))))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (convergesTo_const_mul (ofQ' r)
            (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x u))
          (TrigAddCReal.convergesTo_neg (convergesTo_const (ofQ' (q*r)))))))

/-- Actual spatial variance plus the square of the scalar centering error. -/
theorem centerApprox_diagonal (x : PhysicalSpan base) (q : Q') :
    Equiv (P (centerApprox x q) (centerApprox x q))
      (add (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb 0 x x)
        (mul (sub (P x u) (ofQ' q)) (sub (P x u) (ofQ' q)))) := by
  have herror := TrigAddCReal.convergesTo_add
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x u)
    (TrigAddCReal.convergesTo_neg (convergesTo_const (ofQ' q)))
  exact Equiv_of_limit_of_equal
    (fun margin => by
      simpa only [recenter_centerApprox, recenter_unit] using
        BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_diagonal
          hw0 hw1 (paddedWidth base margin) (recenter margin x) q)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (centerApprox x q) (centerApprox x q))
    (TrigAddCReal.convergesTo_add
      (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb 0 x x)
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        herror herror))

/-- Exact squared-distance identity, not an assumed completion estimate. -/
theorem centerApprox_distance (x : PhysicalSpan base) (q r : Q') :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb (centerApprox x q) (centerApprox x r))
      (ofQ' ((q + -r)^2)) :=
  Equiv_of_limit_of_equal
    (fun margin => by
      simpa only [recenter_centerApprox] using
        BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_distance
          hw0 hw1 (paddedWidth base margin) (recenter margin x) q r)
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb (centerApprox x q) (centerApprox x r))
    (convergesTo_const (ofQ' ((q + -r)^2)))

#print axioms recenter_centerApprox
#print axioms centerApprox_pairing_left
#print axioms centerApprox_pairing_right
#print axioms centerApprox_unit
#print axioms centerApprox_pairing
#print axioms centerApprox_diagonal
#print axioms centerApprox_distance

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenterAlgebra
