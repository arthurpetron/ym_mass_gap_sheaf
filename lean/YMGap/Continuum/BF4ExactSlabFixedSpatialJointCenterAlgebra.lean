/-
# Literal rational centering for the actual joint reflected form

Subtracting q times the original unit gives another guarded physical
presentation. The proved joint bilinear laws compute its mixed pairing,
unit coefficient and diagonal. Changing q to r has squared distance
exactly (q-r)^2, with no norm estimate or analytic input.

These identities support a later explicit Cauchy centering stream and
its same-carrier completion. No completed linear/scalar interface or
completed centered operator is postulated here. Nome and width stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (scaleSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (unitSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSpan advanceSpan_append advanceSpan_scale)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction (advanceSpan_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime physicalTime_zero unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointDistSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)

/-- The actual physical presentation x minus the rational multiple q of unit. -/
def centerApprox {width : Nat} (x : PhysicalSpan width) (q : Q') : PhysicalSpan width :=
  differenceSpan x (smulSpan q (unit width))

/-- Rational centering commutes with the literal physical time advance. -/
theorem physicalTime_centerApprox {width : Nat} (n : Nat)
    (x : PhysicalSpan width) (q : Q') :
    physicalTime n (centerApprox x q) = centerApprox (physicalTime n x) q := by
  apply Subtype.ext
  change advanceSpan n (x.val ++ scaleSpan (-1) (scaleSpan q unitSpan)) =
    advanceSpan n x.val ++ scaleSpan (-1) (scaleSpan q unitSpan)
  rw [advanceSpan_append, advanceSpan_scale, advanceSpan_scale, advanceSpan_unit]

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add ha (neg_congr hc)

/-- A scalar abbreviation used only inside the finite algebra proofs. -/
private def centerValue (A B C : CReal) (q r : Q') : CReal :=
  sub (sub A (mul (ofQ' q) B)) (sub (mul (ofQ' r) C) (ofQ' (q*r)))

private theorem centerValue_expand (A B C : CReal) (q r : Q') :
    Equiv (sub (sub A (mul (ofQ' r) C)) (mul (ofQ' q) (sub B (ofQ' r))))
      (centerValue A B C q r) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.mul (.var 4) (.var 2))))
      (.neg (.mul (.var 3) (.add (.var 1) (.neg (.var 4))))))
    (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
      (.neg (.add (.mul (.var 4) (.var 2)) (.neg (.mul (.var 3) (.var 4))))))
    (by decide) (fun
      | 0 => A.approx n
      | 1 => B.approx n
      | 2 => C.approx n
      | 3 => q
      | _ => r)

private theorem centerValue_diagonal (A B : CReal) (q : Q') :
    Equiv (centerValue A B B q q)
      (add (sub A (mul B B)) (mul (sub B (ofQ' q)) (sub B (ofQ' q)))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))
      (.neg (.add (.mul (.var 2) (.var 1)) (.neg (.mul (.var 2) (.var 2))))))
    (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
      (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
    (by decide) (fun
      | 0 => A.approx n
      | 1 => B.approx n
      | _ => q)

private theorem centerValue_distance (A B C : CReal) (q r : Q') :
    Equiv
      (sub (sub (centerValue A B C q q) (centerValue A B C q r))
        (sub (centerValue A B C r q) (centerValue A B C r r)))
      (ofQ' ((q + -r)^2)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  let F (a b : Nat) : RingNormaliser.PolyExpr :=
    .add (.add (.var 2) (.neg (.mul (.var a) (.var 3))))
      (.neg (.add (.mul (.var b) (.var 4)) (.neg (.mul (.var a) (.var b)))))
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (F 0 0) (.neg (F 0 1))) (.neg (.add (F 1 0) (.neg (F 1 1)))))
    (.mul (.add (.var 0) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.const 1)))
    (by decide) (fun
      | 0 => q
      | 1 => r
      | 2 => A.approx n
      | 3 => B.approx n
      | _ => C.approx n)

attribute [local irreducible] jointPairing

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "J" => jointPairing hw0 hw1 width
local notation "u" => unit width

theorem centerApprox_pairing_left (x y : PhysicalSpan width) (q : Q') :
    Equiv (J (centerApprox x q) y) (sub (J x y) (mul (ofQ' q) (J u y))) :=
  (jointPairing_difference_left hw0 hw1 width x (smulSpan q u) y).trans
    (sub_congr (Equiv.refl _) (jointPairing_smul_left hw0 hw1 width q u y))

theorem centerApprox_pairing_right (x y : PhysicalSpan width) (r : Q') :
    Equiv (J x (centerApprox y r)) (sub (J x y) (mul (ofQ' r) (J x u))) :=
  (jointPairing_difference_right hw0 hw1 width x y (smulSpan r u)).trans
    (sub_congr (Equiv.refl _) (jointPairing_smul_right hw0 hw1 width r x u))

/-- The remaining unit coefficient is exactly the scalar centering error. -/
theorem centerApprox_unit (x : PhysicalSpan width) (q : Q') :
    Equiv (J (centerApprox x q) u) (sub (J x u) (ofQ' q)) :=
  (centerApprox_pairing_left hw0 hw1 width x u q).trans
    (sub_congr (Equiv.refl _)
      ((TrigSignedAdd.mul_congr_right (jointPairing_unit_unit hw0 hw1 width)).trans
        (CRealAlg.cmul_cone (ofQ' q))))

/-- The exact mixed centered pairing, retaining both physical inputs and
both signed rational coefficients. This is not a positivity estimate. -/
theorem centerApprox_pairing (x y : PhysicalSpan width) (q r : Q') :
    Equiv (J (centerApprox x q) (centerApprox y r))
      (sub (sub (J x y) (mul (ofQ' q) (J u y)))
        (sub (mul (ofQ' r) (J x u)) (ofQ' (q*r)))) := by
  have huy : Equiv (J u (centerApprox y r)) (sub (J u y) (ofQ' r)) :=
    (centerApprox_pairing_right hw0 hw1 width u y r).trans
      (sub_congr (Equiv.refl _)
        ((TrigSignedAdd.mul_congr_right (jointPairing_unit_unit hw0 hw1 width)).trans
          (CRealAlg.cmul_cone (ofQ' r))))
  exact (centerApprox_pairing_left hw0 hw1 width x (centerApprox y r) q).trans
    ((sub_congr (centerApprox_pairing_right hw0 hw1 width x y r)
      (TrigSignedAdd.mul_congr_right huy)).trans
      (centerValue_expand (J x y) (J u y) (J x u) q r))

/-- The diagonal equals the actual centered variance plus the square of the
remaining scalar centering error. -/
theorem centerApprox_diagonal (x : PhysicalSpan width) (q : Q') :
    Equiv (J (centerApprox x q) (centerApprox x q))
      (add (jointCenteredMoment hw0 hw1 width 0 x x)
        (mul (sub (J x u) (ofQ' q)) (sub (J x u) (ofQ' q)))) := by
  have hmean : Equiv (J u x) (J x u) := jointPairing_symm hw0 hw1 width u x
  have hcross : Equiv (centerValue (J x x) (J u x) (J x u) q q)
      (centerValue (J x x) (J x u) (J x u) q q) :=
    sub_congr (sub_congr (Equiv.refl _) (TrigSignedAdd.mul_congr_right hmean))
      (Equiv.refl _)
  have hvariance : Equiv (jointCenteredMoment hw0 hw1 width 0 x x)
      (sub (J x x) (mul (J x u) (J x u))) := by
    unfold jointCenteredMoment
    rw [physicalTime_zero]
    exact sub_congr (Equiv.refl _) (TrigSignedAdd.mul_congr_right hmean)
  exact (centerApprox_pairing hw0 hw1 width x x q q).trans
    (hcross.trans ((centerValue_diagonal (J x x) (J x u) q).trans
      (Equiv_add hvariance.symm (Equiv.refl _))))

/-- Changing only the centering coefficient has exactly its rational
squared difference as joint reflected distance. This is the quantitative
input for constructing an actual centered Cauchy representative. -/
theorem centerApprox_distance (x : PhysicalSpan width) (q r : Q') :
    Equiv (jointDistSq hw0 hw1 width (centerApprox x q) (centerApprox x r))
      (ofQ' ((q + -r)^2)) := by
  have hexpand := jointPairing_difference_diagonal hw0 hw1 width
    (centerApprox x q) (centerApprox x r)
  have hfour := sub_congr
    (sub_congr (centerApprox_pairing hw0 hw1 width x x q q)
      (centerApprox_pairing hw0 hw1 width x x q r))
    (sub_congr (centerApprox_pairing hw0 hw1 width x x r q)
      (centerApprox_pairing hw0 hw1 width x x r r))
  exact hexpand.trans (hfour.trans
    (centerValue_distance (J x x) (J u x) (J x u) q r))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.physicalTime_centerApprox
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_pairing_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_pairing_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra.centerApprox_distance
