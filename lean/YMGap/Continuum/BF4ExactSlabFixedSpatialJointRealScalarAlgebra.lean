/-
# Witnessed real-scalar algebra on the SAME all-nome joint completion

Every scalar operation retains supplied rational Cauchy data.  Vector
equalities are obtained from separation by the actual completed pairing;
no representative or modulus is selected from a quotient real.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
  (completedDistSq)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
  (rationalCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "S" => completedRealSmul hw0 hw1 width

theorem completedRealSmul_addScalar (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S (add s t) (scalarAddCauchy s t cs ct) x =
      completedAdd hw0 hw1 width (S s cs x) (S t ct x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro test
  simp only [completedInner_realSmul_left, completedInner_add_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv (s.approx n) (t.approx n) (X.approx n)))

theorem completedRealSmul_mul (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S s cs (S t ct x) = S (mul s t) (scalarMulCauchy s t cs ct) x := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro test
  simp only [completedInner_realSmul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm
      (Q'.mul_assoc_eqv (s.approx n) (t.approx n) (X.approx n))))

theorem completedRealSmul_zeroScalar (x : V) :
    S (ofQ' 0) (rationalCauchy 0) x = completedZero hw0 hw1 width := by
  rw [completedRealSmul_ofQ', completedSmul_zero]

theorem completedRealSmul_oneScalar (x : V) :
    S (ofQ' 1) (rationalCauchy 1) x = x := by
  rw [completedRealSmul_ofQ', completedSmul_one]

theorem completedRealSmul_negScalar (s : CReal) (cs : QCauchy s.approx) (x : V) :
    S (neg s) (scalarNegCauchy s cs) x = completedNeg hw0 hw1 width (S s cs x) := by
  have hneg : Equiv (neg s) (mul (ofQ' (-1)) s) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => by
      refine Q'.eqv_trans _ (-(1 * s.approx n)) _
        (Q'.eqv_symm (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (s.approx n)))) ?_
      exact Q'.eqv_symm (Q'.neg_mul_eqv 1 (s.approx n)))
  rw [completedRealSmul_congr hw0 hw1 width (neg s) (mul (ofQ' (-1)) s)
    (scalarNegCauchy s cs) (scalarMulCauchy (ofQ' (-1)) s (rationalCauchy (-1)) cs)
    hneg x]
  rw [← completedRealSmul_mul, completedRealSmul_ofQ']
  rfl

theorem completedRealSmul_neg (s : CReal) (cs : QCauchy s.approx) (x : V) :
    S s cs (completedNeg hw0 hw1 width x) = completedNeg hw0 hw1 width (S s cs x) := by
  have hleft := completedRealSmul_mul hw0 hw1 width
    s (ofQ' (-1)) cs (rationalCauchy (-1)) x
  have hright := completedRealSmul_mul hw0 hw1 width
    (ofQ' (-1)) s (rationalCauchy (-1)) cs x
  rw [completedRealSmul_ofQ'] at hleft hright
  exact hleft.trans ((completedRealSmul_congr hw0 hw1 width _ _ _ _
    (CRealAlg.cmul_comm s (ofQ' (-1))) x).trans hright.symm)

theorem completedRealSmul_sub (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    S s cs (completedSub hw0 hw1 width x y) =
      completedSub hw0 hw1 width (S s cs x) (S s cs y) := by
  unfold completedSub
  rw [completedRealSmul_add, completedRealSmul_neg]

theorem completedInner_realSmul_both (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B (S s cs x) (S s cs y) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (B x y)) := by
  rw [completedInner_realSmul_left, completedInner_realSmul_right]

theorem completedInner_realSmul_diagonal (s : CReal) (cs : QCauchy s.approx) (x : V) :
    B (S s cs x) (S s cs x) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (B x x)) :=
  completedInner_realSmul_both hw0 hw1 width s cs x x

theorem completedRealSmul_orthogonal (s : CReal) (cs : QCauchy s.approx)
    (x y : V) (h : B x y = RCzero) : B (S s cs x) y = RCzero := by
  rw [completedInner_realSmul_left, h]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (s.approx n)))

/-- The actual squared norm scales by the square of the supplied real. -/
theorem completedNormSq_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    B (S s cs x) (S s cs x) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (B x x)) :=
  completedInner_realSmul_diagonal hw0 hw1 width s cs x

/-- The actual squared distance scales by the square of the supplied real. -/
theorem completedDistSq_realSmul (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    completedDistSq hw0 hw1 width (S s cs x) (S s cs y) =
      RCmul (Quotient.mk crealSetoid s)
        (RCmul (Quotient.mk crealSetoid s) (completedDistSq hw0 hw1 width x y)) := by
  unfold completedDistSq
  rw [← completedRealSmul_sub, completedInner_realSmul_diagonal]

/-- Real scaling internal to the actual unit-orthogonal sector. -/
def unitComplementRealSmul (s : CReal) (cs : QCauchy s.approx)
    (x : UnitComplement hw0 hw1 width) : UnitComplement hw0 hw1 width :=
  ⟨S s cs x.val,
    completedRealSmul_orthogonal hw0 hw1 width s cs x.val
      (jointCompletedUnit hw0 hw1 width) x.property⟩

theorem unitComplementTime_realSmul (n : Nat) (s : CReal) (cs : QCauchy s.approx)
    (x : UnitComplement hw0 hw1 width) :
    unitComplementTime hw0 hw1 width n (unitComplementRealSmul hw0 hw1 width s cs x) =
      unitComplementRealSmul hw0 hw1 width s cs
        (unitComplementTime hw0 hw1 width n x) :=
  Subtype.ext (completedTime_realSmul hw0 hw1 width n s cs x.val)

#print axioms completedRealSmul_addScalar
#print axioms completedRealSmul_mul
#print axioms completedRealSmul_zeroScalar
#print axioms completedRealSmul_oneScalar
#print axioms completedRealSmul_negScalar
#print axioms completedRealSmul_neg
#print axioms completedRealSmul_sub
#print axioms completedInner_realSmul_both
#print axioms completedInner_realSmul_diagonal
#print axioms completedRealSmul_orthogonal
#print axioms completedNormSq_realSmul
#print axioms completedDistSq_realSmul
#print axioms unitComplementRealSmul
#print axioms unitComplementTime_realSmul

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarAlgebra
