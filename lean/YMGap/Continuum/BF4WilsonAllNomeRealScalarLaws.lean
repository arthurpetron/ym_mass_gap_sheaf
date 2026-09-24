/-
# Algebraic laws for real scaling on the all-nome Wilson completion

The scalar arithmetic retains explicit `QCauchy` data.  All vector laws are
deduced from the already descended pairing and its definiteness; no new
analytic estimate or completion is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarMulCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedRealSmul hw0 hw1

/-- Real scaling distributes over completed vector addition. -/
theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    S s cs (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (S s cs x) (S s cs y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  simp only [completedInner_realSmul_left, completedInner_add_left]
  refine Quotient.inductionOn (B x test) ?_
  intro X
  refine Quotient.inductionOn (B y test) ?_
  exact fun Y => Quotient.sound
    (TrigSignedAddFull.cmul_add s X Y)

/-- Addition of explicit constructive-real scalars acts pointwise. -/
theorem completedRealSmul_addScalar (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S (CReal.add s t) (scalarAddCauchy s t cs ct) x =
      completedAdd hw0 hw1 (S s cs x) (S t ct x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  simp only [completedInner_realSmul_left, completedInner_add_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (TrigSignedAddFull.cadd_mul s t X)

/-- Associativity of explicit constructive-real scaling. -/
theorem completedRealSmul_mul (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S s cs (S t ct x) = S (CReal.mul s t) (scalarMulCauchy s t cs ct) x := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  simp only [completedInner_realSmul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (CRealAlg.cmul_assoc s t X).symm

/-- The completed quadratic form scales by the exact real square. -/
theorem completedInner_realSmul_diagonal (s : CReal) (cs : QCauchy s.approx) (x : V) :
    B (S s cs x) (S s cs x) =
      RCmul (Quotient.mk crealSetoid s)
        (RCmul (Quotient.mk crealSetoid s) (B x x)) := by
  rw [completedInner_realSmul_left, completedInner_realSmul_right]

/-- Real scaling preserves orthogonality to the actual unit state. -/
def vacuumComplementRealSmul (s : CReal) (cs : QCauchy s.approx)
    (x : VacuumComplement hw0 hw1 (width := width)) :
    VacuumComplement hw0 hw1 (width := width) :=
  ⟨S s cs x.val, by
    rw [completedInner_realSmul_right, x.property]
    refine Quotient.inductionOn (Quotient.mk crealSetoid s) ?_
    exact fun scalar => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.mul_zero_eqv (scalar.approx n)))⟩

end YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws

#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws.completedRealSmul_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws.completedRealSmul_addScalar
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws.completedRealSmul_mul
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws.completedInner_realSmul_diagonal
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws.vacuumComplementRealSmul
