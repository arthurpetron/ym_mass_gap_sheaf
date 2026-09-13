/-
# Arithmetic laws for the ORIGINAL thermodynamic real-scalar action

Generic modulus-bearing scalar addition and multiplication are reused
without any vector-space or physical-model premises. The existing semantic
observable identities then prove the SAME thermodynamic action laws.
Subtraction and squared distance respect scaling. No modulus for an
arbitrary legacy quotient real is selected.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar (rationalCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarAddCauchy scalarMulCauchy)

theorem completedRealSmul_addScalar (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : Completion) :
    completedRealSmul (CReal.add s t) (scalarAddCauchy s t cs ct) x =
      completedAdd (completedRealSmul s cs x) (completedRealSmul t ct x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => add_smul (s.approx n) (t.approx n) (embed (X.seq n)))

theorem completedRealSmul_mul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : Completion) :
    completedRealSmul s cs (completedRealSmul t ct x) =
      completedRealSmul (CReal.mul s t) (scalarMulCauchy s t cs ct) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => qsmul_assoc (s.approx n) (t.approx n) (embed (X.seq n)))

theorem completedRealSmul_neg (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    completedRealSmul s cs (completedNeg x) =
      completedNeg (completedRealSmul s cs x) := by
  have hleft := completedRealSmul_mul s (ofQ' (-1)) cs (rationalCauchy (-1)) x
  have hright := completedRealSmul_mul (ofQ' (-1)) s (rationalCauchy (-1)) cs x
  rw [completedRealSmul_ofQ'] at hleft hright
  exact hleft.trans ((completedRealSmul_congr _ _ _ _ (CRealAlg.cmul_comm s (ofQ' (-1))) x).trans hright.symm)

theorem completedRealSmul_sub (s : CReal) (cs : QCauchy s.approx) (x y : Completion) :
    completedRealSmul s cs (completedSub x y) =
      completedSub (completedRealSmul s cs x) (completedRealSmul s cs y) := by
  unfold completedSub
  rw [completedRealSmul_add, completedRealSmul_neg]

theorem completedInner_realSmul_diagonal (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    completedInner (completedRealSmul s cs x) (completedRealSmul s cs x) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (completedInner x x)) := by
  rw [completedInner_realSmul_left, completedInner_realSmul_right]

theorem completedDist_realSmul (s : CReal) (cs : QCauchy s.approx) (x y : Completion) :
    completedDist (completedRealSmul s cs x) (completedRealSmul s cs y) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (completedDist x y)) := by
  unfold completedDist
  rw [← completedRealSmul_sub, completedInner_realSmul_diagonal]

end YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedRealSmul_addScalar
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedRealSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedRealSmul_neg
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedRealSmul_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedInner_realSmul_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra.completedDist_realSmul
