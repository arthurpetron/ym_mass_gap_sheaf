/-
# Real-scalar action on the SAME original thermodynamic completion

The explicitly constructed scalar stream has the original pairing
homogeneity law. Positive definiteness separates states by their pairings,
so both vector representatives and scalar representatives/moduli descend
without selecting any quotient representative.

The action takes a real and QCauchy data for its approximation stream.
This is not a claim that such data can be selected for every legacy
quotient real. No physical time, stationary vacuum or gap is assumed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy

local notation "D" => seminorm

/-- No duality representation theorem: test the difference against itself. -/
theorem completed_eq_of_pairings (x y : Completion)
    (h : ∀ z, completedInner x z = completedInner y z) : x = y := by
  let d := completedSub x y
  have hd : completedInner d d = RCzero := calc
    completedInner d d =
        RCadd (completedInner x d) (completedInner (completedNeg y) d) :=
      completedInner_add_left x (completedNeg y) d
    _ = RCadd (completedInner y d) (completedInner (completedNeg y) d) :=
      congrArg (fun a => RCadd a (completedInner (completedNeg y) d)) (h d)
    _ = completedInner (completedAdd y (completedNeg y)) d :=
      (completedInner_add_left y (completedNeg y) d).symm
    _ = RCzero := by rw [completedAdd_comm, completedNeg_add, completedInner_zero_left]
  exact (completedDist_zero_iff x y).mp hd

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx) (X Y : (D).Cauchy) :
    Equiv (representativeInner (realScalarCauchy s cs X) Y)
      (CReal.mul s (representativeInner X Y)) :=
  Equiv_of_limit_of_equal (fun n => presentedForm_smul_left (s.approx n) (X.seq n) (Y.seq n))
    (pairSequence_converges (realScalarCauchy s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (y : Completion) :
    completedInner (Quotient.mk (D).completionSetoid (realScalarCauchy s cs X)) y =
      RCmul (Quotient.mk crealSetoid s) (completedInner (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (representativeInner_realScalar_left s cs X Y)

theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy t ct Y) := by
  apply completed_eq_of_pairings
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX, show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hs]

/-- Quotient descent in the vector uses the actual original pairing. -/
def completedRealSmul (s : CReal) (cs : QCauchy s.approx) :
    Completion → Completion :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy s cs X))
    (fun X Y h => realScalarCauchy_congr s s cs cs (Equiv.refl s) X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : Completion) :
    completedInner (completedRealSmul s cs x) y =
      RCmul (Quotient.mk crealSetoid s) (completedInner x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : Completion) :
    completedInner x (completedRealSmul s cs y) =
      RCmul (Quotient.mk crealSetoid s) (completedInner x y) := by
  rw [completedInner_symm x, completedInner_realSmul_left, completedInner_symm y x]

/-- Different scalar streams or different moduli for the same scalar give the same state. -/
theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (x : Completion) :
    completedRealSmul s cs x = completedRealSmul t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr s t cs ct hs X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : Completion) :
    completedRealSmul (ofQ' q) cq x = completedSmul q x := by
  apply completed_eq_of_pairings
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]

theorem completedRealSmul_one (c : QCauchy cone.approx) (x : Completion) :
    completedRealSmul cone c x = x :=
  (completedRealSmul_ofQ' 1 c x).trans (completedSmul_one x)

theorem completedRealSmul_zero (c : QCauchy czero.approx) (x : Completion) :
    completedRealSmul czero c x = completedZero :=
  (completedRealSmul_ofQ' 0 c x).trans (completedSmul_zero x)

theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : Completion) :
    completedRealSmul s cs (completedAdd x y) =
      completedAdd (completedRealSmul s cs x) (completedRealSmul s cs y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise (fun n => qsmul_add (s.approx n) (embed (X.seq n)) (embed (Y.seq n)))

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completed_eq_of_pairings
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.representativeInner_realScalar_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.realScalarCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.realScalarCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedInner_realSmul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedInner_realSmul_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_ofQ'
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar.completedRealSmul_add
