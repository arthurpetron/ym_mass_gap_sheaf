/-
# Real-scalar action on the SAME original completed plaquette state space

The explicit scalar stream constructs states; original inner-product
homogeneity passes to its limit. Positive definiteness then proves that
the resulting state depends only on scalar value and completed vector,
not on either representative or the supplied scalar modulus.

The public action takes a CReal together with QCauchy data for its actual
approximation stream. This does not assert that a modulus can be chosen
for every legacy quotient real. No carrier, form or physical law changes.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

/-- Rational constants supply actual zero-rate data. -/
def rationalCauchy (q : Q') : QCauchy (ofQ' q).approx where
  M _ := 0
  bound := fun _ he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he), Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he)⟩

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

/-- No duality representation theorem: test the difference against itself. -/
theorem completed_eq_of_pairings (x y : Completion w hw0 hw1 half)
    (h : ∀ z, completedInner w hw0 hw1 x z = completedInner w hw0 hw1 y z) : x = y := by
  let d := completedSub w hw0 hw1 x y
  have hd : completedInner w hw0 hw1 d d = RCzero := calc
    completedInner w hw0 hw1 d d =
        RCadd (completedInner w hw0 hw1 x d) (completedInner w hw0 hw1 (completedNeg w hw0 hw1 y) d) :=
      completedInner_add_left w hw0 hw1 x (completedNeg w hw0 hw1 y) d
    _ = RCadd (completedInner w hw0 hw1 y d) (completedInner w hw0 hw1 (completedNeg w hw0 hw1 y) d) :=
      congrArg (fun a => RCadd a (completedInner w hw0 hw1 (completedNeg w hw0 hw1 y) d)) (h d)
    _ = completedInner w hw0 hw1 (completedAdd w hw0 hw1 y (completedNeg w hw0 hw1 y)) d :=
      (completedInner_add_left w hw0 hw1 y (completedNeg w hw0 hw1 y) d).symm
    _ = RCzero := by rw [completedAdd_comm, completedNeg_add, completedInner_zero_left]
  exact (completedDist_zero_iff w hw0 hw1 x y).mp hd

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx) (X Y : (D).Cauchy) :
    Equiv (representativeInner w hw0 hw1 (realScalarCauchy w hw0 hw1 s cs X) Y)
      (CReal.mul s (representativeInner w hw0 hw1 X Y)) :=
  Equiv_of_limit_of_equal (fun n => form_smul_left w hw0 hw1 (s.approx n) (X.seq n) (Y.seq n))
    (pairSequence_converges w hw0 hw1 (realScalarCauchy w hw0 hw1 s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges w hw0 hw1 X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (Quotient.mk (D).completionSetoid (realScalarCauchy w hw0 hw1 s cs X)) y =
      RCmul (Quotient.mk crealSetoid s) (completedInner w hw0 hw1 (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (representativeInner_realScalar_left w hw0 hw1 s cs X Y)

theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy w hw0 hw1 s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy w hw0 hw1 t ct Y) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX, show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hs]

/-- Quotient descent in the vector uses the actual original pairing. -/
def completedRealSmul (s : CReal) (cs : QCauchy s.approx) :
    Completion w hw0 hw1 half → Completion w hw0 hw1 half :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy w hw0 hw1 s cs X))
    (fun X Y h => realScalarCauchy_congr w hw0 hw1 s s cs cs (Equiv.refl s) X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul w hw0 hw1 s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy w hw0 hw1 s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) y =
      RCmul (Quotient.mk crealSetoid s) (completedInner w hw0 hw1 x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing w hw0 hw1 s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x (completedRealSmul w hw0 hw1 s cs y) =
      RCmul (Quotient.mk crealSetoid s) (completedInner w hw0 hw1 x y) := by
  rw [completedInner_symm w hw0 hw1 x, completedInner_realSmul_left, completedInner_symm w hw0 hw1 y x]

/-- Different scalar streams or different moduli for the same scalar give the same state. -/
theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 s cs x = completedRealSmul w hw0 hw1 t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr w hw0 hw1 s t cs ct hs X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 (ofQ' q) cq x = completedSmul w hw0 hw1 q x := by
  apply completed_eq_of_pairings w hw0 hw1
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]

theorem completedRealSmul_one (c : QCauchy cone.approx) (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 cone c x = x :=
  (completedRealSmul_ofQ' w hw0 hw1 1 c x).trans (completedSmul_one w hw0 hw1 x)

theorem completedRealSmul_zero (c : QCauchy czero.approx) (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 czero c x = completedZero w hw0 hw1 half :=
  (completedRealSmul_ofQ' w hw0 hw1 0 c x).trans (completedSmul_zero w hw0 hw1 x)

theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 s cs (completedAdd w hw0 hw1 x y) =
      completedAdd w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) (completedRealSmul w hw0 hw1 s cs y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.smul_add (s.approx n) (lower (X.seq n)) (lower (Y.seq n)),
     RatPolyCoeffEqv.smul_add (s.approx n) (upper (X.seq n)) (upper (Y.seq n))⟩)

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.rationalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completed_eq_of_pairings
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.representativeInner_realScalar_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.realScalarCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.realScalarCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedInner_realSmul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedInner_realSmul_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_ofQ'
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar.completedRealSmul_add
