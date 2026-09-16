/-
# Modulus-bearing real scaling on the SAME physical Cauchy carrier

Actual scalar streams and original pairing homogeneity construct the
action. Positive definiteness proves independence of the supplied scalar
stream, scalar modulus and vector representative. Quotient descent selects
no representatives and uses no modulus from legacy propositional existence.

The scalar argument remains a CReal WITH QCauchy data. This is not an
unrestricted action of bare quotient reals, a completeness theorem, an
isolated vacuum or a physical mass gap. All lattice parameters stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy

def rationalCauchy (q : Q') : QCauchy (ofQ' q).approx where
  M _ := 0
  bound := fun _ he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he), Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he)⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage
local notation "B" => completedInner hw0 hw1 width stage

/-- Testing the actual difference against itself suffices; no duality choice. -/
theorem completed_eq_of_pairings (x y : Completion hw0 hw1 width stage)
    (h : ∀ z, B x z = B y z) : x = y := by
  let d := completedSub hw0 hw1 width stage x y
  have hd : B d d = RCzero := calc
    B d d = RCadd (B x d) (B (completedNeg hw0 hw1 width stage y) d) :=
      completedInner_add_left hw0 hw1 width stage x (completedNeg hw0 hw1 width stage y) d
    _ = RCadd (B y d) (B (completedNeg hw0 hw1 width stage y) d) :=
      congrArg (fun a => RCadd a (B (completedNeg hw0 hw1 width stage y) d)) (h d)
    _ = B (completedAdd hw0 hw1 width stage y (completedNeg hw0 hw1 width stage y)) d :=
      (completedInner_add_left hw0 hw1 width stage y (completedNeg hw0 hw1 width stage y) d).symm
    _ = RCzero := by rw [completedAdd_comm, completedNeg_add, completedInner_zero_left]
  exact (completedDist_zero_iff hw0 hw1 width stage x y).mp hd

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx) (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width stage (realScalarCauchy hw0 hw1 width stage s cs X) Y)
      (CReal.mul s (representativeInner hw0 hw1 width stage X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_smul_left hw0 hw1 width (s.approx n) (X.seq n).val (Y.seq n).val stage)
    (pairSequence_converges hw0 hw1 width stage (realScalarCauchy hw0 hw1 width stage s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges hw0 hw1 width stage X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (y : Completion hw0 hw1 width stage) :
    B (Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width stage s cs X)) y =
      RCmul (Quotient.mk crealSetoid s) (B (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (representativeInner_realScalar_left hw0 hw1 width stage s cs X Y)

theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width stage s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width stage t ct Y) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX,
    show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hs]

def completedRealSmul (s : CReal) (cs : QCauchy s.approx) :
    Completion hw0 hw1 width stage → Completion hw0 hw1 width stage :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width stage s cs X))
    (fun X Y h => realScalarCauchy_congr hw0 hw1 width stage s s cs cs (Equiv.refl s) X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul hw0 hw1 width stage s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width stage s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : Completion hw0 hw1 width stage) :
    B (completedRealSmul hw0 hw1 width stage s cs x) y = RCmul (Quotient.mk crealSetoid s) (B x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing hw0 hw1 width stage s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : Completion hw0 hw1 width stage) :
    B x (completedRealSmul hw0 hw1 width stage s cs y) = RCmul (Quotient.mk crealSetoid s) (B x y) := by
  rw [completedInner_symm hw0 hw1 width stage x, completedInner_realSmul_left,
    completedInner_symm hw0 hw1 width stage y x]

theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hs : Equiv s t) (x : Completion hw0 hw1 width stage) :
    completedRealSmul hw0 hw1 width stage s cs x = completedRealSmul hw0 hw1 width stage t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr hw0 hw1 width stage s t cs ct hs X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : Completion hw0 hw1 width stage) :
    completedRealSmul hw0 hw1 width stage (ofQ' q) cq x = completedSmul hw0 hw1 width stage q x := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]

theorem completedRealSmul_one (c : QCauchy cone.approx) (x : Completion hw0 hw1 width stage) :
    completedRealSmul hw0 hw1 width stage cone c x = x :=
  (completedRealSmul_ofQ' hw0 hw1 width stage 1 c x).trans (completedSmul_one hw0 hw1 width stage x)

theorem completedRealSmul_zero (c : QCauchy czero.approx) (x : Completion hw0 hw1 width stage) :
    completedRealSmul hw0 hw1 width stage czero c x = completedZero hw0 hw1 width stage :=
  (completedRealSmul_ofQ' hw0 hw1 width stage 0 c x).trans (completedSmul_zero hw0 hw1 width stage x)

theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : Completion hw0 hw1 width stage) :
    completedRealSmul hw0 hw1 width stage s cs (completedAdd hw0 hw1 width stage x y) =
      completedAdd hw0 hw1 width stage (completedRealSmul hw0 hw1 width stage s cs x)
        (completedRealSmul hw0 hw1 width stage s cs y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => smulSpan_add hw0 hw1 width stage (s.approx n) (X.seq n) (Y.seq n))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.rationalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completed_eq_of_pairings
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.representativeInner_realScalar_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.realScalarCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.realScalarCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedInner_realSmul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedInner_realSmul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_ofQ'
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar.completedRealSmul_add
