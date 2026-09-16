/-
# Actual rational linear operations on the reflected Cauchy carrier

The original squared-distance addition and scaling estimates provide the
existing modulus-bearing completion constructors. Pointwise equality of
pairings supplies nullity, so signed-list algebra descends without asserting
literal equality of different presentations or selecting representatives.

Only the generic scalar tolerance is reused from the earlier plaquette
module. The carrier, distance and operations here are the SAME fixed-spatial
original ones. Completed bilinearity, scalar extension and completeness are
separate consumers; no physical mass gap or continuum claim is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

def addition : (D).BinaryQuadraticLipschitz where
  toFun := addSpan
  contraction := distSq_add hw0 hw1 width stage

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smulSpan c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (c*c)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    exact leEv_trans (leEv_of_equiv (distSq_smul hw0 hw1 width stage c x y))
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def completedAdd : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage →
    Completion hw0 hw1 width stage :=
  (addition hw0 hw1 width stage).completionMap

def completedSmul (c : Q') : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage :=
  (scalarContinuous hw0 hw1 width stage c).completionMap

def completedNeg : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage :=
  completedSmul hw0 hw1 width stage (-1)

/-- The actual completed addition retains both supplied quarter-tolerance rates. -/
theorem addition_cauchy_modulus (X Y : (D).Cauchy) (epsilon : Q') :
    ((addition hw0 hw1 width stage).mapCauchy X Y).modulus epsilon =
      max (X.modulus (HalfPow.half*(HalfPow.half*epsilon)))
        (Y.modulus (HalfPow.half*(HalfPow.half*epsilon))) := rfl

theorem scalar_cauchy_modulus (c epsilon : Q') (X : (D).Cauchy) :
    ((scalarContinuous hw0 hw1 width stage c).mapCauchy X).modulus epsilon =
      X.modulus (scalarTolerance c epsilon) := rfl

/-- Pairing equality supplies a zero-modulus closeness witness, not a new relation. -/
def closeOfPointwisePairingEq {X Y : (D).Cauchy}
    (h : ∀ n, PairingEq hw0 hw1 width stage (X.seq n) (Y.seq n)) : (D).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => null_of_pairingEq hw0 hw1 width stage (h n))

theorem completion_eq_of_pointwise {X Y : (D).Cauchy}
    (h : ∀ n, PairingEq hw0 hw1 width stage (X.seq n) (Y.seq n)) :
    Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y :=
  Quotient.sound ⟨closeOfPointwisePairingEq hw0 hw1 width stage h⟩

theorem completedAdd_embedSpan (x y : PhysicalSpan width) :
    completedAdd hw0 hw1 width stage (embedSpan hw0 hw1 width stage x)
        (embedSpan hw0 hw1 width stage y) =
      embedSpan hw0 hw1 width stage (addSpan x y) := rfl

theorem completedSmul_embedSpan (c : Q') (x : PhysicalSpan width) :
    completedSmul hw0 hw1 width stage c (embedSpan hw0 hw1 width stage x) =
      embedSpan hw0 hw1 width stage (smulSpan c x) := rfl

theorem completedAdd_assoc (x y z : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (completedAdd hw0 hw1 width stage x y) z =
      completedAdd hw0 hw1 width stage x (completedAdd hw0 hw1 width stage y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => addSpan_assoc hw0 hw1 width stage (X.seq n) (Y.seq n) (Z.seq n))

theorem completedAdd_comm (x y : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage x y = completedAdd hw0 hw1 width stage y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => addSpan_comm hw0 hw1 width stage (X.seq n) (Y.seq n))

theorem completedZero_add (x : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (completedZero hw0 hw1 width stage) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => zero_addSpan hw0 hw1 width stage (X.seq n))

theorem completedNeg_add (x : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (completedNeg hw0 hw1 width stage x) x =
      completedZero hw0 hw1 width stage := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => neg_addSpan hw0 hw1 width stage (X.seq n))

theorem completedSmul_one (x : Completion hw0 hw1 width stage) :
    completedSmul hw0 hw1 width stage 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => smulSpan_one hw0 hw1 width stage (X.seq n))

theorem completedSmul_zero (x : Completion hw0 hw1 width stage) :
    completedSmul hw0 hw1 width stage 0 x = completedZero hw0 hw1 width stage := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => smulSpan_zero hw0 hw1 width stage (X.seq n))

theorem completedSmul_mul (a b : Q') (x : Completion hw0 hw1 width stage) :
    completedSmul hw0 hw1 width stage a (completedSmul hw0 hw1 width stage b x) =
      completedSmul hw0 hw1 width stage (a*b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => pairingEq_symm hw0 hw1 width stage
      (smulSpan_mul hw0 hw1 width stage a b (X.seq n)))

theorem completedSmul_add (c : Q') (x y : Completion hw0 hw1 width stage) :
    completedSmul hw0 hw1 width stage c (completedAdd hw0 hw1 width stage x y) =
      completedAdd hw0 hw1 width stage (completedSmul hw0 hw1 width stage c x)
        (completedSmul hw0 hw1 width stage c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => smulSpan_add hw0 hw1 width stage c (X.seq n) (Y.seq n))

theorem completedAdd_smul (a b : Q') (x : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (completedSmul hw0 hw1 width stage a x)
        (completedSmul hw0 hw1 width stage b x) =
      completedSmul hw0 hw1 width stage (a+b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => pairingEq_symm hw0 hw1 width stage
      (add_smulSpan hw0 hw1 width stage a b (X.seq n)))

theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : Completion hw0 hw1 width stage) :
    completedSmul hw0 hw1 width stage a x = completedSmul hw0 hw1 width stage b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width stage
    (fun n => smulSpan_congr hw0 hw1 width stage h (X.seq n))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.addition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.scalarContinuous
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedAdd
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedNeg
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.addition_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.scalar_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.closeOfPointwisePairingEq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completion_eq_of_pointwise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedAdd_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedAdd_assoc
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedAdd_comm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedZero_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedNeg_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedAdd_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear.completedSmul_congr
