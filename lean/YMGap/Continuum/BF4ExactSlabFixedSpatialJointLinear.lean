/-
# Rational linear operations on the actual joint completion

The finite-stage signed-span algebra and squared-distance estimates pass to
the cutoff-removed joint seminorm before the generic explicit-modulus
completion machinery is applied.  Thus every operation below acts on the
existing `JointCompletion`; no stage-indexed completion is identified with it.

Pointwise algebra is tested at every finite cutoff stage.  Its finite pairing
nullity converges to nullity for the joint distance, giving a constructive
closeness witness on Cauchy representatives.  This supplies rational linear
laws only; it adds no analytic estimate or continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan distSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

/-- Addition satisfies the same quadratic Lipschitz estimate after the actual
cutoff limit, not by transport from a stage-indexed completion. -/
theorem jointDistSq_add (x x' y y' : PhysicalSpan width) :
    leEv (jointDistSq hw0 hw1 width (addSpan x y) (addSpan x' y'))
      (add (add (jointDistSq hw0 hw1 width x x') (jointDistSq hw0 hw1 width x x'))
        (add (jointDistSq hw0 hw1 width y y') (jointDistSq hw0 hw1 width y y'))) :=
  leEv_of_convergesTo_le
    (distSq_converges_joint hw0 hw1 width (addSpan x y) (addSpan x' y'))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width x x')
        (distSq_converges_joint hw0 hw1 width x x'))
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width y y')
        (distSq_converges_joint hw0 hw1 width y y')))
    (fun stage => distSq_add hw0 hw1 width stage x x' y y')

/-- Rational scaling has its exact squared factor in the actual joint limit. -/
theorem jointDistSq_smul (c : Q') (x y : PhysicalSpan width) :
    Equiv (jointDistSq hw0 hw1 width (smulSpan c x) (smulSpan c y))
      (mul (ofQ' (c*c)) (jointDistSq hw0 hw1 width x y)) :=
  Equiv_of_limit_of_equal
    (fun stage => distSq_smul hw0 hw1 width stage c x y)
    (distSq_converges_joint hw0 hw1 width (smulSpan c x) (smulSpan c y))
    (convergesTo_const_mul (ofQ' (c*c)) (distSq_converges_joint hw0 hw1 width x y))

def addition : (D).BinaryQuadraticLipschitz where
  toFun := addSpan
  contraction := jointDistSq_add hw0 hw1 width

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smulSpan c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (c*c)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    exact leEv_trans (leEv_of_equiv (jointDistSq_smul hw0 hw1 width c x y))
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def completedAdd : JointCompletion hw0 hw1 width → JointCompletion hw0 hw1 width →
    JointCompletion hw0 hw1 width :=
  (addition hw0 hw1 width).completionMap

def completedSmul (c : Q') : JointCompletion hw0 hw1 width → JointCompletion hw0 hw1 width :=
  (scalarContinuous hw0 hw1 width c).completionMap

def completedZero : JointCompletion hw0 hw1 width :=
  jointEmbedSpan hw0 hw1 width (zero width)

def completedNeg : JointCompletion hw0 hw1 width → JointCompletion hw0 hw1 width :=
  completedSmul hw0 hw1 width (-1)

def completedSub (x y : JointCompletion hw0 hw1 width) : JointCompletion hw0 hw1 width :=
  completedAdd hw0 hw1 width x (completedNeg hw0 hw1 width y)

/-- The generic addition map retains both explicit quarter-tolerance moduli. -/
theorem addition_cauchy_modulus (X Y : (D).Cauchy) (epsilon : Q') :
    ((addition hw0 hw1 width).mapCauchy X Y).modulus epsilon =
      max (X.modulus (HalfPow.half*(HalfPow.half*epsilon)))
        (Y.modulus (HalfPow.half*(HalfPow.half*epsilon))) := rfl

theorem scalar_cauchy_modulus (c epsilon : Q') (X : (D).Cauchy) :
    ((scalarContinuous hw0 hw1 width c).mapCauchy X).modulus epsilon =
      X.modulus (scalarTolerance c epsilon) := rfl

/-- Finite-stage pairing equality at every cutoff gives joint-limit nullity at
each sequence index, hence a zero-modulus completion closeness witness. -/
def closeOfPointwisePairingEq {X Y : (D).Cauchy}
    (h : ∀ n stage, PairingEq hw0 hw1 width stage (X.seq n) (Y.seq n)) : (D).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => Equiv_of_limit_of_equal
      (fun stage => null_of_pairingEq hw0 hw1 width stage (h n stage))
      (distSq_converges_joint hw0 hw1 width (X.seq n) (Y.seq n))
      (convergesTo_const czero))

theorem completion_eq_of_pointwise {X Y : (D).Cauchy}
    (h : ∀ n stage, PairingEq hw0 hw1 width stage (X.seq n) (Y.seq n)) :
    Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y :=
  Quotient.sound ⟨closeOfPointwisePairingEq hw0 hw1 width h⟩

theorem completedAdd_embedSpan (x y : PhysicalSpan width) :
    completedAdd hw0 hw1 width (jointEmbedSpan hw0 hw1 width x)
        (jointEmbedSpan hw0 hw1 width y) =
      jointEmbedSpan hw0 hw1 width (addSpan x y) := rfl

theorem completedSmul_embedSpan (c : Q') (x : PhysicalSpan width) :
    completedSmul hw0 hw1 width c (jointEmbedSpan hw0 hw1 width x) =
      jointEmbedSpan hw0 hw1 width (smulSpan c x) := rfl

theorem completedZero_embedSpan :
    completedZero hw0 hw1 width = jointEmbedSpan hw0 hw1 width (zero width) := rfl

theorem completedNeg_embedSpan (x : PhysicalSpan width) :
    completedNeg hw0 hw1 width (jointEmbedSpan hw0 hw1 width x) =
      jointEmbedSpan hw0 hw1 width (smulSpan (-1) x) := rfl

theorem completedSub_embedSpan (x y : PhysicalSpan width) :
    completedSub hw0 hw1 width (jointEmbedSpan hw0 hw1 width x)
        (jointEmbedSpan hw0 hw1 width y) =
      jointEmbedSpan hw0 hw1 width (addSpan x (smulSpan (-1) y)) := rfl

theorem completedAdd_assoc (x y z : JointCompletion hw0 hw1 width) :
    completedAdd hw0 hw1 width (completedAdd hw0 hw1 width x y) z =
      completedAdd hw0 hw1 width x (completedAdd hw0 hw1 width y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => addSpan_assoc hw0 hw1 width stage (X.seq n) (Y.seq n) (Z.seq n))

theorem completedAdd_comm (x y : JointCompletion hw0 hw1 width) :
    completedAdd hw0 hw1 width x y = completedAdd hw0 hw1 width y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => addSpan_comm hw0 hw1 width stage (X.seq n) (Y.seq n))

theorem completedZero_add (x : JointCompletion hw0 hw1 width) :
    completedAdd hw0 hw1 width (completedZero hw0 hw1 width) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => zero_addSpan hw0 hw1 width stage (X.seq n))

theorem completedNeg_add (x : JointCompletion hw0 hw1 width) :
    completedAdd hw0 hw1 width (completedNeg hw0 hw1 width x) x =
      completedZero hw0 hw1 width := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => neg_addSpan hw0 hw1 width stage (X.seq n))

theorem completedSmul_one (x : JointCompletion hw0 hw1 width) :
    completedSmul hw0 hw1 width 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => smulSpan_one hw0 hw1 width stage (X.seq n))

theorem completedSmul_zero (x : JointCompletion hw0 hw1 width) :
    completedSmul hw0 hw1 width 0 x = completedZero hw0 hw1 width := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => smulSpan_zero hw0 hw1 width stage (X.seq n))

theorem completedSmul_mul (a b : Q') (x : JointCompletion hw0 hw1 width) :
    completedSmul hw0 hw1 width a (completedSmul hw0 hw1 width b x) =
      completedSmul hw0 hw1 width (a*b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => pairingEq_symm hw0 hw1 width stage
      (smulSpan_mul hw0 hw1 width stage a b (X.seq n)))

theorem completedSmul_add (c : Q') (x y : JointCompletion hw0 hw1 width) :
    completedSmul hw0 hw1 width c (completedAdd hw0 hw1 width x y) =
      completedAdd hw0 hw1 width (completedSmul hw0 hw1 width c x)
        (completedSmul hw0 hw1 width c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => smulSpan_add hw0 hw1 width stage c (X.seq n) (Y.seq n))

theorem completedAdd_smul (a b : Q') (x : JointCompletion hw0 hw1 width) :
    completedAdd hw0 hw1 width (completedSmul hw0 hw1 width a x)
        (completedSmul hw0 hw1 width b x) =
      completedSmul hw0 hw1 width (a+b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => pairingEq_symm hw0 hw1 width stage
      (add_smulSpan hw0 hw1 width stage a b (X.seq n)))

theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : JointCompletion hw0 hw1 width) :
    completedSmul hw0 hw1 width a x = completedSmul hw0 hw1 width b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise hw0 hw1 width
    (fun n stage => smulSpan_congr hw0 hw1 width stage h (X.seq n))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.jointDistSq_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.jointDistSq_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.addition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.scalarContinuous
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedAdd
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedNeg
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.addition_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.scalar_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.closeOfPointwisePairingEq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completion_eq_of_pointwise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedAdd_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedZero_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedNeg_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSub_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedAdd_assoc
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedAdd_comm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedZero_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedNeg_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedAdd_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear.completedSmul_congr
