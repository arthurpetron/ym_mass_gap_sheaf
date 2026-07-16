/-
# A quotient-free strict-cylinder OS reflection seminorm

This file packages the fixed-root limiting Gram quadratic as a functional on
finite half-space cylinder-vector presentations.  Two presentations denote
the same vector when their coefficients agree, as exact rationals, after
pullback to every complete lower-half support.  This semantic relation is an
equivalence, the limiting reflection quadratic descends through it, and the
append chart implements presentation-level addition compatibly.

Thus the strict reflected construction now exposes a presentation-independent
positive quadratic form on the constructive finite cylinder algebra, without
forming a quotient or appealing to choice.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact coefficient congruence for finite support Grams -/

theorem finiteJointQuadratic_coefficient_eqv
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q')
    (hcoefficient : ∀ state, state ∈ states →
      leftCoefficient state ≈ rightCoefficient state) :
    finiteJointQuadratic states leftCoefficient joint ≈
      finiteJointQuadratic states rightCoefficient joint := by
  unfold finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  have hproduct :
      leftCoefficient left * leftCoefficient right ≈
        rightCoefficient left * rightCoefficient right :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (hcoefficient left hleft))
      (Q'.mul_eqv_congr_left _ _ _
        (hcoefficient right hright))
  exact Q'.mul_eqv_congr_right _ _ _ hproduct

theorem centralNormalizedSupportReflectionQuadratic_coefficient_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q')
    (hcoefficient : ∀ support,
      leftCoefficient support ≈ rightCoefficient support) :
    centralNormalizedSupportReflectionQuadratic
        coupling hcoupling cutoff half leftCoefficient ≈
      centralNormalizedSupportReflectionQuadratic
        coupling hcoupling cutoff half rightCoefficient := by
  unfold centralNormalizedSupportReflectionQuadratic Q'.divPos
    centralSupportReflectionQuadratic
  apply Q'.mul_eqv_congr_right
  exact finiteJointQuadratic_coefficient_eqv
    (centralHalfSupportSpace half) leftCoefficient rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
    (fun support _ => hcoefficient support)

/-! ## 2. Cylinder-vector presentations and their semantic relation -/

structure StrictJointCylinderVector (base : Nat) where
  roots : List (List Nat)
  rootsCanonical : ∀ root, root ∈ roots →
    root ∈ canonicalSurfacePolymers base
  coefficient : List Bool → Q'

/-- Equality of represented cylinder vectors after pullback to every complete
support.  `Q'.eqv` is used rather than representation equality of rationals. -/
def StrictJointCylinderVectorEquivalent {base : Nat}
    (left right : StrictJointCylinderVector base) : Prop :=
  ∀ radius support,
    left.coefficient
        (centralStrictLocalQueryCode radius base left.roots support) ≈
      right.coefficient
        (centralStrictLocalQueryCode radius base right.roots support)

theorem strictJointCylinderVectorEquivalent_refl
    {base : Nat} (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent vector vector := by
  intro radius support
  exact Q'.eqv_refl _

theorem strictJointCylinderVectorEquivalent_symm
    {base : Nat} {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalent left right) :
    StrictJointCylinderVectorEquivalent right left := by
  intro radius support
  exact Q'.eqv_symm (h radius support)

theorem strictJointCylinderVectorEquivalent_trans
    {base : Nat} {first middle last : StrictJointCylinderVector base}
    (hfirst : StrictJointCylinderVectorEquivalent first middle)
    (hlast : StrictJointCylinderVectorEquivalent middle last) :
    StrictJointCylinderVectorEquivalent first last := by
  intro radius support
  exact Q'.eqv_trans _ _ _
    (hfirst radius support) (hlast radius support)

theorem strictJointCylinderVectorEquivalent_equivalence
    (base : Nat) :
    Equivalence
      (@StrictJointCylinderVectorEquivalent base) :=
  ⟨strictJointCylinderVectorEquivalent_refl,
    @strictJointCylinderVectorEquivalent_symm base,
    @strictJointCylinderVectorEquivalent_trans base⟩

/-! ## 3. Descent of the limiting reflection quadratic -/

def StrictJointCylinderVector.reflectionQuadratic
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) : CReal :=
  centralNormalizedStrictJointFixedQuadraticLimit
    coupling hcoupling hle vector.rootsCanonical vector.coefficient

@[simp] theorem StrictJointCylinderVector.reflectionQuadratic_approx
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (vector : StrictJointCylinderVector base) :
    (vector.reflectionQuadratic hcoupling hle).approx stage =
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base vector.roots vector.coefficient stage := rfl

theorem strictJointCylinderVectorSequence_eqv_of_equivalent
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right)
    (stage : Nat) :
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base left.roots left.coefficient stage ≈
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base right.roots right.coefficient stage := by
  have hleft :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base left.roots left.coefficient stage
  have hright :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base right.roots right.coefficient stage
  have hsupport :=
    centralNormalizedSupportReflectionQuadratic_coefficient_eqv
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff base stage)
      (strictQueryBase base + stage)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode
          (strictQueryBase base + stage) base left.roots)
        left.coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode
          (strictQueryBase base + stage) base right.roots)
        right.coefficient)
      (fun support => hequivalent
        (strictQueryBase base + stage) support)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hsupport (Q'.eqv_symm hright))

/-- The CReal reflection quadratic descends through semantic presentation
equivalence. -/
theorem StrictJointCylinderVector.reflectionQuadratic_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right) :
    CReal.Equiv
      (left.reflectionQuadratic hcoupling hle)
      (right.reflectionQuadratic hcoupling hle) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderVectorSequence_eqv_of_equivalent
    coupling hcoupling hequivalent stage
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

/-- Presentation-independent strict cylinder reflection positivity. -/
theorem StrictJointCylinderVector.reflectionQuadratic_geRat_zero
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    ExpPos.geRat (vector.reflectionQuadratic hcoupling hle) 0 :=
  centralNormalizedStrictJointFixedQuadraticLimit_reflectionPositive
    hcoupling hle vector.rootsCanonical vector.coefficient

/-! ## 4. A quotient-free additive presentation algebra -/

def StrictJointCylinderVector.add
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVector base where
  roots := left.roots ++ right.roots
  rootsCanonical := canonicalRoots_append
    left.rootsCanonical right.rootsCanonical
  coefficient := fun bits =>
    left.coefficient
        (leftAppendStrictJointFingerprint left.roots.length bits) +
      right.coefficient
        (rightAppendStrictJointFingerprint left.roots.length bits)

theorem StrictJointCylinderVector.add_coefficient_code
    {base : Nat} (left right : StrictJointCylinderVector base)
    (radius : Nat) (support : List Nat) :
    (left.add right).coefficient
        (centralStrictLocalQueryCode radius base
          (left.add right).roots support) ≈
      left.coefficient
          (centralStrictLocalQueryCode radius base left.roots support) +
        right.coefficient
          (centralStrictLocalQueryCode radius base right.roots support) := by
  change
    left.coefficient
          (leftAppendStrictJointFingerprint left.roots.length
            (centralStrictLocalQueryCode radius base
              (left.roots ++ right.roots) support)) +
        right.coefficient
          (rightAppendStrictJointFingerprint left.roots.length
            (centralStrictLocalQueryCode radius base
              (left.roots ++ right.roots) support)) ≈ _
  have hleft := strictJointFingerprintRecoding_append_left
    base left.roots right.roots radius support
  have hright := strictJointFingerprintRecoding_append_right
    base left.roots right.roots radius support
  rw [← hleft, ← hright]
  exact Q'.eqv_refl _

theorem strictJointCylinderVectorEquivalent_add
    {base : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    StrictJointCylinderVectorEquivalent
      (left.add right) (left'.add right') := by
  intro radius support
  exact Q'.eqv_trans _ _ _
    (StrictJointCylinderVector.add_coefficient_code
      left right radius support)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (hleft radius support) (hright radius support))
      (Q'.eqv_symm
        (StrictJointCylinderVector.add_coefficient_code
          left' right' radius support)))

def StrictJointCylinderVector.smul
    {base : Nat} (scalar : Q')
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVector base where
  roots := vector.roots
  rootsCanonical := vector.rootsCanonical
  coefficient := fun bits => scalar * vector.coefficient bits

theorem strictJointCylinderVectorEquivalent_smul
    {base : Nat} (scalar : Q')
    {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right) :
    StrictJointCylinderVectorEquivalent
      (left.smul scalar) (right.smul scalar) := by
  intro radius support
  exact Q'.mul_eqv_congr_left _ _ _
    (hequivalent radius support)

/-- The cylinder OS2 statement exposed by this construction: every finite
strict half-space cylinder vector has a nonnegative limiting reflected norm. -/
def StrictJointCylinderReflectionPositive
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) : Prop :=
  ∀ {base : Nat} (vector : StrictJointCylinderVector base),
    ExpPos.geRat (vector.reflectionQuadratic hcoupling hle) 0

theorem strictJointCylinderReflectionPositive_holds
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    StrictJointCylinderReflectionPositive hcoupling hle := by
  intro base vector
  exact vector.reflectionQuadratic_geRat_zero hcoupling hle

#print axioms finiteJointQuadratic_coefficient_eqv
#print axioms centralNormalizedSupportReflectionQuadratic_coefficient_eqv
#print axioms strictJointCylinderVectorEquivalent_equivalence
#print axioms strictJointCylinderVectorSequence_eqv_of_equivalent
#print axioms StrictJointCylinderVector.reflectionQuadratic_equiv
#print axioms StrictJointCylinderVector.reflectionQuadratic_geRat_zero
#print axioms strictJointCylinderVectorEquivalent_add
#print axioms strictJointCylinderVectorEquivalent_smul
#print axioms strictJointCylinderReflectionPositive_holds

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
