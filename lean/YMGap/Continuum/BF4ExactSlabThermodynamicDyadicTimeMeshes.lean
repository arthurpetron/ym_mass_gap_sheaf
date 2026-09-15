/-
# Coherent positive dyadic time meshes on the ORIGINAL completion

The depth-zero generator is exactly the original T2; depth one is exactly
the previously constructed root S. Repeated explicit root transformations
construct every subsequent generator, and two finer steps equal one
coarser step on every original vector. Each finite mesh has a positive
symmetric contraction semigroup, fixes the same original unit, preserves
centering, and has constructed output representatives. Iterated doubling
proves exact refinement consistency. The coarsest mesh is pinned to the
pre-existing even geometric times, not just to an abstract semigroup.

These are coherent meshes, NOT yet a quotient-indexed dyadic/real-time
semigroup or continuity as time tends to zero. Every generator has the
same possible kernel as T2; zero kernel and geometric T1 identification
are not asserted. Physical-scale/continuum/Clay obligations stay open;
the original SU(2) nome and spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinSequenceWrap (eval01)
open YMGap.Continuum.UniformSquareRootPolynomial (rootSequence polynomial_nonnegative polynomial_abs_bound)
open YMGap.Continuum.UniformPolynomialRootTransform (IntervalSequence rootTransform)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction
  (rootAction rootAction_square rootAction_pairing rootAction_kernel)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction

local notation "point" X => Quotient.mk seminorm.completionSetoid X

def coordinateInterval : IntervalSequence where
  sequence := constantSequence [0,1]
  bounds := fun _ t ht h1 => ⟨Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv (eval01 t)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval01 t)) h1⟩

def originalRootInterval : IntervalSequence where
  sequence := rootSequence
  bounds := fun n t ht h1 => ⟨polynomial_nonnegative n t ht h1,
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) (polynomial_abs_bound n t ht h1)⟩

/-- Start with the SAME already-constructed S, not a new unpinned square-root choice. -/
def rootFamily : Nat → IntervalSequence
  | 0 => originalRootInterval
  | n+1 => rootTransform (rootFamily n)

def generatorSequence : Nat → IntervalSequence
  | 0 => coordinateInterval
  | n+1 => rootFamily n

def generator (depth : Nat) : Completion → Completion := sequenceAction (generatorSequence depth).sequence

theorem generator_zero (x : Completion) : generator 0 x=twoStepTransfer x :=
  (constantSequence_action [0,1] x).trans (operator_coordinate x)

theorem generator_one (x : Completion) : generator 1 x=rootAction x := rfl

theorem generator_square (depth : Nat) (x : Completion) :
    generator (depth+1) (generator (depth+1) x)=generator depth x := by
  cases depth with
  | zero => rw [generator_one,generator_one,generator_zero]; exact rootAction_square x
  | succ depth => exact transformedAction_square (rootFamily depth) x

theorem generator_pairing (depth : Nat) (x y : Completion) :
    completedInner (generator (depth+1) x) (generator (depth+1) y)=completedInner (generator depth x) y := by
  cases depth with
  | zero => rw [generator_one,generator_one,generator_zero]; exact rootAction_pairing x y
  | succ depth => exact transformedAction_pairing (rootFamily depth) x y

theorem generator_add (depth : Nat) (x y : Completion) :
    generator depth (completedAdd x y)=completedAdd (generator depth x) (generator depth y) := sequenceAction_add _ x y

theorem generator_smul (depth : Nat) (c : Q') (x : Completion) :
    generator depth (completedSmul c x)=completedSmul c (generator depth x) := sequenceAction_smul _ c x

theorem generator_symmetric (depth : Nat) (x y : Completion) :
    completedInner (generator depth x) y=completedInner x (generator depth y) := sequenceAction_symmetric _ x y

theorem generator_nonnegative (depth : Nat) (x : Completion) :
    RCnonneg (completedInner (generator depth x) x) := intervalAction_nonnegative (generatorSequence depth) x

theorem generator_contraction (depth : Nat) (x : Completion) :
    RCle (completedInner (generator depth x) (generator depth x)) (completedInner x x) :=
  intervalAction_contraction (generatorSequence depth) x

theorem generator_center (depth : Nat) (x : Completion) :
    generator depth (center x)=center (generator depth x) := intervalAction_center _ x

theorem rootFamily_unit : ∀ n,sequenceAction (rootFamily n).sequence completedUnit=completedUnit
  | 0 => originalRoot_unit
  | n+1 => transformedAction_preserves_fixed (rootFamily n) completedUnit (rootFamily_unit n)

theorem generator_unit (depth : Nat) : generator depth completedUnit=completedUnit := by
  cases depth with
  | zero => exact (generator_zero _).trans twoStepTransfer_unit
  | succ n => exact rootFamily_unit n

theorem rootFamily_kernel : ∀ n,∀ x : Completion,
    sequenceAction (rootFamily n).sequence x=completedZero ↔ twoStepTransfer x=completedZero
  | 0,x => rootAction_kernel x
  | n+1,x => (transformedAction_kernel (rootFamily n) x).trans (rootFamily_kernel n x)

theorem generator_kernel (depth : Nat) (x : Completion) :
    generator depth x=completedZero ↔ twoStepTransfer x=completedZero := by
  cases depth with
  | zero => rw [generator_zero]
  | succ n => exact rootFamily_kernel n x

def generatorCertificate (depth : Nat) (X : seminorm.Cauchy) :=
  sequenceActionCertificate (generatorSequence depth).sequence X

/-- Number of fine steps, on a fixed mesh. One depth-zero step is original geometric time two. -/
def time (depth : Nat) : Nat → Completion → Completion
  | 0,x => x
  | n+1,x => generator depth (time depth n x)

theorem time_add (depth m n : Nat) (x : Completion) :
    time depth (m+n) x=time depth m (time depth n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add,time,time,ih]

theorem time_commutes_generator (depth n : Nat) (x : Completion) :
    time depth n (generator depth x)=generator depth (time depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (generator depth) ih

theorem time_add_state (depth n : Nat) (x y : Completion) :
    time depth n (completedAdd x y)=completedAdd (time depth n x) (time depth n y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [time,ih,generator_add]; rfl

theorem time_smul (depth n : Nat) (c : Q') (x : Completion) :
    time depth n (completedSmul c x)=completedSmul c (time depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [time,ih,generator_smul]; rfl

theorem time_symmetric (depth n : Nat) (x y : Completion) :
    completedInner (time depth n x) y=completedInner x (time depth n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      change completedInner (generator depth (time depth n x)) y=completedInner x (generator depth (time depth n y))
      rw [generator_symmetric,ih,time_commutes_generator]

theorem time_nonnegative (depth : Nat) : ∀ n,∀ x : Completion, RCnonneg (completedInner (time depth n x) x)
  | 0,x => completedInner_nonnegative x
  | 1,x => generator_nonnegative depth x
  | n+2,x => by
      change RCnonneg (completedInner (generator depth (generator depth (time depth n x))) x)
      rw [generator_symmetric,← time_commutes_generator]
      exact time_nonnegative depth n (generator depth x)

theorem time_contraction (depth n : Nat) (x : Completion) :
    RCle (completedInner (time depth n x) (time depth n x)) (completedInner x x) := by
  induction n with
  | zero => exact RCle_refl _
  | succ n ih => exact RCle_trans (generator_contraction depth (time depth n x)) ih

theorem time_unit (depth n : Nat) : time depth n completedUnit=completedUnit := by
  induction n with
  | zero => rfl
  | succ n ih => rw [time,ih,generator_unit]

theorem time_center (depth n : Nat) (x : Completion) : time depth n (center x)=center (time depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [time,ih,generator_center]; rfl

/-- Two fine steps literally equal one coarse step, on the same original states. -/
theorem time_double (depth n : Nat) (x : Completion) : time (depth+1) (n+n) x=time depth n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show (n+1)+(n+1)=((n+n)+1)+1 by omega,time,time,generator_square,ih]
      rfl

def doubleSteps : Nat → Nat → Nat
  | 0,n => n
  | k+1,n => doubleSteps k n+doubleSteps k n

/-- Computed refinement count, with exact equality at every finite depth. -/
theorem time_refinement (depth refinement n : Nat) (x : Completion) :
    time (depth+refinement) (doubleSteps refinement n) x=time depth n x := by
  induction refinement with
  | zero => rfl
  | succ k ih =>
      change time ((depth+k)+1) (doubleSteps k n+doubleSteps k n) x=time depth n x
      rw [time_double,ih]

/-- The entire coarsest mesh is the pre-existing EVEN geometric-time semigroup. -/
theorem time_original_even (n : Nat) (x : Completion) : time 0 n x=completedTime (2*n) x := by
  induction n with
  | zero => exact (completedTime_zero x).symm
  | succ n ih => rw [time,generator_zero,ih]; exact twoStepTransfer_advance n x

theorem time_moments (depth n : Nat) (x y : Completion) :
    completedInner (time depth (n+n) x) y=completedInner (time depth n x) (time depth n y) := by
  rw [time_add,time_symmetric]

/-- Supplied original input representatives construct original output representatives at every mesh point. -/
def timeRepresentative (depth : Nat) : Nat → seminorm.Cauchy → seminorm.Cauchy
  | 0,X => X
  | n+1,X => actionRepresentative (generatorSequence depth).sequence (timeRepresentative depth n X)

theorem timeRepresentative_pin (depth n : Nat) (X : seminorm.Cauchy) :
    (point (timeRepresentative depth n X))=time depth n (point X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (point (actionRepresentative (generatorSequence depth).sequence (timeRepresentative depth n X)))=
        generator depth (time depth n (point X))
      rw [actionRepresentative_pin,ih]
      rfl

end YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.coordinateInterval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.originalRootInterval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.rootFamily
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generatorSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.rootFamily_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.rootFamily_kernel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generator_kernel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.generatorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_commutes_generator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_add_state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_double
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.doubleSteps
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_refinement
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_original_even
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.time_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.timeRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes.timeRepresentative_pin
