/-
# The raw strict-cylinder coefficient l1 norm does not descend

An adjacent duplicate root forces the first two genuine fingerprint bits to
agree.  A coefficient supported only on the impossible word `[true, false]`
therefore represents the zero cylinder observable, although its raw finite
coefficient `l1` norm is one.  Thus the signed clustering estimate cannot be
made norm-relative by bounding this presentation norm directly by the OS
reflection seminorm.

The next normed object must first discard unreachable fingerprint modes (and
then quotient any remaining Gram nullspace).
-/

import YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation

namespace YMGap.Continuum.Z4StrictJointCoefficientL1Fence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder

local infix:50 " ≈ " => Q'.eqv

/-- Presentation-level coefficient norm used by the signed covariance tail. -/
def strictJointVectorCoefficientL1
    {base : Nat} (vector : StrictJointCylinderVector base) : Q' :=
  coefficientL1
    (strictJointFingerprintSpace vector.roots.length)
    vector.coefficient

/-- A coefficient carried by the impossible unequal duplicate word. -/
def duplicateGhostCoefficient (bits : List Bool) : Q' :=
  if bits = [true, false] then 1 else 0

theorem duplicateGhostCoefficient_duplicateHead_zero (bits : List Bool) :
    duplicateGhostCoefficient
      (duplicateHeadStrictJointFingerprint bits) = 0 := by
  cases bits with
  | nil => rfl
  | cons bit tail =>
      cases bit <;>
        simp [duplicateGhostCoefficient,
          duplicateHeadStrictJointFingerprint]

private def duplicateRootCanonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ [root, root] →
      target ∈ canonicalSurfacePolymers base :=
  canonicalRoots_cons hroot
    (canonicalRoots_cons hroot
      (fun _target htarget => (List.not_mem_nil htarget).elim))

/-- Nonzero raw coefficient table representing the zero observable. -/
def duplicateGhostVector
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    StrictJointCylinderVector base where
  roots := [root, root]
  rootsCanonical := duplicateRootCanonical hroot
  coefficient := duplicateGhostCoefficient

/-- Zero coefficient table on the same duplicate-root chart. -/
def duplicateZeroVector
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    StrictJointCylinderVector base where
  roots := [root, root]
  rootsCanonical := duplicateRootCanonical hroot
  coefficient := fun _ => 0

/-- The ghost and zero presentations denote the same strict cylinder vector. -/
theorem duplicateGhostVector_equivalent_zero
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    StrictJointCylinderVectorEquivalent
      (duplicateGhostVector root hroot)
      (duplicateZeroVector root hroot) := by
  intro radius support
  change duplicateGhostCoefficient
      (centralStrictLocalQueryCode radius base [root, root] support) ≈ 0
  rw [centralStrictLocalQueryCode_duplicateHead]
  exact Q'.eqv_of_eq
    (duplicateGhostCoefficient_duplicateHead_zero
      (centralStrictLocalQueryCode radius base [root] support))

/-- The ghost presentation has raw coefficient norm one. -/
theorem duplicateGhostVector_coefficientL1_eqv_one
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointVectorCoefficientL1
      (duplicateGhostVector root hroot) ≈ 1 := by
  change coefficientL1
      (strictJointFingerprintSpace 2) duplicateGhostCoefficient ≈ 1
  unfold coefficientL1 strictJointFingerprintSpace duplicateGhostCoefficient
    listQSum Q'.abs
  decide

/-- The semantically equal zero presentation has raw coefficient norm zero. -/
theorem duplicateZeroVector_coefficientL1_eqv_zero
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointVectorCoefficientL1
      (duplicateZeroVector root hroot) ≈ 0 := by
  change coefficientL1
      (strictJointFingerprintSpace 2) (fun _ => (0 : Q')) ≈ 0
  unfold coefficientL1 strictJointFingerprintSpace listQSum Q'.abs
  decide

/-- The raw coefficient `l1` norm is not invariant under semantic equivalence. -/
theorem strictJointVectorCoefficientL1_not_semantic_invariant
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    ¬ (strictJointVectorCoefficientL1
          (duplicateGhostVector root hroot) ≈
        strictJointVectorCoefficientL1
          (duplicateZeroVector root hroot)) := by
  intro hinvariant
  have honeZero : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (duplicateGhostVector_coefficientL1_eqv_one root hroot))
      (Q'.eqv_trans _ _ _ hinvariant
        (duplicateZeroVector_coefficientL1_eqv_zero root hroot))
  exact (by decide : ¬ ((1 : Q') ≈ 0)) honeZero

/-- Consequently the reflection quadratic cannot repair the raw coefficient
norm: the ghost has the same quadratic as the zero vector. -/
theorem duplicateGhostVector_reflectionQuadratic_equiv_zero
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    {base : Nat} (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      ((duplicateGhostVector root hroot).reflectionQuadratic
        hcoupling hle)
      ((duplicateZeroVector root hroot).reflectionQuadratic
        hcoupling hle) :=
  StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle (duplicateGhostVector_equivalent_zero root hroot)

#print axioms duplicateGhostVector_equivalent_zero
#print axioms duplicateGhostVector_coefficientL1_eqv_one
#print axioms strictJointVectorCoefficientL1_not_semantic_invariant
#print axioms duplicateGhostVector_reflectionQuadratic_equiv_zero

end YMGap.Continuum.Z4StrictJointCoefficientL1Fence
