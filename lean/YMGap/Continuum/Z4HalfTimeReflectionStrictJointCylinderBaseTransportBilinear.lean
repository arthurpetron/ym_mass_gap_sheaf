/-
# Bilinear isometry of strict-cylinder base transport

Canonical zero-extension to a larger source box was already proved to
preserve the limiting reflection quadratic.  Here that diagonal result is
polarized constructively.  First, base transport is shown to commute exactly
with the quotient-free presentation addition and rational scaling.  The
polarized reflection form then gives the full two-vector isometry.

This is the compatibility needed to place all base-indexed strict-cylinder
carriers in one isometric direct system.  It does not assert time-translation
self-adjointness.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
import YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem strictJointCylinderVector_ext_local
    {base : Nat} {left right : StrictJointCylinderVector base}
    (hroots : left.roots = right.roots)
    (hcoefficient : left.coefficient = right.coefficient) :
    left = right := by
  obtain ⟨leftRoots, leftCanonical, leftCoefficient⟩ := left
  obtain ⟨rightRoots, rightCanonical, rightCoefficient⟩ := right
  simp only at hroots hcoefficient
  subst rightRoots
  subst rightCoefficient
  rfl

/-- Canonical base transport commutes exactly with presentation addition. -/
theorem boxTransportStrictJointCylinderVector_add
    {base : Nat} (padding : Nat)
    (left right : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector
        (Nat.le_add_right base padding) (left.add right) =
      (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base padding) left).add
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base padding) right) := by
  apply strictJointCylinderVector_ext_local
  · exact List.map_append
  · funext bits
    change
      left.coefficient
          (leftAppendStrictJointFingerprint left.roots.length bits) +
        right.coefficient
          (rightAppendStrictJointFingerprint left.roots.length bits) =
      left.coefficient
          (leftAppendStrictJointFingerprint
            (transportedCylinderRoots base (base + padding)
              left.roots).length bits) +
        right.coefficient
          (rightAppendStrictJointFingerprint
            (transportedCylinderRoots base (base + padding)
              left.roots).length bits)
    unfold transportedCylinderRoots
    rw [List.length_map]

/-- Canonical base transport commutes exactly with rational scaling. -/
theorem boxTransportStrictJointCylinderVector_smul
    {base : Nat} (padding : Nat) (scalar : Q')
    (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector
        (Nat.le_add_right base padding) (vector.smul scalar) =
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base padding) vector).smul scalar := by
  apply strictJointCylinderVector_ext_local <;> rfl

private theorem transportedCylinderRoots_self
    {base : Nat} (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    transportedCylinderRoots base base roots = roots := by
  induction roots with
  | nil => rfl
  | cons root rest inductionHypothesis =>
      simp only [transportedCylinderRoots, List.map_cons]
      rw [transportPolymer_self_of_canonical
        (hroots root List.mem_cons_self)]
      have hrest := inductionHypothesis (fun target htarget =>
        hroots target (List.mem_cons_of_mem root htarget))
      unfold transportedCylinderRoots at hrest
      exact congrArg (List.cons root) hrest

/-- Transport along the reflexive base inequality is the identity vector. -/
theorem boxTransportStrictJointCylinderVector_refl
    {base : Nat} (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector (Nat.le_refl base) vector =
      vector := by
  apply strictJointCylinderVector_ext_local
  · exact transportedCylinderRoots_self vector.roots vector.rootsCanonical
  · rfl

/-- Successive canonical base transports equal the direct transport. -/
theorem boxTransportStrictJointCylinderVector_trans
    {base middle outer : Nat}
    (hbaseMiddle : base ≤ middle) (hmiddleOuter : middle ≤ outer)
    (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hmiddleOuter
        (boxTransportStrictJointCylinderVector hbaseMiddle vector) =
      boxTransportStrictJointCylinderVector
        (Nat.le_trans hbaseMiddle hmiddleOuter) vector := by
  apply strictJointCylinderVector_ext_local
  · exact transportedCylinderRoots_trans
      hbaseMiddle hmiddleOuter vector.rootsCanonical
  · rfl

/-- The indexed time-translation action commutes exactly with canonical base
transport.  This is the commuting square required for descent to the
isometric direct system. -/
theorem timeTranslate_boxTransportStrictJointCylinderVector
    {base outer : Nat} (hbaseOuter : base ≤ outer)
    (shift : Nat) (vector : StrictJointCylinderVector base) :
    timeTranslateStrictJointCylinderVector shift
        (boxTransportStrictJointCylinderVector hbaseOuter vector) =
      boxTransportStrictJointCylinderVector
        (Nat.add_le_add_right hbaseOuter shift)
        (timeTranslateStrictJointCylinderVector shift vector) := by
  apply strictJointCylinderVector_ext_local
  · exact (transportedCylinderRoots_timeShift
      hbaseOuter vector.rootsCanonical).symm
  · rfl

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

/-- Canonical source-box transport is an isometry for the full polarized
strict-cylinder reflection form, not only for its diagonal quadratic. -/
theorem boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (padding : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base padding) left)
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base padding) right))
      (strictJointCylinderReflectionBilinear hcoupling hle left right) := by
  let transportedLeft := boxTransportStrictJointCylinderVector
    (Nat.le_add_right base padding) left
  let transportedRight := boxTransportStrictJointCylinderVector
    (Nat.le_add_right base padding) right
  have hplus :=
    boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv
      hcoupling hle padding (left.add right)
  rw [boxTransportStrictJointCylinderVector_add] at hplus
  have hminus :=
    boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv
      hcoupling hle padding (left.add (right.smul (-1)))
  rw [boxTransportStrictJointCylinderVector_add,
    boxTransportStrictJointCylinderVector_smul] at hminus
  have hpolarized : CReal.Equiv
      (CReal.add
        ((transportedLeft.add transportedRight).reflectionQuadratic
          hcoupling hle)
        (CReal.neg
          ((transportedLeft.add (transportedRight.smul (-1))).reflectionQuadratic
            hcoupling hle)))
      (CReal.add
        ((left.add right).reflectionQuadratic hcoupling hle)
        (CReal.neg
          ((left.add (right.smul (-1))).reflectionQuadratic
            hcoupling hle))) := by
    exact CReal.Equiv.trans
      (CReal.add_congr_left hplus)
      (CReal.add_congr_right (CReal.neg_congr hminus))
  exact creal_mul_congr_right_local hpolarized

#print axioms boxTransportStrictJointCylinderVector_add
#print axioms boxTransportStrictJointCylinderVector_smul
#print axioms boxTransportStrictJointCylinderVector_refl
#print axioms boxTransportStrictJointCylinderVector_trans
#print axioms timeTranslate_boxTransportStrictJointCylinderVector
#print axioms boxTransportStrictJointCylinderVector_reflectionBilinear_equiv

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
