/-
# The doubled-time mixed OS bilinear frontier

The geometric identity for a translated reflection diagonal identifies its
candidate infinite-volume matrix coefficient.  Put the original strict
cylinder and its `2 * shift` time translate in the common presentation box
`base + 2 * shift`; their limiting polarized reflection form is the mixed
Osterwalder--Schrader bilinear expected from

  <T^shift v, T^shift v> = <v, T^(2*shift) v>.

This file constructs that bilinear without identifying it with the translated
diagonal.  The first missing physical input is named as an explicit dyadic
comparison modulus between their rational approximants.  Such a modulus is a
cylinder-covariance/conditional-expectation statement; it is not a sign or
contraction assumption.  From the modulus, the desired constructive-real
identity is derived.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Two cylinders in one common presentation box -/

/-- Canonical zero-extension of a strict-cylinder presentation to a larger
corner box.  Its coefficient table is unchanged. -/
def boxTransportStrictJointCylinderVector
    {base outer : Nat} (hbase : base ≤ outer)
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVector outer where
  roots := transportedCylinderRoots base outer vector.roots
  rootsCanonical := transportedCylinderRoots_canonical
    hbase vector.rootsCanonical
  coefficient := vector.coefficient

@[simp] theorem boxTransportStrictJointCylinderVector_roots
    {base outer : Nat} (hbase : base ≤ outer)
    (vector : StrictJointCylinderVector base) :
    (boxTransportStrictJointCylinderVector hbase vector).roots =
      transportedCylinderRoots base outer vector.roots := rfl

@[simp] theorem boxTransportStrictJointCylinderVector_coefficient
    {base outer : Nat} (hbase : base ≤ outer)
    (vector : StrictJointCylinderVector base) :
    (boxTransportStrictJointCylinderVector hbase vector).coefficient =
      vector.coefficient := rfl

/-- The source argument of the doubled-time mixed form, zero-extended to the
same box as the translated argument. -/
def strictJointDoubledTimeMixedSource
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVector (base + (shift + shift)) :=
  boxTransportStrictJointCylinderVector
    (Nat.le_add_right base (shift + shift)) vector

/-- The second argument is the literal time translate by `2 * shift`. -/
def strictJointDoubledTimeMixedTarget
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVector (base + (shift + shift)) :=
  timeTranslateStrictJointCylinderVector (shift + shift) vector

/-! ## 2. The candidate mixed OS matrix coefficient -/

def strictJointDoubledTimeMixedOSBilinear
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (strictJointDoubledTimeMixedSource shift vector)
    (strictJointDoubledTimeMixedTarget shift vector)

/-- Exact constructive-real identity sought from Euclidean cylinder
covariance.  This proposition names the identity but does not inhabit it. -/
def StrictJointDoubledTimeMixedOSIdentity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : Prop :=
  CReal.Equiv
    ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
      hcoupling hle)
    (strictJointDoubledTimeMixedOSBilinear
      hcoupling hle shift vector)

/-! ## 3. The first missing physical modulus -/

/-- Quantitative cylinder-covariance frontier.  A witness must derive one
nonnegative exact rational bound and prove decay of the literal target-minus-
mixed approximants.  No comparison sign is requested. -/
def StrictJointDoubledTimeMixedOSComparisonModulus
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : Prop :=
  ∃ bound : Q', (0 : Q') ≤ bound ∧
    ∀ stage : Nat,
      Q'.abs
          (((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
                hcoupling hle).approx stage -
            (strictJointDoubledTimeMixedOSBilinear
                hcoupling hle shift vector).approx stage) ≤
        bound * HalfPow.half ^ stage

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-- The dyadic cylinder-covariance modulus is exactly sufficient for the
doubled-time mixed OS identity. -/
theorem strictJointDoubledTimeMixedOSIdentity_of_comparisonModulus
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (hcomparison : StrictJointDoubledTimeMixedOSComparisonModulus
      hcoupling hle shift vector) :
    StrictJointDoubledTimeMixedOSIdentity
      hcoupling hle shift vector := by
  rcases hcomparison with ⟨bound, hbound, hpointwise⟩
  intro epsilon hepsilon
  let scaledTolerance :=
    epsilon * Q'.invSucc bound.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos bound.num.toNat)
  have hscaledFinal : bound * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat bound epsilon
      hbound (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled : bound * HalfPow.half ^ stage ≤
      bound * scaledTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hbound
  have habs :
      Q'.abs
          (((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
                hcoupling hle).approx stage -
            (strictJointDoubledTimeMixedOSBilinear
                hcoupling hle shift vector).approx stage) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hpointwise stage)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

#print axioms boxTransportStrictJointCylinderVector
#print axioms strictJointDoubledTimeMixedOSBilinear
#print axioms strictJointDoubledTimeMixedOSIdentity_of_comparisonModulus

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
