/-
# An actual Wilson backtrack identity on the original source Haar sphere

The original origin-x0 link followed immediately by its reverse is a
closed compatible SourceLoop at base one. Its spin-one character equals
the constant two under every insertion on the source Haar carrier.

The ordered source product is q*(conj(q)*one). Free coefficient algebra
removes the trailing unit; the existing unit-quaternion Haar sphere law
then removes q*conj(q). No free coefficient equality with the constant is
asserted. This finite source certificate is intended for the separate
same-Wilson-state Haar descent, not a full-observable coverage claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4WilsonBacktrackSourceIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
  (entryStart entryFinish pathFinish Compatible wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation (haarUnit_mul_conj)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

attribute [local irreducible] baseLinks link

/-- An actual spatial link, not the off-carrier identity fallback. -/
def backtrackLink : Z4Link := ((0,0,0,0), .x0)

theorem backtrackLink_physical : backtrackLink ∈ baseLinks 1 :=
  (baseLinks_mem_iff 1 backtrackLink).mpr (by
    unfold BF4ExactSlabFixedSpatialTwoLayerBoundary.SliceLink backtrackLink
    decide)

/-- Both entries are the same original link with opposite traversal directions. -/
def sourceLoop : SourceLoop 1 where
  start := (0,0,0,0)
  edges := [⟨backtrackLink, false⟩, ⟨backtrackLink, true⟩]
  compatible := ⟨rfl, ⟨rfl, True.intro⟩⟩
  closed := rfl
  physical := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact backtrackLink_physical

def backtrack : WindowExpression 1 := .loop 0 sourceLoop 1

def constant : WindowExpression 1 := .smul 2 .one

theorem backtrack_within : Within 0 backtrack := Nat.le_refl 0

theorem constant_within : Within 0 constant := True.intro

/-- The original ordered source word is the Haar unit under arbitrary insertions. -/
theorem sourceWord_haar :
    PolyQuaternionHaarCarrierEqv (baseLinks 1).length
      (sourceWord 1 sourceLoop.edges) PolyQuaternion.one := by
  let q := link 1 backtrackLink
  have hunit : HaarCarrierEqv (baseLinks 1).length (polyQuaternionNorm q) polyOne := by
    simpa only [q, link, if_pos backtrackLink_physical] using
      haarNorm_coordinate (List.idxOf_lt_length_of_mem backtrackLink_physical)
  have hword : PolyQuaternionCoeffEqv (sourceWord 1 sourceLoop.edges)
      (PolyQuaternion.mul q (PolyQuaternion.conj q)) := by
    change PolyQuaternionCoeffEqv
      (PolyQuaternion.mul q (PolyQuaternion.mul (PolyQuaternion.conj q) PolyQuaternion.one))
      (PolyQuaternion.mul q (PolyQuaternion.conj q))
    exact (PolyQuaternionCoeffEqv.refl q).mul
      (PolyQuaternionCoeffEqv.mul_one (PolyQuaternion.conj q))
  exact (PolyQuaternionHaarCarrierEqv.of_coeff hword).trans (haarUnit_mul_conj hunit)

/-- Literal original source polynomials, with no ambient placement or action replacement. -/
theorem source_haar : HaarCarrierEqv (baseLinks 1).length
    (sourcePolynomial backtrack) (sourcePolynomial constant) := by
  simpa only [backtrack, constant, sourcePolynomial, Nat.zero_mul,
    liftBoundary, sourceCharacter, characterPolynomial] using
    HaarCarrierEqv.smul 2 sourceWord_haar.scalar

/-- The finite source certificate consumed by supported-Haar state descent. -/
theorem source_supported_haar : SupportedHaarEqv (baseLinks 1).length
    (sourcePolynomial backtrack) (sourcePolynomial constant) :=
  SupportedHaarEqv.of_carrier source_haar

end YMGap.Continuum.BF4WilsonBacktrackSourceIdentity

#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.backtrackLink
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.backtrackLink_physical
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.sourceLoop
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.backtrack
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.constant
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.backtrack_within
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.constant_within
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.sourceWord_haar
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.source_haar
#print axioms YMGap.Continuum.BF4WilsonBacktrackSourceIdentity.source_supported_haar
