/-
# Semantic check for the BF4 based-cycle translation ledger

For one chord, the literal ledger starts with its adapted raw coordinate,
applies the certified start-path left translations and end-path right-inverse
translations, and should produce

```text
P(start) · U_c · P(end)⁻¹.
```

This module states that comparison entirely as finite rational-polynomial
data.  The four componentwise executable prefix checks are sound for the
existing `QuaternionPrefixPolyQuaternionEqv` relation, so no informal
identification of the translated coordinate with a cycle word is needed.
The successful all-cycle check is not asserted here: direct canonical
evaluation is too expensive for the narrow monitored check, leaving either a
structural quaternion anti-homomorphism proof or a batched certificate as the
next honest step.

## Axiom gate

Finite lists, exact rational polynomials, and executable prefix checks only.
No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

namespace YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
open YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

/-! ## 1. The adapted raw cycle word -/

/-- Product of the adapted tree-coordinate quaternions along an index path. -/
def adaptedTreeIndexPathHolonomy : List Nat → PolyQuaternion
  | [] => PolyQuaternion.one
  | treeBlock :: rest =>
      PolyQuaternion.mul
        (PolyQuaternion.coordinateVariable treeBlock)
        (adaptedTreeIndexPathHolonomy rest)

/-- The based-cycle word in the raw adapted carrier: tree blocks `0,...,24`
and chord block `25+c`. -/
def adaptedRawBasedCycleHolonomy
    (cycle : BF4SpatialCycle) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (adaptedTreeIndexPathHolonomy
        (bf4SpatialTreePathIndices (bf4SpatialChord cycle).1))
      (PolyQuaternion.coordinateVariable (bf4AdaptedChordBlock cycle)))
    (PolyQuaternion.conj
      (adaptedTreeIndexPathHolonomy
        (bf4SpatialTreePathIndices
          (YMGap.Continuum.ClusterCount4DProgress.addE
            (bf4SpatialChord cycle).1 (bf4SpatialChord cycle).2))))

/-! ## 2. Apply one cycle's proof-carrying shear word -/

theorem bf4BasedCycleRawTranslationSteps_valid :
    ∀ cycle : BF4SpatialCycle,
      rawSelectedTranslationStepsValid bf4TreeGaugeTailBlocks
        (bf4BasedCycleRawTranslationSteps cycle) = true := by
  decide

def bf4BasedCycleTranslationSteps
    (cycle : BF4SpatialCycle) :
    List (SelectedTranslationStep bf4TreeGaugeTailBlocks) :=
  certifyRawSelectedTranslationSteps
    (bf4BasedCycleRawTranslationSteps cycle)
    (bf4BasedCycleRawTranslationSteps_valid cycle)

def applyBF4BasedCycleTranslationSteps
    (cycle : BF4SpatialCycle) (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps
    (by decide : 0 < bf4TreeGaugeTailBlocks)
    (bf4BasedCycleTranslationSteps cycle) polynomial

def translatedAdaptedChordQuaternion
    (cycle : BF4SpatialCycle) : PolyQuaternion where
  scalar := applyBF4BasedCycleTranslationSteps cycle
    (PolyQuaternion.coordinateVariable
      (bf4AdaptedChordBlock cycle)).scalar
  iPart := applyBF4BasedCycleTranslationSteps cycle
    (PolyQuaternion.coordinateVariable
      (bf4AdaptedChordBlock cycle)).iPart
  jPart := applyBF4BasedCycleTranslationSteps cycle
    (PolyQuaternion.coordinateVariable
      (bf4AdaptedChordBlock cycle)).jPart
  kPart := applyBF4BasedCycleTranslationSteps cycle
    (PolyQuaternion.coordinateVariable
      (bf4AdaptedChordBlock cycle)).kPart

/-! ## 3. Executable componentwise semantic check -/

def canonPolyQuaternion (quaternion : PolyQuaternion) : PolyQuaternion where
  scalar := canonRat quaternion.scalar
  iPart := canonRat quaternion.iPart
  jPart := canonRat quaternion.jPart
  kPart := canonRat quaternion.kPart

def polyQuaternionPrefixCheck
    (blocks : Nat) (left right : PolyQuaternion) : Bool :=
  quaternionPrefixPolynomialCheck blocks
      (canonRat left.scalar) (canonRat right.scalar) &&
    (quaternionPrefixPolynomialCheck blocks
        (canonRat left.iPart) (canonRat right.iPart) &&
      (quaternionPrefixPolynomialCheck blocks
          (canonRat left.jPart) (canonRat right.jPart) &&
        quaternionPrefixPolynomialCheck blocks
          (canonRat left.kPart) (canonRat right.kPart)))

theorem polyQuaternionPrefixCheck_sound
    {blocks : Nat} {left right : PolyQuaternion}
    (hcheck : polyQuaternionPrefixCheck blocks left right = true) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (canonPolyQuaternion left) (canonPolyQuaternion right) := by
  have hsplit :
      quaternionPrefixPolynomialCheck blocks
          (canonRat left.scalar) (canonRat right.scalar) = true ∧
      quaternionPrefixPolynomialCheck blocks
          (canonRat left.iPart) (canonRat right.iPart) = true ∧
      quaternionPrefixPolynomialCheck blocks
          (canonRat left.jPart) (canonRat right.jPart) = true ∧
      quaternionPrefixPolynomialCheck blocks
          (canonRat left.kPart) (canonRat right.kPart) = true := by
    simpa [polyQuaternionPrefixCheck] using hcheck
  simpa [canonPolyQuaternion] using
    ⟨quaternionPrefixPolynomialCheck_sound blocks hsplit.1,
      quaternionPrefixPolynomialCheck_sound blocks hsplit.2.1,
      quaternionPrefixPolynomialCheck_sound blocks hsplit.2.2.1,
      quaternionPrefixPolynomialCheck_sound blocks hsplit.2.2.2⟩

def bf4BasedCycleTranslationSemanticCheck
    (cycle : BF4SpatialCycle) : Bool :=
  polyQuaternionPrefixCheck 48
    (translatedAdaptedChordQuaternion cycle)
    (adaptedRawBasedCycleHolonomy cycle)

/-- A successful finite semantic check identifies the translated raw chord
with its literal rooted based-cycle polynomial. -/
theorem bf4BasedCycleTranslationSemanticCheck_sound
    (cycle : BF4SpatialCycle)
    (hcheck : bf4BasedCycleTranslationSemanticCheck cycle = true) :
    QuaternionPrefixPolyQuaternionEqv 48
      (canonPolyQuaternion (translatedAdaptedChordQuaternion cycle))
      (canonPolyQuaternion (adaptedRawBasedCycleHolonomy cycle)) :=
  polyQuaternionPrefixCheck_sound hcheck

end YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationSemantics

#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationSemantics.bf4BasedCycleRawTranslationSteps_valid
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationSemantics.bf4BasedCycleTranslationSemanticCheck_sound
