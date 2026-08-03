/-
# Literal BF4 raw-link to based-cycle translation ledger

The adapted BF4 boundary carrier has tree blocks `0,...,24` and chord blocks
`25,...,47`.  For every chord `c`, this module reads the already certified
root paths and emits the exact substitution word

```text
P(start(c)) · U_c · P(end(c))⁻¹.
```

The left multipliers follow the start path.  The right inverse multipliers
also follow the end path: successive polynomial substitutions compose in the
opposite order on the right, producing the required reversed inverse word.
All generated selected/multiplier indices are checked constructively, then
converted to the dependent chain interface.  A successful finite polynomial
scan therefore proves full 48-fold Haar preservation for this literal BF4
ledger.

This closes the finite ledger and iterated-Haar layer.  A separate syntactic
identification theorem must still show that applying the ledger to each raw
chord coordinate yields the `assignedBasedCycleHolonomy` polynomial already
defined by the geometry module.

## Axiom gate

Finite BF4 tables, decidable checks, and the constructive translation chain
only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

namespace YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

local infix:50 " ≈ " => Q'.eqv

def bf4TreeGaugeTailBlocks : Nat := 47
def bf4TreeGaugeTotalBlocks : Nat := bf4TreeGaugeTailBlocks + 1

theorem bf4TreeGaugeTotalBlocks_eq : bf4TreeGaugeTotalBlocks = 48 := by
  decide

/-- In the adapted carrier, chord `c` occupies block `25+c`. -/
def bf4AdaptedChordBlock (cycle : BF4SpatialCycle) : Nat :=
  25 + cycle.val

def bf4RawLeftTreeTranslation
    (cycle : BF4SpatialCycle) (treeBlock : Nat) :
    RawSelectedTranslationStep where
  selected := bf4AdaptedChordBlock cycle
  multiplier := treeBlock
  side := .left
  multiplierOrientation := .direct

def bf4RawRightInverseTreeTranslation
    (cycle : BF4SpatialCycle) (treeBlock : Nat) :
    RawSelectedTranslationStep where
  selected := bf4AdaptedChordBlock cycle
  multiplier := treeBlock
  side := .right
  multiplierOrientation := .inverse

/-- The literal pair-shear word for one rooted based cycle. -/
def bf4BasedCycleRawTranslationSteps
    (cycle : BF4SpatialCycle) : List RawSelectedTranslationStep :=
  (bf4SpatialTreePathIndices (bf4SpatialChord cycle).1).map
      (bf4RawLeftTreeTranslation cycle) ++
    (bf4SpatialTreePathIndices
      (addE (bf4SpatialChord cycle).1 (bf4SpatialChord cycle).2)).map
      (bf4RawRightInverseTreeTranslation cycle)

theorem bf4BasedCycleRawTranslationSteps_length
    (cycle : BF4SpatialCycle) :
    (bf4BasedCycleRawTranslationSteps cycle).length =
      (bf4SpatialTreePathIndices (bf4SpatialChord cycle).1).length +
        (bf4SpatialTreePathIndices
          (addE (bf4SpatialChord cycle).1
            (bf4SpatialChord cycle).2)).length := by
  simp [bf4BasedCycleRawTranslationSteps]

/-- All 23 based-cycle words, in canonical chord order. -/
def bf4RawTreeGaugeTranslationLedger :
    List RawSelectedTranslationStep :=
  (List.finRange bf4SpatialCycleCount).flatMap
    bf4BasedCycleRawTranslationSteps

theorem bf4RawTreeGaugeTranslationLedger_length :
    bf4RawTreeGaugeTranslationLedger.length = 139 := by
  decide

/-- Every literal chord block lies in `25,...,47`, every path multiplier lies
in `0,...,24`, and hence every selected/multiplier pair is valid and distinct. -/
theorem bf4RawTreeGaugeTranslationLedger_valid :
    rawSelectedTranslationStepsValid bf4TreeGaugeTailBlocks
      bf4RawTreeGaugeTranslationLedger = true := by
  decide

/-- The proof-carrying translation chain extracted from the literal tables. -/
def bf4TreeGaugeTranslationSteps :
    List (SelectedTranslationStep bf4TreeGaugeTailBlocks) :=
  certifyRawSelectedTranslationSteps bf4RawTreeGaugeTranslationLedger
    bf4RawTreeGaugeTranslationLedger_valid

def applyBF4TreeGaugeTranslationLedger
    (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (by decide : 0 < bf4TreeGaugeTailBlocks)
    bf4TreeGaugeTranslationSteps polynomial

def bf4TreeGaugeTranslationLedgerCheck
    (polynomial : RatPoly) : Bool :=
  selectedTranslationStepsCheck
    (by decide : 0 < bf4TreeGaugeTailBlocks)
    bf4TreeGaugeTranslationSteps polynomial

theorem applyBF4TreeGaugeTranslationLedger_supported
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 48 polynomial) :
    SupportedQuaternionBlocks 48
      (applyBF4TreeGaugeTranslationLedger polynomial) := by
  simpa [bf4TreeGaugeTotalBlocks, bf4TreeGaugeTailBlocks] using
    applySelectedTranslationSteps_supported
      (by decide : 0 < bf4TreeGaugeTailBlocks)
      bf4TreeGaugeTranslationSteps polynomial hsupport

/-- **Exact conditional Haar preservation for the literal BF4 based-cycle
ledger.**  The only hypothesis beyond finite support is the executable scan
of each successive translated polynomial. -/
theorem applyBF4TreeGaugeTranslationLedger_haar_sound
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 48 polynomial)
    (hcheck : bf4TreeGaugeTranslationLedgerCheck polynomial = true) :
    quaternionHaar 48
        (applyBF4TreeGaugeTranslationLedger polynomial) ≈
      quaternionHaar 48 polynomial := by
  simpa [bf4TreeGaugeTotalBlocks, bf4TreeGaugeTailBlocks] using
    applySelectedTranslationSteps_haar_sound
      (by decide : 0 < bf4TreeGaugeTailBlocks)
      bf4TreeGaugeTranslationSteps polynomial hsupport hcheck

end YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger

#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger.bf4RawTreeGaugeTranslationLedger_valid
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger.applyBF4TreeGaugeTranslationLedger_haar_sound
