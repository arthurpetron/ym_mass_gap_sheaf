/-
# Literal 116-link BF4 carrier to five tree-gauge cycle blocks

The 48 lower spatial links do not occupy the first 48 positions of the
literal corrected-slab carrier.  This module closes that finite bookkeeping
gap.  A checked chain of block transpositions puts the 25 tree links first
and the 23 chords second, applies the same 139-shear tree-gauge ledger on the
full 116-block carrier, moves cycles `[0,4,5,6,10]` to the tail, and integrates
the other 111 blocks.

The final Haar theorem discharges the successive finite translation scans
from a degree-five hypothesis on the five surviving chord blocks.  Every
carrier permutation, support claim, source-block identity, scan, and Fubini
step is then constructive.

## Axiom gate

Finite lists, decidable certificates, exact block reindexing, and normalized
quaternion Fubini only.  No `Classical.*`, `native_decide`, `sorry`, custom
axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeFiveHaarBridge
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

namespace YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
open YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Checked block-swap chains -/

structure RawQuaternionBlockSwap : Type where
  first : Nat
  second : Nat

def rawQuaternionBlockSwapValid
    (blocks : Nat) (swap : RawQuaternionBlockSwap) : Bool :=
  decide (swap.first < blocks ∧ swap.second < blocks)

def RawQuaternionBlockSwap.certify
    {blocks : Nat} (swap : RawQuaternionBlockSwap)
    (hvalid : rawQuaternionBlockSwapValid blocks swap = true) :
    QuaternionBlockInvolution blocks := by
  have hbounds : swap.first < blocks ∧ swap.second < blocks :=
    of_decide_eq_true hvalid
  exact blockSwapInvolution blocks swap.first swap.second
    hbounds.1 hbounds.2

def rawQuaternionBlockSwapsValid
    (blocks : Nat) (swaps : List RawQuaternionBlockSwap) : Bool :=
  swaps.all (rawQuaternionBlockSwapValid blocks)

def certifyRawQuaternionBlockSwaps
    {blocks : Nat} (swaps : List RawQuaternionBlockSwap)
    (hvalid : rawQuaternionBlockSwapsValid blocks swaps = true) :
    List (QuaternionBlockInvolution blocks) :=
  swaps.attach.map fun entry =>
    entry.val.certify
      (List.all_eq_true.mp hvalid entry.val entry.property)

def applyQuaternionBlockSwapChain
    {blocks : Nat} :
    List (QuaternionBlockInvolution blocks) → RatPoly → RatPoly
  | [], polynomial => polynomial
  | swap :: rest, polynomial =>
      applyQuaternionBlockSwapChain rest
        (reindexQuaternionPolynomial swap polynomial)

def quaternionBlockSwapChainSource
    {blocks : Nat} :
    List (QuaternionBlockInvolution blocks) → Nat → Nat
  | [], block => block
  | swap :: rest, block =>
      swap.map (quaternionBlockSwapChainSource rest block)

theorem applyQuaternionBlockSwapChain_supported
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks
      (applyQuaternionBlockSwapChain swaps polynomial) := by
  induction swaps generalizing polynomial with
  | nil => simpa [applyQuaternionBlockSwapChain] using hsupport
  | cons swap rest induction =>
      simpa [applyQuaternionBlockSwapChain] using
        induction (reindexQuaternionPolynomial swap polynomial)
          (reindexQuaternionPolynomial_supported swap polynomial)

theorem quaternionHaar_applyQuaternionBlockSwapChain
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (applyQuaternionBlockSwapChain swaps polynomial) ≈
      quaternionHaar blocks polynomial := by
  induction swaps generalizing polynomial with
  | nil => exact Q'.eqv_refl _
  | cons swap rest induction =>
      exact Q'.eqv_trans _
        (quaternionHaar blocks
          (reindexQuaternionPolynomial swap polynomial)) _
        (induction (reindexQuaternionPolynomial swap polynomial)
          (reindexQuaternionPolynomial_supported swap polynomial))
        (quaternionHaar_reindex swap polynomial hsupport)

theorem quaternionBlockSwapChainSource_lt
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    {block : Nat} (hblock : block < blocks) :
    quaternionBlockSwapChainSource swaps block < blocks := by
  induction swaps with
  | nil => exact hblock
  | cons swap rest induction =>
      exact swap.map_lt _ induction

theorem applyQuaternionBlockSwapChain_degreeAtMost
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    {block maxDegree : Nat} (hblock : block < blocks)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost
      (quaternionBlockSwapChainSource swaps block)
      maxDegree polynomial) :
    QuaternionBlockDegreeAtMost block maxDegree
      (applyQuaternionBlockSwapChain swaps polynomial) := by
  induction swaps generalizing block polynomial with
  | nil => simpa [applyQuaternionBlockSwapChain,
      quaternionBlockSwapChainSource] using hdegree
  | cons swap rest induction =>
      apply induction hblock (reindexQuaternionPolynomial swap polynomial)
      apply QuaternionBlockDegreeAtMost.reindex swap
        (quaternionBlockSwapChainSource_lt rest hblock)
      simpa [quaternionBlockSwapChainSource] using hdegree

/-! ## 2. Put the 25 tree and 23 chord links first -/

def bf4AdaptedBoundaryRawBlocks : List Nat :=
  (bf4SpatialTreeLinks ++ bf4SpatialChordLinks).map fun link =>
    (boundaryCompleteSlabLinks 1).idxOf link

theorem bf4AdaptedBoundaryRawBlocks_eq :
    bf4AdaptedBoundaryRawBlocks =
      [4, 1, 0, 24, 10, 5, 39, 2, 68, 28, 25, 44, 22, 71, 40,
       69, 58, 55, 81, 53, 79, 91, 106, 103, 101,
       11, 29, 45, 59, 3, 6, 23, 26, 84, 41, 42, 54, 56, 95,
       107, 70, 72, 80, 82, 92, 93, 102, 104] := by
  decide

/-- Selection-sort transpositions for the literal source-block table above.
Identity swaps have been omitted. -/
def bf4RawCarrierAdaptationSwaps : List RawQuaternionBlockSwap :=
  [⟨0, 4⟩, ⟨2, 4⟩, ⟨3, 24⟩, ⟨4, 10⟩, ⟨6, 39⟩, ⟨7, 10⟩,
   ⟨8, 68⟩, ⟨9, 28⟩, ⟨10, 25⟩, ⟨11, 44⟩, ⟨12, 22⟩,
   ⟨13, 71⟩, ⟨14, 40⟩, ⟨15, 69⟩, ⟨16, 58⟩, ⟨17, 55⟩,
   ⟨18, 81⟩, ⟨19, 53⟩, ⟨20, 79⟩, ⟨21, 91⟩, ⟨22, 106⟩,
   ⟨23, 103⟩, ⟨24, 101⟩, ⟨25, 44⟩, ⟨26, 29⟩, ⟨27, 45⟩,
   ⟨28, 59⟩, ⟨29, 101⟩, ⟨30, 39⟩, ⟨31, 103⟩, ⟨32, 101⟩,
   ⟨33, 84⟩, ⟨34, 41⟩, ⟨35, 42⟩, ⟨36, 54⟩, ⟨37, 56⟩,
   ⟨38, 95⟩, ⟨39, 107⟩, ⟨40, 70⟩, ⟨41, 72⟩, ⟨42, 80⟩,
   ⟨43, 82⟩, ⟨44, 92⟩, ⟨45, 93⟩, ⟨46, 102⟩, ⟨47, 104⟩]

theorem bf4RawCarrierAdaptationSwaps_valid :
    rawQuaternionBlockSwapsValid 116
      bf4RawCarrierAdaptationSwaps = true := by
  decide

def bf4RawCarrierAdaptationSteps :
    List (QuaternionBlockInvolution 116) :=
  certifyRawQuaternionBlockSwaps bf4RawCarrierAdaptationSwaps
    bf4RawCarrierAdaptationSwaps_valid

def adaptBF4RawCarrier (polynomial : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain bf4RawCarrierAdaptationSteps polynomial

/-- After adaptation, blocks `0,...,47` read precisely the 25 tree links
followed by the 23 chord links. -/
theorem bf4RawCarrierAdaptation_source_order :
    (List.range 48).map
        (quaternionBlockSwapChainSource bf4RawCarrierAdaptationSteps) =
      bf4AdaptedBoundaryRawBlocks := by
  rw [bf4AdaptedBoundaryRawBlocks_eq]
  decide

/-! ## 3. Lift the literal 139 shears to all 116 blocks -/

theorem bf4RawTreeGaugeTranslationLedger_valid_116 :
    rawSelectedTranslationStepsValid 115
      bf4RawTreeGaugeTranslationLedger = true := by
  decide

def bf4TreeGaugeTranslationSteps116 :
    List (SelectedTranslationStep 115) :=
  certifyRawSelectedTranslationSteps bf4RawTreeGaugeTranslationLedger
    bf4RawTreeGaugeTranslationLedger_valid_116

def applyBF4TreeGaugeTranslationLedger116
    (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (by decide : 0 < 115)
    bf4TreeGaugeTranslationSteps116 polynomial

def bf4TreeGaugeTranslationLedgerCheck116
    (polynomial : RatPoly) : Bool :=
  selectedTranslationStepsCheck (by decide : 0 < 115)
    bf4TreeGaugeTranslationSteps116 polynomial

theorem applyBF4TreeGaugeTranslationLedger116_supported
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial) :
    SupportedQuaternionBlocks 116
      (applyBF4TreeGaugeTranslationLedger116 polynomial) := by
  simpa using applySelectedTranslationSteps_supported
    (by decide : 0 < 115) bf4TreeGaugeTranslationSteps116
    polynomial hsupport

theorem applyBF4TreeGaugeTranslationLedger116_haar_sound
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial)
    (hcheck : bf4TreeGaugeTranslationLedgerCheck116 polynomial = true) :
    quaternionHaar 116
        (applyBF4TreeGaugeTranslationLedger116 polynomial) ≈
      quaternionHaar 116 polynomial := by
  simpa using applySelectedTranslationSteps_haar_sound
    (by decide : 0 < 115) bf4TreeGaugeTranslationSteps116
    polynomial hsupport hcheck

/-! ## 3a. The five transmitted cycle words alone -/

/-- Only the five cycle substitutions that survive the final marginal are
needed; the other 18 chord coordinates are integrated without translation. -/
def bf4TransmittedRawTreeGaugeTranslationLedger :
    List RawSelectedTranslationStep :=
  bf4TransmittedCycleTable.flatMap bf4BasedCycleRawTranslationSteps

theorem bf4TransmittedRawTreeGaugeTranslationLedger_valid_116 :
    rawSelectedTranslationStepsValid 115
      bf4TransmittedRawTreeGaugeTranslationLedger = true := by
  decide

def bf4TransmittedTreeGaugeTranslationSteps116 :
    List (SelectedTranslationStep 115) :=
  certifyRawSelectedTranslationSteps
    bf4TransmittedRawTreeGaugeTranslationLedger
    bf4TransmittedRawTreeGaugeTranslationLedger_valid_116

def bf4TransmittedAdaptedChordBlocks : List Nat :=
  bf4TransmittedCycleTable.map bf4AdaptedChordBlock

theorem bf4TransmittedAdaptedChordBlocks_eq :
    bf4TransmittedAdaptedChordBlocks = [25, 29, 30, 31, 35] := by
  decide

theorem bf4TransmittedTreeGaugeTranslationSteps116_degreeCompatible :
    selectedTranslationStepsDegreeCompatible
      bf4TransmittedAdaptedChordBlocks
      bf4TransmittedTreeGaugeTranslationSteps116 = true := by
  decide

def applyBF4TransmittedTreeGaugeTranslationLedger116
    (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (by decide : 0 < 115)
    bf4TransmittedTreeGaugeTranslationSteps116 polynomial

theorem applyBF4TransmittedTreeGaugeTranslationLedger116_supported
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial) :
    SupportedQuaternionBlocks 116
      (applyBF4TransmittedTreeGaugeTranslationLedger116 polynomial) := by
  simpa using applySelectedTranslationSteps_supported
    (by decide : 0 < 115)
    bf4TransmittedTreeGaugeTranslationSteps116 polynomial hsupport

/-- Degree at most five on the five chord blocks discharges every successive
left/right translation scan constructively. -/
theorem applyBF4TransmittedTreeGaugeTranslationLedger116_haar_degreeFive
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial)
    (hdegree : QuaternionBlocksDegreeAtMost
      bf4TransmittedAdaptedChordBlocks 5 polynomial) :
    quaternionHaar 116
        (applyBF4TransmittedTreeGaugeTranslationLedger116 polynomial) ≈
      quaternionHaar 116 polynomial := by
  have hscan : selectedTranslationStepsCheck (by decide : 0 < 115)
      bf4TransmittedTreeGaugeTranslationSteps116 polynomial = true := by
    apply selectedTranslationStepsCheck_of_degreeCompatible_five
      (by decide : 0 < 115) bf4TransmittedAdaptedChordBlocks
    · intro block hblock
      rw [bf4TransmittedAdaptedChordBlocks_eq] at hblock
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      omega
    · exact bf4TransmittedTreeGaugeTranslationSteps116_degreeCompatible
    · exact hdegree
  simpa [applyBF4TransmittedTreeGaugeTranslationLedger116] using
    applySelectedTranslationSteps_haar_sound
      (by decide : 0 < 115)
      bf4TransmittedTreeGaugeTranslationSteps116 polynomial hsupport hscan

/-! ## 4. Integrate 111 blocks and retain the five based cycles -/

def bf4BasedCycleFiveTailMap116 (block : Nat) : Nat :=
  if block = 25 then 111
  else if block = 111 then 25
  else if block = 29 then 112
  else if block = 112 then 29
  else if block = 30 then 113
  else if block = 113 then 30
  else if block = 31 then 114
  else if block = 114 then 31
  else if block = 35 then 115
  else if block = 115 then 35
  else block

def bf4BasedCycleFiveTailInvolution116 :
    QuaternionBlockInvolution 116 where
  map := bf4BasedCycleFiveTailMap116
  map_lt := by
    intro block hblock
    by_cases h25 : block = 25
    · subst block; decide
    · by_cases h111 : block = 111
      · subst block; decide
      · by_cases h29 : block = 29
        · subst block; decide
        · by_cases h112 : block = 112
          · subst block; decide
          · by_cases h30 : block = 30
            · subst block; decide
            · by_cases h113 : block = 113
              · subst block; decide
              · by_cases h31 : block = 31
                · subst block; decide
                · by_cases h114 : block = 114
                  · subst block; decide
                  · by_cases h35 : block = 35
                    · subst block; decide
                    · by_cases h115 : block = 115
                      · subst block; decide
                      · simpa [bf4BasedCycleFiveTailMap116, h25, h111,
                          h29, h112, h30, h113, h31, h114, h35, h115]
                        using hblock
  involutive := by
    intro block _
    by_cases h25 : block = 25
    · subst block; decide
    · by_cases h111 : block = 111
      · subst block; decide
      · by_cases h29 : block = 29
        · subst block; decide
        · by_cases h112 : block = 112
          · subst block; decide
          · by_cases h30 : block = 30
            · subst block; decide
            · by_cases h113 : block = 113
              · subst block; decide
              · by_cases h31 : block = 31
                · subst block; decide
                · by_cases h114 : block = 114
                  · subst block; decide
                  · by_cases h35 : block = 35
                    · subst block; decide
                    · by_cases h115 : block = 115
                      · subst block; decide
                      · simp [bf4BasedCycleFiveTailMap116, h25, h111,
                          h29, h112, h30, h113, h31, h114, h35, h115]

def exactRawTreeGaugeBasedCycleFiveHaarMarginal
    (polynomial : RatPoly) : RatPoly :=
  partialHaarHeads 111
    (reindexQuaternionPolynomial bf4BasedCycleFiveTailInvolution116
      (applyBF4TransmittedTreeGaugeTranslationLedger116
        (adaptBF4RawCarrier polynomial)))

theorem exactRawTreeGaugeBasedCycleFiveHaarMarginal_supported_five
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks 5
      (exactRawTreeGaugeBasedCycleFiveHaarMarginal polynomial) := by
  unfold exactRawTreeGaugeBasedCycleFiveHaarMarginal
  apply partialHaarHeads_supported 5 111
  simpa using reindexQuaternionPolynomial_supported
    bf4BasedCycleFiveTailInvolution116
    (applyBF4TransmittedTreeGaugeTranslationLedger116
      (adaptBF4RawCarrier polynomial))

theorem exactRawTreeGaugeBasedCycleFiveHaarMarginal_cycle_order :
    [25, 29, 30, 31, 35].map (fun block => block - 25) =
      [0, 4, 5, 6, 10] := by
  decide

/-- **Literal 116-link to five based-cycle Haar bridge.**  All carrier
adaptation, translated-cycle scans, and 111 integrations are discharged from
the exact degree-five bound on the five surviving chord blocks. -/
theorem quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial)
    (hdegree : QuaternionBlocksDegreeAtMost
      bf4TransmittedAdaptedChordBlocks 5
        (adaptBF4RawCarrier polynomial)) :
    quaternionHaar 116 polynomial ≈
      quaternionHaar 5
        (exactRawTreeGaugeBasedCycleFiveHaarMarginal polynomial) := by
  let adapted := adaptBF4RawCarrier polynomial
  let translated := applyBF4TransmittedTreeGaugeTranslationLedger116 adapted
  have hadaptedSupport : SupportedQuaternionBlocks 116 adapted := by
    exact applyQuaternionBlockSwapChain_supported
      bf4RawCarrierAdaptationSteps polynomial hsupport
  have htranslatedSupport : SupportedQuaternionBlocks 116 translated :=
    applyBF4TransmittedTreeGaugeTranslationLedger116_supported
      adapted hadaptedSupport
  refine Q'.eqv_trans _ (quaternionHaar 116 adapted) _
    (Q'.eqv_symm
      (quaternionHaar_applyQuaternionBlockSwapChain
        bf4RawCarrierAdaptationSteps polynomial hsupport)) ?_
  refine Q'.eqv_trans _ (quaternionHaar 116 translated) _
    (Q'.eqv_symm
      (applyBF4TransmittedTreeGaugeTranslationLedger116_haar_degreeFive
        adapted hadaptedSupport hdegree)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 116
      (reindexQuaternionPolynomial
        bf4BasedCycleFiveTailInvolution116 translated)) _
    (Q'.eqv_symm
      (quaternionHaar_reindex
        bf4BasedCycleFiveTailInvolution116 translated
        htranslatedSupport)) ?_
  simpa [exactRawTreeGaugeBasedCycleFiveHaarMarginal, adapted, translated]
    using Q'.eqv_symm
      (quaternionHaar_partialHaarHeads 5 111
        (reindexQuaternionPolynomial
          bf4BasedCycleFiveTailInvolution116 translated))

end YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier.bf4RawCarrierAdaptation_source_order
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier.quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal
