/-
# Constructive Haar translation at an arbitrary selected block pair

The polynomial translation theorem is naturally stated with the integrated
quaternion in block `0` and its left/right multiplier in block `1`.  A BF4
tree-gauge step starts with two arbitrary distinct link blocks.  This module
provides the exact constructive bridge:

1. swap the selected block to `0`;
2. swap the multiplier's new location to `1` without disturbing `0`;
3. apply the executable finite-polynomial translation certificate; and
4. integrate the selected block.

The resulting polynomial is supported on one fewer quaternion block and has
the same full product-Haar value as the source polynomial.  This is the
composable elementary step required by the 25-link tree-gauge ledger.

## Axiom gate

Explicit finite block involutions, exact polynomial recursion, and the
previously certified translation theorem only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

namespace YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A reusable transposition of two arbitrary blocks -/

def blockSwapMap (first second block : Nat) : Nat :=
  if block = first then second
  else if block = second then first
  else block

def blockSwapInvolution
    (blocks first second : Nat)
    (hfirst : first < blocks) (hsecond : second < blocks) :
    QuaternionBlockInvolution blocks where
  map := blockSwapMap first second
  map_lt := by
    intro block hblock
    by_cases hblockFirst : block = first
    · subst block
      simp only [blockSwapMap]
      exact hsecond
    · by_cases hblockSecond : block = second
      · subst block
        simp only [blockSwapMap, if_neg hblockFirst]
        exact hfirst
      · simp only [blockSwapMap, if_neg hblockFirst,
          if_neg hblockSecond]
        exact hblock
  involutive := by
    intro block _
    by_cases hfirstSecond : first = second
    · subst second
      by_cases hblockFirst : block = first
      · subst block
        simp [blockSwapMap]
      · simp [blockSwapMap, hblockFirst]
    · by_cases hblockFirst : block = first
      · subst block
        simp [blockSwapMap]
      · by_cases hblockSecond : block = second
        · subst block
          have hsecondFirst : second ≠ first :=
            fun heq => hfirstSecond heq.symm
          simp [blockSwapMap, hsecondFirst]
        · simp [blockSwapMap, hblockFirst, hblockSecond]

theorem blockSwapInvolution_map_first
    (blocks first second : Nat)
    (hfirst : first < blocks) (hsecond : second < blocks) :
    (blockSwapInvolution blocks first second hfirst hsecond).map first =
      second := by
  simp [blockSwapInvolution, blockSwapMap]

theorem blockSwapInvolution_map_second
    (blocks first second : Nat)
    (hfirst : first < blocks) (hsecond : second < blocks) :
    (blockSwapInvolution blocks first second hfirst hsecond).map second =
      first := by
  by_cases hfirstSecond : first = second
  · subst second
    simp [blockSwapInvolution, blockSwapMap]
  · have hsecondFirst : second ≠ first :=
      fun heq => hfirstSecond heq.symm
    simp [blockSwapInvolution, blockSwapMap, hsecondFirst]

/-! ## 2. Expose a selected/multiplier pair as blocks zero and one -/

def translationPairHeadPermutation
    (blocks selected : Nat) (hselected : selected < blocks) :
    QuaternionBlockInvolution blocks :=
  headSwapBlockInvolution blocks selected hselected

def translationPairMultiplierLocation
    (blocks selected multiplier : Nat)
    (hselected : selected < blocks) : Nat :=
  (translationPairHeadPermutation blocks selected hselected).map multiplier

private theorem translationPairMultiplierLocation_lt
    (blocks selected multiplier : Nat)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks) :
    translationPairMultiplierLocation blocks selected multiplier hselected <
      blocks :=
  (translationPairHeadPermutation blocks selected hselected).map_lt
    multiplier hmultiplier

private theorem translationPairMultiplierLocation_ne_zero
    (blocks selected multiplier : Nat)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (hdistinct : selected ≠ multiplier) :
    translationPairMultiplierLocation blocks selected multiplier hselected ≠
      0 := by
  intro hzero
  let head := translationPairHeadPermutation blocks selected hselected
  have hmapped := congrArg head.map hzero
  have hinvolutive := head.involutive multiplier hmultiplier
  have hmapZero : head.map 0 = selected :=
    headSwapBlockInvolution_map_zero blocks selected hselected
  change head.map multiplier = 0 at hzero
  rw [hzero, hmapZero] at hinvolutive
  exact hdistinct hinvolutive

def translationPairTailPermutation
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks) :
    QuaternionBlockInvolution blocks :=
  blockSwapInvolution blocks 1
    (translationPairMultiplierLocation blocks selected multiplier hselected)
    hblocks
    (translationPairMultiplierLocation_lt blocks selected multiplier
      hselected hmultiplier)

def exposeTranslationPairPolynomial
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial
    (translationPairTailPermutation blocks selected multiplier
      hblocks hselected hmultiplier)
    (reindexQuaternionPolynomial
      (translationPairHeadPermutation blocks selected hselected)
      polynomial)

theorem translationPairTailPermutation_map_zero
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (hdistinct : selected ≠ multiplier) :
    (translationPairTailPermutation blocks selected multiplier
      hblocks hselected hmultiplier).map 0 = 0 := by
  have hlocation := translationPairMultiplierLocation_ne_zero
    blocks selected multiplier hselected hmultiplier hdistinct
  have hzeroLocation :
      0 ≠ translationPairMultiplierLocation
        blocks selected multiplier hselected :=
    fun heq => hlocation heq.symm
  simp [translationPairTailPermutation, blockSwapInvolution,
    blockSwapMap, hzeroLocation]

theorem translationPairTailPermutation_map_one
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks) :
    (translationPairTailPermutation blocks selected multiplier
      hblocks hselected hmultiplier).map 1 =
      translationPairMultiplierLocation blocks selected multiplier
        hselected := by
  exact blockSwapInvolution_map_first blocks 1
    (translationPairMultiplierLocation blocks selected multiplier hselected)
    hblocks
    (translationPairMultiplierLocation_lt blocks selected multiplier
      hselected hmultiplier)

theorem translationPairHeadPermutation_map_multiplierLocation
    (blocks selected multiplier : Nat)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks) :
    (translationPairHeadPermutation blocks selected hselected).map
        (translationPairMultiplierLocation blocks selected multiplier
          hselected) = multiplier := by
  exact (translationPairHeadPermutation blocks selected hselected).involutive
    multiplier hmultiplier

/-- The exposed block `0` reads the original selected block. -/
theorem exposedTranslationPair_source_zero
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (hdistinct : selected ≠ multiplier) :
    (translationPairHeadPermutation blocks selected hselected).map
        ((translationPairTailPermutation blocks selected multiplier
          hblocks hselected hmultiplier).map 0) = selected := by
  rw [translationPairTailPermutation_map_zero blocks selected multiplier
    hblocks hselected hmultiplier hdistinct]
  exact headSwapBlockInvolution_map_zero blocks selected hselected

/-- The exposed block `1` reads the original multiplier block. -/
theorem exposedTranslationPair_source_one
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks) :
    (translationPairHeadPermutation blocks selected hselected).map
        ((translationPairTailPermutation blocks selected multiplier
          hblocks hselected hmultiplier).map 1) = multiplier := by
  rw [translationPairTailPermutation_map_one blocks selected multiplier
    hblocks hselected hmultiplier]
  exact translationPairHeadPermutation_map_multiplierLocation
    blocks selected multiplier hselected hmultiplier

theorem exposeTranslationPairPolynomial_supported
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier polynomial) := by
  unfold exposeTranslationPairPolynomial
  exact reindexQuaternionPolynomial_supported
    (translationPairTailPermutation blocks selected multiplier
      hblocks hselected hmultiplier) _

/-- The two exposing transpositions preserve the full product-Haar value. -/
theorem quaternionHaar_exposeTranslationPair
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (exposeTranslationPairPolynomial blocks selected multiplier
          hblocks hselected hmultiplier polynomial) ≈
      quaternionHaar blocks polynomial := by
  let head := translationPairHeadPermutation blocks selected hselected
  let tail := translationPairTailPermutation blocks selected multiplier
    hblocks hselected hmultiplier
  let exposedHead := reindexQuaternionPolynomial head polynomial
  exact Q'.eqv_trans _
    (quaternionHaar blocks exposedHead) _
    (quaternionHaar_reindex tail exposedHead
      (reindexQuaternionPolynomial_supported head polynomial))
    (quaternionHaar_reindex head polynomial hsupport)

/-! ## 3. Certified arbitrary-pair left/right translation steps -/

def selectedLeftTranslationPartial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  partialTranslatedHeadPolynomial leftTranslatedHeadQuaternion
    (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier polynomial)

def selectedRightTranslationPartial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  partialTranslatedHeadPolynomial rightTranslatedHeadQuaternion
    (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier polynomial)

def selectedLeftTranslationCheck
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : Bool :=
  translationPolynomialCheck leftTranslationMomentCheck
    (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier polynomial)

def selectedRightTranslationCheck
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : Bool :=
  translationPolynomialCheck rightTranslationMomentCheck
    (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier polynomial)

/-- Undo the two exposing transpositions, in reverse order. -/
def restoreTranslationPairPolynomial
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial
    (translationPairHeadPermutation blocks selected hselected)
    (reindexQuaternionPolynomial
      (translationPairTailPermutation blocks selected multiplier
        hblocks hselected hmultiplier)
      polynomial)

theorem restoreTranslationPairPolynomial_supported
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (restoreTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier polynomial) := by
  unfold restoreTranslationPairPolynomial
  exact reindexQuaternionPolynomial_supported
    (translationPairHeadPermutation blocks selected hselected) _

/-- Restoring the original block order preserves full product Haar. -/
theorem quaternionHaar_restoreTranslationPair
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (restoreTranslationPairPolynomial blocks selected multiplier
          hblocks hselected hmultiplier polynomial) ≈
      quaternionHaar blocks polynomial := by
  let head := translationPairHeadPermutation blocks selected hselected
  let tail := translationPairTailPermutation blocks selected multiplier
    hblocks hselected hmultiplier
  let restoredTail := reindexQuaternionPolynomial tail polynomial
  exact Q'.eqv_trans _
    (quaternionHaar blocks restoredTail) _
    (quaternionHaar_reindex head restoredTail
      (reindexQuaternionPolynomial_supported tail polynomial))
    (quaternionHaar_reindex tail polynomial hsupport)

/-- Expose an arbitrary pair, genuinely left-translate its selected block by
its multiplier, and restore the original block order. -/
def selectedLeftTranslatedPolynomial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  restoreTranslationPairPolynomial (tailBlocks + 1) selected multiplier
    (by omega) hselected hmultiplier
    (translatedHeadPolynomial leftTranslatedHeadQuaternion
      (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
        (by omega) hselected hmultiplier polynomial))

/-- Block-count-preserving right-translation companion. -/
def selectedRightTranslatedPolynomial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  restoreTranslationPairPolynomial (tailBlocks + 1) selected multiplier
    (by omega) hselected hmultiplier
    (translatedHeadPolynomial rightTranslatedHeadQuaternion
      (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
        (by omega) hselected hmultiplier polynomial))

theorem selectedLeftTranslatedPolynomial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks (tailBlocks + 1)
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedLeftTranslatedPolynomial
  exact restoreTranslationPairPolynomial_supported
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier _

theorem selectedRightTranslatedPolynomial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks (tailBlocks + 1)
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedRightTranslatedPolynomial
  exact restoreTranslationPairPolynomial_supported
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier _

/-! ## 3a. Conjugate-multiplier translations -/

/-- Select exactly the three vector coordinates of one quaternion block. -/
def quaternionConjugateCoordinateSelector
    (block coordinate : Nat) : Bool :=
  decide
    (coordinate = 4 * block + 1 ∨
      coordinate = 4 * block + 2 ∨
      coordinate = 4 * block + 3)

/-- Polynomial substitution induced by quaternion conjugation in one block. -/
def conjugateQuaternionBlockPolynomial
    (blocks block : Nat) (polynomial : RatPoly) : RatPoly :=
  signSelectedPolynomial (4 * blocks)
    (quaternionConjugateCoordinateSelector block) polynomial

theorem conjugateQuaternionBlockPolynomial_supported
    (blocks block : Nat) (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks
      (conjugateQuaternionBlockPolynomial blocks block polynomial) := by
  intro term hterm
  unfold conjugateQuaternionBlockPolynomial signSelectedPolynomial at hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  simpa [signSelectedTerm] using hsupport source hsource

theorem quaternionHaar_conjugateQuaternionBlock
    (blocks block : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks
        (conjugateQuaternionBlockPolynomial blocks block polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact quaternionHaar_signSelected blocks
    (quaternionConjugateCoordinateSelector block) polynomial

/-- Left translation by the inverse (quaternion conjugate) of the selected
multiplier, realized as conjugate–translate–conjugate. -/
def selectedLeftInverseTranslatedPolynomial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
    (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct
      (conjugateQuaternionBlockPolynomial
        (tailBlocks + 1) multiplier polynomial))

/-- Right translation by the inverse of the selected multiplier. -/
def selectedRightInverseTranslatedPolynomial
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : RatPoly :=
  conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
    (selectedRightTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct
      (conjugateQuaternionBlockPolynomial
        (tailBlocks + 1) multiplier polynomial))

def selectedLeftInverseTranslationCheck
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : Bool :=
  selectedLeftTranslationCheck tailBlocks selected multiplier
    hblocks hselected hmultiplier hdistinct
    (conjugateQuaternionBlockPolynomial
      (tailBlocks + 1) multiplier polynomial)

def selectedRightInverseTranslationCheck
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) : Bool :=
  selectedRightTranslationCheck tailBlocks selected multiplier
    hblocks hselected hmultiplier hdistinct
    (conjugateQuaternionBlockPolynomial
      (tailBlocks + 1) multiplier polynomial)

theorem selectedLeftInverseTranslatedPolynomial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks (tailBlocks + 1)
      (selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedLeftInverseTranslatedPolynomial
  exact conjugateQuaternionBlockPolynomial_supported
    (tailBlocks + 1) multiplier _
    (selectedLeftTranslatedPolynomial_supported
      tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct _)

theorem selectedRightInverseTranslatedPolynomial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks (tailBlocks + 1)
      (selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedRightInverseTranslatedPolynomial
  exact conjugateQuaternionBlockPolynomial_supported
    (tailBlocks + 1) multiplier _
    (selectedRightTranslatedPolynomial_supported
      tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct _)

theorem selectedLeftTranslationPartial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks tailBlocks
      (selectedLeftTranslationPartial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedLeftTranslationPartial
  exact partialLeftTranslatedHeadPolynomial_supported tailBlocks hblocks _
    (exposeTranslationPairPolynomial_supported
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier polynomial)

theorem selectedRightTranslationPartial_supported
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks tailBlocks
      (selectedRightTranslationPartial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial) := by
  unfold selectedRightTranslationPartial
  exact partialRightTranslatedHeadPolynomial_supported tailBlocks hblocks _
    (exposeTranslationPairPolynomial_supported
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier polynomial)

/-- **Arbitrary-pair constructive left Haar translation.**  A successful
finite scan exposes the selected/multiplier pair, performs the left
translation, integrates the selected block, and preserves the full Haar
value. -/
theorem selectedLeftTranslationCheck_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedLeftTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar tailBlocks
        (selectedLeftTranslationPartial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  let exposed := exposeTranslationPairPolynomial
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier polynomial
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) exposed) _
    (leftTranslationPolynomialCheck_haar_sound tailBlocks hblocks exposed
      (exposeTranslationPairPolynomial_supported
        (tailBlocks + 1) selected multiplier (by omega)
        hselected hmultiplier polynomial)
      hcheck)
    (quaternionHaar_exposeTranslationPair
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier polynomial hsupport)

/-- Arbitrary-pair right-translation companion. -/
theorem selectedRightTranslationCheck_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedRightTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar tailBlocks
        (selectedRightTranslationPartial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  let exposed := exposeTranslationPairPolynomial
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier polynomial
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) exposed) _
    (rightTranslationPolynomialCheck_haar_sound tailBlocks hblocks exposed
      (exposeTranslationPairPolynomial_supported
        (tailBlocks + 1) selected multiplier (by omega)
        hselected hmultiplier polynomial)
      hcheck)
    (quaternionHaar_exposeTranslationPair
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier polynomial hsupport)

/-! ## 4. Block-count-preserving arbitrary-pair translations -/

/-- **Composable arbitrary-pair left Haar invariance.**  Unlike the partial
form above, this theorem keeps every quaternion block: expose, substitute,
and restore are one genuine change of variables. -/
theorem selectedLeftTranslatedPolynomial_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedLeftTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar (tailBlocks + 1)
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  unfold selectedLeftTranslatedPolynomial
  let exposed := exposeTranslationPairPolynomial
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier polynomial
  let translated := translatedHeadPolynomial
    leftTranslatedHeadQuaternion exposed
  change translationPolynomialCheck leftTranslationMomentCheck exposed =
    true at hcheck
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) translated) _
    (quaternionHaar_restoreTranslationPair
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier translated
      (leftTranslatedHeadPolynomial_supported tailBlocks hblocks exposed
        (exposeTranslationPairPolynomial_supported
          (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier polynomial)))
    (Q'.eqv_trans _
      (quaternionHaar (tailBlocks + 1) exposed) _
      (leftTranslatedHeadPolynomial_haar_sound tailBlocks hblocks exposed
        (exposeTranslationPairPolynomial_supported
          (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier polynomial)
        hcheck)
      (quaternionHaar_exposeTranslationPair
        (tailBlocks + 1) selected multiplier (by omega)
        hselected hmultiplier polynomial hsupport))

/-- Composable arbitrary-pair right Haar invariance. -/
theorem selectedRightTranslatedPolynomial_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedRightTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar (tailBlocks + 1)
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  unfold selectedRightTranslatedPolynomial
  let exposed := exposeTranslationPairPolynomial
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier polynomial
  let translated := translatedHeadPolynomial
    rightTranslatedHeadQuaternion exposed
  change translationPolynomialCheck rightTranslationMomentCheck exposed =
    true at hcheck
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) translated) _
    (quaternionHaar_restoreTranslationPair
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier translated
      (rightTranslatedHeadPolynomial_supported tailBlocks hblocks exposed
        (exposeTranslationPairPolynomial_supported
          (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier polynomial)))
    (Q'.eqv_trans _
      (quaternionHaar (tailBlocks + 1) exposed) _
      (rightTranslatedHeadPolynomial_haar_sound tailBlocks hblocks exposed
        (exposeTranslationPairPolynomial_supported
          (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier polynomial)
        hcheck)
      (quaternionHaar_exposeTranslationPair
        (tailBlocks + 1) selected multiplier (by omega)
        hselected hmultiplier polynomial hsupport))

/-- Composable left Haar invariance with a conjugated multiplier. -/
theorem selectedLeftInverseTranslatedPolynomial_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedLeftInverseTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar (tailBlocks + 1)
        (selectedLeftInverseTranslatedPolynomial
          tailBlocks selected multiplier hblocks hselected hmultiplier
          hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  let inverted := conjugateQuaternionBlockPolynomial
    (tailBlocks + 1) multiplier polynomial
  let translated := selectedLeftTranslatedPolynomial
    tailBlocks selected multiplier hblocks hselected hmultiplier hdistinct
    inverted
  change selectedLeftTranslationCheck tailBlocks selected multiplier
    hblocks hselected hmultiplier hdistinct inverted = true at hcheck
  change quaternionHaar (tailBlocks + 1)
      (conjugateQuaternionBlockPolynomial
        (tailBlocks + 1) multiplier translated) ≈
    quaternionHaar (tailBlocks + 1) polynomial
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) translated) _
    (quaternionHaar_conjugateQuaternionBlock
      (tailBlocks + 1) multiplier translated)
    (Q'.eqv_trans _
      (quaternionHaar (tailBlocks + 1) inverted) _
      (selectedLeftTranslatedPolynomial_haar_sound
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct inverted
        (conjugateQuaternionBlockPolynomial_supported
          (tailBlocks + 1) multiplier polynomial hsupport)
        hcheck)
      (quaternionHaar_conjugateQuaternionBlock
        (tailBlocks + 1) multiplier polynomial))

/-- Composable right Haar invariance with a conjugated multiplier. -/
theorem selectedRightInverseTranslatedPolynomial_haar_sound
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      selectedRightInverseTranslationCheck tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct polynomial = true) :
    quaternionHaar (tailBlocks + 1)
        (selectedRightInverseTranslatedPolynomial
          tailBlocks selected multiplier hblocks hselected hmultiplier
          hdistinct polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  let inverted := conjugateQuaternionBlockPolynomial
    (tailBlocks + 1) multiplier polynomial
  let translated := selectedRightTranslatedPolynomial
    tailBlocks selected multiplier hblocks hselected hmultiplier hdistinct
    inverted
  change selectedRightTranslationCheck tailBlocks selected multiplier
    hblocks hselected hmultiplier hdistinct inverted = true at hcheck
  change quaternionHaar (tailBlocks + 1)
      (conjugateQuaternionBlockPolynomial
        (tailBlocks + 1) multiplier translated) ≈
    quaternionHaar (tailBlocks + 1) polynomial
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) translated) _
    (quaternionHaar_conjugateQuaternionBlock
      (tailBlocks + 1) multiplier translated)
    (Q'.eqv_trans _
      (quaternionHaar (tailBlocks + 1) inverted) _
      (selectedRightTranslatedPolynomial_haar_sound
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct inverted
        (conjugateQuaternionBlockPolynomial_supported
          (tailBlocks + 1) multiplier polynomial hsupport)
        hcheck)
      (quaternionHaar_conjugateQuaternionBlock
        (tailBlocks + 1) multiplier polynomial))

end YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.quaternionHaar_exposeTranslationPair
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedLeftTranslationCheck_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedRightTranslationCheck_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedLeftTranslatedPolynomial_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedRightTranslatedPolynomial_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedLeftInverseTranslatedPolynomial_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslation.selectedRightInverseTranslatedPolynomial_haar_sound
