/-
# Constructive chains of selected quaternion Haar translations

A rooted-tree gauge substitution is not one monolithic algebraic rewrite.
At each vertex it applies a finite batch of left/right translations to link
blocks, sometimes by a tree quaternion and sometimes by its inverse.  This
module packages exactly those four elementary cases and proves that an
executable certificate for every successive finite polynomial preserves the
full product-Haar value of the entire chain.

The final interface groups the chain into exactly 25 vertex batches, matching
the displayed BF4 spatial tree.  It deliberately does not invent the literal
BF4 batch ledger: instantiating that finite geometry is the next seam.

## Axiom gate

Finite lists, decidable case splits, and the certified selected-pair
translation theorems only.  No `Classical.*`, `native_decide`, `sorry`, custom
axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

namespace YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

local infix:50 " ≈ " => Q'.eqv

inductive SelectedTranslationSide : Type
  | left
  | right

inductive SelectedMultiplierOrientation : Type
  | direct
  | inverse

/-- One certified pair shear on a fixed `(tailBlocks + 1)`-block carrier. -/
structure SelectedTranslationStep (tailBlocks : Nat) : Type where
  selected : Nat
  multiplier : Nat
  selected_lt : selected < tailBlocks + 1
  multiplier_lt : multiplier < tailBlocks + 1
  distinct : selected ≠ multiplier
  side : SelectedTranslationSide
  multiplierOrientation : SelectedMultiplierOrientation

def applySelectedTranslationStep
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (polynomial : RatPoly) : RatPoly :=
  match step.side, step.multiplierOrientation with
  | .left, .direct =>
      selectedLeftTranslatedPolynomial tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .right, .direct =>
      selectedRightTranslatedPolynomial tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .left, .inverse =>
      selectedLeftInverseTranslatedPolynomial tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .right, .inverse =>
      selectedRightInverseTranslatedPolynomial tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial

def selectedTranslationStepCheck
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (polynomial : RatPoly) : Bool :=
  match step.side, step.multiplierOrientation with
  | .left, .direct =>
      selectedLeftTranslationCheck tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .right, .direct =>
      selectedRightTranslationCheck tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .left, .inverse =>
      selectedLeftInverseTranslationCheck tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial
  | .right, .inverse =>
      selectedRightInverseTranslationCheck tailBlocks
        step.selected step.multiplier hblocks
        step.selected_lt step.multiplier_lt step.distinct polynomial

theorem applySelectedTranslationStep_supported
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks (tailBlocks + 1)
      (applySelectedTranslationStep hblocks step polynomial) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedLeftTranslatedPolynomial_supported tailBlocks
              step.selected step.multiplier hblocks
              step.selected_lt step.multiplier_lt step.distinct polynomial
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedLeftInverseTranslatedPolynomial_supported tailBlocks
              step.selected step.multiplier hblocks
              step.selected_lt step.multiplier_lt step.distinct polynomial
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedRightTranslatedPolynomial_supported tailBlocks
              step.selected step.multiplier hblocks
              step.selected_lt step.multiplier_lt step.distinct polynomial
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedRightInverseTranslatedPolynomial_supported tailBlocks
              step.selected step.multiplier hblocks
              step.selected_lt step.multiplier_lt step.distinct polynomial

/-- Every successful elementary certificate is a genuine full-Haar change of
variables on the unchanged carrier. -/
theorem applySelectedTranslationStep_haar_sound
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck : selectedTranslationStepCheck hblocks step polynomial = true) :
    quaternionHaar (tailBlocks + 1)
        (applySelectedTranslationStep hblocks step polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedLeftTranslatedPolynomial_haar_sound tailBlocks
            step.selected step.multiplier hblocks
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hsupport (by
              simpa [selectedTranslationStepCheck, hside, horientation]
                using hcheck)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedLeftInverseTranslatedPolynomial_haar_sound tailBlocks
            step.selected step.multiplier hblocks
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hsupport (by
              simpa [selectedTranslationStepCheck, hside, horientation]
                using hcheck)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedRightTranslatedPolynomial_haar_sound tailBlocks
            step.selected step.multiplier hblocks
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hsupport (by
              simpa [selectedTranslationStepCheck, hside, horientation]
                using hcheck)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            selectedRightInverseTranslatedPolynomial_haar_sound tailBlocks
            step.selected step.multiplier hblocks
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hsupport (by
              simpa [selectedTranslationStepCheck, hside, horientation]
                using hcheck)

/-! ## Successive finite-polynomial certificates -/

def applySelectedTranslationSteps
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    List (SelectedTranslationStep tailBlocks) → RatPoly → RatPoly
  | [], polynomial => polynomial
  | step :: rest, polynomial =>
      applySelectedTranslationSteps hblocks rest
        (applySelectedTranslationStep hblocks step polynomial)

/-- Each check is run on the polynomial produced by all preceding steps. -/
def selectedTranslationStepsCheck
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    List (SelectedTranslationStep tailBlocks) → RatPoly → Bool
  | [], _ => true
  | step :: rest, polynomial =>
      selectedTranslationStepCheck hblocks step polynomial &&
        selectedTranslationStepsCheck hblocks rest
          (applySelectedTranslationStep hblocks step polynomial)

theorem applySelectedTranslationSteps_supported
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (polynomial : RatPoly),
      SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
      SupportedQuaternionBlocks (tailBlocks + 1)
        (applySelectedTranslationSteps hblocks steps polynomial)
  | [], _, hsupport => hsupport
  | step :: rest, polynomial, _ =>
      applySelectedTranslationSteps_supported hblocks rest
        (applySelectedTranslationStep hblocks step polynomial)
        (applySelectedTranslationStep_supported hblocks step polynomial)

/-- **Constructive iterated selected-pair Haar invariance.** -/
theorem applySelectedTranslationSteps_haar_sound
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (polynomial : RatPoly),
      SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
      selectedTranslationStepsCheck hblocks steps polynomial = true →
      quaternionHaar (tailBlocks + 1)
          (applySelectedTranslationSteps hblocks steps polynomial) ≈
        quaternionHaar (tailBlocks + 1) polynomial
  | [], polynomial, _, _ => Q'.eqv_refl (quaternionHaar _ polynomial)
  | step :: rest, polynomial, hsupport, hcheck => by
      have hsplit :
          selectedTranslationStepCheck hblocks step polynomial = true ∧
            selectedTranslationStepsCheck hblocks rest
              (applySelectedTranslationStep hblocks step polynomial) = true :=
        by simpa [selectedTranslationStepsCheck] using hcheck
      exact Q'.eqv_trans _
        (quaternionHaar (tailBlocks + 1)
          (applySelectedTranslationStep hblocks step polynomial)) _
        (applySelectedTranslationSteps_haar_sound hblocks rest
          (applySelectedTranslationStep hblocks step polynomial)
          (applySelectedTranslationStep_supported hblocks step polynomial)
          hsplit.2)
        (applySelectedTranslationStep_haar_sound hblocks step polynomial
          hsupport hsplit.1)

/-! ## Executably certified raw ledgers -/

/-- Proof-free data used to generate a literal finite geometric ledger. -/
structure RawSelectedTranslationStep : Type where
  selected : Nat
  multiplier : Nat
  side : SelectedTranslationSide
  multiplierOrientation : SelectedMultiplierOrientation

def rawSelectedTranslationStepValid
    (tailBlocks : Nat) (step : RawSelectedTranslationStep) : Bool :=
  decide
    (step.selected < tailBlocks + 1 ∧
      step.multiplier < tailBlocks + 1 ∧
      step.selected ≠ step.multiplier)

def RawSelectedTranslationStep.certify
    {tailBlocks : Nat} (step : RawSelectedTranslationStep)
    (hvalid : rawSelectedTranslationStepValid tailBlocks step = true) :
    SelectedTranslationStep tailBlocks := by
  have hconditions :
      step.selected < tailBlocks + 1 ∧
        step.multiplier < tailBlocks + 1 ∧
        step.selected ≠ step.multiplier :=
    of_decide_eq_true hvalid
  exact
    { selected := step.selected
      multiplier := step.multiplier
      selected_lt := hconditions.1
      multiplier_lt := hconditions.2.1
      distinct := hconditions.2.2
      side := step.side
      multiplierOrientation := step.multiplierOrientation }

def rawSelectedTranslationStepsValid
    (tailBlocks : Nat) (steps : List RawSelectedTranslationStep) : Bool :=
  steps.all (rawSelectedTranslationStepValid tailBlocks)

/-- Convert a successfully checked proof-free ledger into the dependent
steps consumed by the soundness theorem. -/
def certifyRawSelectedTranslationSteps
    {tailBlocks : Nat} (steps : List RawSelectedTranslationStep)
    (hvalid : rawSelectedTranslationStepsValid tailBlocks steps = true) :
    List (SelectedTranslationStep tailBlocks) :=
  steps.attach.map fun entry =>
    entry.val.certify
      (List.all_eq_true.mp hvalid entry.val entry.property)

/-! ## Exactly 25 vertex batches for the BF4 tree -/

/-- A literal BF4 instantiation supplies 25 batches; a batch may contain
several elementary pair shears on links incident to that vertex. -/
structure TwentyFiveVertexTranslationLedger (tailBlocks : Nat) : Type where
  batches : List (List (SelectedTranslationStep tailBlocks))
  batch_count : batches.length = 25

def applyTwentyFiveVertexTranslationLedger
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (ledger : TwentyFiveVertexTranslationLedger tailBlocks)
    (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps hblocks ledger.batches.flatten polynomial

def twentyFiveVertexTranslationLedgerCheck
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (ledger : TwentyFiveVertexTranslationLedger tailBlocks)
    (polynomial : RatPoly) : Bool :=
  selectedTranslationStepsCheck hblocks ledger.batches.flatten polynomial

theorem applyTwentyFiveVertexTranslationLedger_haar_sound
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (ledger : TwentyFiveVertexTranslationLedger tailBlocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (hcheck :
      twentyFiveVertexTranslationLedgerCheck hblocks ledger polynomial =
        true) :
    quaternionHaar (tailBlocks + 1)
        (applyTwentyFiveVertexTranslationLedger hblocks ledger polynomial) ≈
      quaternionHaar (tailBlocks + 1) polynomial := by
  exact applySelectedTranslationSteps_haar_sound hblocks
    ledger.batches.flatten polynomial hsupport hcheck

end YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain.applySelectedTranslationStep_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain.applySelectedTranslationSteps_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain.applyTwentyFiveVertexTranslationLedger_haar_sound
