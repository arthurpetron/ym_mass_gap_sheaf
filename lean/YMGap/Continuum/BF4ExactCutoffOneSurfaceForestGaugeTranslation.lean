/-
# Orientation-aware BF4 surface forest-gauge translation ledger

For every one of the 128 certified closed surfaces, this module converts the
checked rooted maximal-forest paths into the exact selected-pair quaternion
translations on the 32-link active carrier.  To express an old chord through
its based-cycle coordinate, a chord from `tail` to `head` receives

```text
P(tail)^-1 * U_chord * P(head).
```

Both rooted paths are consumed in reverse order, as required by successive
polynomial substitutions.  A forward tail edge acts inversely on the left,
while a forward head edge acts directly on the right; backward edges use the
opposite multiplier orientation.  The Boolean certificate checks all
selected/multiplier bounds, forest/chord separation, and the complete
128-mask ledger geometry.

This file constructs the finite change-of-variables data.  The remaining
semantic step is to identify the translated selected-face factor network
with the pruned chord-only factor network.

## Axiom gate

Finite lists, checked forest paths, and constructive selected-pair Haar
translations only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

local infix:50 " ≈ " => Q'.eqv

/-- The active-carrier block occupied by a compact physical edge. -/
def surfaceActiveBlock (edgeId : Nat) : Nat :=
  activeCarrierToCompactEdgeIds.idxOf edgeId

def surfaceActiveForestBlocks (mask : Nat) : List Nat :=
  (surfacePrimalForestEdgeIds mask).map surfaceActiveBlock

def surfaceActiveChordBlocks (mask : Nat) : List Nat :=
  (surfaceForestGaugeChordEdgeIds mask).map surfaceActiveBlock

/-- Read the checked path from its component root to one vertex. -/
def surfaceRootPath (mask vertexId : Nat) : SurfaceForestPath :=
  ((surfacePrimalRootPaths mask).getD vertexId none).getD []

def surfaceRawLeftInversePathStep
    (selected : Nat) (entry : Nat × Bool) : RawSelectedTranslationStep where
  selected := selected
  multiplier := surfaceActiveBlock entry.1
  side := .left
  multiplierOrientation :=
    if entry.2 then .direct else .inverse

def surfaceRawRightPathStep
    (selected : Nat) (entry : Nat × Bool) : RawSelectedTranslationStep where
  selected := selected
  multiplier := surfaceActiveBlock entry.1
  side := .right
  multiplierOrientation :=
    if entry.2 then .inverse else .direct

/-- The oriented rooted-path shear word for one physical chord. -/
def surfaceChordRawTranslationSteps
    (mask edgeId : Nat) : List RawSelectedTranslationStep :=
  let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
  let selected := surfaceActiveBlock edgeId
  (surfaceRootPath mask endpoints.1).reverse.map
      (surfaceRawLeftInversePathStep selected) ++
    (surfaceRootPath mask endpoints.2).reverse.map
      (surfaceRawRightPathStep selected)

/-- Every chord shear, in the exact low-width chord order used by the
forest-gauge evaluator. -/
def surfaceForestGaugeRawTranslationLedger
    (mask : Nat) : List RawSelectedTranslationStep :=
  (surfaceForestGaugeChordEdgeIds mask).flatMap
    (surfaceChordRawTranslationSteps mask)

def rawSurfaceStepCompatible
    (mask : Nat) (step : RawSelectedTranslationStep) : Bool :=
  decide (step.selected ∈ surfaceActiveChordBlocks mask) &&
    decide (step.multiplier ∈ surfaceActiveForestBlocks mask) &&
    decide (step.multiplier ∉ surfaceActiveChordBlocks mask)

/-- Per-mask finite geometry check for the 32-link change of variables. -/
def surfaceForestGaugeRawTranslationCheck (mask : Nat) : Bool :=
  decide ((surfaceActiveChordBlocks mask).Nodup) &&
    rawSelectedTranslationStepsValid 31
      (surfaceForestGaugeRawTranslationLedger mask) &&
    (surfaceForestGaugeRawTranslationLedger mask).all
      (rawSurfaceStepCompatible mask)

def binarySurfaceForestGaugeRawTranslationCheck : Bool :=
  binarySurfaceMasks.all surfaceForestGaugeRawTranslationCheck

/-- The compact-edge/active-block table is a genuine permutation of all 32
physical edge ids. -/
theorem activeCarrierToCompactEdgeIds_permutationCheck :
    activeCarrierToCompactEdgeIds.length = 32 ∧
      activeCarrierToCompactEdgeIds.Nodup ∧
      activeCarrierToCompactEdgeIds.all (fun edgeId => decide (edgeId < 32)) =
        true := by
  decide

/-- All 128 orientation-aware forest-gauge ledgers are bounded and separate
their selected chord blocks from their forest multiplier blocks. -/
theorem binarySurfaceForestGaugeRawTranslationCheck_true :
    binarySurfaceForestGaugeRawTranslationCheck = true := by
  decide

theorem surfaceForestGaugeRawTranslationCheck_of_mem
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    surfaceForestGaugeRawTranslationCheck mask = true :=
  List.all_eq_true.mp
    binarySurfaceForestGaugeRawTranslationCheck_true mask hmask

theorem surfaceForestGaugeRawTranslationLedger_valid
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    rawSelectedTranslationStepsValid 31
      (surfaceForestGaugeRawTranslationLedger mask) = true := by
  have hcheck := surfaceForestGaugeRawTranslationCheck_of_mem mask hmask
  have hsplit :
      ((surfaceActiveChordBlocks mask).Nodup ∧
        rawSelectedTranslationStepsValid 31
          (surfaceForestGaugeRawTranslationLedger mask) = true) ∧
        ∀ step, step ∈ surfaceForestGaugeRawTranslationLedger mask →
          rawSurfaceStepCompatible mask step = true := by
    simpa [surfaceForestGaugeRawTranslationCheck] using hcheck
  exact hsplit.1.2

theorem surfaceForestGaugeRawTranslationLedger_compatible
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    ∀ step, step ∈ surfaceForestGaugeRawTranslationLedger mask →
      rawSurfaceStepCompatible mask step = true := by
  have hcheck := surfaceForestGaugeRawTranslationCheck_of_mem mask hmask
  have hsplit :
      ((surfaceActiveChordBlocks mask).Nodup ∧
        rawSelectedTranslationStepsValid 31
          (surfaceForestGaugeRawTranslationLedger mask) = true) ∧
        ∀ step, step ∈ surfaceForestGaugeRawTranslationLedger mask →
          rawSurfaceStepCompatible mask step = true := by
    simpa [surfaceForestGaugeRawTranslationCheck] using hcheck
  exact hsplit.2

/-- Proof-carrying 32-link translation steps extracted from the checked raw
ledger. -/
def surfaceForestGaugeTranslationSteps
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    List (SelectedTranslationStep 31) :=
  certifyRawSelectedTranslationSteps
    (surfaceForestGaugeRawTranslationLedger mask)
    (surfaceForestGaugeRawTranslationLedger_valid mask hmask)

private theorem certifiedStep_has_raw_source
    {tailBlocks : Nat} (rawSteps : List RawSelectedTranslationStep)
    (hvalid : rawSelectedTranslationStepsValid tailBlocks rawSteps = true)
    (step : SelectedTranslationStep tailBlocks)
    (hstep : step ∈ certifyRawSelectedTranslationSteps rawSteps hvalid) :
    ∃ source, source ∈ rawSteps ∧
      step.selected = source.selected ∧
      step.multiplier = source.multiplier := by
  unfold certifyRawSelectedTranslationSteps at hstep
  obtain ⟨entry, _, hentry⟩ := List.mem_map.mp hstep
  refine ⟨entry.val, entry.property, ?_, ?_⟩
  · rw [← hentry]
    rfl
  · rw [← hentry]
    rfl

/-- The dependent translation chain inherits the checked raw
forest/chord separation. -/
theorem surfaceForestGaugeTranslationSteps_degreeCompatible
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    selectedTranslationStepsDegreeCompatible
      (surfaceActiveChordBlocks mask)
      (surfaceForestGaugeTranslationSteps mask hmask) = true := by
  apply List.all_eq_true.mpr
  intro step hstep
  obtain ⟨source, hsource, hselected, hmultiplier⟩ :=
    certifiedStep_has_raw_source
      (surfaceForestGaugeRawTranslationLedger mask)
      (surfaceForestGaugeRawTranslationLedger_valid mask hmask)
      step hstep
  have hraw := surfaceForestGaugeRawTranslationLedger_compatible
    mask hmask source hsource
  have hproperties :
      (source.selected ∈ surfaceActiveChordBlocks mask ∧
        source.multiplier ∈ surfaceActiveForestBlocks mask) ∧
      source.multiplier ∉ surfaceActiveChordBlocks mask := by
    simpa [rawSurfaceStepCompatible] using hraw
  unfold selectedTranslationStepDegreeCompatible
  have hselectedMem : step.selected ∈ surfaceActiveChordBlocks mask := by
    rw [hselected]
    exact hproperties.1.1
  rw [decide_eq_true hselectedMem]
  apply List.all_eq_true.mpr
  intro block hblock
  apply decide_eq_true
  intro heq
  apply hproperties.2
  rw [← hmultiplier, ← heq]
  exact hblock

def binarySurfaceActiveChordBlocksBoundCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    (surfaceActiveChordBlocks mask).all fun block => decide (block < 32)

theorem binarySurfaceActiveChordBlocksBoundCheck_true :
    binarySurfaceActiveChordBlocksBoundCheck = true := by
  decide

theorem surfaceActiveChordBlock_lt
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (block : Nat) (hblock : block ∈ surfaceActiveChordBlocks mask) :
    block < 32 := by
  have hrow := List.all_eq_true.mp
    binarySurfaceActiveChordBlocksBoundCheck_true mask hmask
  exact of_decide_eq_true (List.all_eq_true.mp hrow block hblock)

def applySurfaceForestGaugeTranslationLedger
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (polynomial : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (by decide : 0 < 31)
    (surfaceForestGaugeTranslationSteps mask hmask) polynomial

theorem applySurfaceForestGaugeTranslationLedger_supported
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 32 polynomial) :
    SupportedQuaternionBlocks 32
      (applySurfaceForestGaugeTranslationLedger mask hmask polynomial) := by
  simpa [applySurfaceForestGaugeTranslationLedger] using
    applySelectedTranslationSteps_supported
      (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask)
      polynomial hsupport

/-- The complete concrete surface ledger preserves 32-fold product Haar.
The degree hypothesis is deliberately separated from the finite ledger and
is discharged by the selected-face incidence theorem in the next layer. -/
theorem applySurfaceForestGaugeTranslationLedger_haar_degreeFive
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 32 polynomial)
    (hdegree : QuaternionBlocksDegreeAtMost
      (surfaceActiveChordBlocks mask) 5 polynomial) :
    quaternionHaar 32
        (applySurfaceForestGaugeTranslationLedger mask hmask polynomial) ≈
      quaternionHaar 32 polynomial := by
  have hscan : selectedTranslationStepsCheck (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask) polynomial = true := by
    apply selectedTranslationStepsCheck_of_degreeCompatible_five
      (by decide : 0 < 31) (surfaceActiveChordBlocks mask)
    · exact surfaceActiveChordBlock_lt mask hmask
    · exact surfaceForestGaugeTranslationSteps_degreeCompatible mask hmask
    · exact hdegree
  simpa [applySurfaceForestGaugeTranslationLedger] using
    applySelectedTranslationSteps_haar_sound
      (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask)
      polynomial hsupport hscan

/-! ## Source degree and the exact translated-active endpoint -/

def binarySurfaceActiveChordSourceDegreeFiveCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    (surfaceActiveChordBlocks mask).all fun block =>
      decide
        (cutoffOneSlabSelectedBlockDegree
            (quaternionBlockSwapChainSource
              bf4SurfaceActiveCarrierSteps block)
            (embeddedSurfaceLabelling mask) ≤ 5)

/-- The actual selected incidence degree is at most five on every chord of
every certified surface, even though a mask-independent slab incidence bound
would be false for a few active raw links. -/
theorem binarySurfaceActiveChordSourceDegreeFiveCheck_true :
    binarySurfaceActiveChordSourceDegreeFiveCheck = true := by
  decide

theorem surfaceActiveChordSource_degree_le_five
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (block : Nat) (hblock : block ∈ surfaceActiveChordBlocks mask) :
    cutoffOneSlabSelectedBlockDegree
        (quaternionBlockSwapChainSource
          bf4SurfaceActiveCarrierSteps block)
        (embeddedSurfaceLabelling mask) ≤ 5 := by
  have hrow := List.all_eq_true.mp
    binarySurfaceActiveChordSourceDegreeFiveCheck_true mask hmask
  exact of_decide_eq_true (List.all_eq_true.mp hrow block hblock)

private theorem exponentAt_take_of_lt_local (monomial : List Nat) :
    ∀ (count coordinate : Nat), coordinate < count →
      exponentAt (monomial.take count) coordinate =
        exponentAt monomial coordinate
  | 0, coordinate, hcoordinate => False.elim (by omega)
  | count + 1, 0, _ => by
      cases monomial <;> rfl
  | count + 1, coordinate + 1, hcoordinate => by
      cases monomial with
      | nil => rfl
      | cons _ rest =>
          change exponentAt (rest.take count) coordinate =
            exponentAt rest coordinate
          exact exponentAt_take_of_lt_local rest count coordinate (by omega)

theorem trimQuaternionPolynomial_degreeAtMost
    (active block maxDegree : Nat) (hblock : block < active)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost block maxDegree polynomial) :
    QuaternionBlockDegreeAtMost block maxDegree
      (trimQuaternionPolynomial active polynomial) := by
  intro term hterm
  unfold trimQuaternionPolynomial at hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  unfold quaternionBlockDegree
  rw [exponentAt_take_of_lt_local source.1 (4 * active)
        (4 * block) (by omega),
      exponentAt_take_of_lt_local source.1 (4 * active)
        (4 * block + 1) (by omega),
      exponentAt_take_of_lt_local source.1 (4 * active)
        (4 * block + 2) (by omega),
      exponentAt_take_of_lt_local source.1 (4 * active)
        (4 * block + 3) (by omega)]
  exact hdegree source hsource

theorem trimQuaternionPolynomial_supported
    (blocks : Nat) (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (trimQuaternionPolynomial blocks polynomial) := by
  intro term hterm
  unfold trimQuaternionPolynomial at hterm
  obtain ⟨source, _, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact List.length_take_le (4 * blocks) source.1

/-- Every chord selected by a certified surface has degree at most five in
the original 32-link active polynomial. -/
theorem embeddedSurfaceActivePolynomial_chord_degree_five
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    QuaternionBlocksDegreeAtMost
      (surfaceActiveChordBlocks mask) 5
      (embeddedSurfaceActivePolynomial mask) := by
  intro block hblock
  have hblock32 := surfaceActiveChordBlock_lt mask hmask block hblock
  unfold embeddedSurfaceActivePolynomial
  apply trimQuaternionPolynomial_degreeAtMost 32 block 5 hblock32
  apply applyQuaternionBlockSwapChain_degreeAtMost
    bf4SurfaceActiveCarrierSteps (by omega)
  apply hasDegree_to_degreeAtMost
    (exactCorrectedSlabSpinNetworkIntegrand_cutoffOne_blockDegree
      (quaternionBlockSwapChainSource
        bf4SurfaceActiveCarrierSteps block)
      (embeddedSurfaceLabelling mask)
      (embeddedSurfaceLabelling_le_one mask))
  exact surfaceActiveChordSource_degree_le_five
    mask hmask block hblock

/-- The concrete forest ledger carries the original active surface
polynomial to a Haar-equivalent translated polynomial, unconditionally for
every certified surface. -/
theorem embeddedSurfaceActivePolynomial_translation_haar
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (applySurfaceForestGaugeTranslationLedger mask hmask
          (embeddedSurfaceActivePolynomial mask)) ≈
      embeddedSurfaceActiveHaar mask := by
  simpa [embeddedSurfaceActiveHaar] using
    applySurfaceForestGaugeTranslationLedger_haar_degreeFive
      mask hmask (embeddedSurfaceActivePolynomial mask)
      (trimQuaternionPolynomial_supported 32 _)
      (embeddedSurfaceActivePolynomial_chord_degree_five mask hmask)

/-- Only the translated-factor semantic identification remains between the
selected active evaluator and the concrete chord-only forest evaluator. -/
def CutoffOneSurfaceForestGaugeTranslatedSemantics : Prop :=
  ∀ mask : Nat, ∀ hmask : mask ∈ binarySurfaceMasks, mask ≠ 0 →
    quaternionHaar 32
        (applySurfaceForestGaugeTranslationLedger mask hmask
          (embeddedSurfaceActivePolynomial mask)) ≈
      surfaceForestGaugeHaar mask

/-- The translated-factor semantic identity closes the full forest-gauge
transport proposition; Haar invariance and the source degree are now proved
separately. -/
theorem cutoffOneSurfaceForestGaugeTransport_of_translatedSemantics
    (semantics : CutoffOneSurfaceForestGaugeTranslatedSemantics) :
    CutoffOneSurfaceForestGaugeTransport := by
  intro mask hmask hnonzero
  exact Q'.eqv_trans _
    (exactCorrectedSlabHaarCoefficient 1
      (embeddedSurfaceLabelling mask)) _
    (Q'.eqv_symm
      (exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
        mask hmask hnonzero))
    (Q'.eqv_trans _ (embeddedSurfaceActiveHaar mask) _
      (exactEmbeddedSurfaceHaarCoefficient_eq_active mask hmask)
      (Q'.eqv_trans _
        (quaternionHaar 32
          (applySurfaceForestGaugeTranslationLedger mask hmask
            (embeddedSurfaceActivePolynomial mask))) _
        (Q'.eqv_symm
          (embeddedSurfaceActivePolynomial_translation_haar mask hmask))
        (semantics mask hmask hnonzero)))

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.activeCarrierToCompactEdgeIds_permutationCheck
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.binarySurfaceForestGaugeRawTranslationCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.surfaceForestGaugeRawTranslationLedger_valid
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.surfaceForestGaugeTranslationSteps_degreeCompatible
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.applySurfaceForestGaugeTranslationLedger_haar_degreeFive
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.embeddedSurfaceActivePolynomial_chord_degree_five
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.embeddedSurfaceActivePolynomial_translation_haar
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation.cutoffOneSurfaceForestGaugeTransport_of_translatedSemantics
