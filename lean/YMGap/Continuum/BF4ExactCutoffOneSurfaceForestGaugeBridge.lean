/-
# Actual BF4 cutoff-one forest-gauge surface bridge

This module closes the remaining semantic path from the literal 116-link BF4
surface coefficient to the exact five-based-cycle Haar value.  The only new
finite certificate counts compact-word incidences on the mask-dependent chord
blocks; it does not expand a face-factor product.

## Axiom gate

Finite list induction, checked degree-five translation, coefficient probes,
and the already-certified 128 surface evaluations only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

local infix:50 " ≈ " => Q'.eqv

/-! ## Compact selected-word degree -/

/-- One occurrence of the monitored block contributes one to the exact word
degree.  `Nat.beq` keeps the finite incidence path manifestly constructive. -/
def surfaceWordEntryBlockDegree
    (block : Nat) (entry : Nat × Bool) : Nat :=
  if Nat.beq block entry.1 then 1 else 0

/-- Exact occurrence count of one block in one compact oriented word. -/
def surfaceWordBlockDegree (block : Nat) : List (Nat × Bool) → Nat
  | [] => 0
  | entry :: rest =>
      surfaceWordEntryBlockDegree block entry +
        surfaceWordBlockDegree block rest

/-- Exact occurrence count of one block across a list of selected faces. -/
def surfaceFaceIdsBlockDegree (block : Nat) : List Nat → Nat
  | [] => 0
  | faceId :: rest =>
      surfaceWordBlockDegree block (surfaceActiveFaceWord faceId) +
        surfaceFaceIdsBlockDegree block rest

/-- Mask-dependent selected-face incidence in the active 32-block carrier. -/
def activeSurfaceSelectedWordBlockDegree
    (block mask : Nat) : Nat :=
  surfaceFaceIdsBlockDegree block (surfaceSelectedCompactFaceIds mask)

private theorem polyQuaternionOne_blockDegree_zero (block : Nat) :
    HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one := by
  constructor
  · exact hasQuaternionBlockDegree_one block
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0

private theorem orientedCoordinateQuaternion_surfaceWordEntryBlockDegree
    (block : Nat) (entry : Nat × Bool) :
    HasPolyQuaternionBlockDegree block
      (surfaceWordEntryBlockDegree block entry)
      (orientedCoordinateQuaternion entry.1 entry.2) := by
  by_cases hsame : block = entry.1
  · simpa [surfaceWordEntryBlockDegree, hsame] using
      (orientedCoordinateQuaternion_blockDegree entry.1 block entry.2)
  · simpa [surfaceWordEntryBlockDegree, hsame] using
      (orientedCoordinateQuaternion_blockDegree entry.1 block entry.2)

private theorem compactOrientedQuaternionWordFold_blockDegree
    (block : Nat) :
    ∀ (word : List (Nat × Bool)) (total : PolyQuaternion)
      (startDegree : Nat),
      HasPolyQuaternionBlockDegree block startDegree total →
      HasPolyQuaternionBlockDegree block
        (startDegree + surfaceWordBlockDegree block word)
        (word.foldl
          (fun product entry => PolyQuaternion.mul product
            (orientedCoordinateQuaternion entry.1 entry.2)) total)
  | [], total, startDegree, htotal => by
      simpa [surfaceWordBlockDegree] using htotal
  | entry :: rest, total, startDegree, htotal => by
      simp only [List.foldl_cons, surfaceWordBlockDegree]
      exact HasPolyQuaternionBlockDegree.relabel
        (Nat.add_assoc startDegree
          (surfaceWordEntryBlockDegree block entry)
          (surfaceWordBlockDegree block rest))
        (compactOrientedQuaternionWordFold_blockDegree block rest
          (PolyQuaternion.mul total
            (orientedCoordinateQuaternion entry.1 entry.2))
          (startDegree + surfaceWordEntryBlockDegree block entry)
          (htotal.mul
            (orientedCoordinateQuaternion_surfaceWordEntryBlockDegree
              block entry)))

theorem compactOrientedQuaternionWord_blockDegree
    (block : Nat) (word : List (Nat × Bool)) :
    HasPolyQuaternionBlockDegree block
      (surfaceWordBlockDegree block word)
      (compactOrientedQuaternionWord word) := by
  have hword := compactOrientedQuaternionWordFold_blockDegree block
    word PolyQuaternion.one 0 (polyQuaternionOne_blockDegree_zero block)
  simpa [compactOrientedQuaternionWord] using hword

theorem compactFundamentalWordFactor_blockDegree
    (block : Nat) (word : List (Nat × Bool)) :
    HasQuaternionBlockDegree block
      (surfaceWordBlockDegree block word)
      (compactFundamentalWordFactor word) := by
  simpa [compactFundamentalWordFactor, characterPolynomial] using
    (compactOrientedQuaternionWord_blockDegree block word).scalar.smul 2

private theorem surfaceFaceIdFactorProduct_blockDegree (block : Nat) :
    ∀ faceIds : List Nat,
      HasQuaternionBlockDegree block
        (surfaceFaceIdsBlockDegree block faceIds)
        (factorProduct (faceIds.map fun faceId =>
          compactFundamentalWordFactor (surfaceActiveFaceWord faceId)))
  | [] => by
      simpa [surfaceFaceIdsBlockDegree, factorProduct] using
        hasQuaternionBlockDegree_one block
  | faceId :: rest => by
      simp only [List.map_cons, factorProduct, surfaceFaceIdsBlockDegree]
      exact
        (compactFundamentalWordFactor_blockDegree block
          (surfaceActiveFaceWord faceId)).mul
        (surfaceFaceIdFactorProduct_blockDegree block rest)

/-- The selected active word product is exactly homogeneous in a block with
degree equal to its checked selected-face incidence. -/
theorem activeSurfaceSelectedWordFactorProduct_blockDegree
    (block mask : Nat) :
    HasQuaternionBlockDegree block
      (activeSurfaceSelectedWordBlockDegree block mask)
      (factorProduct (activeSurfaceSelectedWordFactors mask)) := by
  simpa [activeSurfaceSelectedWordBlockDegree,
      activeSurfaceSelectedWordFactors, surfaceActiveFaceWord] using
    (surfaceFaceIdFactorProduct_blockDegree block
      (surfaceSelectedCompactFaceIds mask))

/-- Executable degree-five certificate on precisely the mask-dependent chord
blocks monitored by the concrete forest translation ledger. -/
def activeSurfaceSelectedWordChordDegreeFiveCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    (surfaceActiveChordBlocks mask).all fun block =>
      decide (activeSurfaceSelectedWordBlockDegree block mask ≤ 5)

theorem activeSurfaceSelectedWordChordDegreeFiveCheck_true :
    activeSurfaceSelectedWordChordDegreeFiveCheck = true := by
  decide

theorem activeSurfaceSelectedWordBlockDegree_le_five
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (block : Nat) (hblock : block ∈ surfaceActiveChordBlocks mask) :
    activeSurfaceSelectedWordBlockDegree block mask ≤ 5 := by
  have hrow := List.all_eq_true.mp
    activeSurfaceSelectedWordChordDegreeFiveCheck_true mask hmask
  exact of_decide_eq_true (List.all_eq_true.mp hrow block hblock)

theorem activeSurfaceSelectedWordFactorProduct_chord_degree_five
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    QuaternionBlocksDegreeAtMost
      (surfaceActiveChordBlocks mask) 5
      (factorProduct (activeSurfaceSelectedWordFactors mask)) := by
  intro block hblock
  exact hasDegree_to_degreeAtMost
    (activeSurfaceSelectedWordFactorProduct_blockDegree block mask)
    (activeSurfaceSelectedWordBlockDegree_le_five
      mask hmask block hblock)

/-! ## Translated selected words reach the chord-only endpoint -/

private theorem quaternionHaar_polyOne_left_local
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

/-- Coefficient-probe equality in particular gives equality of the bare Haar
functionals. -/
theorem RatPolyCoeffEqv.bareHaar
    {blocks : Nat} {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polyOne left)) _
    (Q'.eqv_symm (quaternionHaar_polyOne_left_local blocks left))
    (Q'.eqv_trans _
      (quaternionHaar blocks (polyMul polyOne right)) _
      (YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.haarCarrier
        h polyOne)
      (quaternionHaar_polyOne_left_local blocks right))

/-- Constructive Haar invariance of the complete forest ledger on the compact
selected-word product. -/
theorem activeSurfaceSelectedWordFactorProduct_translation_haar
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (applySurfaceForestGaugeTranslationLedger mask hmask
          (factorProduct (activeSurfaceSelectedWordFactors mask))) ≈
      quaternionHaar 32
        (factorProduct (activeSurfaceSelectedWordFactors mask)) := by
  exact applySurfaceForestGaugeTranslationLedger_haar_degreeFive
    mask hmask (factorProduct (activeSurfaceSelectedWordFactors mask))
    (activeSurfaceSelectedWordFactorProduct_supported mask hmask)
    (activeSurfaceSelectedWordFactorProduct_chord_degree_five mask hmask)

/-- The compact selected word product reaches the padded substituted factor
product after the certified forest translation. -/
theorem activeSurfaceSelectedWordFactorProduct_haar_padded
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    quaternionHaar 32
        (factorProduct (activeSurfaceSelectedWordFactors mask)) ≈
      quaternionHaar 32
        (factorProduct
          (paddedActiveSubstitutedSurfaceGaugeFactors mask)) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (activeSurfaceSelectedWordFactorProduct_translation_haar mask hmask))
    (RatPolyCoeffEqv.bareHaar
      (applySurfaceForestGaugeLedger_activeWordFactorProduct_coeffEqv
        mask hmask hnonzero))

/-- Full selected-word endpoint, from active face words through the concrete
rooted forest and onto the exact mask-dependent chord evaluator. -/
theorem activeSurfaceSelectedWordFactorProduct_haar_forestGauge
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    quaternionHaar 32
        (factorProduct (activeSurfaceSelectedWordFactors mask)) ≈
      surfaceForestGaugeHaar mask := by
  exact Q'.eqv_trans _ _ _
    (activeSurfaceSelectedWordFactorProduct_haar_padded
      mask hmask hnonzero)
    (paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_endpoint
      mask hmask)

/-! ## Actual 116-link / Haar_5 surface closure -/

/-- The translated active-polynomial semantic obligation is now inhabited for
every nonempty certified surface. -/
theorem cutoffOneSurfaceForestGaugeTranslatedSemantics :
    CutoffOneSurfaceForestGaugeTranslatedSemantics := by
  intro mask hmask hnonzero
  exact Q'.eqv_trans _ (embeddedSurfaceActiveHaar mask) _
    (embeddedSurfaceActivePolynomial_translation_haar mask hmask)
    (Q'.eqv_trans _
      (exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling mask)) _
      (Q'.eqv_symm
        (exactEmbeddedSurfaceHaarCoefficient_eq_active mask hmask))
      (Q'.eqv_trans _
        (embeddedSurfaceSelectedActiveBivalentHaar mask) _
        (exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
          mask hmask hnonzero)
        (Q'.eqv_trans _
          (quaternionHaar 32
            (factorProduct (activeSurfaceSelectedWordFactors mask))) _
          (embeddedSurfaceSelectedActiveBivalentHaar_eq_wordHaar
            mask hmask)
          (activeSurfaceSelectedWordFactorProduct_haar_forestGauge
            mask hmask hnonzero))))

/-- Complete maximal-forest transport from each actual selected BF4 surface
coefficient to its exact chord-only evaluator. -/
theorem cutoffOneSurfaceForestGaugeTransport :
    CutoffOneSurfaceForestGaugeTransport :=
  cutoffOneSurfaceForestGaugeTransport_of_translatedSemantics
    cutoffOneSurfaceForestGaugeTranslatedSemantics

/-- **Actual BF4 Haar_5 surface bridge.**  Every literal 116-link cutoff-one
closed-surface coefficient, equivalently its five-based-cycle marginal on
`[0,4,5,6,10]`, has the certified topological Haar amplitude. -/
theorem actualBF4HaarFiveSurfaceBridge :
    CutoffOneClosedSurfaceTopologicalAmplitude :=
  cutoffOneClosedSurfaceTopologicalAmplitude_of_forestGauge
    cutoffOneSurfaceForestGaugeTransport
    cutoffOneSurfaceForestGaugeEvaluation

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge.activeSurfaceSelectedWordChordDegreeFiveCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge.activeSurfaceSelectedWordFactorProduct_translation_haar
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge.cutoffOneSurfaceForestGaugeTranslatedSemantics
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge.cutoffOneSurfaceForestGaugeTransport
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge.actualBF4HaarFiveSurfaceBridge
