/-
# Descent from the finite-cylinder colimit to the signed centered state

The historical finite-cylinder common-refinement relation states exact event
equality after zero-extension into every common outer box.  This file proves
that the equality survives the centered re-encoding used by the bilateral
receding state.  The two key facts are constructive:

* equality of finite Boolean cylinder events is preserved by any common map
  on their marked roots; and
* centered canonical re-encoding commutes literally with canonical
  zero-extension through an intermediate box.

Consequently the old quotient-free common-refinement equivalence implies the
new aligned equivalence, so the unconditional signed centered value descends
to the already-defined finite-cylinder colimit.
-/

import YMGap.Continuum.Z4FiniteCylinderPresentationColimit
import YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement

namespace YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. Boolean event equality survives a common root re-encoding -/

def markedPreimageFamily
    (leftRoots rightRoots : List (List Nat))
    (reencode : List Nat → List Nat)
    (targetFamily : List (List Nat)) : List (List Nat) :=
  (leftRoots ++ rightRoots).filter
    (fun root => familyContainsPolymerB (reencode root) targetFamily)

theorem familyOccurrenceFingerprint_markedPreimage_left
    (leftRoots rightRoots : List (List Nat))
    (reencode : List Nat → List Nat)
    (targetFamily : List (List Nat)) :
    familyOccurrenceFingerprint leftRoots
        (markedPreimageFamily leftRoots rightRoots reencode targetFamily) =
      familyOccurrenceFingerprint (leftRoots.map reencode)
        targetFamily := by
  unfold familyOccurrenceFingerprint
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply, familyContainsPolymerB]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, markedPreimageFamily, List.mem_filter]
  constructor
  · intro hmem
    simpa [familyContainsPolymerB] using hmem.2
  · intro hmem
    exact ⟨List.mem_append_left rightRoots hroot,
      by simpa [familyContainsPolymerB] using hmem⟩

theorem familyOccurrenceFingerprint_markedPreimage_right
    (leftRoots rightRoots : List (List Nat))
    (reencode : List Nat → List Nat)
    (targetFamily : List (List Nat)) :
    familyOccurrenceFingerprint rightRoots
        (markedPreimageFamily leftRoots rightRoots reencode targetFamily) =
      familyOccurrenceFingerprint (rightRoots.map reencode)
        targetFamily := by
  unfold familyOccurrenceFingerprint
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply, familyContainsPolymerB]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, markedPreimageFamily, List.mem_filter]
  constructor
  · intro hmem
    simpa [familyContainsPolymerB] using hmem.2
  · intro hmem
    exact ⟨List.mem_append_right leftRoots hroot,
      by simpa [familyContainsPolymerB] using hmem⟩

theorem cylinderEvent_eq_map_common
    {leftRoots rightRoots : List (List Nat)}
    {leftPredicate rightPredicate : List Bool → Bool}
    (hevent : cylinderEvent leftRoots leftPredicate =
      cylinderEvent rightRoots rightPredicate)
    (reencode : List Nat → List Nat) :
    cylinderEvent (leftRoots.map reencode) leftPredicate =
      cylinderEvent (rightRoots.map reencode) rightPredicate := by
  funext targetFamily
  let sourceFamily := markedPreimageFamily
    leftRoots rightRoots reencode targetFamily
  have hsource := congrFun hevent sourceFamily
  unfold cylinderEvent at hsource ⊢
  rw [familyOccurrenceFingerprint_markedPreimage_left,
    familyOccurrenceFingerprint_markedPreimage_right] at hsource
  exact hsource

/-! ## 2. Canonical zero-extension commutes with centered re-encoding -/

private theorem sameSupport_map_centeredShift
    {left right : List Z4Plaq} (offset : Nat)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map (uniformShiftPlaquette offset))
      (right.map (uniformShiftPlaquette offset)) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, hsupport.2 source hsource, rfl⟩

theorem centeredOffsetCanonicalRoot_transport
    {source middle radius : Nat}
    (hsourceMiddle : source ≤ middle)
    (hmiddleRadius : middle ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers source) :
    centeredOffsetCanonicalRoot radius middle
        (transportPolymer source middle root) =
      centeredOffsetCanonicalRoot radius source root := by
  have htransport : transportPolymer source middle root ∈
      canonicalSurfacePolymers middle :=
    transportPolymer_mem_canonicalSurfacePolymers
      hsourceMiddle hroot
  have hleft : centeredOffsetCanonicalRoot radius middle
      (transportPolymer source middle root) ∈
        canonicalSurfacePolymers (centeredBoxBase radius) :=
    centeredOffsetCanonicalRoot_canonical hmiddleRadius htransport
  have hright : centeredOffsetCanonicalRoot radius source root ∈
      canonicalSurfacePolymers (centeredBoxBase radius) :=
    centeredOffsetCanonicalRoot_canonical
      (Nat.le_trans hsourceMiddle hmiddleRadius) hroot
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftSupport := centeredOffsetCanonicalRoot_sameSupport
    hmiddleRadius htransport
  have hrightSupport := centeredOffsetCanonicalRoot_sameSupport
    (Nat.le_trans hsourceMiddle hmiddleRadius) hroot
  have htransportSupport := transportPolymer_sameSupport
    hsourceMiddle (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hmapped := sameSupport_map_centeredShift radius htransportSupport
  exact sameSupport_trans hleftSupport
    (sameSupport_trans (sameSupport_symm hmapped)
      (sameSupport_symm hrightSupport))

theorem centeredOffsetCylinderRoots_transport
    {source middle radius : Nat}
    (hsourceMiddle : source ≤ middle)
    (hmiddleRadius : middle ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers source) :
    (transportedCylinderRoots source middle roots).map
        (centeredOffsetCanonicalRoot radius middle) =
      centeredOffsetCylinderRoots radius source roots := by
  unfold transportedCylinderRoots centeredOffsetCylinderRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact centeredOffsetCanonicalRoot_transport
    hsourceMiddle hmiddleRadius (hroots root hroot)

/-! ## 3. The signed presentation viewed in the historical finite colimit -/

/-- Forget only the signed chart origin.  The diagonal base, canonical roots,
and Boolean predicate are retained literally. -/
def signedCenteredFinitePresentation
    (presentation : SignedCenteredCylinderPresentation) :
    FiniteCylinderPresentation where
  chart := {
    base := signedCenteredPresentationDiagonalBase presentation
    roots := presentation.chart.roots
    rootsCanonical := signedCenteredPresentation_rootsCanonical presentation
  }
  predicate := presentation.predicate

/-- Centered re-encoding of an arbitrary historical finite presentation at
one absolute radius. -/
def centeredFinitePresentationEvent
    (absoluteRadius : Nat)
    (presentation : FiniteCylinderPresentation) :
    List (List Nat) → Bool :=
  cylinderEvent
    (centeredOffsetCylinderRoots absoluteRadius
      presentation.chart.base presentation.chart.roots)
    presentation.predicate

theorem centeredRecedingCylinderEvent_aligned_eq
    (presentation : SignedCenteredCylinderPresentation)
    (absoluteRadius : Nat)
    (hbase : signedCenteredPresentationDiagonalBase presentation ≤
      absoluteRadius) :
    centeredRecedingCylinderEvent
        (signedCenteredPresentationDiagonalBase presentation)
        (signedCenteredPresentationAlignedStage presentation absoluteRadius)
        presentation.chart.roots presentation.predicate =
      centeredFinitePresentationEvent absoluteRadius
        (signedCenteredFinitePresentation presentation) := by
  unfold centeredRecedingCylinderEvent centeredRecedingStageRoots
    centeredRecedingStageRadius signedCenteredPresentationAlignedStage
    centeredFinitePresentationEvent signedCenteredFinitePresentation
  rw [Nat.add_sub_of_le hbase]

/-! ## 4. The old refinement relation implies exact centered equality -/

theorem centeredFinitePresentationEvent_eq_of_refines
    {source target : FiniteCylinderPresentation}
    (hrefines : CylinderPresentationRefines source target)
    {absoluteRadius : Nat}
    (htarget : target.chart.base ≤ absoluteRadius) :
    centeredFinitePresentationEvent absoluteRadius target =
      centeredFinitePresentationEvent absoluteRadius source := by
  have hsource : source.chart.base ≤ absoluteRadius :=
    Nat.le_trans hrefines.base_le htarget
  have hevent := hrefines.event_eq absoluteRadius htarget
  unfold targetCylinderEvent at hevent
  have hmapped := cylinderEvent_eq_map_common hevent
    (centeredOffsetCanonicalRoot absoluteRadius absoluteRadius)
  have htargetRoots := centeredOffsetCylinderRoots_transport
    htarget (Nat.le_refl absoluteRadius)
      target.chart.rootsCanonical
  have hsourceRoots := centeredOffsetCylinderRoots_transport
    hsource (Nat.le_refl absoluteRadius)
      source.chart.rootsCanonical
  unfold centeredFinitePresentationEvent
  rw [← htargetRoots, ← hsourceRoots]
  exact hmapped

theorem signedCenteredPresentationAlignedEquivalent_of_finiteEquivalent
    {left right : SignedCenteredCylinderPresentation}
    (hequivalent : CylinderPresentationEquivalent
      (signedCenteredFinitePresentation left)
      (signedCenteredFinitePresentation right)) :
    SignedCenteredPresentationAlignedEquivalent left right := by
  rcases hequivalent with ⟨common, hleft, hright⟩
  refine ⟨common.chart.base, ?_, ?_, ?_⟩
  · exact hleft.base_le
  · exact hright.base_le
  · intro absoluteRadius habsolute
    have hleftAbsolute :
        signedCenteredPresentationDiagonalBase left ≤ absoluteRadius :=
      Nat.le_trans hleft.base_le habsolute
    have hrightAbsolute :
        signedCenteredPresentationDiagonalBase right ≤ absoluteRadius :=
      Nat.le_trans hright.base_le habsolute
    rw [centeredRecedingCylinderEvent_aligned_eq
        left absoluteRadius hleftAbsolute,
      centeredRecedingCylinderEvent_aligned_eq
        right absoluteRadius hrightAbsolute]
    exact Eq.trans
      (Eq.symm
        (centeredFinitePresentationEvent_eq_of_refines
          hleft habsolute))
      (centeredFinitePresentationEvent_eq_of_refines
        hright habsolute)

/-! Even identical signed charts and supports do not imply the historical
common-refinement relation: the Boolean predicate is indispensable.  This is
the finite-colimit form of the existing chart-only counterexample. -/
theorem chart_equality_does_not_imply_finiteEquivalent :
    emptySignedCenteredTruePresentation.chart =
        emptySignedCenteredFalsePresentation.chart ∧
      ¬ CylinderPresentationEquivalent
        (signedCenteredFinitePresentation
          emptySignedCenteredTruePresentation)
        (signedCenteredFinitePresentation
          emptySignedCenteredFalsePresentation) := by
  constructor
  · rfl
  · intro hequivalent
    exact chart_equality_does_not_imply_aligned_equivalence.2
      (signedCenteredPresentationAlignedEquivalent_of_finiteEquivalent
        hequivalent)

theorem couplingParametricSignedCenteredPresentationValueAtAnchor_respects_finiteEquivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {left right : SignedCenteredCylinderPresentation}
    (hequivalent : CylinderPresentationEquivalent
      (signedCenteredFinitePresentation left)
      (signedCenteredFinitePresentation right)) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle left)
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle right) := by
  exact couplingParametricSignedCenteredPresentationValueAtAnchor_respects
    hcoupling hle
    (signedCenteredPresentationAlignedEquivalent_of_finiteEquivalent
      hequivalent)

/-- The unconditional signed centered value, bundled with descent through the
historical quotient-free finite-cylinder common-refinement relation. -/
structure SignedCenteredFiniteColimitCylinderEvaluation where
  evaluate : SignedCenteredCylinderPresentation → CReal
  respects : ∀ left right,
    CylinderPresentationEquivalent
      (signedCenteredFinitePresentation left)
      (signedCenteredFinitePresentation right) →
      CReal.Equiv (evaluate left) (evaluate right)

def couplingParametricSignedCenteredFiniteColimitCylinderEvaluation
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    SignedCenteredFiniteColimitCylinderEvaluation where
  evaluate := couplingParametricSignedCenteredPresentationValueAtAnchor
    coupling hcoupling hle
  respects := fun _ _ hequivalent =>
    couplingParametricSignedCenteredPresentationValueAtAnchor_respects_finiteEquivalent
      hcoupling hle hequivalent

#print axioms cylinderEvent_eq_map_common
#print axioms centeredOffsetCanonicalRoot_transport
#print axioms centeredOffsetCylinderRoots_transport
#print axioms centeredRecedingCylinderEvent_aligned_eq
#print axioms centeredFinitePresentationEvent_eq_of_refines
#print axioms signedCenteredPresentationAlignedEquivalent_of_finiteEquivalent
#print axioms chart_equality_does_not_imply_finiteEquivalent
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor_respects_finiteEquivalent
#print axioms couplingParametricSignedCenteredFiniteColimitCylinderEvaluation

end YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent
