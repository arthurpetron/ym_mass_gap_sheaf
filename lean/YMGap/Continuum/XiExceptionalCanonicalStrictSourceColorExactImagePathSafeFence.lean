/-
# Exact-image path-safe compatibility fence

Restricting the canonical colored carrier to its exact source image removes
the ambient star overcount, but exact-image membership does not itself imply
the compatibility package needed by the existing path-safe allocation.

This module links the previously checked four-occurrence right-pivot source
directly to the exact image.  Its canonical code is in the exact image and
the constructive image decoder returns that precise source entry.  Nevertheless
its routed external residual is incompatible, so no `PathSafeRoutedFacts`
package exists for it.  The remaining analytic attack must therefore allocate
the explicit cross-side residual conflict; it cannot obtain path-safe facts
merely by recognizing an exact carrier image.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImage
import YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImagePathSafeFence

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImage

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Exact reconstruction of every encoded source entry -/

theorem entryCanonicalSourceColorCode_exactImageB_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exactCanonicalSourceImageB Gamma qP b1 b2
      (entryCanonicalSourceColorCode Gamma qP b1 b2 entry) = true := by
  apply (exactCanonicalSourceImageB_true_iff_entry
    Gamma qP b1 b2 _).mpr
  exact ⟨entry, List.mem_attach _ entry, rfl⟩

theorem exactCanonicalSourceReconstruct_encoded_entry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exactCanonicalSourceReconstruct Gamma qP b1 b2
        (entryCanonicalSourceColorCode Gamma qP b1 b2 entry) =
      some entry := by
  have himage := entryCanonicalSourceColorCode_exactImageB_true
    Gamma qP b1 b2 entry
  obtain ⟨other, hfind, _, hcode⟩ :=
    exactCanonicalSourceReconstruct_some_of_image
      Gamma qP b1 b2
      (entryCanonicalSourceColorCode Gamma qP b1 b2 entry) himage
  have hentry : other = entry :=
    entryCanonicalSourceColorCode_injective
      Gamma qP b1 b2 other entry hcode
  subst other
  exact hfind

/-! ## The precise obstruction to the existing path-safe target -/

theorem pathSafeRoutedFacts_imply_externalCompatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (facts : PathSafeRoutedFacts Gamma qP b1 b2 entry) :
    routedExternalCompatibleB Gamma qP b1 b2 entry = true := by
  simpa [routedExternalCompatibleB, entryRoutedExternal,
    routedLeftResidual, routedRightResidual] using facts.externalCompatible

def noPathSafeFactsOfExternalIncompatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hincompatible :
      routedExternalCompatibleB Gamma qP b1 b2 entry = false) :
    PathSafeRoutedFacts Gamma qP b1 b2 entry → False := by
  intro facts
  have htrue := pathSafeRoutedFacts_imply_externalCompatible
    Gamma qP b1 b2 entry facts
  rw [hincompatible] at htrue
  cases htrue

structure ExactImagePathSafeCounterexample where
  L : Lattice
  inst : DecidableEq L.Plaquette
  Gamma : List (Polymer L)
  qP : Polymer L → Bool
  b1 : Polymer L → Bool
  b2 : Polymer L → Bool
  entry : @ExceptionalSourceEntry L inst Gamma qP b1 b2
  fourOccurrences : Gamma.length = 4
  image : @exactCanonicalSourceImageB L inst Gamma qP b1 b2
      (@entryCanonicalSourceColorCode L inst Gamma qP b1 b2 entry) = true
  reconstructs : @exactCanonicalSourceReconstruct L inst Gamma qP b1 b2
      (@entryCanonicalSourceColorCode L inst Gamma qP b1 b2 entry) =
        some entry
  externalIncompatible :
    @routedExternalCompatibleB L inst Gamma qP b1 b2 entry = false
  pathSafeFactsImpossible :
    @PathSafeRoutedFacts L inst Gamma qP b1 b2 entry → False

def crossDetourExactImagePathSafeCounterexample :
    ExactImagePathSafeCounterexample :=
  { L := _
    inst := inferInstance
    Gamma := _
    qP := _
    b1 := _
    b2 := _
    entry :=
      YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence.entry
    fourOccurrences := by decide
    image := entryCanonicalSourceColorCode_exactImageB_true _ _ _ _ _
    reconstructs := exactCanonicalSourceReconstruct_encoded_entry _ _ _ _ _
    externalIncompatible :=
      YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence.routed_external_incompatible
    pathSafeFactsImpossible := noPathSafeFactsOfExternalIncompatible
      _ _ _ _ _
      YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence.routed_external_incompatible }

theorem exact_image_does_not_force_pathSafe_facts :
    Nonempty ExactImagePathSafeCounterexample :=
  ⟨crossDetourExactImagePathSafeCounterexample⟩

#print axioms entryCanonicalSourceColorCode_exactImageB_true
#print axioms exactCanonicalSourceReconstruct_encoded_entry
#print axioms pathSafeRoutedFacts_imply_externalCompatible
#print axioms noPathSafeFactsOfExternalIncompatible
#print axioms crossDetourExactImagePathSafeCounterexample
#print axioms exact_image_does_not_force_pathSafe_facts

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImagePathSafeFence
