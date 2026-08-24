/-
# Exact closure-or-crossing-edge decision for the embedded cutoff-two component

The embedded-boundary checker has a sound successful branch.  This file makes
its failed branch equally explicit: structural recursion over the finite
Cartesian pair list returns either a proof-carrying closure certificate or a
literal later support edge from the embedded cutoff-two vacuum component to a
new state.

The crossing target is then classified into the exact existing shell split:
it is either outside the whole cutoff-two positive carrier or belongs to a
previously separate cutoff-two positive component.  A crossing edge of the
first kind is not mislabeled as a component merger.

No larger-cutoff closure or crossing outcome is claimed in advance.  No
cofinal stability, completed contraction, thermodynamic/continuum
construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Generic constructive inspection of a finite Boolean scan -/

private inductive ListAllNotOutcome
    {Item : Type} (test : Item → Bool) (items : List Item) : Type
  | certified (all_not : items.all (fun item => !(test item)) = true)
  | found (item : Item) (item_mem : item ∈ items) (test_true : test item = true)

private def inspectListAllNot
    {Item : Type} (test : Item → Bool) :
    ∀ items : List Item, ListAllNotOutcome test items
  | [] => ListAllNotOutcome.certified rfl
  | first :: rest => by
      cases hfirst : test first with
      | true =>
          exact ListAllNotOutcome.found first List.mem_cons_self hfirst
      | false =>
          cases inspectListAllNot test rest with
          | certified hrest =>
              exact ListAllNotOutcome.certified (by
                simp only [List.all_cons, hfirst, Bool.not_false, hrest,
                  Bool.true_and])
          | found item hmem htrue =>
              exact ListAllNotOutcome.found item
                (List.mem_cons_of_mem first hmem) htrue

/-! ## 2. Exact closure-or-boundary-exit data -/

/-- Constructively inspect the exact pair list underlying the boundary scan. -/
def cutoffTwoEmbeddedVacuumBoundaryClosureDecision
    (later : Nat) (hcutoff : 2 ≤ later) :
    Sum (CutoffTwoEmbeddedVacuumBoundaryClosedCertificate later)
      (CutoffTwoEmbeddedVacuumBoundaryExit later) := by
  let embedded :=
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0
  let newStates := cutoffTwoEdgeLoadNewStates later
  let adjacent := fun pair : Nat × Nat =>
    centralPhysicalFiniteSupportAdjacentB
      cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
  cases inspectListAllNot adjacent (cartesian embedded newStates) with
  | certified hclosed =>
      exact Sum.inl
        { certified := by
            unfold cutoffTwoEmbeddedVacuumBoundaryClosedCheck
            exact hclosed }
  | found pair hpair hedge =>
      have hparts :=
        (mem_cartesian_iff embedded newStates pair).mp hpair
      have htargetParts :=
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mp
          hparts.2
      exact Sum.inr
        { source := pair.1
          target := pair.2
          source_mem_embedded := hparts.1
          target_not_mem_embedded := htargetParts.2
          source_mem_later_sector :=
            centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
              hcutoff hparts.1
          target_mem_later_sector := htargetParts.1
          edge := hedge }

/-! ## 3. Exact semantic trichotomy for the scan -/

/-- Every fixed later cutoff constructively yields one of three honest cases:
closed boundary, a crossing to a genuinely new positive state, or a crossing
into a previously separate old-positive component. -/
def cutoffTwoEmbeddedVacuumBoundaryTrichotomy
    (later : Nat) (hcutoff : 2 ≤ later) :
    Sum (CutoffTwoEmbeddedVacuumBoundaryClosedCertificate later)
      (Sum (CutoffTwoBoundaryExitOutsidePositiveTarget later)
        (CutoffTwoBoundaryExitComponentMergerTarget later)) := by
  cases cutoffTwoEmbeddedVacuumBoundaryClosureDecision later hcutoff with
  | inl certificate =>
      exact Sum.inl certificate
  | inr boundary =>
      exact Sum.inr
        (CutoffTwoEmbeddedVacuumBoundaryExit.targetShellDecision boundary)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision.cutoffTwoEmbeddedVacuumBoundaryClosureDecision
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision.cutoffTwoEmbeddedVacuumBoundaryTrichotomy
