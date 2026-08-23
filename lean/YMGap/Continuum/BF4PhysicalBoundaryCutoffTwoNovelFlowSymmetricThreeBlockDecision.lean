/-
# Exact finite decision for all three oriented symmetric BF4 blocks

The symmetric capacity compiler needs old--old, old-to-new, and new--new
payments.  The cross block already has a finite sufficient ceiling check.  This
module adds exact finite scans for the two diagonal blocks and combines all
three scans into a single cofinal interface.

At a fixed cutoff, constructive inspection returns either the complete
three-block capacity certificate or a literal failed edge, tagged by its
block.  Cross failure still concerns the conservative ratio-ceiling test and
therefore does not refute exact cross capacity; diagonal failure is exact for
the displayed capacity inequality.

The cofinal family is not inhabited here.  No scan-success theorem, uniform
analytic estimate, thermodynamic/continuum construction, or Clay conclusion
is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Exact diagonal-block scans -/

def cutoffTwoNovelSymmetricOldOldCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later pair.1 pair.2 ≤
        cutoffTwoNovelAllocatedKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricOldOldCapacityCheck_sound
    (later : Nat)
    (hcheck : cutoffTwoNovelSymmetricOldOldCapacityCheck later = true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadOldStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target := by
  unfold cutoffTwoNovelSymmetricOldOldCapacityCheck at hcheck
  intro source hsource target htarget
  have hpair : (source, target) ∈
      cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later) :=
    (mem_cartesian_iff _ _ (source, target)).2 ⟨hsource, htarget⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target) hpair)

theorem cutoffTwoNovelSymmetricOldOldCapacityCheck_complete
    (later : Nat)
    (hcapacity : ∀ source,
      source ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadOldStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target) :
    cutoffTwoNovelSymmetricOldOldCapacityCheck later = true := by
  unfold cutoffTwoNovelSymmetricOldOldCapacityCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hblocks :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later) pair).1 hpair
  apply decide_eq_true
  exact hcapacity pair.1 hblocks.1 pair.2 hblocks.2

def cutoffTwoNovelSymmetricNewNewCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later pair.1 pair.2 ≤
        cutoffTwoNovelAllocatedKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricNewNewCapacityCheck_sound
    (later : Nat)
    (hcheck : cutoffTwoNovelSymmetricNewNewCapacityCheck later = true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadNewStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target := by
  unfold cutoffTwoNovelSymmetricNewNewCapacityCheck at hcheck
  intro source hsource target htarget
  have hpair : (source, target) ∈
      cartesian
        (cutoffTwoEdgeLoadNewStates later)
        (cutoffTwoEdgeLoadNewStates later) :=
    (mem_cartesian_iff _ _ (source, target)).2 ⟨hsource, htarget⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target) hpair)

theorem cutoffTwoNovelSymmetricNewNewCapacityCheck_complete
    (later : Nat)
    (hcapacity : ∀ source,
      source ∈ cutoffTwoEdgeLoadNewStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target) :
    cutoffTwoNovelSymmetricNewNewCapacityCheck later = true := by
  unfold cutoffTwoNovelSymmetricNewNewCapacityCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hblocks :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
  apply decide_eq_true
  exact hcapacity pair.1 hblocks.1 pair.2 hblocks.2

/-! ## 2. One Boolean certificate for the three oriented blocks -/

def cutoffTwoNovelSymmetricThreeBlockCapacityCheck
    (later : Nat) : Bool :=
  cutoffTwoNovelSymmetricOldOldCapacityCheck later &&
    (cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later &&
      cutoffTwoNovelSymmetricNewNewCapacityCheck later)

/-- Success of the combined scan supplies exactly the three fields consumed by
the symmetry-reduced finite capacity compiler. -/
def cutoffTwoNovelSymmetricOrientedCapacityAt_of_threeBlockCheck
    (later : Nat)
    (hcheck : cutoffTwoNovelSymmetricThreeBlockCapacityCheck later = true) :
    CutoffTwoNovelSymmetricOrientedCapacityAt later := by
  have houter := (Bool.and_eq_true _ _).mp hcheck
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  let cross := cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check
    later hinner.1
  exact
    { old_old := cutoffTwoNovelSymmetricOldOldCapacityCheck_sound
        later houter.1
      old_new := cross.old_new
      new_new := cutoffTwoNovelSymmetricNewNewCapacityCheck_sound
        later hinner.2 }

theorem cutoffTwoNovelSymmetricThreeBlockCapacityCheck_complete
    (later : Nat)
    (hold : cutoffTwoNovelSymmetricOldOldCapacityCheck later = true)
    (hcross :
      cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later = true)
    (hnew : cutoffTwoNovelSymmetricNewNewCapacityCheck later = true) :
    cutoffTwoNovelSymmetricThreeBlockCapacityCheck later = true := by
  unfold cutoffTwoNovelSymmetricThreeBlockCapacityCheck
  exact (Bool.and_eq_true _ _).mpr
    ⟨hold, (Bool.and_eq_true _ _).mpr ⟨hcross, hnew⟩⟩

/-! ## 3. Constructive certificate-or-tagged-overloaded-edge inspection -/

inductive CutoffTwoNovelSymmetricThreeBlockCapacityOutcome
    (later : Nat) : Type 1
  | certified
      (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
  | overloadedOldOldEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadOldStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target)
  | overloadedCrossCeilingEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_ceiling_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedNewNewEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadNewStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target)

/-- Inspect all three finite blocks, preserving the first literal failed edge
as Type-level data. -/
def inspectCutoffTwoNovelSymmetricThreeBlockCapacity
    (later : Nat) :
    CutoffTwoNovelSymmetricThreeBlockCapacityOutcome later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later pair.1 pair.2)
      (fun pair : Nat × Nat =>
        cutoffTwoNovelAllocatedKernel later pair.1 pair.2)
      (cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later)) with
  | failed pair hpair hfailure =>
      have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadOldStates later) pair).1 hpair
      exact CutoffTwoNovelSymmetricThreeBlockCapacityOutcome.overloadedOldOldEdge
        pair.1 pair.2 hblocks.1 hblocks.2 hfailure
  | certified hold =>
      cases inspectCutoffTwoNovelSymmetricCrossFiniteRatioCeiling later with
      | overloadedCeilingEdge source target hsource htarget hfailure =>
          exact
            CutoffTwoNovelSymmetricThreeBlockCapacityOutcome.overloadedCrossCeilingEdge
              source target hsource htarget hfailure
      | certified cross =>
          cases inspectListComparison
              (fun pair : Nat × Nat =>
                cutoffTwoNovelSimpleFlowCoercivityFloor *
                  cutoffTwoNovelSymmetricEdgeLoad later pair.1 pair.2)
              (fun pair : Nat × Nat =>
                cutoffTwoNovelAllocatedKernel later pair.1 pair.2)
              (cartesian
                (cutoffTwoEdgeLoadNewStates later)
                (cutoffTwoEdgeLoadNewStates later)) with
          | failed pair hpair hfailure =>
              have hblocks :=
                (mem_cartesian_iff
                  (cutoffTwoEdgeLoadNewStates later)
                  (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
              exact
                CutoffTwoNovelSymmetricThreeBlockCapacityOutcome.overloadedNewNewEdge
                  pair.1 pair.2 hblocks.1 hblocks.2 hfailure
          | certified hnew =>
              apply CutoffTwoNovelSymmetricThreeBlockCapacityOutcome.certified
              exact
                { old_old := fun source hsource target htarget =>
                    hold (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩)
                  old_new := cross.old_new
                  new_new := fun source hsource target htarget =>
                    hnew (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩) }

/-! ## 4. Cofinal checked schedules compile to completed contraction -/

/-- A cofinal schedule on which the transparent three-block checker succeeds.
This is the remaining finite analytic input, not an inhabited theorem. -/
structure CutoffTwoCofinalNovelSymmetricThreeBlockCheck : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelSymmetricThreeBlockCapacityCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelSymmetricThreeBlockCheck

def toCofinalNovelSymmetricOrientedCapacity
    (checked : CutoffTwoCofinalNovelSymmetricThreeBlockCheck) :
    CutoffTwoCofinalNovelSymmetricOrientedCapacity where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  capacity := fun request =>
    cutoffTwoNovelSymmetricOrientedCapacityAt_of_threeBlockCheck
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked : CutoffTwoCofinalNovelSymmetricThreeBlockCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricThreeBlockCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.cutoffTwoNovelSymmetricOldOldCapacityCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.cutoffTwoNovelSymmetricNewNewCapacityCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.cutoffTwoNovelSymmetricOrientedCapacityAt_of_threeBlockCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.inspectCutoffTwoNovelSymmetricThreeBlockCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.CutoffTwoCofinalNovelSymmetricThreeBlockCheck.toCompletedStrictContractionData
