/-
# Cofinal symmetric BF4 compiler with an exactly checked cross block

The old-to-new field of the symmetric three-block capacity interface now has
an exact finite Boolean checker at every cutoff.  This module substitutes those
checks into the cofinal compiler.  The resulting Type-level family asks only
for:

* a cofinal cutoff schedule;
* successful old-to-new scans on that schedule;
* explicit old--old capacity; and
* explicit new--new capacity.

Each successful scan constructs the cross field, and symmetry supplies the
reverse cross orientation.  The existing compiler then yields completed
vacuum-sector strict contraction.

The cofinal family is not inhabited here.  In particular the check-success,
old--old, and new--new fields remain honest analytic inputs.  No
thermodynamic/continuum construction or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

/-- Cofinal three-block capacity data in which the cross block is supplied by
the exact symmetric finite checker rather than an opaque inequality field. -/
structure CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  cross_check : ∀ request,
    cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck
      (anchor request) = true
  old_old : ∀ request source,
    source ∈ cutoffTwoEdgeLoadOldStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadOldStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad
            (anchor request) source target ≤
        cutoffTwoNovelAllocatedKernel
          (anchor request) source target
  new_new : ∀ request source,
    source ∈ cutoffTwoEdgeLoadNewStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad
            (anchor request) source target ≤
        cutoffTwoNovelAllocatedKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity

/-- The checked cross block and the two explicit same-block payments assemble
the existing cofinal symmetric oriented capacity family. -/
def toCofinalNovelSymmetricOrientedCapacity
    (family : CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity) :
    CutoffTwoCofinalNovelSymmetricOrientedCapacity where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  capacity := fun request => by
    let cross : CutoffTwoNovelSymmetricOldNewConditionalCapacityAt
        (family.anchor request) :=
      cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check
        (family.anchor request) (family.cross_check request)
    exact
      { old_old := fun source hsource target htarget =>
          family.old_old request source hsource target htarget
        old_new := fun source hsource target htarget =>
          cross.old_new source hsource target htarget
        new_new := fun source hsource target htarget =>
          family.new_new request source hsource target htarget }

/-- Cofinal success of the exact cross scans plus the two same-block capacity
fields reaches the completed vacuum-sector strict-contraction interface. -/
def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler.CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity.toCofinalNovelSymmetricOrientedCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler.CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity.toCompletedStrictContractionData
