/-
# Boolean capacity scans and the conditional-Harnack frontier

The executable edge scan and the explicit conditional-Harnack target are two
presentations of the same finite statement.  This module proves that
equivalence on the actual full vacuum-sector carrier and transports cofinal
certificates in both directions.

The bridge is purely finite and algebraic.  It does not produce a cofinal
Harnack estimate, a completed gap inhabitant, a thermodynamic/continuum limit,
or a Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor

/-! ## 1. Exact finite equivalence -/

theorem cutoffTwoNovelEdgeCapacityCheck_iff_conditionalHarnack
    (later : Nat) :
    cutoffTwoNovelEdgeCapacityCheck later = true ↔
      ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalHarnackLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target := by
  constructor
  · intro hcheck source hsource target htarget
    have hfloor := cutoffTwoNovelEdgeCapacityCheck_sound later hcheck
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hfloor
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)
    have hfinite := cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
      later source target hsource htarget
    have hcapacity := Q'.le_trans' _ _ _ hscaled hfinite
    exact
      (cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget
        hsource target).mp hcapacity
  · intro hharnack
    apply cutoffTwoNovelEdgeCapacityCheck_complete
    exact cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_conditionalHarnack
      later hharnack

/-! ## 2. Cofinal certificates are transportable in both directions -/

namespace CutoffTwoCofinalNovelConditionalHarnackBound

def toEdgeCapacityCheck
    (bound : CutoffTwoCofinalNovelConditionalHarnackBound) :
    CutoffTwoCofinalNovelEdgeCapacityCheck where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  check := fun request =>
    (cutoffTwoNovelEdgeCapacityCheck_iff_conditionalHarnack
      (bound.anchor request)).mpr (bound.harnack request)

end CutoffTwoCofinalNovelConditionalHarnackBound

namespace CutoffTwoCofinalNovelEdgeCapacityCheck

def toConditionalHarnackBound
  (checked : CutoffTwoCofinalNovelEdgeCapacityCheck) :
    CutoffTwoCofinalNovelConditionalHarnackBound where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  harnack := by
    intro request source hsource target htarget
    have hall :=
      (cutoffTwoNovelEdgeCapacityCheck_iff_conditionalHarnack
        (checked.anchor request)).mp (checked.check request)
    exact hall source hsource target htarget

end CutoffTwoCofinalNovelEdgeCapacityCheck

theorem cofinal_harnack_roundtrip_anchor
    (bound : CutoffTwoCofinalNovelConditionalHarnackBound) :
    (CutoffTwoCofinalNovelEdgeCapacityCheck.toConditionalHarnackBound
      (CutoffTwoCofinalNovelConditionalHarnackBound.toEdgeCapacityCheck
        bound)).anchor =
      bound.anchor :=
  rfl

theorem cofinal_edge_roundtrip_anchor
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck) :
    (CutoffTwoCofinalNovelConditionalHarnackBound.toEdgeCapacityCheck
      (CutoffTwoCofinalNovelEdgeCapacityCheck.toConditionalHarnackBound
        checked)).anchor =
      checked.anchor :=
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge.cutoffTwoNovelEdgeCapacityCheck_iff_conditionalHarnack
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge.CutoffTwoCofinalNovelConditionalHarnackBound.toEdgeCapacityCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge.CutoffTwoCofinalNovelEdgeCapacityCheck.toConditionalHarnackBound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge.cofinal_harnack_roundtrip_anchor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge.cofinal_edge_roundtrip_anchor
