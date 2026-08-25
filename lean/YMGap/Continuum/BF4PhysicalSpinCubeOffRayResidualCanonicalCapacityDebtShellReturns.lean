/-
# Explicit return points for the three canonical BF4 capacity-debt shell faces

The canonical later-to-current index recoding searches for an embedded old
preimage and otherwise returns the vacuum index zero.  On a coordinate proved
to lie outside the embedded image, the fallback is therefore not merely a
totalization device: it is definitionally the selected return point.

This module proves that fact and rewrites the three shell-face comparisons to
their explicit earlier endpoints:

* old-new returns to `(recoveredOld, 0)`;
* new-old returns to `(0, recoveredOld)`; and
* new-new returns to `(0, 0)`.

Independent analytic envelopes may now target those literal observable pairs
and then compile back to the existing face, shell, and full correlated-debt
interfaces.  No such envelope is inhabited.  The fixed strong-coupling anchor
is not the physical AF/grouped-BF4 trajectory, and no thermodynamic,
continuum, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.SummableCRealStepVariation

/-! ## 1. Non-image search returns the explicit fallback -/

theorem firstMappedPreimageOr_eq_fallback_of_not_mem_map
    (map : Nat -> Nat) (fallback target : Nat) :
    forall items : List Nat,
      target ∉ items.map map ->
        firstMappedPreimageOr map fallback target items = fallback
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : map head ≠ target := by
        intro heq
        apply hnot
        rw [List.map_cons]
        exact List.mem_cons.mpr (Or.inl heq.symm)
      simp only [firstMappedPreimageOr, hhead, if_false]
      apply firstMappedPreimageOr_eq_fallback_of_not_mem_map
      intro htail
      apply hnot
      rw [List.map_cons]
      exact List.mem_cons.mpr (Or.inr htail)

theorem anchorNextIndexToCurrent_eq_zero_of_newShell
    (scale index : Nat)
    (hindex : AnchorIndexInNewShell scale index) :
    anchorNextIndexToCurrent scale index = 0 := by
  unfold anchorNextIndexToCurrent
  exact firstMappedPreimageOr_eq_fallback_of_not_mem_map
    (anchorCurrentIndexToNext scale) 0 index
    (anchorVacuumSectorIndices scale) hindex.2

/-! ## 2. Literal return pairs for all three shell faces -/

def anchorOldNewReturnPair (scale : Nat) (pair : Nat × Nat) : Nat × Nat :=
  (anchorNextIndexToCurrent scale pair.1, 0)

def anchorNewOldReturnPair (scale : Nat) (pair : Nat × Nat) : Nat × Nat :=
  (0, anchorNextIndexToCurrent scale pair.2)

def anchorNewNewReturnPair (_scale : Nat) (_pair : Nat × Nat) : Nat × Nat :=
  (0, 0)

theorem anchorNextPairToCurrent_eq_oldNewReturn
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInOldNewShell scale pair) :
    anchorNextPairToCurrent scale pair =
      anchorOldNewReturnPair scale pair := by
  apply Prod.ext
  · rfl
  · exact anchorNextIndexToCurrent_eq_zero_of_newShell
      scale pair.2 hpair.2

theorem anchorNextPairToCurrent_eq_newOldReturn
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewOldShell scale pair) :
    anchorNextPairToCurrent scale pair =
      anchorNewOldReturnPair scale pair := by
  apply Prod.ext
  · exact anchorNextIndexToCurrent_eq_zero_of_newShell
      scale pair.1 hpair.1
  · rfl

theorem anchorNextPairToCurrent_eq_newNewReturn
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewNewShell scale pair) :
    anchorNextPairToCurrent scale pair =
      anchorNewNewReturnPair scale pair := by
  apply Prod.ext
  · exact anchorNextIndexToCurrent_eq_zero_of_newShell
      scale pair.1 hpair.1
  · exact anchorNextIndexToCurrent_eq_zero_of_newShell
      scale pair.2 hpair.2

theorem anchorOldNewReturnPair_mem
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInOldNewShell scale pair) :
    anchorOldNewReturnPair scale pair ∈ anchorVacuumSectorPairs scale := by
  rw [← anchorNextPairToCurrent_eq_oldNewReturn scale pair hpair]
  exact anchorNextPairToCurrent_mem scale pair

theorem anchorNewOldReturnPair_mem
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewOldShell scale pair) :
    anchorNewOldReturnPair scale pair ∈ anchorVacuumSectorPairs scale := by
  rw [← anchorNextPairToCurrent_eq_newOldReturn scale pair hpair]
  exact anchorNextPairToCurrent_mem scale pair

theorem anchorNewNewReturnPair_mem
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewNewShell scale pair) :
    anchorNewNewReturnPair scale pair ∈ anchorVacuumSectorPairs scale := by
  rw [← anchorNextPairToCurrent_eq_newNewReturn scale pair hpair]
  exact anchorNextPairToCurrent_mem scale pair

/-! ## 3. Observable-explicit return envelopes -/

structure AnchorCanonicalOldNewReturnCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_return : forall scale pair,
    AnchorPairInOldNewShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorOldNewReturnPair scale pair) + variation scale

structure AnchorCanonicalNewOldReturnCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_return : forall scale pair,
    AnchorPairInNewOldShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNewOldReturnPair scale pair) + variation scale

structure AnchorCanonicalNewNewReturnCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_return : forall scale pair,
    AnchorPairInNewNewShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNewNewReturnPair scale pair) + variation scale

def AnchorCanonicalOldNewReturnCapacityDebtEnvelope.toFaceEnvelope
    (data : AnchorCanonicalOldNewReturnCapacityDebtEnvelope) :
    AnchorCanonicalOldNewCapacityDebtEnvelope where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro scale pair hpair
    rw [anchorNextPairToCurrent_eq_oldNewReturn scale pair hpair]
    exact data.next_le_return scale pair hpair

def AnchorCanonicalNewOldReturnCapacityDebtEnvelope.toFaceEnvelope
    (data : AnchorCanonicalNewOldReturnCapacityDebtEnvelope) :
    AnchorCanonicalNewOldCapacityDebtEnvelope where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro scale pair hpair
    rw [anchorNextPairToCurrent_eq_newOldReturn scale pair hpair]
    exact data.next_le_return scale pair hpair

def AnchorCanonicalNewNewReturnCapacityDebtEnvelope.toFaceEnvelope
    (data : AnchorCanonicalNewNewReturnCapacityDebtEnvelope) :
    AnchorCanonicalNewNewCapacityDebtEnvelope where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro scale pair hpair
    rw [anchorNextPairToCurrent_eq_newNewReturn scale pair hpair]
    exact data.next_le_return scale pair hpair

/-! ## 4. Explicit return estimates rejoin the same correlated path -/

def anchorCanonicalNewShellCapacityDebtEnvelopeOfReturns
    (oldNew : AnchorCanonicalOldNewReturnCapacityDebtEnvelope)
    (newOld : AnchorCanonicalNewOldReturnCapacityDebtEnvelope)
    (newNew : AnchorCanonicalNewNewReturnCapacityDebtEnvelope) :
    AnchorCanonicalNewShellCapacityDebtEnvelope :=
  anchorCanonicalNewShellCapacityDebtEnvelopeOfFaces
    oldNew.toFaceEnvelope newOld.toFaceEnvelope newNew.toFaceEnvelope

def anchorCanonicalCapacityDebtEnvelopeOfTransportAndReturns
    (transport : AnchorCanonicalTransportedCapacityDebtEnvelope)
    (oldNew : AnchorCanonicalOldNewReturnCapacityDebtEnvelope)
    (newOld : AnchorCanonicalNewOldReturnCapacityDebtEnvelope)
    (newNew : AnchorCanonicalNewNewReturnCapacityDebtEnvelope) :
    AnchorCanonicalCapacityDebtEnvelope :=
  anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell transport
    (anchorCanonicalNewShellCapacityDebtEnvelopeOfReturns
      oldNew newOld newNew)

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.firstMappedPreimageOr_eq_fallback_of_not_mem_map
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorNextIndexToCurrent_eq_zero_of_newShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorNextPairToCurrent_eq_oldNewReturn
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorNextPairToCurrent_eq_newOldReturn
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorNextPairToCurrent_eq_newNewReturn
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorCanonicalNewShellCapacityDebtEnvelopeOfReturns
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.anchorCanonicalCapacityDebtEnvelopeOfTransportAndReturns
