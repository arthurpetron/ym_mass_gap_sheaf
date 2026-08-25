/-
# Old-component and new-shell compiler for correlated BF4 capacity debt

The correlated capacity-debt envelope still quantifies over two changing
finite pair carriers.  This module locates its geometric content exactly.

The later carrier is divided into the image of the earlier carrier under the
physical cutoff embedding and its decidable complement.  On the embedded old
component, the constructive reverse recoding is already a proved left
inverse, so the required comparison is a transported two-sided estimate.  On
the complement, only the genuinely new-shell comparison remains.  Independent
summable budgets for those two regions add to the single envelope required by
the downstream maximum and persistence compilers.

No transported estimate, shell estimate, budget, or initial-slack witness is
constructed here.  In particular, no analytic persistence theorem is hidden
in the finite-list split.  The fixed strong-coupling anchor is not the
physical AF/grouped-BF4 trajectory, and no thermodynamic, continuum, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

/-! ## 1. Exact embedded-old and new-shell pair regions -/

/-- The literal image of the earlier vacuum-sector pair carrier in the next
cutoff.  Membership is decidable and supplies an actual earlier preimage. -/
def anchorEmbeddedOldPairCarrier (scale : Nat) : List (Nat × Nat) :=
  (anchorVacuumSectorPairs scale).map (anchorCurrentPairToNext scale)

theorem anchorCurrentPairToNext_mem_embeddedOld
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    anchorCurrentPairToNext scale pair ∈
      anchorEmbeddedOldPairCarrier scale := by
  exact List.mem_map.mpr ⟨pair, hpair, rfl⟩

theorem anchorEmbeddedOldPairCarrier_mem_next
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorEmbeddedOldPairCarrier scale) :
    pair ∈ anchorVacuumSectorPairs (scale + 1) := by
  obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hpair
  rw [← hmap]
  exact anchorCurrentPairToNext_mem scale currentPair hcurrentPair

/-- On exactly the embedded-old region, forward transport after the canonical
reverse search returns the given later pair. -/
theorem anchorCurrentPairToNext_nextToCurrent_of_mem_embeddedOld
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorEmbeddedOldPairCarrier scale) :
    anchorCurrentPairToNext scale (anchorNextPairToCurrent scale pair) =
      pair := by
  obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hpair
  rw [← hmap]
  rw [anchorNextPairToCurrent_currentToNext
    scale currentPair hcurrentPair]

/-- A later pair is in the genuinely new shell when it is in the exact next
carrier but not in the literal image of the earlier pair carrier. -/
def AnchorPairInNewShell (scale : Nat) (pair : Nat × Nat) : Prop :=
  pair ∈ anchorVacuumSectorPairs (scale + 1) ∧
    pair ∉ anchorEmbeddedOldPairCarrier scale

theorem anchorPair_old_or_newShell
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs (scale + 1)) :
    pair ∈ anchorEmbeddedOldPairCarrier scale ∨
      AnchorPairInNewShell scale pair := by
  by_cases hold : pair ∈ anchorEmbeddedOldPairCarrier scale
  · exact Or.inl hold
  · exact Or.inr ⟨hpair, hold⟩

/-! ## 2. Independently estimable old and shell envelopes -/

/-- Two-sided capacity-debt transport on the embedded old component.  Both
inequalities are indexed by the actual earlier pair, so the already proved
left inverse removes any reverse-search ambiguity. -/
structure AnchorCanonicalTransportedCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  current_le_next : forall scale pair,
    pair ∈ anchorVacuumSectorPairs scale ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence scale pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence
            (scale + 1) (anchorCurrentPairToNext scale pair) +
          variation scale
  next_le_current : forall scale pair,
    pair ∈ anchorVacuumSectorPairs scale ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence
          (scale + 1) (anchorCurrentPairToNext scale pair) <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale pair +
          variation scale

/-- The sole comparison on the genuinely new pair shell.  Its earlier
comparison point is definitionally the same canonical reverse recoding used
by the final dynamic-maximum compiler. -/
structure AnchorCanonicalNewShellCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_current : forall scale pair,
    AnchorPairInNewShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair) + variation scale

private theorem base_add_leftVariation_le_total
    (base leftVariation rightVariation : Q')
    (hright : (0 : Q') <= rightVariation) :
    base + leftVariation <= base + (leftVariation + rightVariation) := by
  exact Q'.add_le_add_left base leftVariation
    (leftVariation + rightVariation)
    (Q'.add_le_self_of_nonneg leftVariation rightVariation hright)

private theorem base_add_rightVariation_le_total
    (base leftVariation rightVariation : Q')
    (hleft : (0 : Q') <= leftVariation) :
    base + rightVariation <= base + (leftVariation + rightVariation) := by
  have hgrow : rightVariation <= rightVariation + leftVariation :=
    Q'.add_le_self_of_nonneg rightVariation leftVariation hleft
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left base rightVariation
      (rightVariation + leftVariation) hgrow)
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_left base
        (rightVariation + leftVariation)
        (leftVariation + rightVariation)
        (Q'.add_comm_eqv rightVariation leftVariation)))

/-! ## 3. The two regions contract to the single correlated envelope -/

/-- Add the independently summable transported-old and new-shell budgets.
The only case split is decidable membership in the exact embedded carrier. -/
def anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell
    (transport : AnchorCanonicalTransportedCapacityDebtEnvelope)
    (shell : AnchorCanonicalNewShellCapacityDebtEnvelope) :
    AnchorCanonicalCapacityDebtEnvelope where
  variation := fun scale =>
    transport.variation scale + shell.variation scale
  variation_nonnegative := fun scale =>
    Q'.zero_le_add _ _
      (transport.variation_nonnegative scale)
      (shell.variation_nonnegative scale)
  tailControl := addAntitoneTailControl
    transport.tailControl shell.tailControl
  current_le_next := by
    intro scale pair hpair
    exact Q'.le_trans' _ _ _
      (transport.current_le_next scale pair hpair)
      (base_add_leftVariation_le_total
        (anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence
          (scale + 1) (anchorCurrentPairToNext scale pair))
        (transport.variation scale) (shell.variation scale)
        (shell.variation_nonnegative scale))
  next_le_current := by
    intro scale pair hpair
    rcases anchorPair_old_or_newShell scale pair hpair with hold | hshell
    · obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hold
      rw [← hmap]
      rw [anchorNextPairToCurrent_currentToNext
        scale currentPair hcurrentPair]
      exact Q'.le_trans' _ _ _
        (transport.next_le_current scale currentPair hcurrentPair)
        (base_add_leftVariation_le_total
          (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale currentPair)
          (transport.variation scale) (shell.variation scale)
          (shell.variation_nonnegative scale))
    · exact Q'.le_trans' _ _ _
        (shell.next_le_current scale pair hshell)
        (base_add_rightVariation_le_total
          (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair))
          (transport.variation scale) (shell.variation scale)
          (transport.variation_nonnegative scale))

/-- After the geometric split, only the unchanged total-budget and
cutoff-zero slack witnesses remain before completed-family construction. -/
def anchorCanonicalCapacityDebtPersistenceOfTransportAndShell
    (transport : AnchorCanonicalTransportedCapacityDebtEnvelope)
    (shell : AnchorCanonicalNewShellCapacityDebtEnvelope)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorCanonicalCapacityDebtMaximumVariation
        (anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell
          transport shell)).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence where
  envelope :=
    anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell transport shell
  budget := budget
  budget_pos := budget_pos
  budget_from_zero := budget_from_zero
  initial_closure := initial_closure

/-- Explicit end-to-end contraction of the old/shell analytic certificates
to the existing completed fixed-anchor family. -/
def anchorGeometricCompletedFamilyOfTransportAndShell
    (transport : AnchorCanonicalTransportedCapacityDebtEnvelope)
    (shell : AnchorCanonicalNewShellCapacityDebtEnvelope)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorCanonicalCapacityDebtMaximumVariation
        (anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell
          transport shell)).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  (anchorCanonicalCapacityDebtPersistenceOfTransportAndShell
    transport shell budget budget_pos budget_from_zero initial_closure).toAnchorGeometricCompletedFamily

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorCurrentPairToNext_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorEmbeddedOldPairCarrier_mem_next
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorCurrentPairToNext_nextToCurrent_of_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorPair_old_or_newShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorCanonicalCapacityDebtPersistenceOfTransportAndShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.anchorGeometricCompletedFamilyOfTransportAndShell
