/-
# Three-face decomposition of the canonical BF4 capacity-debt shell

The exact later pair carrier is a Cartesian square.  Relative to the embedded
earlier index carrier, its genuinely new part therefore has three ordered
faces:

* embedded-old source and new target;
* new source and embedded-old target; and
* new source and new target.

This module proves that these faces exhaust the previously defined new pair
shell and gives each face an independent summable correlated-debt envelope.
Their budgets add constructively to the single new-shell envelope, which then
joins the transported-old compiler without changing the downstream observable.

No face estimate is inhabited.  The decomposition only exposes three analytic
producers that may be built in parallel.  The fixed strong-coupling anchor is
not the physical AF/grouped-BF4 trajectory, and no thermodynamic, continuum,
or Clay conclusion is asserted.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Embedded-old and new index regions -/

def anchorVacuumSectorIndices (scale : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorIndices
    anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0

def anchorEmbeddedOldIndexCarrier (scale : Nat) : List Nat :=
  (anchorVacuumSectorIndices scale).map (anchorCurrentIndexToNext scale)

def AnchorIndexInNewShell (scale index : Nat) : Prop :=
  index ∈ anchorVacuumSectorIndices (scale + 1) ∧
    index ∉ anchorEmbeddedOldIndexCarrier scale

theorem anchorEmbeddedOldIndexCarrier_mem_next
    (scale index : Nat)
    (hindex : index ∈ anchorEmbeddedOldIndexCarrier scale) :
    index ∈ anchorVacuumSectorIndices (scale + 1) := by
  obtain ⟨currentIndex, hcurrentIndex, hmap⟩ := List.mem_map.mp hindex
  rw [← hmap]
  exact anchorCurrentIndexToNext_mem scale currentIndex hcurrentIndex

/-- Pair embedding is exactly coordinatewise index embedding. -/
theorem mem_anchorEmbeddedOldPairCarrier_iff
    (scale : Nat) (pair : Nat × Nat) :
    pair ∈ anchorEmbeddedOldPairCarrier scale ↔
      pair.1 ∈ anchorEmbeddedOldIndexCarrier scale ∧
        pair.2 ∈ anchorEmbeddedOldIndexCarrier scale := by
  constructor
  · intro hpair
    obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hpair
    have hmembers := (mem_cartesian_iff _ _ currentPair).mp hcurrentPair
    rw [← hmap]
    exact
      ⟨List.mem_map.mpr ⟨currentPair.1, hmembers.1, rfl⟩,
        List.mem_map.mpr ⟨currentPair.2, hmembers.2, rfl⟩⟩
  · intro hmembers
    obtain ⟨currentSource, hcurrentSource, hsourceMap⟩ :=
      List.mem_map.mp hmembers.1
    obtain ⟨currentTarget, hcurrentTarget, htargetMap⟩ :=
      List.mem_map.mp hmembers.2
    apply List.mem_map.mpr
    refine ⟨(currentSource, currentTarget), ?_, ?_⟩
    · exact (mem_cartesian_iff _ _ _).mpr
        ⟨hcurrentSource, hcurrentTarget⟩
    · apply Prod.ext
      · exact hsourceMap
      · exact htargetMap

/-! ## 2. The three exact ordered shell faces -/

def AnchorPairInOldNewShell (scale : Nat) (pair : Nat × Nat) : Prop :=
  pair.1 ∈ anchorEmbeddedOldIndexCarrier scale ∧
    AnchorIndexInNewShell scale pair.2

def AnchorPairInNewOldShell (scale : Nat) (pair : Nat × Nat) : Prop :=
  AnchorIndexInNewShell scale pair.1 ∧
    pair.2 ∈ anchorEmbeddedOldIndexCarrier scale

def AnchorPairInNewNewShell (scale : Nat) (pair : Nat × Nat) : Prop :=
  AnchorIndexInNewShell scale pair.1 ∧
    AnchorIndexInNewShell scale pair.2

/-- Every genuinely new pair belongs to exactly one of the three useful
ordered face alternatives (we only need exhaustiveness downstream). -/
theorem anchorNewShellPair_face_cases
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewShell scale pair) :
    AnchorPairInOldNewShell scale pair ∨
      AnchorPairInNewOldShell scale pair ∨
        AnchorPairInNewNewShell scale pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair.1
  change pair.1 ∈ anchorVacuumSectorIndices (scale + 1) ∧
      pair.2 ∈ anchorVacuumSectorIndices (scale + 1) at hmembers
  by_cases hsourceOld : pair.1 ∈ anchorEmbeddedOldIndexCarrier scale
  · by_cases htargetOld : pair.2 ∈ anchorEmbeddedOldIndexCarrier scale
    · exact False.elim (hpair.2
        ((mem_anchorEmbeddedOldPairCarrier_iff scale pair).mpr
          ⟨hsourceOld, htargetOld⟩))
    · exact Or.inl ⟨hsourceOld, hmembers.2, htargetOld⟩
  · by_cases htargetOld : pair.2 ∈ anchorEmbeddedOldIndexCarrier scale
    · exact Or.inr (Or.inl
        ⟨⟨hmembers.1, hsourceOld⟩, htargetOld⟩)
    · exact Or.inr (Or.inr
        ⟨⟨hmembers.1, hsourceOld⟩, ⟨hmembers.2, htargetOld⟩⟩)

/-! ## 3. Three independent face envelopes -/

structure AnchorCanonicalOldNewCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_current : forall scale pair,
    AnchorPairInOldNewShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair) + variation scale

structure AnchorCanonicalNewOldCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_current : forall scale pair,
    AnchorPairInNewOldShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair) + variation scale

structure AnchorCanonicalNewNewCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_current : forall scale pair,
    AnchorPairInNewNewShell scale pair ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair) + variation scale

private theorem left_le_threeSum
    (left middle right : Q')
    (hmiddle : (0 : Q') <= middle)
    (hright : (0 : Q') <= right) :
    left <= left + (middle + right) :=
  Q'.add_le_self_of_nonneg left (middle + right)
    (Q'.zero_le_add middle right hmiddle hright)

private theorem middle_le_threeSum
    (left middle right : Q')
    (hleft : (0 : Q') <= left)
    (hright : (0 : Q') <= right) :
    middle <= left + (middle + right) := by
  have hmiddleRight : middle <= middle + right :=
    Q'.add_le_self_of_nonneg middle right hright
  have hleftInsert : middle + right <= (middle + right) + left :=
    Q'.add_le_self_of_nonneg (middle + right) left hleft
  exact Q'.le_trans' _ _ _ hmiddleRight
    (Q'.le_trans' _ _ _ hleftInsert
      (Q'.le_of_eqv (Q'.add_comm_eqv (middle + right) left)))

private theorem right_le_threeSum
    (left middle right : Q')
    (hleft : (0 : Q') <= left)
    (hmiddle : (0 : Q') <= middle) :
    right <= left + (middle + right) := by
  have hmiddleInsert : right <= right + middle :=
    Q'.add_le_self_of_nonneg right middle hmiddle
  have hreorder : right + middle <= middle + right :=
    Q'.le_of_eqv (Q'.add_comm_eqv right middle)
  have hleftInsert : middle + right <= (middle + right) + left :=
    Q'.add_le_self_of_nonneg (middle + right) left hleft
  exact Q'.le_trans' _ _ _ hmiddleInsert
    (Q'.le_trans' _ _ _ hreorder
      (Q'.le_trans' _ _ _ hleftInsert
        (Q'.le_of_eqv (Q'.add_comm_eqv (middle + right) left))))

private theorem base_add_component_le_threeSum
    (base component left middle right : Q')
    (hcomponent : component <= left + (middle + right)) :
    base + component <= base + (left + (middle + right)) :=
  Q'.add_le_add_left base component (left + (middle + right)) hcomponent

/-! ## 4. Parallel face estimates contract to the shell and full envelope -/

def anchorCanonicalNewShellCapacityDebtEnvelopeOfFaces
    (oldNew : AnchorCanonicalOldNewCapacityDebtEnvelope)
    (newOld : AnchorCanonicalNewOldCapacityDebtEnvelope)
    (newNew : AnchorCanonicalNewNewCapacityDebtEnvelope) :
    AnchorCanonicalNewShellCapacityDebtEnvelope where
  variation := fun scale =>
    oldNew.variation scale +
      (newOld.variation scale + newNew.variation scale)
  variation_nonnegative := fun scale =>
    Q'.zero_le_add _ _
      (oldNew.variation_nonnegative scale)
      (Q'.zero_le_add _ _
        (newOld.variation_nonnegative scale)
        (newNew.variation_nonnegative scale))
  tailControl := addAntitoneTailControl oldNew.tailControl
    (addAntitoneTailControl newOld.tailControl newNew.tailControl)
  next_le_current := by
    intro scale pair hpair
    rcases anchorNewShellPair_face_cases scale pair hpair with
      holdNew | hnewOld | hnewNew
    · exact Q'.le_trans' _ _ _
        (oldNew.next_le_current scale pair holdNew)
        (base_add_component_le_threeSum
          (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair))
          (oldNew.variation scale)
          (oldNew.variation scale) (newOld.variation scale)
          (newNew.variation scale)
          (left_le_threeSum
            (oldNew.variation scale) (newOld.variation scale)
            (newNew.variation scale)
            (newOld.variation_nonnegative scale)
            (newNew.variation_nonnegative scale)))
    · exact Q'.le_trans' _ _ _
        (newOld.next_le_current scale pair hnewOld)
        (base_add_component_le_threeSum
          (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair))
          (newOld.variation scale)
          (oldNew.variation scale) (newOld.variation scale)
          (newNew.variation scale)
          (middle_le_threeSum
            (oldNew.variation scale) (newOld.variation scale)
            (newNew.variation scale)
            (oldNew.variation_nonnegative scale)
            (newNew.variation_nonnegative scale)))
    · exact Q'.le_trans' _ _ _
        (newNew.next_le_current scale pair hnewNew)
        (base_add_component_le_threeSum
          (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair))
          (newNew.variation scale)
          (oldNew.variation scale) (newOld.variation scale)
          (newNew.variation scale)
          (right_le_threeSum
            (oldNew.variation scale) (newOld.variation scale)
            (newNew.variation scale)
            (oldNew.variation_nonnegative scale)
            (newOld.variation_nonnegative scale)))

/-- The transported-old compiler and all three parallel shell-face compilers
reconstruct the exact single correlated envelope. -/
def anchorCanonicalCapacityDebtEnvelopeOfTransportAndFaces
    (transport : AnchorCanonicalTransportedCapacityDebtEnvelope)
    (oldNew : AnchorCanonicalOldNewCapacityDebtEnvelope)
    (newOld : AnchorCanonicalNewOldCapacityDebtEnvelope)
    (newNew : AnchorCanonicalNewNewCapacityDebtEnvelope) :
    AnchorCanonicalCapacityDebtEnvelope :=
  anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell transport
    (anchorCanonicalNewShellCapacityDebtEnvelopeOfFaces
      oldNew newOld newNew)

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.anchorEmbeddedOldIndexCarrier_mem_next
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.mem_anchorEmbeddedOldPairCarrier_iff
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.anchorNewShellPair_face_cases
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.anchorCanonicalNewShellCapacityDebtEnvelopeOfFaces
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.anchorCanonicalCapacityDebtEnvelopeOfTransportAndFaces
