/-
# Three matched shell faces for correlated capacity debt

At a fixed physical scale the next vacuum-sector pair carrier is a Cartesian
square.  Relative to the embedded current index carrier, its genuinely new
part has three ordered faces: old-new, new-old, and new-new.  This module
proves that those faces exhaust the exact new pair shell and gives each face
an independent summable correlated-debt envelope.

The three face budgets add to the new-shell envelope, which joins the
transported-old envelope and contracts through the unchanged matched
capacity-debt observable to the completed family.  No face estimate, tail
allowance, or initial closure is inhabited here.  No continuum or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Embedded-old and new index regions -/

def matchedEventualCanonicalVacuumSectorIndices
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorIndices
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + offset) 0

def matchedEventualCanonicalEmbeddedOldIndexCarrier
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : List Nat :=
  (matchedEventualCanonicalVacuumSectorIndices
    trajectory transitionStart physicalScale offset).map
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale offset)

def MatchedEventualCanonicalIndexInNewShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat) : Prop :=
  index ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (offset + 1) ∧
    index ∉ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale offset

theorem matchedEventualCanonicalEmbeddedOldIndexCarrier_mem_next
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat)
    (hindex : index ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale offset) :
    index ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (offset + 1) := by
  obtain ⟨currentIndex, hcurrentIndex, hmap⟩ := List.mem_map.mp hindex
  rw [← hmap]
  exact matchedEventualCanonicalCurrentIndexToNext_mem
    trajectory transitionStart physicalScale offset currentIndex hcurrentIndex

/-- Pair embedding is literally coordinatewise index embedding. -/
theorem mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    pair ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
        trajectory transitionStart physicalScale offset ↔
      pair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale offset ∧
        pair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale offset := by
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

/-! ## 2. Three exact ordered shell faces -/

def MatchedEventualCanonicalPairInOldNewShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Prop :=
  pair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale offset ∧
    MatchedEventualCanonicalIndexInNewShell
      trajectory transitionStart physicalScale offset pair.2

def MatchedEventualCanonicalPairInNewOldShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Prop :=
  MatchedEventualCanonicalIndexInNewShell
      trajectory transitionStart physicalScale offset pair.1 ∧
    pair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale offset

def MatchedEventualCanonicalPairInNewNewShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Prop :=
  MatchedEventualCanonicalIndexInNewShell
      trajectory transitionStart physicalScale offset pair.1 ∧
    MatchedEventualCanonicalIndexInNewShell
      trajectory transitionStart physicalScale offset pair.2

theorem matchedEventualCanonicalNewShellPair_face_cases
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewShell
      trajectory transitionStart physicalScale offset pair) :
    MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair ∨
      MatchedEventualCanonicalPairInNewOldShell
          trajectory transitionStart physicalScale offset pair ∨
        MatchedEventualCanonicalPairInNewNewShell
          trajectory transitionStart physicalScale offset pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair.1
  change pair.1 ∈ matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (offset + 1) ∧
      pair.2 ∈ matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (offset + 1) at hmembers
  by_cases hsourceOld : pair.1 ∈
      matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale offset
  · by_cases htargetOld : pair.2 ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale offset
    · exact False.elim (hpair.2
        ((mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff
          trajectory transitionStart physicalScale offset pair).mpr
          ⟨hsourceOld, htargetOld⟩))
    · exact Or.inl ⟨hsourceOld, hmembers.2, htargetOld⟩
  · by_cases htargetOld : pair.2 ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale offset
    · exact Or.inr (Or.inl
        ⟨⟨hmembers.1, hsourceOld⟩, htargetOld⟩)
    · exact Or.inr (Or.inr
        ⟨⟨hmembers.1, hsourceOld⟩, ⟨hmembers.2, htargetOld⟩⟩)

/-! ## 3. Three independent face envelopes -/

structure MatchedEventualCanonicalOldNewCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_current : forall offset pair,
    MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

structure MatchedEventualCanonicalNewOldCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_current : forall offset pair,
    MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

structure MatchedEventualCanonicalNewNewCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_current : forall offset pair,
    MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

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

/-! ## 4. Parallel faces contract to the exact new shell -/

def matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfFaces
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (oldNew : MatchedEventualCanonicalOldNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewShellCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := fun offset =>
    oldNew.variation offset +
      (newOld.variation offset + newNew.variation offset)
  variation_nonnegative := fun offset =>
    Q'.zero_le_add _ _
      (oldNew.variation_nonnegative offset)
      (Q'.zero_le_add _ _
        (newOld.variation_nonnegative offset)
        (newNew.variation_nonnegative offset))
  tailControl := addAntitoneTailControl oldNew.tailControl
    (addAntitoneTailControl newOld.tailControl newNew.tailControl)
  next_le_current := by
    intro offset pair hpair
    rcases matchedEventualCanonicalNewShellPair_face_cases
      trajectory transitionStart physicalScale offset pair hpair with
      holdNew | hnewOld | hnewNew
    · exact Q'.le_trans' _ _ _
        (oldNew.next_le_current offset pair holdNew)
        (base_add_component_le_threeSum
          (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair))
          (oldNew.variation offset)
          (oldNew.variation offset) (newOld.variation offset)
          (newNew.variation offset)
          (left_le_threeSum
            (oldNew.variation offset) (newOld.variation offset)
            (newNew.variation offset)
            (newOld.variation_nonnegative offset)
            (newNew.variation_nonnegative offset)))
    · exact Q'.le_trans' _ _ _
        (newOld.next_le_current offset pair hnewOld)
        (base_add_component_le_threeSum
          (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair))
          (newOld.variation offset)
          (oldNew.variation offset) (newOld.variation offset)
          (newNew.variation offset)
          (middle_le_threeSum
            (oldNew.variation offset) (newOld.variation offset)
            (newNew.variation offset)
            (oldNew.variation_nonnegative offset)
            (newNew.variation_nonnegative offset)))
    · exact Q'.le_trans' _ _ _
        (newNew.next_le_current offset pair hnewNew)
        (base_add_component_le_threeSum
          (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair))
          (newNew.variation offset)
          (oldNew.variation offset) (newOld.variation offset)
          (newNew.variation offset)
          (right_le_threeSum
            (oldNew.variation offset) (newOld.variation offset)
            (newNew.variation offset)
            (oldNew.variation_nonnegative offset)
            (newOld.variation_nonnegative offset)))

/-- The transported-old lane and all three shell-face lanes reconstruct the
single exact matched correlated envelope. -/
def matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndFaces
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (transport : MatchedEventualCanonicalTransportedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (oldNew : MatchedEventualCanonicalOldNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale :=
  matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
    transport
    (matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfFaces
      oldNew newOld newNew)

/-- Four scale-indexed leaf estimates rejoin the exact correlated observable
and construct the unchanged completed matched family. -/
def matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndFaces
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (transport : forall physicalScale,
      MatchedEventualCanonicalTransportedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (oldNew : forall physicalScale,
      MatchedEventualCanonicalOldNewCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (newOld : forall physicalScale,
      MatchedEventualCanonicalNewOldCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (newNew : forall physicalScale,
      MatchedEventualCanonicalNewNewCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndFaces
                (transport physicalScale)
                (oldNew physicalScale) (newOld physicalScale)
                (newNew physicalScale)))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    DynamicVacuumSectorCompletedFamily 0 :=
  matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily
    trajectory transitionStart
    (fun physicalScale =>
      matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndFaces
        (transport physicalScale)
        (oldNew physicalScale) (newOld physicalScale)
        (newNew physicalScale))
    tailAllowance tailAllowance_pos initial_closure

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.matchedEventualCanonicalEmbeddedOldIndexCarrier_mem_next
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.matchedEventualCanonicalNewShellPair_face_cases
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndFaces
