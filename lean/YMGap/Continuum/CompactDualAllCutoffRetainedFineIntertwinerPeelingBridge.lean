/-
# From retained all-cutoff targets to canonical component peeling

The lossless all-cutoff kernel retains exactly a fine physical labelling and
one accepted global link-intertwiner assignment.  The connected-component
machinery was developed on the attached version of precisely that expanded
datum.  This module identifies the two carriers constructively, embeds any
pair of retained targets in the accepted two-replica carrier, and runs the
existing complete canonical component peeling on it.

It also identifies the one-row normalized probability density with the
normalized expanded-source weight used by the component estimates.  Thus the
probability-flow and component-dynamics compilers now meet on the same object;
no forgetting projection is used at this seam.

No reflection lift, strict contraction estimate, spectral gap, continuum
limit, or Clay theorem is claimed.

## Axiom gate

Subtype attachment, exact rational algebra, and the existing well-founded
component peeling only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedProjection
import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The retained sector is the expanded component carrier -/

theorem allCutoffRetainedFineTarget_mem_iff
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment) :
    (Sum.inr target : AllCutoffRetainedTarget) ∈
        allCutoffRetainedTargets S ↔
      target ∈ slabExpandedFineSources S.fine := by
  unfold allCutoffRetainedTargets
  constructor
  · intro htarget
    rcases List.mem_append.mp htarget with hcoarse | hretained
    · obtain ⟨coarseState, _, heq⟩ := List.mem_map.mp hcoarse
      cases heq
    · obtain ⟨fineTarget, hfineTarget, heq⟩ :=
        List.mem_map.mp hretained
      injection heq with heq'
      exact heq' ▸ hfineTarget
  · intro htarget
    apply List.mem_append.mpr
    exact Or.inr (List.mem_map.mpr ⟨target, htarget, rfl⟩)

/-- Attach the exact expanded-carrier membership already encoded by a
retained target. -/
def retainedFineTargetExpandedEntry
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    SlabExpandedFineSourceEntry S.fine :=
  ⟨target, (allCutoffRetainedFineTarget_mem_iff S target).mp htarget⟩

/-- The physical source attached to the same retained target. -/
def retainedFineTargetPhysicalSource
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    SlabPhysicalSourceEntry S.fine :=
  ⟨target.1,
    (mem_slabExpandedFineSources_iff.mp
      ((allCutoffRetainedFineTarget_mem_iff S target).mp htarget)).1⟩

/-! ## 2. The exact normalized density seen by component estimates -/

/-- Normalize one literal expanded-source weight by the complete physical
partition. -/
def slabExpandedFineEntryNormalizedMass
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) : Q' :=
  Q'.divPos
    (slabExpandedFineEntryWeight D entry)
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- Weighting the retained conditional row by its normalized physical source
mass gives exactly the normalized expanded-source density used by component
peeling. -/
theorem normalizedMass_mul_retainedKernel_eqv_expandedMass
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hpositive : (0 : Q') < S.fine.physicalTerm target.1) :
    S.fine.normalizedMass target.1 *
        retainedSamePhysicalStateKernel
          (retainedFineTargetPhysicalSource S target htarget)
          hpositive target ≈
      slabExpandedFineEntryNormalizedMass S.fine
        (retainedFineTargetExpandedEntry S target htarget) := by
  have hcode : slabPhysicalStateCode S.fine target.1 =
      slabPhysicalStateCode S.fine target.1 := rfl
  unfold retainedSamePhysicalStateKernel
  rw [show (retainedFineTargetPhysicalSource S target htarget).1 =
    target.1 by rfl]
  rw [if_pos hcode]
  unfold SlabPhysicalData.normalizedMass Q'.divPos
    slabExpandedFineEntryNormalizedMass
  let inverse := Q'.recipPos S.fine.physicalPartition
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  let conditional :=
    retainedFineIntertwinerConditionalKernel
      (retainedSourceOfPhysicalEntry
        (retainedFineTargetPhysicalSource S target htarget) hpositive)
      target.2
  refine Q'.eqv_trans _
    ((S.fine.physicalTerm target.1 * conditional) * inverse) _ ?_ ?_
  · refine Q'.eqv_trans _
      (S.fine.physicalTerm target.1 * (inverse * conditional)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (S.fine.physicalTerm target.1 * (conditional * inverse)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv inverse conditional)
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  change
    (S.fine.physicalTerm target.1 * conditional) * inverse ≈
      slabExpandedFineEntryWeight S.fine
          (retainedFineTargetExpandedEntry S target htarget) * inverse
  apply Q'.mul_eqv_congr_right
  unfold slabExpandedFineEntryWeight slabExpandedFineSourceWeight
  exact physicalTerm_mul_conditionalKernel_eqv_fiberWeight
    (retainedSourceOfPhysicalEntry
      (retainedFineTargetPhysicalSource S target htarget) hpositive)
    target.2

/-! ## 3. Any two retained targets enter the accepted paired carrier -/

def retainedFinePairAcceptedState
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    SlabAcceptedTwoReplicaState S.fine :=
  (retainedFineTargetExpandedEntry S left hleft,
    retainedFineTargetExpandedEntry S right hright)

theorem retainedFinePairAcceptedState_mem
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    retainedFinePairAcceptedState S left right hleft hright ∈
      slabAcceptedTwoReplicaStates S.fine :=
  slabAcceptedTwoReplicaState_mem S.fine _

theorem retainedFinePairAcceptedState_mass
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    slabAcceptedTwoReplicaStateMass
        (retainedFinePairAcceptedState S left right hleft hright) =
      slabPhysicalLabellingMass S.fine.extent left.1 +
        slabPhysicalLabellingMass S.fine.extent right.1 := by
  rfl

/-! ## 4. Complete component peeling of the retained pair -/

def retainedFinePairFullPeeling
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    SlabAcceptedPairedCanonicalPeelingOutput S.fine :=
  slabAcceptedPairCanonicalPeeling
    S.fine (slabPhysicalFaceEdges S.fine.extent)
    (fun _ hface => hface)
    (retainedFinePairAcceptedState S left right hleft hright)

theorem retainedFinePairFullPeeling_final_zero
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    ∀ faceId, faceId ∈ slabPhysicalFaceEdges S.fine.extent →
      (retainedFinePairFullPeeling S left right hleft hright).1.1.1.1
          faceId = 0 ∧
        (retainedFinePairFullPeeling S left right hleft hright).1.2.1.1
          faceId = 0 := by
  exact slabAcceptedPairCanonicalPeeling_final_zero
    S.fine (slabPhysicalFaceEdges S.fine.extent)
    (fun _ hface => hface)
    (retainedFinePairAcceptedState S left right hleft hright)

theorem retainedFinePairFullPeeling_trace_valid
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    ∀ record,
      record ∈ (retainedFinePairFullPeeling
        S left right hleft hright).2 → record.Valid S.fine.extent := by
  exact slabAcceptedPairCanonicalPeeling_trace_valid
    S.fine (slabPhysicalFaceEdges S.fine.extent)
    (fun _ hface => hface)
    (retainedFinePairAcceptedState S left right hleft hright)

private theorem listNatWeight_eq_zero_of_pointwise
    {A : Type} (weight : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → weight item = 0) →
      listNatWeight weight items = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [listNatWeight, hzero head List.mem_cons_self,
        Nat.zero_add]
      exact listNatWeight_eq_zero_of_pointwise weight tail
        (fun item hitem => hzero item (List.mem_cons_of_mem head hitem))

theorem retainedFinePairFullPeeling_final_mass_zero
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    slabAcceptedTwoReplicaStateMass
        (retainedFinePairFullPeeling S left right hleft hright).1 = 0 := by
  have hzero := retainedFinePairFullPeeling_final_zero
    S left right hleft hright
  unfold slabAcceptedTwoReplicaStateMass slabPhysicalLabellingMass
  have hleftZero :
      listNatWeight
          (retainedFinePairFullPeeling
            S left right hleft hright).1.1.1.1
          (slabPhysicalFaceEdges S.fine.extent) = 0 := by
    apply listNatWeight_eq_zero_of_pointwise
    intro faceId hface
    exact (hzero faceId hface).1
  have hrightZero :
      listNatWeight
          (retainedFinePairFullPeeling
            S left right hleft hright).1.2.1.1
          (slabPhysicalFaceEdges S.fine.extent) = 0 := by
    apply listNatWeight_eq_zero_of_pointwise
    intro faceId hface
    exact (hzero faceId hface).2
  rw [hleftZero, hrightZero]

/-- The valid component trace removes exactly the complete two-replica
physical mass carried by the two retained targets. -/
theorem retainedFinePairFullPeeling_traceMass_exact
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S) :
    slabAcceptedPairedPeelTraceMass
        (retainedFinePairFullPeeling S left right hleft hright).2 =
      slabPhysicalLabellingMass S.fine.extent left.1 +
        slabPhysicalLabellingMass S.fine.extent right.1 := by
  have htelescope := slabAcceptedPairCanonicalPeeling_mass_telescope
    S.fine (slabPhysicalFaceEdges S.fine.extent)
    (fun _ hface => hface)
    (retainedFinePairAcceptedState S left right hleft hright)
  have hfinal := retainedFinePairFullPeeling_final_mass_zero
    S left right hleft hright
  have hinitial := retainedFinePairAcceptedState_mass
    S left right hleft hright
  change
    slabAcceptedTwoReplicaStateMass
          (retainedFinePairFullPeeling S left right hleft hright).1 +
        slabAcceptedPairedPeelTraceMass
          (retainedFinePairFullPeeling S left right hleft hright).2 =
      slabAcceptedTwoReplicaStateMass
        (retainedFinePairAcceptedState S left right hleft hright)
      at htelescope
  rw [hfinal, hinitial] at htelescope
  omega

/-! ## Axiom audit -/

#print axioms allCutoffRetainedFineTarget_mem_iff
#print axioms normalizedMass_mul_retainedKernel_eqv_expandedMass
#print axioms retainedFinePairAcceptedState_mem
#print axioms retainedFinePairFullPeeling_final_zero
#print axioms retainedFinePairFullPeeling_trace_valid
#print axioms retainedFinePairFullPeeling_traceMass_exact

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
