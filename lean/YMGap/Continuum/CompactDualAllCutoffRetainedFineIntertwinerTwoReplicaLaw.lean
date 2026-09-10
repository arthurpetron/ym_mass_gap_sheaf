/-
# Exact two-replica law on the retained all-cutoff sector

At positive coupling, every retained expanded source has strictly positive
literal weight.  Since its fine-intertwiner weight occurs in the exact finite
fiber decomposition of the corresponding physical row, that physical row is
itself strictly positive.  Thus the targetwise retained blocked-density
identity applies without an additional row-positivity hypothesis.

This module then multiplies two such identities.  The resulting point mass is
exactly the normalized accepted two-replica weight already used by canonical
component peeling, with denominator the square of the physical partition.
Consequently the retained probability law and the component-weight compiler
agree on the same paired object, not merely after a forgetting projection.

No summation over a connected event, contraction estimate, reflection lift,
spectral gap, continuum limit, or Clay theorem is claimed.

## Axiom gate

Finite list induction, positivity, and exact rational quotient algebra only.
No classical choice, placeholder, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedDensity
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedDensity
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive expanded sources have positive physical rows -/

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A},
      selected ∈ items → value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

/-- A retained expanded entry at positive coupling forces positivity of its
genuine physical row; its positive fiber term occurs in the exact finite
fiber sum reconstructing that row. -/
theorem retainedFineTargetPhysicalTerm_pos_of_coupling_pos
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hcoupling : (0 : Q') < S.fine.coupling) :
    (0 : Q') < S.fine.physicalTerm target.1 := by
  let entry := retainedFineTargetExpandedEntry S target htarget
  have hwitness : target.2 ∈
      slabFineFusionWitnesses S.fine target.1 :=
    (mem_slabExpandedFineSources_iff.mp entry.2).2
  have hselectedPos : (0 : Q') <
      retainedFineIntertwinerPhysicalFiberWeight
        S.fine target.1 target.2 := by
    simpa only [entry, slabExpandedFineEntryWeight,
      slabExpandedFineSourceWeight] using
      slabExpandedFineEntryWeight_pos_of_coupling_pos
        S.fine hcoupling entry
  have hselectedLe :
      retainedFineIntertwinerPhysicalFiberWeight
          S.fine target.1 target.2 ≤
        listQSum
          (retainedFineIntertwinerPhysicalFiberWeight S.fine target.1)
          (slabFineFusionWitnesses S.fine target.1) := by
    apply listQSum_member_le_nonnegative
      (retainedFineIntertwinerPhysicalFiberWeight S.fine target.1)
    · intro witness
      exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.half
          target.1 witness
    · exact hwitness
  have hsumPos := Q'.pos_of_lt_of_le hselectedPos hselectedLe
  exact Q'.pos_of_lt_of_le hsumPos
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_total S.fine target.1))

/-! ## 2. Exact normalization of the accepted paired weight -/

/-- The accepted paired Gibbs point mass, normalized by the square of the
complete physical partition. -/
def slabAcceptedTwoReplicaStateNormalizedMass
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) : Q' :=
  Q'.divPos
    (slabAcceptedTwoReplicaStateWeight D state)
    (D.physicalPartition * D.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul4_rearrange_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
        (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
          (Q'.mul_eqv_congr_right (b * c) (c * b) d
            (Q'.mul_comm_eqv b c)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
            (Q'.mul_assoc_eqv c b d))
          (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))))))

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem normalizedEntryMass_mul_eqv_acceptedNormalizedMass
    (D : SlabPhysicalData)
    (left right : SlabExpandedFineSourceEntry D) :
    slabExpandedFineEntryNormalizedMass D left *
        slabExpandedFineEntryNormalizedMass D right ≈
      slabAcceptedTwoReplicaStateNormalizedMass D (left, right) := by
  let partitionPos := slabParametricKPhysicalPartition_pos
    D.coupling_nonnegative D.cutoff D.extent
  let squarePos := Q'.mul_pos partitionPos partitionPos
  apply Q'.eqv_symm
  apply divPos_eqv_of_eqv_mul_local squarePos
  refine Q'.eqv_trans _
    ((slabExpandedFineEntryNormalizedMass D left * D.physicalPartition) *
      (slabExpandedFineEntryNormalizedMass D right * D.physicalPartition)) _
    ?_ ?_
  · exact Q'.eqv_symm
      (mul_eqv_both_local
        (Q'.divPos_mul_eqv
          (slabExpandedFineEntryWeight D left)
          D.physicalPartition partitionPos)
        (Q'.divPos_mul_eqv
          (slabExpandedFineEntryWeight D right)
          D.physicalPartition partitionPos))
  · exact mul4_rearrange_local
      (slabExpandedFineEntryNormalizedMass D left)
      D.physicalPartition
      (slabExpandedFineEntryNormalizedMass D right)
      D.physicalPartition

/-! ## 3. The retained product law is the accepted paired law -/

/-- Product point mass assigned by the two independent copies of the enriched
retained blocked law. -/
def retainedFinePairBlockedPointMass
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment) : Q' :=
  allCutoffRetainedFineIntertwinerBlockedMass S (.inr left) *
    allCutoffRetainedFineIntertwinerBlockedMass S (.inr right)

/-- On two incoherent retained targets at positive coupling, the actual
two-replica blocked point mass is exactly the normalized accepted paired
weight used by component peeling. -/
theorem retainedFinePairBlockedPointMass_eqv_acceptedNormalizedMass
    (S : SlabScalePair)
    (left right : EdgeLabelling × SlabFusionWitnessAssignment)
    (hleft : (Sum.inr left : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hright : (Sum.inr right : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (hleftIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S left.1)
    (hrightIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S right.1) :
    retainedFinePairBlockedPointMass S left right ≈
      slabAcceptedTwoReplicaStateNormalizedMass S.fine
        (retainedFinePairAcceptedState S left right hleft hright) := by
  have hleftPositive :=
    retainedFineTargetPhysicalTerm_pos_of_coupling_pos
      S left hleft hcoupling
  have hrightPositive :=
    retainedFineTargetPhysicalTerm_pos_of_coupling_pos
      S right hright hcoupling
  refine Q'.eqv_trans _
    (slabExpandedFineEntryNormalizedMass S.fine
        (retainedFineTargetExpandedEntry S left hleft) *
      slabExpandedFineEntryNormalizedMass S.fine
        (retainedFineTargetExpandedEntry S right hright)) _ ?_ ?_
  · exact mul_eqv_both_local
      (allCutoffRetainedBlockedMass_eqv_expandedMass_of_incoherent
        S left hleft hleftPositive hleftIncoherent)
      (allCutoffRetainedBlockedMass_eqv_expandedMass_of_incoherent
        S right hright hrightPositive hrightIncoherent)
  · exact normalizedEntryMass_mul_eqv_acceptedNormalizedMass
      S.fine
      (retainedFineTargetExpandedEntry S left hleft)
      (retainedFineTargetExpandedEntry S right hright)

/-! ## Axiom audit -/

#print axioms retainedFineTargetPhysicalTerm_pos_of_coupling_pos
#print axioms slabAcceptedTwoReplicaStateNormalizedMass
#print axioms retainedFinePairBlockedPointMass_eqv_acceptedNormalizedMass

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw
