/-
# Reflection of the retained fine-intertwiner fibre

The lossless all-cutoff block carrier retains a complete fine SU(2)
intertwiner assignment whenever the ordinary coarse recoupling row is empty.
To reflect that carrier, it is unnecessary to choose a geometric convention
for every internal trivalent coordinate.  The production fibre is already a
duplicate-free ordered finite list, and reflection preserves its cardinality.

This module therefore gives the retained fibre a canonical constructive
reflection: record each assignment by its exact finite auxiliary word, read
its written rank, and select the same rank in the reflected physical fibre.
The finite words are injective on the production carrier.  Equal fibre
cardinality follows from the proved SU(2) link-multiplicity reflection law.
Consequently the rank transport lands in the reflected carrier and applying
it twice returns the original assignment.

This is a carrier theorem.  Reflection covariance of the enriched stochastic
kernel and of its pushed law are subsequent layers.  No OS positivity,
spectral estimate, continuum limit, or Clay theorem is asserted.

## Axiom gate

Structural finite-list ranks and the exact SU(2) multiplicity reflection
identity only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabExpandedTargetKey
import YMGap.Continuum.CompactDualWholeSlabRecouplingReflection
import YMGap.Continuum.FiniteBistochasticRankReindex

namespace YMGap.Continuum.CompactDualRetainedFineIntertwinerReflection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingReflection
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. Exact finite keys and their written ranks -/

/-- The finite auxiliary word is an exact decidable key for one assignment
inside a fixed production fibre. -/
def slabFineFusionWitnessKey
    (D : SlabPhysicalData)
    (assignment : SlabFusionWitnessAssignment) : List (List Nat) :=
  slabFusionWitnessAssignmentWords D.extent assignment

/-- The written key list of the complete retained fibre over one physical
state. -/
def slabFineFusionWitnessKeys
    (D : SlabPhysicalData) (physical : EdgeLabelling) :
    List (List (List Nat)) :=
  (slabFineFusionWitnesses D physical).map
    (slabFineFusionWitnessKey D)

/-- Exact finite keys have no duplicates on a fixed production fibre. -/
theorem slabFineFusionWitnessKeys_nodup
    (D : SlabPhysicalData) (physical : EdgeLabelling) :
    (slabFineFusionWitnessKeys D physical).Nodup := by
  unfold slabFineFusionWitnessKeys
  apply nodup_map_of_injOn
  · exact YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration.slabFineFusionWitnesses_nodup
      D physical
  · intro left hleft right hright hkey
    exact slabFusionWitnessAssignment_eq_of_words_eq
      D.cutoff D.extent physical physical left right hleft hright hkey

/-- Written rank of one assignment key in its physical production fibre. -/
def slabFineFusionWitnessRank
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (assignment : SlabFusionWitnessAssignment) : Nat :=
  listRank (slabFineFusionWitnessKey D assignment)
    (slabFineFusionWitnessKeys D physical)

private theorem listAtRank_map_local
    {A B : Type} (map : A → B) (fallback : A) :
    ∀ (items : List A) (rank : Nat),
      listAtRank (map fallback) (items.map map) rank =
        map (listAtRank fallback items rank)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: tail, rank + 1 =>
      listAtRank_map_local map fallback tail rank

/-! ## 2. Equal-rank reflection of the retained fibre -/

/-- Reflect a retained fine-intertwiner assignment by selecting the equal
written rank in the reflected physical fibre.  The empty assignment is only
a total fallback; membership proofs below show that it is never inspected on
the production carrier. -/
def reflectRetainedFineIntertwiner
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (assignment : SlabFusionWitnessAssignment) :
    SlabFusionWitnessAssignment :=
  listAtRank []
    (slabFineFusionWitnesses D (D.reflectLabelling physical))
    (slabFineFusionWitnessRank D physical assignment)

/-- Reflection preserves the exact cardinality of the retained production
fibre over every physical state in the slab carrier. -/
theorem slabFineFusionWitnesses_reflection_length
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    (slabFineFusionWitnesses
        D (D.reflectLabelling physical)).length =
      (slabFineFusionWitnesses D physical).length := by
  rw [slabFineFusionWitnesses_length,
    slabFineFusionWitnesses_length]
  exact slabLinkMultiplicityProduct_supported_reflection D hphysical

/-- Equal-rank reflection lands in the literal reflected production fibre. -/
theorem reflectRetainedFineIntertwiner_mem
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings)
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈
      slabFineFusionWitnesses D physical) :
    reflectRetainedFineIntertwiner D physical assignment ∈
      slabFineFusionWitnesses D (D.reflectLabelling physical) := by
  apply listAtRank_mem_of_lt
  rw [slabFineFusionWitnesses_reflection_length D hphysical]
  have hkey : slabFineFusionWitnessKey D assignment ∈
      slabFineFusionWitnessKeys D physical := by
    unfold slabFineFusionWitnessKeys
    exact List.mem_map.mpr ⟨assignment, hassignment, rfl⟩
  have hrank := listRank_lt_length_of_mem
    (slabFineFusionWitnessKey D assignment) hkey
  simpa only [slabFineFusionWitnessRank,
    slabFineFusionWitnessKeys, List.length_map] using hrank

/-- The reflected assignment has exactly the source's written key rank in
the reflected fibre. -/
theorem reflectRetainedFineIntertwiner_rank
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings)
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈
      slabFineFusionWitnesses D physical) :
    slabFineFusionWitnessRank D (D.reflectLabelling physical)
        (reflectRetainedFineIntertwiner D physical assignment) =
      slabFineFusionWitnessRank D physical assignment := by
  let rank := slabFineFusionWitnessRank D physical assignment
  let reflectedWitnesses :=
    slabFineFusionWitnesses D (D.reflectLabelling physical)
  have hrankLt : rank < reflectedWitnesses.length := by
    rw [slabFineFusionWitnesses_reflection_length D hphysical]
    have hkey : slabFineFusionWitnessKey D assignment ∈
        slabFineFusionWitnessKeys D physical := by
      unfold slabFineFusionWitnessKeys
      exact List.mem_map.mpr ⟨assignment, hassignment, rfl⟩
    have hlt := listRank_lt_length_of_mem
      (slabFineFusionWitnessKey D assignment) hkey
    simpa only [rank, slabFineFusionWitnessRank,
      slabFineFusionWitnessKeys, List.length_map] using hlt
  have hrankKeys : rank <
      (slabFineFusionWitnessKeys
        D (D.reflectLabelling physical)).length := by
    simpa only [slabFineFusionWitnessKeys, List.length_map] using hrankLt
  unfold slabFineFusionWitnessRank reflectRetainedFineIntertwiner
  change listRank
      (slabFineFusionWitnessKey D
        (listAtRank [] reflectedWitnesses rank))
      (slabFineFusionWitnessKeys
        D (D.reflectLabelling physical)) = rank
  rw [← listAtRank_map_local
    (slabFineFusionWitnessKey D) [] reflectedWitnesses rank]
  exact listRank_listAtRank_eq_of_lt
    (slabFineFusionWitnessKey D [])
    (slabFineFusionWitnessKeys_nodup
      D (D.reflectLabelling physical)) rank hrankKeys

private theorem listAtRank_witnessRank_eq
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    listAtRank [] (slabFineFusionWitnesses D physical)
        (slabFineFusionWitnessRank D physical assignment) =
      assignment := by
  let rank := slabFineFusionWitnessRank D physical assignment
  have hkey : slabFineFusionWitnessKey D assignment ∈
      slabFineFusionWitnessKeys D physical := by
    unfold slabFineFusionWitnessKeys
    exact List.mem_map.mpr ⟨assignment, hassignment, rfl⟩
  have hrankKeys := listRank_lt_length_of_mem
    (slabFineFusionWitnessKey D assignment) hkey
  have hrankWitnesses : rank <
      (slabFineFusionWitnesses D physical).length := by
    simpa only [rank, slabFineFusionWitnessRank,
      slabFineFusionWitnessKeys, List.length_map] using hrankKeys
  have hselected := listAtRank_mem_of_lt []
    (slabFineFusionWitnesses D physical) rank hrankWitnesses
  apply slabFusionWitnessAssignment_eq_of_words_eq
    D.cutoff D.extent physical physical _ _ hselected hassignment
  change slabFineFusionWitnessKey D
      (listAtRank [] (slabFineFusionWitnesses D physical) rank) =
    slabFineFusionWitnessKey D assignment
  rw [← listAtRank_map_local
    (slabFineFusionWitnessKey D) []
    (slabFineFusionWitnesses D physical) rank]
  exact listAtRank_listRank_eq_of_mem
    (slabFineFusionWitnessKey D [])
    (slabFineFusionWitnessKey D assignment) hkey

/-- Equal-rank retained reflection is an involution on the literal
production fibre. -/
theorem reflectRetainedFineIntertwiner_involutive
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings)
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈
      slabFineFusionWitnesses D physical) :
    reflectRetainedFineIntertwiner D (D.reflectLabelling physical)
        (reflectRetainedFineIntertwiner D physical assignment) =
      assignment := by
  have hrank := reflectRetainedFineIntertwiner_rank
    D hphysical hassignment
  have hrank' :
      slabFineFusionWitnessRank D (D.reflectLabelling physical)
          (listAtRank []
            (slabFineFusionWitnesses D (D.reflectLabelling physical))
            (slabFineFusionWitnessRank D physical assignment)) =
        slabFineFusionWitnessRank D physical assignment := by
    simpa only [reflectRetainedFineIntertwiner] using hrank
  unfold reflectRetainedFineIntertwiner
  rw [hrank']
  have hinvolutive :
      D.reflectLabelling (D.reflectLabelling physical) = physical := by
    unfold SlabPhysicalData.reflectLabelling
    apply reflectSupportedSlabFaceLabelling_involutive
    intro id hid
    exact (YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.boundedEdgeLabellings_sound
      D.cutoff D.faceEdges physical hphysical).2 id hid
  rw [hinvolutive]
  exact listAtRank_witnessRank_eq D physical hassignment

/-! ## Axiom audit -/

#print axioms slabFineFusionWitnessKeys_nodup
#print axioms slabFineFusionWitnesses_reflection_length
#print axioms reflectRetainedFineIntertwiner_mem
#print axioms reflectRetainedFineIntertwiner_rank
#print axioms reflectRetainedFineIntertwiner_involutive

end YMGap.Continuum.CompactDualRetainedFineIntertwinerReflection
