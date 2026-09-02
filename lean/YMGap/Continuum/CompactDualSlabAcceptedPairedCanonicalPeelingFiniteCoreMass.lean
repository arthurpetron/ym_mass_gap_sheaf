/-
# Cutoff-independent finite-core mass along accepted paired peeling

For one physical coordinate, splitting a legal drop into the paid exterior
and residual core parts makes the residual part exactly the decrease of
`min spin threshold`.  Summing over the corrected-slab face carrier and both
replicas gives a potential which telescopes through the complete accepted
canonical peeling.

On the complete face list the terminal state is zero, so the total residual
core mass along the entire path is exactly the initial threshold-truncated
pair mass.  In particular it is bounded by

  2 * faceCount * threshold,

independently of the representation cutoff.  This controls the accumulated
noncontractive `2^core` exponent; inverse-fiber entropy summation remains the
next step.

Constructive contract: natural-number arithmetic, explicit finite sums, and
well-founded accepted peeling only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Coordinatewise threshold potential -/

/-- Physical mass remaining after truncating every displayed coordinate at a
fixed threshold. -/
def slabThresholdCoreMass
    (extent : Nat) (threshold : Nat) (physical : SlabLabelling) : Nat :=
  listNatWeight (fun faceId => min (physical faceId) threshold)
    (slabPhysicalFaceEdges extent)

/-- Two-replica threshold potential. -/
def slabAcceptedTwoReplicaThresholdCoreMass
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) : Nat :=
  slabThresholdCoreMass D.extent threshold state.1.1.1 +
    slabThresholdCoreMass D.extent threshold state.2.1.1

/-- At one coordinate, residual core drop is exactly the loss of truncated
potential. -/
theorem min_sub_add_coreResidualDropCount
    (physical drop threshold : Nat) (hdrop : drop <= physical) :
    min (physical - drop) threshold +
        (drop - min drop (physical - threshold)) =
      min physical threshold := by
  by_cases hphysical : physical <= threshold
  · have hsub : physical - threshold = 0 := Nat.sub_eq_zero_of_le hphysical
    have hlower : physical - drop <= threshold := by omega
    rw [Nat.min_eq_left hphysical, Nat.min_eq_left hlower, hsub,
      Nat.min_eq_right (Nat.zero_le drop)]
    omega
  · have hthreshold : threshold <= physical := by omega
    rw [Nat.min_eq_right hthreshold]
    by_cases hsmall : drop <= physical - threshold
    · have hlower : threshold <= physical - drop := by omega
      rw [Nat.min_eq_right hlower, Nat.min_eq_left hsmall]
      omega
    · have hlarge : physical - threshold <= drop := by omega
      have hlower : physical - drop <= threshold := by omega
      rw [Nat.min_eq_left hlower, Nat.min_eq_right hlarge]
      omega

private theorem listNatWeight_thresholdCore_telescope
    (physical drop : Nat -> Nat) (threshold : Nat) :
    forall faces : List Nat,
      (forall faceId, faceId ∈ faces -> drop faceId <= physical faceId) ->
      listNatWeight (fun faceId =>
          min (physical faceId - drop faceId) threshold) faces +
        listNatWeight (fun faceId =>
          coreResidualDropCount physical threshold drop faceId) faces =
        listNatWeight (fun faceId => min (physical faceId) threshold) faces
  | [], _ => rfl
  | faceId :: faces, hdrop => by
      have hhead := min_sub_add_coreResidualDropCount
        (physical faceId) (drop faceId) threshold
        (hdrop faceId List.mem_cons_self)
      have htail := listNatWeight_thresholdCore_telescope
        physical drop threshold faces
          (fun next hnext =>
            hdrop next (List.mem_cons_of_mem faceId hnext))
      simp only [listNatWeight, coreResidualDropCount,
        exteriorDropCount] at htail ⊢
      omega

private theorem flatMap_replicate_length
    (drop : Nat -> Nat) : forall faces : List Nat,
    (faces.flatMap fun faceId => List.replicate (drop faceId) faceId).length =
      listNatWeight drop faces
  | [] => rfl
  | faceId :: faces => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, listNatWeight]
      rw [flatMap_replicate_length drop faces]

theorem slabFaceDropList_length_eq_listNatWeight
    (extent : Nat) (drop : Nat -> Nat) :
    (slabFaceDropList extent drop).length =
      listNatWeight drop (slabPhysicalFaceEdges extent) := by
  unfold slabFaceDropList
  exact flatMap_replicate_length drop (slabPhysicalFaceEdges extent)

/-! ## 2. One accepted component step -/

/-- The residual size of one actual accepted component is exactly the loss of
the one-replica threshold potential. -/
theorem acceptedExpandedSourceLowerAt_thresholdCoreMass_add_residual
    (D : SlabPhysicalData) (threshold faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    slabThresholdCoreMass D.extent threshold
          (acceptedExpandedSourceLowerAt
            D faceId hface entry hpositive).1.1 +
        acceptedExpandedSourceCoreResidualSizeAt
          D threshold faceId hface entry hpositive =
      slabThresholdCoreMass D.extent threshold entry.1.1 := by
  let seed := acceptedExpandedSourceRootSeed
    D faceId hface entry hpositive
  change slabThresholdCoreMass D.extent threshold
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) +
      (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
        seed threshold).length =
    slabThresholdCoreMass D.extent threshold entry.1.1
  unfold SlabFusionWitnessFaceStrandSeed.coreResidualFaces
    highSpinCoreResidualFaces
  rw [slabFaceDropList_length_eq_listNatWeight]
  unfold slabThresholdCoreMass
    SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  exact listNatWeight_thresholdCore_telescope
    entry.1.1 (slabFaceStrandSelectionCount seed.selected)
      threshold (slabPhysicalFaceEdges D.extent)
      (fun selectedFaceId _ =>
        slabFaceStrandSelectionCount_le seed.selected selectedFaceId)

/-- The paired threshold potential obeys the same exact conservation law for
either selected side. -/
theorem SlabAcceptedPairedPeelChoice.lowerState_thresholdCoreMass_add_residual
    (D : SlabPhysicalData) (threshold : Nat)
    {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedTwoReplicaThresholdCoreMass
          D threshold choice.lowerState +
        slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice =
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state := by
  cases choice with
  | left faceId hface hpositive =>
      have hstep :=
        acceptedExpandedSourceLowerAt_thresholdCoreMass_add_residual
          D threshold faceId hface state.1 hpositive
      change
        (slabThresholdCoreMass D.extent threshold
              (acceptedExpandedSourceLowerAt
                D faceId hface state.1 hpositive).1.1 +
            slabThresholdCoreMass D.extent threshold state.2.1.1) +
          acceptedExpandedSourceCoreResidualSizeAt
            D threshold faceId hface state.1 hpositive =
        slabThresholdCoreMass D.extent threshold state.1.1.1 +
          slabThresholdCoreMass D.extent threshold state.2.1.1
      omega
  | right faceId hface hleftZero hpositive =>
      have hstep :=
        acceptedExpandedSourceLowerAt_thresholdCoreMass_add_residual
          D threshold faceId hface state.2 hpositive
      change
        (slabThresholdCoreMass D.extent threshold state.1.1.1 +
            slabThresholdCoreMass D.extent threshold
              (acceptedExpandedSourceLowerAt
                D faceId hface state.2 hpositive).1.1) +
          acceptedExpandedSourceCoreResidualSizeAt
            D threshold faceId hface state.2 hpositive =
        slabThresholdCoreMass D.extent threshold state.1.1.1 +
          slabThresholdCoreMass D.extent threshold state.2.1.1
      omega

/-! ## 3. Complete residual-core profile -/

/-- Terminal accepted state and total residual-core mass accumulated along
the deterministic canonical path. -/
abbrev SlabAcceptedPairedFiniteCorePeelingOutput
    (D : SlabPhysicalData) := SlabAcceptedTwoReplicaState D × Nat

def slabAcceptedPairCanonicalFiniteCorePeeling
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    (state : SlabAcceptedTwoReplicaState D) ->
      SlabAcceptedPairedFiniteCorePeelingOutput D
  | state =>
      match slabAcceptedPairCanonicalChoice? D state faces hphysical with
      | none => (state, 0)
      | some choice =>
          let tail := slabAcceptedPairCanonicalFiniteCorePeeling
            D threshold faces hphysical choice.lowerState
          (tail.1,
            slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice +
              tail.2)
termination_by state => slabAcceptedTwoReplicaStateMass state
decreasing_by
  exact choice.lowerState_mass_lt

/-- Exact potential telescope through the full recursive path. -/
theorem slabAcceptedPairCanonicalFiniteCorePeeling_telescope
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalFiniteCorePeeling
      D threshold faces hphysical state
    slabAcceptedTwoReplicaThresholdCoreMass D threshold result.1 +
        result.2 =
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state := by
  change slabAcceptedTwoReplicaThresholdCoreMass D threshold
        (slabAcceptedPairCanonicalFiniteCorePeeling
          D threshold faces hphysical state).1 +
      (slabAcceptedPairCanonicalFiniteCorePeeling
        D threshold faces hphysical state).2 =
    slabAcceptedTwoReplicaThresholdCoreMass D threshold state
  rw [slabAcceptedPairCanonicalFiniteCorePeeling]
  split
  · exact Nat.add_zero _
  · rename_i choice hchoice
    have hstep :=
      SlabAcceptedPairedPeelChoice.lowerState_thresholdCoreMass_add_residual
        D threshold choice
    have htail := slabAcceptedPairCanonicalFiniteCorePeeling_telescope
      D threshold faces hphysical choice.lowerState
    change slabAcceptedTwoReplicaThresholdCoreMass D threshold
          (slabAcceptedPairCanonicalFiniteCorePeeling
            D threshold faces hphysical choice.lowerState).1 +
        (slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice +
          (slabAcceptedPairCanonicalFiniteCorePeeling
            D threshold faces hphysical choice.lowerState).2) =
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state
    omega
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- The finite-core recursion has the same terminal zero property on its
scanned face list. -/
theorem slabAcceptedPairCanonicalFiniteCorePeeling_final_zero
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall faceId, faceId ∈ faces ->
      let result := slabAcceptedPairCanonicalFiniteCorePeeling
        D threshold faces hphysical state
      result.1.1.1.1 faceId = 0 ∧ result.1.2.1.1 faceId = 0 := by
  change forall faceId, faceId ∈ faces ->
    (slabAcceptedPairCanonicalFiniteCorePeeling
      D threshold faces hphysical state).1.1.1.1 faceId = 0 ∧
      (slabAcceptedPairCanonicalFiniteCorePeeling
        D threshold faces hphysical state).1.2.1.1 faceId = 0
  rw [slabAcceptedPairCanonicalFiniteCorePeeling]
  split
  · rename_i hchoice
    intro faceId hface
    exact (slabAcceptedPairCanonicalChoice?_eq_none_iff
      D state faces hphysical).mp hchoice faceId hface
  · rename_i choice hchoice
    exact slabAcceptedPairCanonicalFiniteCorePeeling_final_zero
      D threshold faces hphysical choice.lowerState
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

private theorem listNatWeight_eq_zero_of_pointwise
    {A : Type} (weight : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> weight item = 0) ->
      listNatWeight weight items = 0
  | [], _ => rfl
  | item :: items, hzero => by
      simp only [listNatWeight, hzero item List.mem_cons_self,
        Nat.zero_add]
      exact listNatWeight_eq_zero_of_pointwise weight items
        (fun next hnext =>
          hzero next (List.mem_cons_of_mem item hnext))

/-- On the complete physical face list, total residual mass is exactly the
initial threshold-truncated pair mass. -/
theorem slabAcceptedPairCanonicalFiniteCorePeeling_residualMass_eq
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalFiniteCorePeeling
      D threshold D.faceEdges
        (fun faceId hface => by
          simpa only [SlabPhysicalData.faceEdges] using hface)
        state
    result.2 = slabAcceptedTwoReplicaThresholdCoreMass D threshold state := by
  let hphysical : forall faceId, faceId ∈ D.faceEdges ->
      faceId ∈ slabPhysicalFaceEdges D.extent := fun faceId hface => by
    simpa only [SlabPhysicalData.faceEdges] using hface
  let result := slabAcceptedPairCanonicalFiniteCorePeeling
    D threshold D.faceEdges hphysical state
  have htelescope := slabAcceptedPairCanonicalFiniteCorePeeling_telescope
    D threshold D.faceEdges hphysical state
  have hzero := slabAcceptedPairCanonicalFiniteCorePeeling_final_zero
    D threshold D.faceEdges hphysical state
  have hleft : slabThresholdCoreMass D.extent threshold
      result.1.1.1.1 = 0 := by
    unfold slabThresholdCoreMass
    apply listNatWeight_eq_zero_of_pointwise
    intro faceId hface
    rw [(hzero faceId (by
      simpa only [SlabPhysicalData.faceEdges] using hface)).1]
    exact Nat.min_eq_left (Nat.zero_le threshold)
  have hright : slabThresholdCoreMass D.extent threshold
      result.1.2.1.1 = 0 := by
    unfold slabThresholdCoreMass
    apply listNatWeight_eq_zero_of_pointwise
    intro faceId hface
    rw [(hzero faceId (by
      simpa only [SlabPhysicalData.faceEdges] using hface)).2]
    exact Nat.min_eq_left (Nat.zero_le threshold)
  change result.2 =
    slabAcceptedTwoReplicaThresholdCoreMass D threshold state
  change slabAcceptedTwoReplicaThresholdCoreMass D threshold result.1 +
      result.2 =
    slabAcceptedTwoReplicaThresholdCoreMass D threshold state at htelescope
  unfold slabAcceptedTwoReplicaThresholdCoreMass at htelescope
  rw [hleft, hright] at htelescope
  unfold slabAcceptedTwoReplicaThresholdCoreMass
  omega

private theorem listNatWeight_le_length_mul
    {A : Type} (weight : A -> Nat) (bound : Nat) : forall items : List A,
    (forall item, item ∈ items -> weight item <= bound) ->
      listNatWeight weight items <= items.length * bound
  | [], _ => by
      simp only [listNatWeight, List.length_nil, Nat.zero_mul]
      exact Nat.le_refl 0
  | item :: items, hbound => by
      have hhead := hbound item List.mem_cons_self
      have htail := listNatWeight_le_length_mul weight bound items
        (fun next hnext =>
          hbound next (List.mem_cons_of_mem item hnext))
      simp only [listNatWeight, List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem slabAcceptedTwoReplicaThresholdCoreMass_le
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedTwoReplicaThresholdCoreMass D threshold state <=
      2 * D.faceEdges.length * threshold := by
  have hleft : slabThresholdCoreMass D.extent threshold state.1.1.1 <=
      D.faceEdges.length * threshold := by
    unfold slabThresholdCoreMass SlabPhysicalData.faceEdges
    apply listNatWeight_le_length_mul
    intro faceId _
    exact Nat.min_le_right _ _
  have hright : slabThresholdCoreMass D.extent threshold state.2.1.1 <=
      D.faceEdges.length * threshold := by
    unfold slabThresholdCoreMass SlabPhysicalData.faceEdges
    apply listNatWeight_le_length_mul
    intro faceId _
    exact Nat.min_le_right _ _
  unfold slabAcceptedTwoReplicaThresholdCoreMass
  calc
    slabThresholdCoreMass D.extent threshold state.1.1.1 +
          slabThresholdCoreMass D.extent threshold state.2.1.1 <=
        D.faceEdges.length * threshold +
          D.faceEdges.length * threshold := Nat.add_le_add hleft hright
    _ = 2 * D.faceEdges.length * threshold := by
      rw [Nat.two_mul, Nat.add_mul]

/-- **Cutoff-independent complete-path core budget.**  The accumulated
noncontractive core exponent depends only on the physical face count and the
moving threshold, never on the representation cutoff. -/
theorem slabAcceptedPairCanonicalFiniteCorePeeling_residualMass_le
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalFiniteCorePeeling
      D threshold D.faceEdges
        (fun faceId hface => by
          simpa only [SlabPhysicalData.faceEdges] using hface)
        state
    result.2 <= 2 * D.faceEdges.length * threshold := by
  change (slabAcceptedPairCanonicalFiniteCorePeeling
      D threshold D.faceEdges
        (fun faceId hface => by
          simpa only [SlabPhysicalData.faceEdges] using hface)
        state).2 <= 2 * D.faceEdges.length * threshold
  rw [slabAcceptedPairCanonicalFiniteCorePeeling_residualMass_eq]
  exact slabAcceptedTwoReplicaThresholdCoreMass_le D threshold state

#print axioms slabThresholdCoreMass
#print axioms min_sub_add_coreResidualDropCount
#print axioms acceptedExpandedSourceLowerAt_thresholdCoreMass_add_residual
#print axioms SlabAcceptedPairedPeelChoice.lowerState_thresholdCoreMass_add_residual
#print axioms slabAcceptedPairCanonicalFiniteCorePeeling
#print axioms slabAcceptedPairCanonicalFiniteCorePeeling_telescope
#print axioms slabAcceptedPairCanonicalFiniteCorePeeling_residualMass_eq
#print axioms slabAcceptedPairCanonicalFiniteCorePeeling_residualMass_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass
