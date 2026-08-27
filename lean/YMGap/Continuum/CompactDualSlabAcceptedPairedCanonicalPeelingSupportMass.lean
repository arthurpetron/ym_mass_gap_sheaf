/-
# Support control and paid mass of canonical paired peeling

The complete canonical trace was proved injective, but its relevance to the
connected observable residue still requires two geometric facts.  Every
selected root lies in the fixed scanned component, and every lowering is
pointwise monotone.  Hence the terminal zero state on that component forces
the trace to remove at least the component's complete initial twice-spin mass.

For the target-rooted union-support component of a connected observable pair,
the preceding lattice-animal theorem already bounds that mass below by
`L-infinity distance + 1`.  The canonical trace therefore pays the same
separation in its total peel exponent.

Constructive contract: pointwise natural subtraction and finite list sums
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Every accepted peel is pointwise monotone -/

theorem acceptedExpandedSourceLowerAt_physical_le
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId)
    (queryFaceId : Nat) :
    (acceptedExpandedSourceLowerAt
      D faceId hface entry hpositive).1.1 queryFaceId ≤
        entry.1.1 queryFaceId := by
  unfold acceptedExpandedSourceLowerAt
    SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection
    lowerEdgeLabellingBy
  exact Nat.sub_le _ _

theorem SlabAcceptedPairedPeelChoice.lowerState_physical_le
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state)
    (queryFaceId : Nat) :
    choice.lowerState.1.1.1 queryFaceId ≤ state.1.1.1 queryFaceId ∧
      choice.lowerState.2.1.1 queryFaceId ≤ state.2.1.1 queryFaceId := by
  cases choice with
  | left faceId hface hpositive =>
      exact ⟨acceptedExpandedSourceLowerAt_physical_le
        D faceId hface state.1 hpositive queryFaceId,
        Nat.le_refl _⟩
  | right faceId hface _ hpositive =>
      exact ⟨Nat.le_refl _,
        acceptedExpandedSourceLowerAt_physical_le
          D faceId hface state.2 hpositive queryFaceId⟩

/-- The terminal accepted pair is pointwise below the initial pair. -/
theorem slabAcceptedPairCanonicalPeeling_final_physical_le
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ queryFaceId,
      let finalState :=
        (slabAcceptedPairCanonicalPeeling
          D faces hphysical state).1
      finalState.1.1.1 queryFaceId ≤ state.1.1.1 queryFaceId ∧
        finalState.2.1.1 queryFaceId ≤ state.2.1.1 queryFaceId := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro queryFaceId
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rename_i choice hchoice
    intro queryFaceId
    have htail := slabAcceptedPairCanonicalPeeling_final_physical_le
      D faces hphysical choice.lowerState queryFaceId
    have hstep :=
      SlabAcceptedPairedPeelChoice.lowerState_physical_le
        choice queryFaceId
    exact ⟨Nat.le_trans htail.1 hstep.1,
      Nat.le_trans htail.2 hstep.2⟩
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 2. Trace roots remain in the fixed component -/

@[simp] theorem slabAcceptedPairedPeelChoiceRecord_rootFaceId
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    (slabAcceptedPairedPeelChoiceRecord choice).rootFaceId =
      choice.faceId := by
  cases choice <;> rfl

theorem slabAcceptedPairCanonicalPeeling_trace_root_mem
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ record,
      record ∈ (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).2 → record.rootFaceId ∈ faces := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro record hmem
    cases hmem
  · rename_i choice hchoice
    intro record hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · subst record
      simpa only [slabAcceptedPairedPeelChoiceRecord_rootFaceId] using
          slabAcceptedPairCanonicalChoice?_some_face_mem
            D state faces hphysical choice hchoice
    · exact slabAcceptedPairCanonicalPeeling_trace_root_mem
        D faces hphysical choice.lowerState record htail
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 3. Exact paid component mass -/

private theorem listNatWeight_add
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      listNatWeight (fun item => left item + right item) items =
        listNatWeight left items + listNatWeight right items
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight]
      rw [listNatWeight_add left right tail]
      omega

private theorem listNatWeight_congr
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → left item = right item) →
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [listNatWeight]
      rw [heq head List.mem_cons_self]
      rw [listNatWeight_congr left right tail
        (fun item hmem =>
          heq item (List.mem_cons_of_mem head hmem))]

private theorem listNatWeight_sub_add
    {A : Type} (initial final : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → final item ≤ initial item) →
      listNatWeight (fun item => initial item - final item) items +
          listNatWeight final items =
        listNatWeight initial items
  | [], _ => rfl
  | head :: tail, hle => by
      have hhead := hle head List.mem_cons_self
      have htail := listNatWeight_sub_add initial final tail
        (fun item hmem =>
          hle item (List.mem_cons_of_mem head hmem))
      simp only [listNatWeight]
      omega

theorem slabAcceptedTwoReplicaStateMass_eq_combined
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedTwoReplicaStateMass state =
      listNatWeight
        (fun faceId => state.1.1.1 faceId + state.2.1.1 faceId)
        (slabPhysicalFaceEdges D.extent) := by
  unfold slabAcceptedTwoReplicaStateMass slabPhysicalLabellingMass
  exact (listNatWeight_add state.1.1.1 state.2.1.1
    (slabPhysicalFaceEdges D.extent)).symm

/-- Complete canonical peeling pays at least the initial twice-spin mass on
the fixed face list. -/
theorem slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hfacesNodup : faces.Nodup)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    listNatWeight
          (fun faceId => state.1.1.1 faceId + state.2.1.1 faceId)
          faces ≤
      slabAcceptedPairedPeelTraceMass
        (slabAcceptedPairCanonicalPeeling
          D faces hphysical state).2 := by
  let result := slabAcceptedPairCanonicalPeeling
    D faces hphysical state
  change
    listNatWeight
          (fun faceId => state.1.1.1 faceId + state.2.1.1 faceId)
          faces ≤
      slabAcceptedPairedPeelTraceMass result.2
  let initialWeight : Nat → Nat := fun faceId =>
    state.1.1.1 faceId + state.2.1.1 faceId
  let finalWeight : Nat → Nat := fun faceId =>
    result.1.1.1.1 faceId + result.1.2.1.1 faceId
  have hfinalLe : ∀ faceId,
      finalWeight faceId ≤ initialWeight faceId := by
    intro faceId
    have hle := slabAcceptedPairCanonicalPeeling_final_physical_le
      D faces hphysical state faceId
    have hle' :
        result.1.1.1.1 faceId ≤ state.1.1.1 faceId ∧
          result.1.2.1.1 faceId ≤ state.2.1.1 faceId := by
      simpa only [result] using hle
    unfold initialWeight finalWeight
    omega
  have hfinalZero : ∀ faceId, faceId ∈ faces →
      finalWeight faceId = 0 := by
    intro faceId hface
    have hzero := slabAcceptedPairCanonicalPeeling_final_zero
      D faces hphysical state faceId hface
    have hzero' :
        result.1.1.1.1 faceId = 0 ∧
          result.1.2.1.1 faceId = 0 := by
      simpa only [result] using hzero
    unfold finalWeight
    omega
  have hcomponentEq :
      listNatWeight initialWeight faces =
        listNatWeight
          (fun faceId => initialWeight faceId - finalWeight faceId)
          faces := by
    apply listNatWeight_congr
    intro faceId hface
    rw [hfinalZero faceId hface]
    omega
  have hcomponentLe :
      listNatWeight
          (fun faceId => initialWeight faceId - finalWeight faceId)
          faces ≤
        listNatWeight
          (fun faceId => initialWeight faceId - finalWeight faceId)
          (slabPhysicalFaceEdges D.extent) :=
    listNatWeight_le_of_nodup_mem _ faces
      (slabPhysicalFaceEdges D.extent) hfacesNodup hphysical
  have hdropAdd := listNatWeight_sub_add initialWeight finalWeight
    (slabPhysicalFaceEdges D.extent)
      (fun faceId _ => hfinalLe faceId)
  have hinitialMass := slabAcceptedTwoReplicaStateMass_eq_combined D state
  have hfinalMass := slabAcceptedTwoReplicaStateMass_eq_combined D result.1
  have htelescope :
      slabAcceptedTwoReplicaStateMass result.1 +
          slabAcceptedPairedPeelTraceMass result.2 =
        slabAcceptedTwoReplicaStateMass state := by
    simpa only [result] using
      slabAcceptedPairCanonicalPeeling_mass_telescope
        D faces hphysical state
  unfold initialWeight finalWeight at hcomponentEq hcomponentLe hdropAdd
  rw [hinitialMass, hfinalMass] at htelescope
  rw [hcomponentEq]
  omega

/-! ## 4. The connected observable trace pays separation -/

/-- Canonical peeling of the original target-rooted union-support component. -/
def slabObservablePairTargetSupportCanonicalPeeling
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    SlabAcceptedPairedCanonicalPeelingOutput D :=
  slabAcceptedPairCanonicalPeeling D
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)
    (fun faceId hface =>
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget pair hpair faceId hface)
    (slabObservableTwoReplicaPairToAcceptedState pair)

/-- Every connected residue pair produces a canonical trace whose total
removed multiplicity is at least observable separation plus one. -/
theorem slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair = true) :
    linfDist
          (slabPlaquetteAt D.extent rootFaceId)
          (slabPlaquetteAt D.extent targetFaceId) + 1 ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  have hcomponent :=
    slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
      D
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (rootComponent_nodup
        (slabSupportFaceAdjacentB D.extent)
        (slabTwoReplicaSupportFaceVertices D.extent
          pair.1.1.1 pair.2.1.1)
        targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
  have hfloor :=
    slabObservableTwoReplicaPairPairedSupportConnected_componentMass_floor
      D rootFaceId targetFaceId htarget pair hpair hconnected
  exact Nat.le_trans hfloor hcomponent

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass.slabAcceptedPairCanonicalPeeling_trace_root_mem
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass.slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass.slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
