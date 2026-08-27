/-
# One global entropy carrier for a canonically peeled observable pair

At fixed canonical trace mass `M`, the source pair has three finite information
channels:

* a global support-shape word in a carrier of size `625^M`;
* a paired physical-value word in a carrier of size `8^M`;
* both active auxiliary row tables in an adaptive carrier of size `4096^M`.

The adaptive carrier depends on the preceding physical data.  We eliminate
that dependency without enlarging the count: record the constructive
first-occurrence position of the production row table in its own carrier.
Equal shape and physical words identify the specifications, so equal positions
then identify the row tables.  Together with a common canonical terminal, the
global reconstruction theorem makes the resulting aggregate code injective.

Thus every duplicate-free fixed-terminal, fixed-trace-mass source family has
cardinality at most

  (625 * 8 * 4096)^M = 20480000^M.

Constructive contract: structural finite-list ranks, explicit finite carriers,
and proved reconstruction only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. A constructive first-occurrence rank inside a finite list -/

/-- Zero-based position, totalized to zero outside the list. -/
def finiteListRank {A : Type} [DecidableEq A] (item : A) : List A -> Nat
  | [] => 0
  | head :: tail =>
      if item = head then 0 else finiteListRank item tail + 1

theorem finiteListRank_lt_length_of_mem
    {A : Type} [DecidableEq A] (item : A) :
    forall items : List A, item ∈ items ->
      finiteListRank item items < items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases heq : item = head
      · simp [finiteListRank, heq]
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail
        have ih := finiteListRank_lt_length_of_mem item tail htail
        simp only [finiteListRank, if_neg heq, List.length_cons]
        omega

/-- Total list lookup used to decode a known member rank. -/
def finiteListAtRank {A : Type} (fallback : A) : List A -> Nat -> A
  | [], _ => fallback
  | head :: _, 0 => head
  | _ :: tail, rank + 1 => finiteListAtRank fallback tail rank

/-- Decoding the first-occurrence rank of any member returns that member. -/
theorem finiteListAtRank_rank_eq_of_mem
    {A : Type} [DecidableEq A] (fallback item : A) :
    forall items : List A, item ∈ items ->
      finiteListAtRank fallback items (finiteListRank item items) = item
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases heq : item = head
      · subst item
        simp [finiteListRank, finiteListAtRank]
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail
        have ih := finiteListAtRank_rank_eq_of_mem
          fallback item tail htail
        simp [finiteListRank, finiteListAtRank, heq, ih]

/-! ## 2. The three-channel aggregate code -/

/-- A source pair attached to the relevant observable four-cell. -/
abbrev SlabObservableFourCellPairEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  {pair : SlabObservableTwoReplicaPair D rootFaceId //
    pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId}

/-- The exact product base of shape, physical, and active auxiliary entropy. -/
def slabObservablePairedGlobalEntropyBase : Nat := 20480000

/-- Finite aggregate code at a common trace-mass budget. -/
structure SlabObservablePairedGlobalEntropyCode where
  shape : List (Fin (z4Chain.D + 1))
  physical : List Nat
  auxiliaryRank : Nat
deriving DecidableEq

/-- Rank both active source auxiliary fields in their own adaptive carrier. -/
def slabObservablePairTargetSupportActiveAuxiliaryRank
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : Nat :=
  finiteListRank
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D pair targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D pair targetFaceId)

theorem slabObservablePairTargetSupportActiveAuxiliaryRank_eq
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    slabObservablePairTargetSupportActiveAuxiliaryRank D pair targetFaceId =
      finiteListRank
        (slabObservablePairTargetSupportActiveAuxiliaryRows
          D pair targetFaceId)
        (slabObservablePairTargetSupportActiveAuxiliaryCarrier
          D pair targetFaceId) := rfl

attribute [irreducible]
  slabObservablePairTargetSupportActiveAuxiliaryRank

/-- Combine the three production channels at budget `mass`. -/
def slabObservablePairTargetSupportGlobalEntropyCode
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (mass : Nat) : SlabObservablePairedGlobalEntropyCode where
  shape := slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
    D rootFaceId targetFaceId htarget entry.1 entry.2 mass
  physical := slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
    D rootFaceId targetFaceId htarget entry.1 entry.2 mass
  auxiliaryRank := slabObservablePairTargetSupportActiveAuxiliaryRank
    D entry.1 targetFaceId

/-- One source-independent product carrier at mass `M`. -/
def slabObservablePairedGlobalEntropyCarrier
    (mass : Nat) : List SlabObservablePairedGlobalEntropyCode :=
  (rootedAnimalPaddedTourCarrier z4Chain mass).flatMap fun shape =>
    (pairedPhysicalValueCarrier mass).flatMap fun physical =>
      (List.range (4096 ^ mass)).map fun auxiliaryRank =>
        { shape := shape
          physical := physical
          auxiliaryRank := auxiliaryRank }

private theorem flatMap_const_length
    {A B : Type} (items : List A) (f : A -> List B) (length : Nat)
    (hlength : forall item, item ∈ items -> (f item).length = length) :
    (items.flatMap f).length = items.length * length := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hlength head List.mem_cons_self,
        ih (fun item hitem =>
          hlength item (List.mem_cons_of_mem head hitem))]
      rw [Nat.succ_mul]
      omega

/-- Exact aggregate cardinality. -/
theorem slabObservablePairedGlobalEntropyCarrier_length
    (mass : Nat) :
    (slabObservablePairedGlobalEntropyCarrier mass).length =
      slabObservablePairedGlobalEntropyBase ^ mass := by
  unfold slabObservablePairedGlobalEntropyCarrier
  rw [flatMap_const_length
    (rootedAnimalPaddedTourCarrier z4Chain mass)
    (fun _ => (pairedPhysicalValueCarrier mass).flatMap fun physical =>
      (List.range (4096 ^ mass)).map fun auxiliaryRank =>
        ({ shape := _
           physical := physical
           auxiliaryRank := auxiliaryRank } :
          SlabObservablePairedGlobalEntropyCode))
    ((pairedPhysicalValueCarrier mass).length * 4096 ^ mass)]
  · rw [slabObservableTwoReplicaPairTargetSupportGlobalShapeCarrier_length,
      pairedPhysicalValueCarrier_length]
    unfold slabObservablePairedGlobalEntropyBase
    rw [← Nat.mul_pow, ← Nat.mul_pow]
  · intro shape _
    apply flatMap_const_length
    intro physical _
    rw [List.length_map, List.length_range]

/-! ## 3. Production membership and aggregate faithfulness -/

/-- The canonical trace pays the complete paired physical mass on the initial
target component. -/
theorem slabObservablePairTargetSupportMass_le_canonicalTraceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairTargetSupportMass D pair targetFaceId ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  exact slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
    D
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)
    (rootComponent_nodup
      (slabSupportFaceAdjacentB D.extent)
      (slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1) targetFaceId)
    (fun faceId hface =>
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget pair hpair faceId hface)
    (slabObservableTwoReplicaPairToAcceptedState pair)

/-- The same trace mass is a valid padding budget for the global support
shape word. -/
theorem slabObservablePairTargetSupportPlaquettes_length_le_canonicalTraceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  exact Nat.le_trans
    (slabObservableTwoReplicaPairTargetSupportPlaquettes_length_le_component
      D pair targetFaceId)
    (Nat.le_trans
      (slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
        D rootFaceId targetFaceId htarget pair hpair)
      (slabObservablePairTargetSupportMass_le_canonicalTraceMass
        D rootFaceId targetFaceId htarget pair hpair))

/-- A production rank lies below the length of its original adaptive carrier. -/
theorem slabObservablePairTargetSupportActiveAuxiliaryRank_lt_carrierLength
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    slabObservablePairTargetSupportActiveAuxiliaryRank
        D pair targetFaceId <
      (slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D pair targetFaceId).length := by
  rw [slabObservablePairTargetSupportActiveAuxiliaryRank_eq]
  exact finiteListRank_lt_length_of_mem
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D pair targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D pair targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
      D pair (targetFaceId := targetFaceId))

/-- Any larger mass budget also bounds the adaptive active-row carrier. -/
theorem slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le_mass
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hcomponentMass :
      slabObservableTwoReplicaPairTargetSupportMass
        D entry.1 targetFaceId ≤ mass) :
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D entry.1 targetFaceId).length ≤ 4096 ^ mass := by
  exact Nat.le_trans
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le
      D rootFaceId targetFaceId htarget entry.1 entry.2)
    (Nat.pow_le_pow_right (by decide) hcomponentMass)

private theorem slabObservablePairTargetSupportActiveAuxiliaryRank_lt
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (htraceMass : slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget entry.1 entry.2).2 = mass) :
    slabObservablePairTargetSupportActiveAuxiliaryRank
        D entry.1 targetFaceId < 4096 ^ mass := by
  have hcomponentTrace :=
    slabObservablePairTargetSupportMass_le_canonicalTraceMass
      D rootFaceId targetFaceId htarget entry.1 entry.2
  have hcomponentMass :
      slabObservableTwoReplicaPairTargetSupportMass
        D entry.1 targetFaceId ≤ mass := by
    rw [← htraceMass]
    exact hcomponentTrace
  exact Nat.lt_of_lt_of_le
    (slabObservablePairTargetSupportActiveAuxiliaryRank_lt_carrierLength
      D entry.1 targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le_mass
      D rootFaceId targetFaceId mass htarget entry hcomponentMass)

theorem slabObservablePairTargetSupportGlobalEntropyCode_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (htraceMass : slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget entry.1 entry.2).2 = mass) :
    slabObservablePairTargetSupportGlobalEntropyCode
        D rootFaceId targetFaceId htarget entry mass ∈
      slabObservablePairedGlobalEntropyCarrier mass := by
  unfold slabObservablePairedGlobalEntropyCarrier
  apply List.mem_flatMap.mpr
  refine ⟨slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
      D rootFaceId targetFaceId htarget entry.1 entry.2 mass, ?_, ?_⟩
  · apply slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem
    rw [← htraceMass]
    exact
      slabObservablePairTargetSupportPlaquettes_length_le_canonicalTraceMass
        D rootFaceId targetFaceId htarget entry.1 entry.2
  · apply List.mem_flatMap.mpr
    refine ⟨slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
      D rootFaceId targetFaceId htarget entry.1 entry.2 mass, ?_, ?_⟩
    · have hphysical :=
        slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_mem
          D rootFaceId targetFaceId htarget entry.1 entry.2 mass
      rw [htraceMass] at hphysical
      exact hphysical
    · apply List.mem_map.mpr
      refine ⟨slabObservablePairTargetSupportActiveAuxiliaryRank
        D entry.1 targetFaceId, ?_, rfl⟩
      exact List.mem_range.mpr
        (slabObservablePairTargetSupportActiveAuxiliaryRank_lt
          D rootFaceId targetFaceId mass htarget entry htraceMass)

private theorem slabObservablePairTargetSupportActiveAuxiliarySpecifications_eq_of_activeLinks_eq
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hactive :
      slabObservableTwoReplicaPairTargetSupportActiveLinks
          D left targetFaceId =
        slabObservableTwoReplicaPairTargetSupportActiveLinks
          D right targetFaceId)
    (hphysical : left.1.1.1 = right.1.1.1 ∧
      left.2.1.1 = right.2.1.1) :
    slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D left targetFaceId =
      slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D right targetFaceId := by
  unfold slabObservablePairTargetSupportActiveAuxiliarySpecifications
    slabObservablePairTargetSupportActiveLinkCoordinates
  rw [hactive]
  apply List.map_congr_left
  intro coordinate _
  congr 1
  unfold slabObservablePairActiveAuxiliaryMassAt
  cases coordinate.2 <;> simp [hphysical.1, hphysical.2]

private theorem slabObservablePairTargetSupportActiveAuxiliarySpecifications_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left.1 left.2 mass =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right.1 right.2 mass)
    (hphysical : left.1.1.1.1 = right.1.1.1.1 ∧
      left.1.2.1.1 = right.1.2.1.1) :
    slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D left.1 targetFaceId =
      slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D right.1 targetFaceId := by
  have hactive :=
    slabObservablePairTargetSupportActiveLinks_eq_of_globalShapeCode_eq
      D rootFaceId targetFaceId htarget left.1 right.1 left.2 right.2
        mass hshape
  exact
    slabObservablePairTargetSupportActiveAuxiliarySpecifications_eq_of_activeLinks_eq
      D left.1 right.1 hactive hphysical

/-- At a common terminal and trace mass, the aggregate code is injective on
the attached four-cell source entries. -/
theorem slabObservablePairTargetSupportGlobalEntropyCode_injective
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (left right : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hleftTerminal :
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget left.1 left.2).1 = terminal)
    (hrightTerminal :
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget right.1 right.2).1 = terminal)
    (hleftMass : slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget left.1 left.2).2 = mass)
    (hrightMass : slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget right.1 right.2).2 = mass)
    (hcode : slabObservablePairTargetSupportGlobalEntropyCode
        D rootFaceId targetFaceId htarget left mass =
      slabObservablePairTargetSupportGlobalEntropyCode
        D rootFaceId targetFaceId htarget right mass) :
    left = right := by
  have hshape := congrArg
    SlabObservablePairedGlobalEntropyCode.shape hcode
  have hphysicalCode := congrArg
    SlabObservablePairedGlobalEntropyCode.physical hcode
  have hrank := congrArg
    SlabObservablePairedGlobalEntropyCode.auxiliaryRank hcode
  change slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
      D rootFaceId targetFaceId htarget left.1 left.2 mass =
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
      D rootFaceId targetFaceId htarget right.1 right.2 mass at hshape
  change slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
      D rootFaceId targetFaceId htarget left.1 left.2 mass =
    slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
      D rootFaceId targetFaceId htarget right.1 right.2 mass
    at hphysicalCode
  change slabObservablePairTargetSupportActiveAuxiliaryRank
      D left.1 targetFaceId =
    slabObservablePairTargetSupportActiveAuxiliaryRank
      D right.1 targetFaceId at hrank
  have hterminal :
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget left.1 left.2).1 =
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget right.1 right.2).1 :=
    hleftTerminal.trans hrightTerminal.symm
  have htraceMass := hleftMass.trans hrightMass.symm
  have hvalues :=
    slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_eq_values
      D rootFaceId targetFaceId htarget left.1 right.1 left.2 right.2
        mass htraceMass hphysicalCode
  have hphysical :=
    slabObservablePair_sourcePhysical_eq_of_terminal_eq_of_globalWords_eq
      D rootFaceId targetFaceId htarget left.1 right.1 left.2 right.2
        mass hterminal hshape hvalues
  have hspecifications :=
    slabObservablePairTargetSupportActiveAuxiliarySpecifications_eq
      D rootFaceId targetFaceId mass htarget left right hshape hphysical
  have hcarrier :
      slabObservablePairTargetSupportActiveAuxiliaryCarrier
          D left.1 targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryCarrier
          D right.1 targetFaceId := by
    unfold slabObservablePairTargetSupportActiveAuxiliaryCarrier
    rw [hspecifications]
  have hleftRows :=
    slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
      D left.1 (targetFaceId := targetFaceId)
  have hrightRows :=
    slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
      D right.1 (targetFaceId := targetFaceId)
  have hrightRowsCommon :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D right.1 targetFaceId ∈
        slabObservablePairTargetSupportActiveAuxiliaryCarrier
          D left.1 targetFaceId := by
    unfold slabObservablePairTargetSupportActiveAuxiliaryCarrier
    rw [hspecifications]
    exact hrightRows
  have hrankCommon := hrank
  rw [slabObservablePairTargetSupportActiveAuxiliaryRank_eq,
    slabObservablePairTargetSupportActiveAuxiliaryRank_eq] at hrankCommon
  rw [← hcarrier] at hrankCommon
  have hleftDecode := finiteListAtRank_rank_eq_of_mem
    ([] : List (List Nat))
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D left.1 targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D left.1 targetFaceId)
    hleftRows
  have hrightDecode := finiteListAtRank_rank_eq_of_mem
    ([] : List (List Nat))
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D right.1 targetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D left.1 targetFaceId)
    hrightRowsCommon
  have hrows : slabObservablePairTargetSupportActiveAuxiliaryRows
        D left.1 targetFaceId =
      slabObservablePairTargetSupportActiveAuxiliaryRows
        D right.1 targetFaceId := by
    calc
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D left.1 targetFaceId =
          finiteListAtRank ([] : List (List Nat))
            (slabObservablePairTargetSupportActiveAuxiliaryCarrier
              D left.1 targetFaceId)
            (finiteListRank
              (slabObservablePairTargetSupportActiveAuxiliaryRows
                D left.1 targetFaceId)
              (slabObservablePairTargetSupportActiveAuxiliaryCarrier
                D left.1 targetFaceId)) := hleftDecode.symm
      _ = finiteListAtRank ([] : List (List Nat))
            (slabObservablePairTargetSupportActiveAuxiliaryCarrier
              D left.1 targetFaceId)
            (finiteListRank
              (slabObservablePairTargetSupportActiveAuxiliaryRows
                D right.1 targetFaceId)
              (slabObservablePairTargetSupportActiveAuxiliaryCarrier
                D left.1 targetFaceId)) := by rw [hrankCommon]
      _ = slabObservablePairTargetSupportActiveAuxiliaryRows
          D right.1 targetFaceId := hrightDecode
  apply Subtype.ext
  exact
    slabObservablePair_eq_of_terminal_eq_of_globalShapeCode_eq_of_physicalValues_eq_of_activeRows_eq
      D rootFaceId targetFaceId htarget left.1 right.1 left.2 right.2
        mass hterminal hshape hvalues hrows

/-! ## 4. Fixed-terminal, fixed-mass fiber capacity -/

/-- The global product carrier bounds every duplicate-free common-terminal
source family of one exact canonical trace mass. -/
theorem slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_length_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : ∀ source, source ∈ sources →
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hmass : ∀ source, source ∈ sources →
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 = mass) :
    sources.length ≤ slabObservablePairedGlobalEntropyBase ^ mass := by
  let codeOf : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId → SlabObservablePairedGlobalEntropyCode :=
    fun source => slabObservablePairTargetSupportGlobalEntropyCode
      D rootFaceId targetFaceId htarget source mass
  have hcodesNodup : (sources.map codeOf).Nodup := by
    apply nodup_map_of_injOn codeOf sources hsources
    intro left hleft right hright hcode
    exact slabObservablePairTargetSupportGlobalEntropyCode_injective
      D rootFaceId targetFaceId mass htarget terminal left right
      (hterminal left hleft) (hterminal right hright)
      (hmass left hleft) (hmass right hright) hcode
  have hsubset : ∀ code, code ∈ sources.map codeOf →
      code ∈ slabObservablePairedGlobalEntropyCarrier mass := by
    intro code hcode
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcode
    exact slabObservablePairTargetSupportGlobalEntropyCode_mem
      D rootFaceId targetFaceId mass htarget source (hmass source hsource)
  have hlength := nodup_subset_length_le
    (sources.map codeOf)
    (slabObservablePairedGlobalEntropyCarrier mass)
    hcodesNodup hsubset
  rw [List.length_map,
    slabObservablePairedGlobalEntropyCarrier_length] at hlength
  exact hlength

#print axioms finiteListRank
#print axioms finiteListRank_lt_length_of_mem
#print axioms finiteListAtRank_rank_eq_of_mem
#print axioms slabObservablePairTargetSupportGlobalEntropyCode
#print axioms slabObservablePairedGlobalEntropyCarrier
#print axioms slabObservablePairedGlobalEntropyCarrier_length
#print axioms slabObservablePairTargetSupportGlobalEntropyCode_mem
#print axioms slabObservablePairTargetSupportGlobalEntropyCode_injective
#print axioms slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_length_le

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
