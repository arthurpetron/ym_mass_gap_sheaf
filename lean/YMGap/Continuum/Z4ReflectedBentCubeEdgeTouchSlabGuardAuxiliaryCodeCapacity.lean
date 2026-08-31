/-
# A cutoff-independent auxiliary code for the guarded reflected component

The cleared guard confines the complete target-rooted physical-support
component to the fixed reflected pattern.  Its paired physical mass is
therefore bounded by one natural number which contains no cutoff, accepted
state, or auxiliary assignment.

The existing active-row compiler gives both source auxiliary fields an
adaptive carrier of size at most `4096^M`, where `M` is the physical mass of
that component.  Specializing the mass bound puts every guarded source row
in one fixed finite rank interval.  Equal physical fields identify the
adaptive carriers, so equality of those ranks recovers the complete stored
active-row tables.

This is a finite auxiliary-capacity theorem, not yet a decoder for the
cross-replica face switch.  Recovering the source assignments outside the
stored active rows, or proving that the final switched target supplies the
missing provenance, remains downstream.

Constructive contract: finite weighted-list inclusion, structural list
ranks, and the existing accepted auxiliary carrier only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFaceMaskSupport

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFaceMaskSupport
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. The fixed physical-mass budget -/

/-- Complete two-replica twice-spin mass of the fixed reflected pattern.
This natural number is independent of the ambient cutoff and accepted
background state. -/
def reflectedBentGuardPatternPhysicalMass : Nat :=
  listNatWeight
    (fun faceId =>
      reflectedBentSwitchLeftPhysical faceId +
        reflectedBentSwitchRightPhysical faceId)
    reflectedBentPatternFaceIds

private theorem listNatWeight_congr_local {A : Type}
    (left right : A -> Nat) :
    forall items : List A,
      (forall item, item ∈ items -> left item = right item) ->
        listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listNatWeight]
      rw [hagree head List.mem_cons_self]
      exact congrArg (right head + ·)
        (listNatWeight_congr_local left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem)))

/-- Any accepted pair with the guarded graft physical fields has target
component mass bounded by the fixed reflected-pattern mass. -/
theorem reflectedBentGuardGraft_pairTargetSupportMass_le_patternMass
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state) :
    slabObservableTwoReplicaPairTargetSupportMass
        D pair reflectedBentTargetFaceId ≤
      reflectedBentGuardPatternPhysicalMass := by
  unfold slabObservableTwoReplicaPairTargetSupportMass
  rw [hleft, hright]
  have hcomponentExtent :
      slabTwoReplicaTargetSupportComponent D.extent
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          reflectedBentTargetFaceId =
        slabTwoReplicaTargetSupportComponent 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          reflectedBentTargetFaceId := by
    rw [hextent]
  rw [hcomponentExtent]
  let component := slabTwoReplicaTargetSupportComponent 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    reflectedBentTargetFaceId
  have hsubset : forall faceId, faceId ∈ component ->
      faceId ∈ reflectedBentPatternFaceIds := by
    intro faceId hface
    exact reflectedBentGuardGraft_targetSupportComponent_subset_pattern
      D hextent state hface
  have hweight :
      listNatWeight
          (fun faceId =>
            reflectedBentGuardGraftLeftPhysical D hextent state faceId +
              reflectedBentGuardGraftRightPhysical D hextent state faceId)
          component =
        listNatWeight
          (fun faceId =>
            reflectedBentSwitchLeftPhysical faceId +
              reflectedBentSwitchRightPhysical faceId)
          component := by
    apply listNatWeight_congr_local
    intro faceId hface
    have hpattern := hsubset faceId hface
    have hguard := reflectedBentPatternFace_mem_guard hpattern
    rw [reflectedBentGuardGraftLeftPhysical_eq_pattern_on_guard
        D hextent state faceId hguard,
      reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
        D hextent state faceId hguard]
  rw [hweight]
  unfold reflectedBentGuardPatternPhysicalMass
  apply listNatWeight_le_of_nodup_mem
  · exact rootComponent_nodup
      (slabSupportFaceAdjacentB 5)
      (slabTwoReplicaSupportFaceVertices 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state))
      reflectedBentTargetFaceId
  · exact hsubset

/-! ## 2. A fixed rank interval for every guarded auxiliary row -/

/-- The existing first-occurrence rank of both active source row tables. -/
def reflectedBentGuardGraft_pairActiveAuxiliaryCode
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) : Nat :=
  slabObservablePairTargetSupportActiveAuxiliaryRank
    D pair reflectedBentTargetFaceId

/-- Every guarded active-row carrier has cutoff-independent length bound. -/
theorem reflectedBentGuardGraft_pairActiveAuxiliaryCarrier_length_le
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state) :
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D pair reflectedBentTargetFaceId).length ≤
      4096 ^ reflectedBentGuardPatternPhysicalMass := by
  exact Nat.le_trans
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
      pair hpair)
    (Nat.pow_le_pow_right (by decide)
      (reflectedBentGuardGraft_pairTargetSupportMass_le_patternMass
        D hextent state pair hleft hright))

/-- The guarded auxiliary rank lies in one fixed interval, independent of
the representation cutoff and accepted background state. -/
theorem reflectedBentGuardGraft_pairActiveAuxiliaryCode_lt
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state) :
    reflectedBentGuardGraft_pairActiveAuxiliaryCode D pair <
      4096 ^ reflectedBentGuardPatternPhysicalMass := by
  unfold reflectedBentGuardGraft_pairActiveAuxiliaryCode
  exact Nat.lt_of_lt_of_le
    (slabObservablePairTargetSupportActiveAuxiliaryRank_lt_carrierLength
      D pair reflectedBentTargetFaceId)
    (reflectedBentGuardGraft_pairActiveAuxiliaryCarrier_length_le
      D hextent state pair hpair hleft hright)

/-- One explicit source-independent carrier for guarded auxiliary codes. -/
def reflectedBentGuardActiveAuxiliaryCodeSpace : List Nat :=
  List.range (4096 ^ reflectedBentGuardPatternPhysicalMass)

theorem reflectedBentGuardGraft_pairActiveAuxiliaryCode_mem_codeSpace
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state) :
    reflectedBentGuardGraft_pairActiveAuxiliaryCode D pair ∈
      reflectedBentGuardActiveAuxiliaryCodeSpace := by
  unfold reflectedBentGuardActiveAuxiliaryCodeSpace
  exact List.mem_range.mpr
    (reflectedBentGuardGraft_pairActiveAuxiliaryCode_lt
      D hextent state pair hpair hleft hright)

@[simp] theorem reflectedBentGuardActiveAuxiliaryCodeSpace_length :
    reflectedBentGuardActiveAuxiliaryCodeSpace.length =
      4096 ^ reflectedBentGuardPatternPhysicalMass := by
  unfold reflectedBentGuardActiveAuxiliaryCodeSpace
  exact List.length_range

/-! ## 3. Equal physical fields make the rank code faithful for active rows -/

private theorem activeLinks_eq_of_physical_eq
    (D : SlabPhysicalData)
    (first second :
      SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hleft : first.1.1.1 = second.1.1.1)
    (hright : first.2.1.1 = second.2.1.1) :
    slabObservableTwoReplicaPairTargetSupportActiveLinks
        D first reflectedBentTargetFaceId =
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D second reflectedBentTargetFaceId := by
  unfold slabObservableTwoReplicaPairTargetSupportActiveLinks
  rw [hleft, hright]

theorem reflectedBentGuard_pairActiveAuxiliaryCarrier_eq_of_physical_eq
    (D : SlabPhysicalData)
    (first second :
      SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hleft : first.1.1.1 = second.1.1.1)
    (hright : first.2.1.1 = second.2.1.1) :
    slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D first reflectedBentTargetFaceId =
      slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D second reflectedBentTargetFaceId := by
  have hactive := activeLinks_eq_of_physical_eq
    D first second hleft hright
  have hspecifications :
      slabObservablePairTargetSupportActiveAuxiliarySpecifications
          D first reflectedBentTargetFaceId =
        slabObservablePairTargetSupportActiveAuxiliarySpecifications
          D second reflectedBentTargetFaceId := by
    unfold slabObservablePairTargetSupportActiveAuxiliarySpecifications
      slabObservablePairTargetSupportActiveLinkCoordinates
    rw [hactive]
    apply List.map_congr_left
    intro coordinate _
    congr 1
    unfold slabObservablePairActiveAuxiliaryMassAt
    cases coordinate.2 <;> simp [hleft, hright]
  unfold slabObservablePairTargetSupportActiveAuxiliaryCarrier
  rw [hspecifications]

/-- Once the two physical fields are fixed, equality of the bounded
auxiliary code recovers both complete active-row tables. -/
theorem reflectedBentGuard_pairActiveAuxiliaryRows_eq_of_physical_eq_of_code_eq
    (D : SlabPhysicalData)
    (first second :
      SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hleft : first.1.1.1 = second.1.1.1)
    (hright : first.2.1.1 = second.2.1.1)
    (hcode : reflectedBentGuardGraft_pairActiveAuxiliaryCode D first =
      reflectedBentGuardGraft_pairActiveAuxiliaryCode D second) :
    slabObservablePairTargetSupportActiveAuxiliaryRows
        D first reflectedBentTargetFaceId =
      slabObservablePairTargetSupportActiveAuxiliaryRows
        D second reflectedBentTargetFaceId := by
  have hcarrier :=
    reflectedBentGuard_pairActiveAuxiliaryCarrier_eq_of_physical_eq
      D first second hleft hright
  have hfirstRows :=
    slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
      D first (targetFaceId := reflectedBentTargetFaceId)
  have hsecondRows :=
    slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
      D second (targetFaceId := reflectedBentTargetFaceId)
  have hsecondRowsCommon :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D second reflectedBentTargetFaceId ∈
        slabObservablePairTargetSupportActiveAuxiliaryCarrier
          D first reflectedBentTargetFaceId := by
    rw [hcarrier]
    exact hsecondRows
  have hrankCommon := hcode
  unfold reflectedBentGuardGraft_pairActiveAuxiliaryCode at hrankCommon
  rw [slabObservablePairTargetSupportActiveAuxiliaryRank_eq,
    slabObservablePairTargetSupportActiveAuxiliaryRank_eq] at hrankCommon
  rw [← hcarrier] at hrankCommon
  have hfirstDecode := finiteListAtRank_rank_eq_of_mem
    ([] : List (List Nat))
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D first reflectedBentTargetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D first reflectedBentTargetFaceId)
    hfirstRows
  have hsecondDecode := finiteListAtRank_rank_eq_of_mem
    ([] : List (List Nat))
    (slabObservablePairTargetSupportActiveAuxiliaryRows
      D second reflectedBentTargetFaceId)
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
      D first reflectedBentTargetFaceId)
    hsecondRowsCommon
  calc
    slabObservablePairTargetSupportActiveAuxiliaryRows
        D first reflectedBentTargetFaceId =
        finiteListAtRank ([] : List (List Nat))
          (slabObservablePairTargetSupportActiveAuxiliaryCarrier
            D first reflectedBentTargetFaceId)
          (finiteListRank
            (slabObservablePairTargetSupportActiveAuxiliaryRows
              D first reflectedBentTargetFaceId)
            (slabObservablePairTargetSupportActiveAuxiliaryCarrier
              D first reflectedBentTargetFaceId)) := hfirstDecode.symm
    _ = finiteListAtRank ([] : List (List Nat))
          (slabObservablePairTargetSupportActiveAuxiliaryCarrier
            D first reflectedBentTargetFaceId)
          (finiteListRank
            (slabObservablePairTargetSupportActiveAuxiliaryRows
              D second reflectedBentTargetFaceId)
            (slabObservablePairTargetSupportActiveAuxiliaryCarrier
              D first reflectedBentTargetFaceId)) := by rw [hrankCommon]
    _ = slabObservablePairTargetSupportActiveAuxiliaryRows
        D second reflectedBentTargetFaceId := hsecondDecode

/-! ## 4. The joint mask-and-active-row provenance code -/

/-- The two remaining finite provenance channels for a guarded source pair. -/
structure ReflectedBentGuardProvenanceCode where
  mask : List Bool
  auxiliary : Nat
deriving DecidableEq

def reflectedBentGuardGraft_pairProvenanceCode
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    ReflectedBentGuardProvenanceCode where
  mask := reflectedBentGuardGraft_pairFaceSwapMaskCode D pair
  auxiliary := reflectedBentGuardGraft_pairActiveAuxiliaryCode D pair

@[simp] theorem reflectedBentGuardGraft_pairProvenanceCode_mask
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardGraft_pairProvenanceCode D pair).mask =
      reflectedBentGuardGraft_pairFaceSwapMaskCode D pair := rfl

@[simp] theorem reflectedBentGuardGraft_pairProvenanceCode_auxiliary
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardGraft_pairProvenanceCode D pair).auxiliary =
      reflectedBentGuardGraft_pairActiveAuxiliaryCode D pair := rfl

/-- One source-independent product carrier for every guarded provenance
code. -/
def reflectedBentGuardProvenanceCodeSpace :
    List ReflectedBentGuardProvenanceCode :=
  reflectedBentGuardFaceSwapMaskCodeSpace.flatMap fun mask =>
    reflectedBentGuardActiveAuxiliaryCodeSpace.map fun auxiliary =>
      { mask := mask, auxiliary := auxiliary }

theorem reflectedBentGuardGraft_pairProvenanceCode_mem_codeSpace
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state) :
    reflectedBentGuardGraft_pairProvenanceCode D pair ∈
      reflectedBentGuardProvenanceCodeSpace := by
  unfold reflectedBentGuardProvenanceCodeSpace
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraft_pairFaceSwapMaskCode D pair,
    reflectedBentGuardGraft_pairFaceSwapMaskCode_mem_codeSpace D pair, ?_⟩
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraft_pairActiveAuxiliaryCode D pair,
    reflectedBentGuardGraft_pairActiveAuxiliaryCode_mem_codeSpace
      D hextent state pair hpair hleft hright, rfl⟩

private theorem flatMap_const_length_local
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

@[simp] theorem reflectedBentGuardProvenanceCodeSpace_length :
    reflectedBentGuardProvenanceCodeSpace.length =
      2 ^ reflectedBentPatternFaceIds.length *
        4096 ^ reflectedBentGuardPatternPhysicalMass := by
  unfold reflectedBentGuardProvenanceCodeSpace
  rw [flatMap_const_length_local
    reflectedBentGuardFaceSwapMaskCodeSpace
    (fun mask =>
      reflectedBentGuardActiveAuxiliaryCodeSpace.map fun auxiliary =>
        ({ mask := mask, auxiliary := auxiliary } :
          ReflectedBentGuardProvenanceCode))
    (4096 ^ reflectedBentGuardPatternPhysicalMass)]
  · rw [reflectedBentGuardFaceSwapMaskCodeSpace_length]
  · intro mask _
    rw [List.length_map,
      reflectedBentGuardActiveAuxiliaryCodeSpace_length]

/-- Equal final switched targets and equal fixed provenance codes recover
the complete source physical fields, the whole strand mask, and both stored
active auxiliary-row tables.  The only unproved decoder step after this
theorem is reconstruction of complete source assignments from those data. -/
theorem reflectedBentGuardGraft_provenance_of_target_eq_of_code_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (firstState secondState : SlabAcceptedTwoReplicaState D)
    (first second : SlabObservablePairedFaceSwitchablePair
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hfirstLeft : first.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent firstState)
    (hfirstRight : first.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent firstState)
    (hsecondLeft : second.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent secondState)
    (hsecondRight : second.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent secondState)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        first =
      slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        second)
    (hcode : reflectedBentGuardGraft_pairProvenanceCode D first.pair =
      reflectedBentGuardGraft_pairProvenanceCode D second.pair) :
    (first.pair.1.1.1 = second.pair.1.1.1 ∧
        first.pair.2.1.1 = second.pair.2.1.1) ∧
      slabObservableTwoReplicaPairPairedFaceSwapMask
          D first.pair reflectedBentTargetFaceId =
        slabObservableTwoReplicaPairPairedFaceSwapMask
          D second.pair reflectedBentTargetFaceId ∧
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D first.pair reflectedBentTargetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D second.pair reflectedBentTargetFaceId := by
  have hmaskCode := congrArg ReflectedBentGuardProvenanceCode.mask hcode
  have hauxiliaryCode :=
    congrArg ReflectedBentGuardProvenanceCode.auxiliary hcode
  rw [reflectedBentGuardGraft_pairProvenanceCode_mask,
    reflectedBentGuardGraft_pairProvenanceCode_mask] at hmaskCode
  rw [reflectedBentGuardGraft_pairProvenanceCode_auxiliary,
    reflectedBentGuardGraft_pairProvenanceCode_auxiliary] at hauxiliaryCode
  have hmask :=
    reflectedBentGuardGraft_pairFaceSwapMask_eq_of_code_eq
      D hextent firstState secondState first.pair second.pair
      first.pair_mem second.pair_mem
      hfirstLeft hfirstRight hsecondLeft hsecondRight hmaskCode
  have hphysical :=
    slabObservablePairedFaceSwitchable_sourcePhysical_eq_of_targetPair_eq_of_mask_eq
      first second htargetPair hmask
  exact ⟨hphysical, hmask,
    reflectedBentGuard_pairActiveAuxiliaryRows_eq_of_physical_eq_of_code_eq
      D first.pair second.pair hphysical.1 hphysical.2 hauxiliaryCode⟩

#print axioms reflectedBentGuardPatternPhysicalMass
#print axioms reflectedBentGuardGraft_pairTargetSupportMass_le_patternMass
#print axioms reflectedBentGuardGraft_pairActiveAuxiliaryCarrier_length_le
#print axioms reflectedBentGuardGraft_pairActiveAuxiliaryCode_lt
#print axioms reflectedBentGuardGraft_pairActiveAuxiliaryCode_mem_codeSpace
#print axioms reflectedBentGuardActiveAuxiliaryCodeSpace_length
#print axioms reflectedBentGuard_pairActiveAuxiliaryCarrier_eq_of_physical_eq
#print axioms reflectedBentGuard_pairActiveAuxiliaryRows_eq_of_physical_eq_of_code_eq
#print axioms reflectedBentGuardGraft_pairProvenanceCode_mem_codeSpace
#print axioms reflectedBentGuardProvenanceCodeSpace_length
#print axioms reflectedBentGuardGraft_provenance_of_target_eq_of_code_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
