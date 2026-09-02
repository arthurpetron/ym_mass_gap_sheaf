/-
# Locality of the arbitrary-coupling residual core

The first complete terminal-fiber estimate bounded its residual core counter
by a whole-slab threshold potential.  Canonical target-support peeling is much
more local: its terminal is zero on the initial target-rooted support
component and is literally unchanged outside that component.

Combining this physical locality with the exact threshold-potential telescope
proves that the profile's residual core counter is exactly the initial
threshold-truncated two-replica mass on that component.  In particular,

  coreMass <= 2 * component.length * threshold.

This removes the spurious charge for faces outside the observable component.
It does not yet control the remaining local low-spin mass uniformly; that is
the next coercivity edge.

Constructive contract: finite duplicate-free list sums, canonical peeling
locality, and natural-number arithmetic only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCoreLocality

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Exact finite support masking -/

private theorem range_nodup_local :
    forall count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem listNatWeight_congr_local
    {A : Type} (left right : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> left item = right item) ->
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [listNatWeight]
      rw [heq head List.mem_cons_self]
      rw [listNatWeight_congr_local left right tail
        (fun item hitem => heq item (List.mem_cons_of_mem head hitem))]

private theorem listNatWeight_add_local
    {A : Type} (left right : A -> Nat) : forall items : List A,
    listNatWeight (fun item => left item + right item) items =
      listNatWeight left items + listNatWeight right items
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight]
      rw [listNatWeight_add_local left right tail]
      omega

private theorem listNatWeight_mask_eq_filter
    {A : Type} [DecidableEq A] (weight : A -> Nat)
    (support : List A) : forall items : List A,
    listNatWeight
        (fun item => if item ∈ support then weight item else 0) items =
      listNatWeight weight
        (items.filter (fun item => decide (item ∈ support)))
  | [] => rfl
  | head :: tail => by
      by_cases hhead : head ∈ support
      · simp only [listNatWeight, hhead, if_true, decide_true,
          List.filter_cons]
        rw [listNatWeight_mask_eq_filter weight support tail]
      · simp only [listNatWeight, hhead, if_false, decide_false,
          List.filter_cons, Nat.zero_add]
        exact listNatWeight_mask_eq_filter weight support tail

/-- Masking a duplicate-free ambient list by a duplicate-free included
support has exactly the same weighted sum as summing on the support itself. -/
private theorem listNatWeight_mask_eq_support
    {A : Type} [DecidableEq A] (weight : A -> Nat)
    (support ambient : List A)
    (hsupportNodup : support.Nodup) (hambientNodup : ambient.Nodup)
    (hsubset : forall item, item ∈ support -> item ∈ ambient) :
    listNatWeight
        (fun item => if item ∈ support then weight item else 0) ambient =
      listNatWeight weight support := by
  let selected := ambient.filter (fun item => decide (item ∈ support))
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup hambientNodup
  have hselectedSubset : forall item, item ∈ selected -> item ∈ support := by
    intro item hitem
    exact of_decide_eq_true (List.mem_filter.mp hitem).2
  have hselectedLe := listNatWeight_le_of_nodup_mem weight
    selected support hselectedNodup hselectedSubset
  have hsupportMask :
      listNatWeight
          (fun item => if item ∈ support then weight item else 0) support =
        listNatWeight weight support := by
    apply listNatWeight_congr_local
    intro item hitem
    rw [if_pos hitem]
  have hsupportLe := listNatWeight_le_of_nodup_mem
    (fun item => if item ∈ support then weight item else 0)
    support ambient hsupportNodup hsubset
  have hmask := listNatWeight_mask_eq_filter weight support ambient
  change listNatWeight weight selected <= listNatWeight weight support
    at hselectedLe
  have hsupportLe' :
      listNatWeight weight support <= listNatWeight weight selected := by
    calc
      listNatWeight weight support =
          listNatWeight
            (fun item => if item ∈ support then weight item else 0)
            support := hsupportMask.symm
      _ <= listNatWeight
          (fun item => if item ∈ support then weight item else 0)
          ambient := hsupportLe
      _ = listNatWeight weight selected := hmask
  rw [hmask]
  exact Nat.le_antisymm hselectedLe hsupportLe'

/-- If a field is zero on `support` and unchanged outside it, the ambient
truncated potential splits exactly into the initial support potential and the
final ambient potential. -/
private theorem listNatWeight_cleared_support_decomposition
    {A : Type} [DecidableEq A]
    (initial final : A -> Nat) (threshold : Nat)
    (support ambient : List A)
    (hsupportNodup : support.Nodup) (hambientNodup : ambient.Nodup)
    (hsubset : forall item, item ∈ support -> item ∈ ambient)
    (hzero : forall item, item ∈ support -> final item = 0)
    (houtside : forall item, item ∈ ambient -> item ∉ support ->
      final item = initial item) :
    listNatWeight (fun item => min (initial item) threshold) ambient =
      listNatWeight (fun item => min (initial item) threshold) support +
        listNatWeight (fun item => min (final item) threshold) ambient := by
  let supportWeight := fun item : A =>
    if item ∈ support then min (initial item) threshold else 0
  let finalWeight := fun item : A => min (final item) threshold
  have hpointwise : forall item, item ∈ ambient ->
      min (initial item) threshold = supportWeight item + finalWeight item := by
    intro item hitem
    by_cases hsupport : item ∈ support
    · unfold supportWeight finalWeight
      rw [if_pos hsupport, hzero item hsupport]
      simp only [Nat.min_eq_left (Nat.zero_le threshold), Nat.add_zero]
    · unfold supportWeight finalWeight
      rw [if_neg hsupport, houtside item hitem hsupport, Nat.zero_add]
  have hcongr := listNatWeight_congr_local
    (fun item => min (initial item) threshold)
    (fun item => supportWeight item + finalWeight item)
    ambient hpointwise
  have hadd := listNatWeight_add_local supportWeight finalWeight ambient
  have hmask := listNatWeight_mask_eq_support
    (fun item => min (initial item) threshold)
    support ambient hsupportNodup hambientNodup hsubset
  unfold supportWeight finalWeight at hadd
  rw [hcongr, hadd, hmask]

/-! ## 2. The exact observable component core -/

/-- The profile's residual core is exactly the initial threshold-truncated
two-replica mass on the target-rooted support component. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_core_eq_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId threshold : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let component := slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId
    let result := slabAcceptedPairCanonicalHighSpinProfile D threshold
      component
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
    result.2.2.2 =
      listNatWeight
        (fun faceId =>
          min (pair.1.1.1 faceId) threshold +
            min (pair.2.1.1 faceId) threshold)
        component := by
  let component := slabTwoReplicaTargetSupportComponent D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
  let hphysical : forall faceId, faceId ∈ component ->
      faceId ∈ slabPhysicalFaceEdges D.extent := fun faceId hface =>
    slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
      D rootFaceId targetFaceId htarget pair hpair faceId hface
  let initial := slabObservableTwoReplicaPairToAcceptedState pair
  let result := slabAcceptedPairCanonicalHighSpinProfile
    D threshold component hphysical initial
  let canonical := slabAcceptedPairCanonicalPeeling
    D component hphysical initial
  have hcomponentNodup : component.Nodup := by
    unfold component slabTwoReplicaTargetSupportComponent
    exact rootComponent_nodup
      (slabSupportFaceAdjacentB D.extent)
      (slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1)
      targetFaceId
  have hambientNodup : (slabPhysicalFaceEdges D.extent).Nodup := by
    unfold slabPhysicalFaceEdges
    exact range_nodup_local _
  have hforget := slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
    D threshold component hphysical initial
  have hterminal : result.1 = canonical.1 := by
    exact congrArg Prod.fst hforget
  have hzero : forall faceId, faceId ∈ component ->
      result.1.1.1.1 faceId = 0 ∧ result.1.2.1.1 faceId = 0 := by
    intro faceId hface
    have h := slabAcceptedPairCanonicalPeeling_final_zero
      D component hphysical initial faceId hface
    simpa only [result, canonical, hterminal] using h
  have houtside : forall faceId,
      faceId ∈ slabPhysicalFaceEdges D.extent -> faceId ∉ component ->
      result.1.1.1.1 faceId = pair.1.1.1 faceId ∧
        result.1.2.1.1 faceId = pair.2.1.1 faceId := by
    intro faceId _ houtside
    have h :=
      slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
        D rootFaceId targetFaceId htarget pair hpair faceId
        (by simpa only [component] using houtside)
    have hcanonicalLeft : canonical.1.1.1.1 faceId =
        pair.1.1.1 faceId := by
      simpa only [canonical, component, initial,
        slabObservablePairTargetSupportCanonicalPeeling,
        slabObservableTwoReplicaPairToAcceptedState,
        slabObservablePositiveSourceEntryToAccepted] using h.1
    have hcanonicalRight : canonical.1.2.1.1 faceId =
        pair.2.1.1 faceId := by
      simpa only [canonical, component, initial,
        slabObservablePairTargetSupportCanonicalPeeling,
        slabObservableTwoReplicaPairToAcceptedState,
        slabObservablePositiveSourceEntryToAccepted] using h.2
    exact And.intro
      ((congrArg (fun state => state.1.1.1 faceId) hterminal).trans
        hcanonicalLeft)
      ((congrArg (fun state => state.2.1.1 faceId) hterminal).trans
        hcanonicalRight)
  have hleftDecomposition :=
    listNatWeight_cleared_support_decomposition
      pair.1.1.1 result.1.1.1.1 threshold component
      (slabPhysicalFaceEdges D.extent) hcomponentNodup hambientNodup
      hphysical (fun faceId hface => (hzero faceId hface).1)
      (fun faceId hface hout => (houtside faceId hface hout).1)
  have hrightDecomposition :=
    listNatWeight_cleared_support_decomposition
      pair.2.1.1 result.1.2.1.1 threshold component
      (slabPhysicalFaceEdges D.extent) hcomponentNodup hambientNodup
      hphysical (fun faceId hface => (hzero faceId hface).2)
      (fun faceId hface hout => (houtside faceId hface hout).2)
  have htelescope := slabAcceptedPairCanonicalHighSpinProfile_core_telescope
    D threshold component hphysical initial
  have hcomponentAdd := listNatWeight_add_local
    (fun faceId => min (pair.1.1.1 faceId) threshold)
    (fun faceId => min (pair.2.1.1 faceId) threshold)
    component
  change result.2.2.2 = _
  change
    (slabThresholdCoreMass D.extent threshold result.1.1.1.1 +
        slabThresholdCoreMass D.extent threshold result.1.2.1.1) +
      result.2.2.2 =
    slabThresholdCoreMass D.extent threshold pair.1.1.1 +
      slabThresholdCoreMass D.extent threshold pair.2.1.1 at htelescope
  unfold slabThresholdCoreMass at htelescope
  rw [hleftDecomposition, hrightDecomposition] at htelescope
  rw [hcomponentAdd]
  omega

private theorem listNatWeight_le_length_mul_local
    {A : Type} (weight : A -> Nat) (bound : Nat) : forall items : List A,
    (forall item, item ∈ items -> weight item <= bound) ->
      listNatWeight weight items <= items.length * bound
  | [], _ => by
      simp only [listNatWeight, List.length_nil, Nat.zero_mul]
      exact Nat.le_refl 0
  | item :: items, hbound => by
      have hhead := hbound item List.mem_cons_self
      have htail := listNatWeight_le_length_mul_local weight bound items
        (fun next hnext => hbound next (List.mem_cons_of_mem item hnext))
      simp only [listNatWeight, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- Local component-size ceiling for the exact residual core counter. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_core_le_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId threshold : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let component := slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId
    let result := slabAcceptedPairCanonicalHighSpinProfile D threshold
      component
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
    result.2.2.2 <= 2 * component.length * threshold := by
  let component := slabTwoReplicaTargetSupportComponent D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
  let result := slabAcceptedPairCanonicalHighSpinProfile D threshold
    component
    (fun faceId hface =>
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget pair hpair faceId hface)
    (slabObservableTwoReplicaPairToAcceptedState pair)
  have heq :=
    slabObservablePairTargetSupportCanonicalHighSpinProfile_core_eq_component
      D rootFaceId targetFaceId threshold htarget pair hpair
  have hbound := listNatWeight_le_length_mul_local
    (fun faceId =>
      min (pair.1.1.1 faceId) threshold +
        min (pair.2.1.1 faceId) threshold)
    (2 * threshold) component
    (fun faceId _ => by
      have hleft := Nat.min_le_right (pair.1.1.1 faceId) threshold
      have hright := Nat.min_le_right (pair.2.1.1 faceId) threshold
      exact Nat.le_trans (Nat.add_le_add hleft hright) (by omega))
  change result.2.2.2 <= 2 * component.length * threshold
  rw [heq]
  calc
    listNatWeight
        (fun faceId =>
          min (pair.1.1.1 faceId) threshold +
            min (pair.2.1.1 faceId) threshold)
        component <= component.length * (2 * threshold) := hbound
    _ = 2 * component.length * threshold := by ac_rfl

#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_core_eq_component
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_core_le_component

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCoreLocality
