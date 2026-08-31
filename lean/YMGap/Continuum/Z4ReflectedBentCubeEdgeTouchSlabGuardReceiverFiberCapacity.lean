/-
# Fixed receiver-fiber capacity for the reflected guard switch

Package any switchable source whose two physical fields arise from one
reflected guard graft.  For a fixed final switched receiver, the complete
provenance decoder makes the provenance code injective on such sources.
Every code lies in the explicit source-independent carrier, so every finite
duplicate-free guarded receiver fiber has cardinality at most

`2 ^ |pattern faces| * 4096 ^ pattern physical mass`.

This is the unweighted counting form of the cutoff-independent collision
bound.  The next bridge must partition the connected recoupling column by
these codes and use bistochastic column normalization to obtain the scaled
weighted capacity needed by the retained-fraction argument.

Constructive contract: finite list filtering, explicit decidable equality,
one-occurrence deletion, and the proved provenance decoder only.  No
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardProvenanceDecoder

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardReceiverFiberCapacity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardProvenanceDecoder

local instance reflectedBentGuardReceiverPairDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D reflectedBentRootFaceId

/-- A switchable source with proof that its physical fields arise from one
accepted reflected guard background.  The background witness lives in `Prop`;
the data carrier is the switchable source itself. -/
abbrev ReflectedBentGuardSwitchableSource
    (D : SlabPhysicalData) (hextent : D.extent = 5) :=
  { source : SlabObservablePairedFaceSwitchablePair
      D reflectedBentRootFaceId reflectedBentTargetFaceId //
    ∃ state : SlabAcceptedTwoReplicaState D,
      source.pair.1.1.1 =
          reflectedBentGuardGraftLeftPhysical D hextent state ∧
        source.pair.2.1.1 =
          reflectedBentGuardGraftRightPhysical D hextent state }

def reflectedBentGuardSwitchableSourceTarget
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (source : ReflectedBentGuardSwitchableSource D hextent) :
    SlabObservableTwoReplicaPair D reflectedBentRootFaceId :=
  slabObservablePairedFaceSwitchableTargetPair
    D reflectedBentRootFaceId reflectedBentTargetFaceId
    (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
    source.1

def reflectedBentGuardSwitchableSourceCode
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    (source : ReflectedBentGuardSwitchableSource D hextent) :
    ReflectedBentGuardProvenanceCode :=
  reflectedBentGuardGraft_pairProvenanceCode D source.1.pair

def reflectedBentGuardSwitchableReceiverFiber
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List (ReflectedBentGuardSwitchableSource D hextent) :=
  sources.filter fun source => decide
    (target = reflectedBentGuardSwitchableSourceTarget D hextent source)

theorem mem_reflectedBentGuardSwitchableReceiverFiber_iff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (source : ReflectedBentGuardSwitchableSource D hextent) :
    source ∈ reflectedBentGuardSwitchableReceiverFiber
        D hextent sources target ↔
      source ∈ sources ∧
        target = reflectedBentGuardSwitchableSourceTarget
          D hextent source := by
  unfold reflectedBentGuardSwitchableReceiverFiber
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem reflectedBentGuardSwitchableReceiverFiber_nodup
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (hsources : sources.Nodup)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardSwitchableReceiverFiber
      D hextent sources target).Nodup := by
  unfold reflectedBentGuardSwitchableReceiverFiber
  exact List.filter_sublist.nodup hsources

/-- On one final receiver fiber, equal provenance codes identify the complete
proof-carrying guarded source. -/
theorem reflectedBentGuardSwitchableSource_eq_of_mem_receiverFiber_of_code_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (first second : ReflectedBentGuardSwitchableSource D hextent)
    (hfirst : first ∈ reflectedBentGuardSwitchableReceiverFiber
      D hextent sources target)
    (hsecond : second ∈ reflectedBentGuardSwitchableReceiverFiber
      D hextent sources target)
    (hcode : reflectedBentGuardSwitchableSourceCode D first =
      reflectedBentGuardSwitchableSourceCode D second) :
    first = second := by
  obtain ⟨firstState, hfirstLeft, hfirstRight⟩ := first.2
  obtain ⟨secondState, hsecondLeft, hsecondRight⟩ := second.2
  have hfirstTarget :=
    (mem_reflectedBentGuardSwitchableReceiverFiber_iff
      D hextent sources target first).mp hfirst |>.2
  have hsecondTarget :=
    (mem_reflectedBentGuardSwitchableReceiverFiber_iff
      D hextent sources target second).mp hsecond |>.2
  have htarget : reflectedBentGuardSwitchableSourceTarget
      D hextent first =
        reflectedBentGuardSwitchableSourceTarget D hextent second :=
    hfirstTarget.symm.trans hsecondTarget
  apply Subtype.ext
  exact reflectedBentGuardGraft_source_eq_of_target_eq_of_provenanceCode_eq
    D hextent firstState secondState first.1 second.1
      hfirstLeft hfirstRight hsecondLeft hsecondRight htarget hcode

private theorem nodup_map_of_injective_on_local
    {A B : Type} (map : A -> B) : forall items : List A,
    items.Nodup ->
      (forall left, left ∈ items -> forall right, right ∈ items ->
        map left = map right -> left = right) ->
      (items.map map).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hitems, hinjective => by
      have hparts := List.nodup_cons.mp hitems
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        have hsame := hinjective head List.mem_cons_self item
          (List.mem_cons_of_mem head hitem) heq.symm
        exact hparts.1 (hsame ▸ hitem)
      · exact nodup_map_of_injective_on_local map tail hparts.2
          (fun left hleft right hright heq =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) heq)

private def removeOneLocal {A : Type} [DecidableEq A]
    (item : A) : List A -> List A
  | [] => []
  | head :: tail =>
      if head = item then tail else head :: removeOneLocal item tail

private theorem removeOneLocal_length {A : Type} [DecidableEq A]
    (item : A) : forall items : List A,
    item ∈ items -> (removeOneLocal item items).length + 1 = items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      show (if head = item then tail
        else head :: removeOneLocal item tail).length + 1 =
          (head :: tail).length
      by_cases heq : head = item
      · rw [if_pos heq, List.length_cons]
      · rw [if_neg heq, List.length_cons, List.length_cons]
        have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead.symm)
          · exact htail
        have ih := removeOneLocal_length item tail htail
        omega

private theorem mem_removeOneLocal_of_ne {A : Type} [DecidableEq A]
    (item : A) : forall items : List A, forall other : A,
    other ∈ items -> other ≠ item ->
      other ∈ removeOneLocal item items
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, other, hmem, hne => by
      show other ∈ (if head = item then tail
        else head :: removeOneLocal item tail)
      by_cases heq : head = item
      · rw [if_pos heq]
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact False.elim (hne (hhead.trans heq))
        · exact htail
      · rw [if_neg heq]
        rcases List.mem_cons.mp hmem with hhead | htail
        · rw [hhead]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (mem_removeOneLocal_of_ne item tail other htail hne)

private theorem nodup_subset_length_le_local
    {A : Type} [DecidableEq A] : forall left right : List A,
    left.Nodup ->
      (forall item, item ∈ left -> item ∈ right) ->
      left.length ≤ right.length
  | [], _, _, _ => Nat.zero_le _
  | head :: tail, right, hleft, hsubset => by
      have hhead : head ∈ right := hsubset head List.mem_cons_self
      have hparts := List.nodup_cons.mp hleft
      have htail : forall item, item ∈ tail ->
          item ∈ removeOneLocal head right := by
        intro item hitem
        have hne : item ≠ head := by
          intro heq
          apply hparts.1
          rw [← heq]
          exact hitem
        exact mem_removeOneLocal_of_ne head right item
          (hsubset item (List.mem_cons_of_mem head hitem)) hne
      have ih := nodup_subset_length_le_local tail
        (removeOneLocal head right) hparts.2 htail
      have hlength := removeOneLocal_length head right hhead
      show tail.length + 1 ≤ right.length
      omega

def reflectedBentGuardSwitchableReceiverFiberCodes
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List ReflectedBentGuardProvenanceCode :=
  (reflectedBentGuardSwitchableReceiverFiber
    D hextent sources target).map
      (reflectedBentGuardSwitchableSourceCode D)

theorem reflectedBentGuardSwitchableReceiverFiberCodes_nodup
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (hsources : sources.Nodup)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardSwitchableReceiverFiberCodes
      D hextent sources target).Nodup := by
  unfold reflectedBentGuardSwitchableReceiverFiberCodes
  apply nodup_map_of_injective_on_local
  · exact reflectedBentGuardSwitchableReceiverFiber_nodup
      D hextent sources hsources target
  · intro first hfirst second hsecond hcode
    exact
      reflectedBentGuardSwitchableSource_eq_of_mem_receiverFiber_of_code_eq
        D hextent sources target first second hfirst hsecond hcode

theorem reflectedBentGuardSwitchableReceiverFiberCode_mem_codeSpace
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (source : ReflectedBentGuardSwitchableSource D hextent) :
    reflectedBentGuardSwitchableSourceCode D source ∈
      reflectedBentGuardProvenanceCodeSpace := by
  obtain ⟨state, hleft, hright⟩ := source.2
  exact reflectedBentGuardGraft_pairProvenanceCode_mem_codeSpace
    D hextent state source.1.pair source.1.pair_mem hleft hright

/-- Every duplicate-free finite guarded source family has a fixed receiver
fiber bounded by the cutoff-independent provenance carrier. -/
theorem reflectedBentGuardSwitchableReceiverFiber_length_le_codeSpace
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (hsources : sources.Nodup)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardSwitchableReceiverFiber
        D hextent sources target).length ≤
      reflectedBentGuardProvenanceCodeSpace.length := by
  rw [← List.length_map]
  exact nodup_subset_length_le_local
    (reflectedBentGuardSwitchableReceiverFiberCodes
      D hextent sources target)
    reflectedBentGuardProvenanceCodeSpace
    (reflectedBentGuardSwitchableReceiverFiberCodes_nodup
      D hextent sources hsources target)
    (fun code hcode => by
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp hcode
      exact reflectedBentGuardSwitchableReceiverFiberCode_mem_codeSpace
        D hextent source)

theorem reflectedBentGuardSwitchableReceiverFiber_length_le_fixed
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (sources : List (ReflectedBentGuardSwitchableSource D hextent))
    (hsources : sources.Nodup)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardSwitchableReceiverFiber
        D hextent sources target).length ≤
      2 ^ reflectedBentPatternFaceIds.length *
        4096 ^ reflectedBentGuardPatternPhysicalMass := by
  rw [← reflectedBentGuardProvenanceCodeSpace_length]
  exact reflectedBentGuardSwitchableReceiverFiber_length_le_codeSpace
    D hextent sources hsources target

#print axioms reflectedBentGuardSwitchableSourceTarget
#print axioms reflectedBentGuardSwitchableSourceCode
#print axioms reflectedBentGuardSwitchableReceiverFiber
#print axioms reflectedBentGuardSwitchableSource_eq_of_mem_receiverFiber_of_code_eq
#print axioms reflectedBentGuardSwitchableReceiverFiberCodes_nodup
#print axioms reflectedBentGuardSwitchableReceiverFiber_length_le_codeSpace
#print axioms reflectedBentGuardSwitchableReceiverFiber_length_le_fixed

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardReceiverFiberCapacity
