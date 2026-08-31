/-
# The actual finite guarded connected row carrier

The provenance decoder and code-fiber estimate apply to arbitrary
duplicate-free families of guarded final-target preimages.  This module
constructs the underlying row carrier rather than postulating such a family.
It filters the already duplicate-free global connected source-choice carrier
by a decidable scan through the complete finite accepted-state carrier.

Every positive successful choice from every literal reflected guard graft is
retained.  Consequently the fixed provenance scaling preserves a row mass of
at least `scale * 1/4` at every positive cutoff.  A structural first-match
scan compiles the actual target fibers, and the fixed scaling gives both
unweighted unit column capacity and physical Gibbs-weighted target capacity.

Constructive contract: finite lists, Boolean scans, proof-carrying subtypes,
and exact `Q'` arithmetic only.  No `Classical`, choice, `native_decide`,
`sorry`, new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualCutoffOneTotalKernel
import YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedCodeFiberCapacity
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedRowCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.SlabObservablePairedFaceSwitchDecoderCertificate
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedCodeFiberCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

private theorem filterMap_nodup_of_separated_local
    {A B : Type} (emit : A → Option B) :
    ∀ items : List A, items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        left ≠ right → ∀ value,
          emit left = some value → emit right = some value → False) →
      (items.filterMap emit).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hseparated => by
      have hparts := List.nodup_cons.mp hnodup
      have htail := filterMap_nodup_of_separated_local emit tail hparts.2
        (fun left hleft right hright hne value hleftSome hrightSome =>
          hseparated left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hne
            value hleftSome hrightSome)
      cases hemit : emit head with
      | none =>
          simp only [List.filterMap_cons, hemit]
          exact htail
      | some value =>
          simp only [List.filterMap_cons, hemit]
          apply List.nodup_cons.mpr
          refine ⟨?_, htail⟩
          intro hmem
          obtain ⟨right, hright, hrightSome⟩ := List.mem_filterMap.mp hmem
          exact hseparated head List.mem_cons_self right
            (List.mem_cons_of_mem head hright)
            (fun heq => hparts.1 (heq ▸ hright))
            value hemit hrightSome

/-! ## 1. A decidable finite guardedness scan -/

/-- Whether one connected source-choice has the physical fields of the guard
graft of a specified accepted background state. -/
def reflectedBentGuardConnectedSourceChoiceMatchesStateB
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (state : SlabAcceptedTwoReplicaState D) : Bool :=
  supportedLabellingEqB D.faceEdges item.1.1.1.1.1
      (reflectedBentGuardGraftLeftPhysical D hextent state) &&
    supportedLabellingEqB D.faceEdges item.1.1.2.1.1
      (reflectedBentGuardGraftRightPhysical D hextent state)

/-- A source-choice is guarded when some member of the complete finite
accepted-state carrier supplies its two physical fields. -/
def reflectedBentGuardConnectedSourceChoiceB
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) : Bool :=
  (slabAcceptedTwoReplicaStates D).any fun state =>
    reflectedBentGuardConnectedSourceChoiceMatchesStateB
      D hextent item state

theorem reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardConnectedSourceChoiceMatchesStateB
        D hextent item state = true ↔
      item.1.1.1.1.1 =
          reflectedBentGuardGraftLeftPhysical D hextent state ∧
        item.1.1.2.1.1 =
          reflectedBentGuardGraftRightPhysical D hextent state := by
  unfold reflectedBentGuardConnectedSourceChoiceMatchesStateB
  rw [Bool.and_eq_true]
  rw [supportedLabellingEqB_true_iff
      item.1.1.1.physical_mem
      (reflectedBentGuardGraftLeftPhysical_mem_of_one_le
        D hcutoff hextent state)]
  rw [supportedLabellingEqB_true_iff
      ((mem_slabExpandedFineSources_iff.mp item.1.1.2.2).1)
      (reflectedBentGuardGraftRightPhysical_mem D hextent state)]

theorem reflectedBentGuardConnectedSourceChoiceB_eq_true_iff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    reflectedBentGuardConnectedSourceChoiceB D hextent item = true ↔
      ∃ state : SlabAcceptedTwoReplicaState D,
        item.1.1.1.1.1 =
            reflectedBentGuardGraftLeftPhysical D hextent state ∧
          item.1.1.2.1.1 =
            reflectedBentGuardGraftRightPhysical D hextent state := by
  constructor
  · intro hguarded
    obtain ⟨state, _, hmatch⟩ := List.any_eq_true.mp hguarded
    exact ⟨state,
      (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
        D hcutoff hextent item state).mp hmatch⟩
  · rintro ⟨state, hleft, hright⟩
    apply List.any_eq_true.mpr
    exact ⟨state, slabAcceptedTwoReplicaState_mem D state,
      (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
        D hcutoff hextent item state).mpr ⟨hleft, hright⟩⟩

/-! ## 2. The duplicate-free actual guarded row carrier -/

/-- All positive successful connected source-choice entries whose physical
source pair is a reflected guard graft of some accepted state. -/
def reflectedBentGuardConnectedSourceChoices
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  (slabObservablePairedConnectedStrandSourceChoices
    D reflectedBentRootFaceId reflectedBentTargetFaceId).filter fun item =>
      reflectedBentGuardConnectedSourceChoiceB D hextent item

theorem mem_reflectedBentGuardConnectedSourceChoices_iff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    item ∈ reflectedBentGuardConnectedSourceChoices D hextent ↔
      item ∈ slabObservablePairedConnectedStrandSourceChoices
          D reflectedBentRootFaceId reflectedBentTargetFaceId ∧
        ∃ state : SlabAcceptedTwoReplicaState D,
          item.1.1.1.1.1 =
              reflectedBentGuardGraftLeftPhysical D hextent state ∧
            item.1.1.2.1.1 =
              reflectedBentGuardGraftRightPhysical D hextent state := by
  unfold reflectedBentGuardConnectedSourceChoices
  rw [List.mem_filter]
  exact and_congr_right fun _ =>
    reflectedBentGuardConnectedSourceChoiceB_eq_true_iff
      D hcutoff hextent item

theorem reflectedBentGuardConnectedSourceChoices_nodup
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    (reflectedBentGuardConnectedSourceChoices D hextent).Nodup := by
  unfold reflectedBentGuardConnectedSourceChoices
  exact List.filter_sublist.nodup
    (slabObservablePairedConnectedStrandSourceChoices_nodup
      D reflectedBentRootFaceId reflectedBentTargetFaceId)

/-! ## 3. Every literal guarded row embeds without thinning -/

theorem reflectedBentGuardGraftConnectedSourceChoice_mem_global
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : SlabObservablePairedConnectedStrandChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state))
    (hchoice : choice ∈ slabObservablePairedConnectedStrandChoices
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state)) :
    (⟨reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state, choice⟩ :
      SlabObservablePairedConnectedStrandSourceChoice
        D reflectedBentRootFaceId reflectedBentTargetFaceId) ∈
      slabObservablePairedConnectedStrandSourceChoices
        D reflectedBentRootFaceId reflectedBentTargetFaceId := by
  unfold slabObservablePairedConnectedStrandSourceChoices
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      D hcutoff hextent state, ?_, ?_⟩
  · exact List.mem_attach _ _
  · unfold slabObservablePairedConnectedStrandSourceChoiceBlock
    exact List.mem_map.mpr ⟨choice, hchoice, rfl⟩

theorem reflectedBentGuardGraftConnectedSourceChoice_guarded
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : SlabObservablePairedConnectedStrandChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state)) :
    reflectedBentGuardConnectedSourceChoiceB D hextent
      (⟨reflectedBentGuardGraftConnectedStrandSourceAtCutoff
          D hcutoff hextent state, choice⟩ :
        SlabObservablePairedConnectedStrandSourceChoice
          D reflectedBentRootFaceId reflectedBentTargetFaceId) = true := by
  apply List.any_eq_true.mpr
  refine ⟨state, slabAcceptedTwoReplicaState_mem D state, ?_⟩
  apply (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
    D hcutoff hextent _ state).mpr
  constructor
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical]
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]

theorem reflectedBentGuardGraftConnectedSourceChoice_mem_guarded
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : SlabObservablePairedConnectedStrandChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state))
    (hchoice : choice ∈ slabObservablePairedConnectedStrandChoices
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state)) :
    (⟨reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state, choice⟩ :
      SlabObservablePairedConnectedStrandSourceChoice
        D reflectedBentRootFaceId reflectedBentTargetFaceId) ∈
      reflectedBentGuardConnectedSourceChoices D hextent := by
  apply (mem_reflectedBentGuardConnectedSourceChoices_iff
    D hcutoff hextent _).mpr
  refine ⟨
    reflectedBentGuardGraftConnectedSourceChoice_mem_global
      D hcutoff hextent state choice hchoice, state, ?_, ?_⟩
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical]
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]

/-! ## 4. The fixed scaling preserves a literal row floor -/

/-- The receiver-capacity normalization attached to the fixed provenance
code carrier. -/
def reflectedBentGuardConnectedRowScale : Q' :=
  Q'.invSucc reflectedBentGuardProvenanceCodeSpace.length

/-- The total mass of the literal guarded connected row after applying the
fixed receiver-capacity scale. -/
def reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Q' :=
  let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
    D hcutoff hextent state
  reflectedBentGuardConnectedRowScale *
    listQSum
      (slabObservablePairedConnectedStrandWeight D
        reflectedBentRootFaceId reflectedBentTargetFaceId source)
      (slabObservablePairedConnectedStrandChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId source)

theorem reflectedBentGuardGraftConnectedScaledRowMassAtCutoff_quarter
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardConnectedRowScale * oneQuarter ≤
      reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
        D hcutoff hextent state := by
  unfold reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_quarter
      D hcutoff hextent state)
    (Q'.invSucc_nonneg reflectedBentGuardProvenanceCodeSpace.length)

/-! ## 5. Compile every actual fixed-target fiber -/

theorem reflectedBentGuardConnectedTargetPreimage_guarded_of_matches
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target)
    (state : SlabAcceptedTwoReplicaState D)
    (hmatch : reflectedBentGuardConnectedSourceChoiceMatchesStateB
      D hextent item.1 state = true) :
    ∃ background : SlabAcceptedTwoReplicaState D,
      (slabObservablePairedStrandSuccessfulSwitchablePair
        item.1.1.toRecouplingSource item.1.2).pair.1.1.1 =
          reflectedBentGuardGraftLeftPhysical D hextent background ∧
      (slabObservablePairedStrandSuccessfulSwitchablePair
        item.1.1.toRecouplingSource item.1.2).pair.2.1.1 =
          reflectedBentGuardGraftRightPhysical D hextent background := by
  have hfields :=
    (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
      D hcutoff hextent item.1 state).mp hmatch
  refine ⟨state, ?_, ?_⟩
  · simpa only [slabObservablePairedStrandSuccessfulSwitchablePair,
      slabObservablePairedStrandRecoupledPair_leftPhysical] using hfields.1
  · simpa only [slabObservablePairedStrandSuccessfulSwitchablePair,
      slabObservablePairedStrandRecoupledPair_rightPhysical] using hfields.2

/-- Scan accepted backgrounds in list order and emit the first guarded proof
for a fixed target preimage.  The state is selected as data, avoiding any
elimination of a merely propositional existential into `Type`. -/
def reflectedBentGuardConnectedTargetPreimageFromStates?
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target) :
    List (SlabAcceptedTwoReplicaState D) →
      Option (ReflectedBentGuardConnectedTargetPreimage D hextent target)
  | [] => none
  | state :: states =>
      if hmatch : reflectedBentGuardConnectedSourceChoiceMatchesStateB
          D hextent item.1 state = true then
        some ⟨item,
          reflectedBentGuardConnectedTargetPreimage_guarded_of_matches
            D hcutoff hextent target item state hmatch⟩
      else
        reflectedBentGuardConnectedTargetPreimageFromStates?
          D hcutoff hextent target item states

theorem reflectedBentGuardConnectedTargetPreimageFromStates_val_eq_of_some
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target) :
    ∀ states output,
      reflectedBentGuardConnectedTargetPreimageFromStates?
          D hcutoff hextent target item states = some output →
        output.1 = item
  | [], output, hsome => by
      cases hsome
  | state :: states, output, hsome => by
      unfold reflectedBentGuardConnectedTargetPreimageFromStates? at hsome
      split at hsome
      next hmatch =>
        cases Option.some.inj hsome
        rfl
      next hnot =>
        exact reflectedBentGuardConnectedTargetPreimageFromStates_val_eq_of_some
          D hcutoff hextent target item states output hsome

theorem reflectedBentGuardConnectedTargetPreimageFromStates_exists_of_mem_match
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target) :
    ∀ states state,
      state ∈ states →
      reflectedBentGuardConnectedSourceChoiceMatchesStateB
          D hextent item.1 state = true →
        ∃ output,
          reflectedBentGuardConnectedTargetPreimageFromStates?
            D hcutoff hextent target item states = some output
  | [], state, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, state, hmem, hmatch => by
      by_cases hhead : reflectedBentGuardConnectedSourceChoiceMatchesStateB
          D hextent item.1 head = true
      · refine ⟨⟨item,
          reflectedBentGuardConnectedTargetPreimage_guarded_of_matches
            D hcutoff hextent target item head hhead⟩, ?_⟩
        unfold reflectedBentGuardConnectedTargetPreimageFromStates?
        rw [dif_pos hhead]
      · have htail : state ∈ tail := by
          rcases List.mem_cons.mp hmem with heq | htail
          · subst state
            exact absurd hmatch hhead
          · exact htail
        obtain ⟨output, houtput⟩ :=
          reflectedBentGuardConnectedTargetPreimageFromStates_exists_of_mem_match
            D hcutoff hextent target item tail state htail hmatch
        refine ⟨output, ?_⟩
        unfold reflectedBentGuardConnectedTargetPreimageFromStates?
        rw [dif_neg hhead]
        exact houtput

/-- The actual proof-carrying guarded preimages of one final receiver.  Each
global target preimage emits at most one value, using its first matching
accepted background. -/
def reflectedBentGuardConnectedTargetPreimages
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List (ReflectedBentGuardConnectedTargetPreimage D hextent target) :=
  (slabObservablePairedConnectedStrandTargetPreimages
    D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardConnectedTargetFace_mem D hextent) target).attach.filterMap
        fun item => reflectedBentGuardConnectedTargetPreimageFromStates?
          D hcutoff hextent target item
          (slabAcceptedTwoReplicaStates D)

theorem reflectedBentGuardConnectedTargetPreimages_nodup
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardConnectedTargetPreimages
      D hcutoff hextent target).Nodup := by
  unfold reflectedBentGuardConnectedTargetPreimages
  apply filterMap_nodup_of_separated_local
  · exact attach_nodup_of_nodup _
      (slabObservablePairedConnectedStrandTargetPreimages_nodup
        D reflectedBentRootFaceId reflectedBentTargetFaceId
          (reflectedBentGuardConnectedTargetFace_mem D hextent) target)
  · intro left _ right _ hne value hleft hright
    apply hne
    exact
      (reflectedBentGuardConnectedTargetPreimageFromStates_val_eq_of_some
        D hcutoff hextent target left
          (slabAcceptedTwoReplicaStates D) value hleft).symm.trans
      (reflectedBentGuardConnectedTargetPreimageFromStates_val_eq_of_some
        D hcutoff hextent target right
          (slabAcceptedTwoReplicaStates D) value hright)

/-- Every guarded row entry that realizes `target` is emitted exactly once
up to proof irrelevance by the concrete first-background target compiler. -/
theorem reflectedBentGuardConnectedTargetPreimages_complete
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hitem : item ∈ reflectedBentGuardConnectedSourceChoices D hextent)
    (htarget : target =
      slabObservablePairedConnectedStrandSourceChoiceRealize
        D reflectedBentRootFaceId reflectedBentTargetFaceId
          (reflectedBentGuardConnectedTargetFace_mem D hextent) item) :
    ∃ output,
      output ∈ reflectedBentGuardConnectedTargetPreimages
          D hcutoff hextent target ∧
        output.1.1 = item := by
  have hparts :=
    (mem_reflectedBentGuardConnectedSourceChoices_iff
      D hcutoff hextent item).mp hitem
  have htargetMem : item ∈
      slabObservablePairedConnectedStrandTargetPreimages
        D reflectedBentRootFaceId reflectedBentTargetFaceId
          (reflectedBentGuardConnectedTargetFace_mem D hextent) target :=
    (mem_slabObservablePairedConnectedStrandTargetPreimages_iff
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent)
        target item).mpr ⟨hparts.1, htarget⟩
  let preimage : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target :=
    ⟨item, htargetMem⟩
  obtain ⟨state, hfields⟩ := hparts.2
  have hmatch : reflectedBentGuardConnectedSourceChoiceMatchesStateB
      D hextent preimage.1 state = true :=
    (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
      D hcutoff hextent item state).mpr hfields
  obtain ⟨output, houtput⟩ :=
    reflectedBentGuardConnectedTargetPreimageFromStates_exists_of_mem_match
      D hcutoff hextent target preimage
        (slabAcceptedTwoReplicaStates D) state
        (slabAcceptedTwoReplicaState_mem D state) hmatch
  refine ⟨output, ?_, ?_⟩
  · unfold reflectedBentGuardConnectedTargetPreimages
    apply List.mem_filterMap.mpr
    exact ⟨preimage, List.mem_attach _ preimage, houtput⟩
  · have hval :=
      reflectedBentGuardConnectedTargetPreimageFromStates_val_eq_of_some
        D hcutoff hextent target preimage
          (slabAcceptedTwoReplicaStates D) output houtput
    exact congrArg Subtype.val hval

/-- Forget only the proof fields from the guarded target candidates.  This is
the concrete fixed-target fiber of source-choice entries. -/
def reflectedBentGuardConnectedTargetSourceChoices
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  (reflectedBentGuardConnectedTargetPreimages
    D hcutoff hextent target).map fun item => item.1.1

theorem reflectedBentGuardConnectedTargetSourceChoices_nodup
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardConnectedTargetSourceChoices
      D hcutoff hextent target).Nodup := by
  unfold reflectedBentGuardConnectedTargetSourceChoices
  apply nodup_map_of_injective_local
  · intro left right heq
    apply Subtype.ext
    exact Subtype.ext heq
  · exact reflectedBentGuardConnectedTargetPreimages_nodup
      D hcutoff hextent target

/-- **Actual guarded receiver capacity.**  The fixed provenance scaling gives
unit column capacity on the concrete proof-carrying target fiber compiled
above. -/
theorem reflectedBentGuardConnectedActualTargetPreimages_scaled_sum_le_one
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    listQSum
        (fun item => reflectedBentGuardConnectedRowScale *
          reflectedBentGuardConnectedTargetPreimageWeight D item)
        (reflectedBentGuardConnectedTargetPreimages
          D hcutoff hextent target) ≤
      (1 : Q') := by
  unfold reflectedBentGuardConnectedRowScale
  exact reflectedBentGuardConnectedTargetPreimages_scaled_sum_le_one
    D hextent target
    (reflectedBentGuardConnectedTargetPreimages
      D hcutoff hextent target)
    (reflectedBentGuardConnectedTargetPreimages_nodup
      D hcutoff hextent target)

/-! ## 6. The same actual columns respect physical Gibbs capacity -/

/-- The physical Gibbs weight attached to the source row of one compiled
guarded target preimage. -/
def reflectedBentGuardConnectedTargetPreimageSourceWeight
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (item : ReflectedBentGuardConnectedTargetPreimage D hextent target) : Q' :=
  slabObservableTwoReplicaPairWeight D item.1.1.1.1

/-- **Actual Gibbs-weighted receiver capacity.**  Exact physical-weight
preservation across the successful face switch upgrades the scaled local
column bound to a bound by the available Gibbs weight of the final receiver.
This is still a finite-cutoff statement; it does not yet sum the accepted
background fibers or assert an aggregate retained fraction. -/
theorem reflectedBentGuardConnectedActualTargetPreimages_scaled_physical_sum_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    listQSum
        (fun item =>
          reflectedBentGuardConnectedTargetPreimageSourceWeight D item *
            (reflectedBentGuardConnectedRowScale *
              reflectedBentGuardConnectedTargetPreimageWeight D item))
        (reflectedBentGuardConnectedTargetPreimages
          D hcutoff hextent target) ≤
      slabObservableTwoReplicaPairWeight D target := by
  let items := reflectedBentGuardConnectedTargetPreimages
    D hcutoff hextent target
  let targetWeight := slabObservableTwoReplicaPairWeight D target
  let scaledWeight := fun item :
      ReflectedBentGuardConnectedTargetPreimage D hextent target =>
    reflectedBentGuardConnectedRowScale *
      reflectedBentGuardConnectedTargetPreimageWeight D item
  have hweights :
      listQSum
          (fun item =>
            reflectedBentGuardConnectedTargetPreimageSourceWeight D item *
              scaledWeight item)
          items ≈
        listQSum (fun item => targetWeight * scaledWeight item) items := by
    apply listQSum_congr_on
    intro item _
    apply Q'.mul_eqv_congr_right
    have hpreserved :=
      slabObservablePairedStrandRecoupledTargetPair_weight_preserved
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent)
        item.1.1.1.toRecouplingSource item.1.1.2
    have htarget :
        slabObservablePairedStrandRecoupledTargetPair
            D reflectedBentRootFaceId reflectedBentTargetFaceId
              (reflectedBentGuardConnectedTargetFace_mem D hextent)
              item.1.1.1.toRecouplingSource item.1.1.2 = target := by
      simpa only [slabObservablePairedConnectedStrandSourceChoiceRealize,
        slabObservablePairedConnectedStrandRealize] using item.1.target_eq.symm
    simpa only [reflectedBentGuardConnectedTargetPreimageSourceWeight,
        targetWeight] using
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hpreserved)
        (Q'.eqv_of_eq
          (congrArg (slabObservableTwoReplicaPairWeight D) htarget))
  have hfactor :
      listQSum (fun item => targetWeight * scaledWeight item) items ≈
        targetWeight * listQSum scaledWeight items :=
    listQSum_mul_left targetWeight scaledWeight items
  have hcapacity : listQSum scaledWeight items ≤ (1 : Q') := by
    exact reflectedBentGuardConnectedActualTargetPreimages_scaled_sum_le_one
      D hcutoff hextent target
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ targetWeight hcapacity
    (slabObservableTwoReplicaPairWeight_nonnegative
      D reflectedBentRootFaceId target)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hweights hfactor))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv targetWeight)))

#print axioms reflectedBentGuardConnectedSourceChoiceB_eq_true_iff
#print axioms reflectedBentGuardConnectedSourceChoices_nodup
#print axioms reflectedBentGuardGraftConnectedSourceChoice_mem_guarded
#print axioms reflectedBentGuardGraftConnectedScaledRowMassAtCutoff_quarter
#print axioms reflectedBentGuardConnectedTargetPreimages_nodup
#print axioms reflectedBentGuardConnectedTargetPreimages_complete
#print axioms reflectedBentGuardConnectedActualTargetPreimages_scaled_sum_le_one
#print axioms reflectedBentGuardConnectedTargetPreimageSourceWeight
#print axioms reflectedBentGuardConnectedActualTargetPreimages_scaled_physical_sum_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedRowCarrier
