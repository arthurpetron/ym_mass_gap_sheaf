/-
# Literal separated-cylinder mass inside the successful observable row

The literal cylinder is now known pointwise to realize a disconnected
observable recoupling.  This module proves the finite multiplicity and
weight-preserving injection needed to place its whole quarter-mass inside the
successful-choice filter of the canonical observable row.

Constructive contract: finite list recursion, equality transport, exact
rational weights, and the checked pointwise success certificate only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccess
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccessfulMass

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem map_nodup_of_injective_on {A B : Type}
    (map : A → B) : ∀ items : List A,
    items.Nodup →
    (∀ first, first ∈ items → ∀ second, second ∈ items →
      map first = map second → first = second) →
    (items.map map).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
        have hsame := hinjective head List.mem_cons_self other
          (List.mem_cons_of_mem head hother) heq.symm
        subst other
        exact hparts.1 hother
      · exact map_nodup_of_injective_on map tail hparts.2
          (fun first hfirst second hsecond heq =>
            hinjective first (List.mem_cons_of_mem head hfirst)
              second (List.mem_cons_of_mem head hsecond) heq)

/-- The pivot-cylinder enumeration has no multiplicities. -/
theorem reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_nodup
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5},
      (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList).Nodup
  | [] => by
      simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff]
      exact List.nodup_nil
  | linked :: rest => by
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_true]
        apply map_nodup_of_injective_on
        · apply finiteBistochasticTargetAssignments_nodup
          intro package hpackage
          obtain ⟨tailLinked, _, rfl⟩ := List.mem_map.mp hpackage
          unfold slabPhysicalPairRecouplingPackageAtLink
          exact slabPhysicalPairRecouplingKernelPackage_targets_nodup
            (slabIncidentPlaqIds 5 tailLinked.1).length
            (slabPhysicalPairRecouplingDataAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              tailLinked)
        · intro first _ second _ heq
          exact congrArg Prod.snd heq
      · simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_false]
        change (cartesian
          (slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked).kernel.targets
          (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
            D hcutoff hextent state rest)).Nodup
        apply cartesian_nodup
        · unfold slabPhysicalPairRecouplingPackageAtLink
          exact slabPhysicalPairRecouplingKernelPackage_targets_nodup
            (slabIncidentPlaqIds 5 linked.1).length
            (slabPhysicalPairRecouplingDataAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              linked)
        · exact reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_nodup
            D hcutoff hextent state rest

#print axioms reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_nodup

abbrev ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  {target // target ∈
    reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
      D hcutoff hextent state linkedList}

def reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (member : ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
      D hcutoff hextent state linkedList) :
    ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state :=
  .mk linkedList hlinks member.1
    (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
      D hcutoff hextent state linkedList member.1 member.2)
    (reflectedBentGuardGraftStandardTarget_noMarkedFaceChainAtCutoff
      D hcutoff hextent state linkedList member.1
      (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_pinned
        D hcutoff hextent state linkedList member.1 member.2))

def reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (member : ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
      D hcutoff hextent state linkedList) :
    SlabObservablePairedStrandRecouplingChoice D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state) :=
  (reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff
    D hcutoff hextent state linkedList hlinks member).observableChoice

theorem reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (member : ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
      D hcutoff hextent state linkedList) :
    reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
        D hcutoff hextent state linkedList hlinks member ∈
      slabObservablePairedStrandRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) :=
  (reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff
    D hcutoff hextent state linkedList hlinks member).observableChoice_mem

theorem reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_success
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (member : ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
      D hcutoff hextent state linkedList) :
    slabObservablePairedStrandRecouplingSuccessB D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
        D hcutoff hextent state linkedList hlinks member) = true :=
  reflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff_success
    D hcutoff hextent state
    (reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff
      D hcutoff hextent state linkedList hlinks member)

theorem reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_injective
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (first second : ReflectedBentGuardGraftLiteralCylinderMemberAtCutoff
      D hcutoff hextent state linkedList)
    (heq : reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
        D hcutoff hextent state linkedList hlinks first =
      reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
        D hcutoff hextent state linkedList hlinks second) :
    first = second := by
  apply Subtype.ext
  apply observablePairedTargetOfWrittenAtExtent_injective D 5 hextent
    reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    linkedList
    (literalCylinderObservablePackages_eq
      D hcutoff hextent state linkedList hlinks)
  simpa only [
    reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff,
    reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff,
    ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff.observableChoice]
    using heq

def reflectedBentGuardGraftLiteralObservablePinnedTargetRawWeightAtCutoff
    {D : SlabPhysicalData} {hcutoff : 1 ≤ D.cutoff}
    {hextent : D.extent = 5}
    {state : SlabAcceptedTwoReplicaState D}
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) : Q' :=
  match input with
  | .mk linkedList _ target _ _ =>
      reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
        D hcutoff hextent state linkedList target

structure ReflectedBentGuardGraftLiteralObservableWeightedTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) : Type where
  cylinderWeight : Q'
  cylinderWeight_eq : cylinderWeight =
    reflectedBentGuardGraftLiteralObservablePinnedTargetRawWeightAtCutoff input
  observableWeight_eqv :
    slabObservablePairedStrandRecouplingWeight D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) input.observableChoice ≈ cylinderWeight

opaque reflectedBentGuardGraftLiteralObservableWeightedTargetOfPinnedAtCutoff
    {D : SlabPhysicalData} {hcutoff : 1 ≤ D.cutoff}
    {hextent : D.extent = 5}
    {state : SlabAcceptedTwoReplicaState D}
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) :
    ReflectedBentGuardGraftLiteralObservableWeightedTargetAtCutoff
      D hcutoff hextent state input := by
  rcases input with ⟨linkedList, hlinks, target, target_mem, hnoChain⟩
  let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    D hcutoff hextent state
  let hpackages :=
    (congrArg (fun currentExtent =>
      slabPhysicalPairRecouplingPackages currentExtent
        source.1.1.1.1 source.1.2.1.1) hextent).trans
      (literalCylinderObservablePackages_eq
        D hcutoff hextent state linkedList hlinks)
  have htransport := finiteBistochasticProductWeight_transport_eqv
    hpackages
    (literalObservableProductionSourceAtCutoff
      D hcutoff hextent state)
    target
  let hsourcePackages :=
    (slabPhysicalPairRecouplingPackages_transport_extent
      D.extent 5 hextent
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
        D hcutoff hextent state)
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
        D hcutoff hextent state)).trans
      (congrArg (fun links => links.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) hlinks.symm)
  have hsource :
      transportFiniteBistochasticSourceAssignment hsourcePackages
          (literalObservableProductionSourceAtCutoff
            D hcutoff hextent state) =
        slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (reflectedBentGuardGraftLeftAssignment D hextent state)
          (reflectedBentGuardGraftRightAssignment D hextent state)
          (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
            D hcutoff hextent state)
          (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
            D hcutoff hextent state)
          linkedList := by
    simpa only [hsourcePackages, source,
      literalObservableProductionSourceAtCutoff] using
      (slabPhysicalPairRecouplingProductionSource_transport_extent_to_links
        D.cutoff D.extent 5 hextent
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
          D hcutoff hextent state)
        source.1.1.1.2 source.1.2.1.2
        (reflectedBentGuardGraftLeftAssignment D hextent state)
        (reflectedBentGuardGraftRightAssignment D hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftAssignment
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightAssignment
          D hcutoff hextent state)
        source.1.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem source.1.2)
        (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
          D hcutoff hextent state)
        linkedList hlinks.symm)
  have hequalities : hpackages = hsourcePackages :=
    Subsingleton.elim _ _
  rw [hequalities, hsource] at htransport
  refine
    { cylinderWeight :=
        reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList target
      cylinderWeight_eq := rfl
      observableWeight_eqv := ?_ }
  simpa only [source, hpackages,
    slabObservablePairedStrandRecouplingWeight,
    slabPhysicalPairRecouplingKernel,
    literalObservableProductionSourceAtCutoff,
    ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff.observableChoice,
    observablePairedTargetOfWrittenAtExtent,
    reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff]
    using htransport

theorem reflectedBentGuardGraftLiteralObservableDisconnectionMass_quarter_of_writtenLinks
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList) :
    oneQuarter ≤
      slabObservablePairedStrandDisconnectionMass D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) := by
  let targets := reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
    D hcutoff hextent state linkedList
  let sourceWeight := fun member : {target // target ∈ targets} =>
    reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
      D hcutoff hextent state linkedList member.1
  let encode := fun member : {target // target ∈ targets} =>
    reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff
      D hcutoff hextent state linkedList hlinks member
  have hsumLe : listQSum sourceWeight targets.attach ≤
      slabObservablePairedStrandDisconnectionMass D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) := by
    unfold slabObservablePairedStrandDisconnectionMass
    apply listQSum_le_of_injective_nodup
      targets.attach
      (slabObservablePairedStrandSuccessfulRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state))
      sourceWeight
      (slabObservablePairedStrandRecouplingWeight D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state))
      encode
    · exact attach_nodup_of_nodup _
        (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_nodup
          D hcutoff hextent state linkedList)
    · unfold slabObservablePairedStrandSuccessfulRecouplingChoices
        slabObservablePairedStrandRecouplingChoices
      exact List.filter_sublist.nodup
        (slabPhysicalPairRecouplingKernel_targets_nodup D.extent
          (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
            D hcutoff hextent state).1.1.1.1
          (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
            D hcutoff hextent state).1.2.1.1)
    · intro member _
      unfold encode slabObservablePairedStrandSuccessfulRecouplingChoices
      apply List.mem_filter.mpr
      exact ⟨
        reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_mem
          D hcutoff hextent state linkedList hlinks member,
        reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_success
          D hcutoff hextent state linkedList hlinks member⟩
    · intro first _ second _ heq
      unfold encode at heq
      exact reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_injective
        D hcutoff hextent state linkedList hlinks first second heq
    · intro member _
      let input :=
        reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff
          D hcutoff hextent state linkedList hlinks member
      let weighted :=
        reflectedBentGuardGraftLiteralObservableWeightedTargetOfPinnedAtCutoff
          input
      have hweight : weighted.cylinderWeight = sourceWeight member := by
        rw [weighted.cylinderWeight_eq]
        rfl
      have heqv :
          slabObservablePairedStrandRecouplingWeight D
              reflectedBentRootFaceId reflectedBentTargetFaceId
              (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
                D hcutoff hextent state) (encode member) ≈
            sourceWeight member := by
        apply Q'.eqv_trans _ weighted.cylinderWeight _
        · simpa only [weighted, input, encode,
            reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff,
            reflectedBentGuardGraftLiteralObservablePinnedTargetFromMemberAtCutoff]
            using weighted.observableWeight_eqv
        · exact Q'.eqv_of_eq hweight
      exact Q'.ge_of_eqv heqv
    · intro choice _
      exact slabObservablePairedStrandRecouplingWeight_nonnegative D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) choice
  have hattach : listQSum sourceWeight targets.attach =
      listQSum
        (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList) targets := by
    simpa only [sourceWeight] using
      (listQSum_attach
        (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList) targets)
  have hfloor :=
    reflectedBentGuardGraftPivotCylinderFromAtCutoff_weight_sum_floor
      D hcutoff hextent state linkedList hnodup hpivot
  have hfloor' : oneQuarter ≤
      listQSum
        (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList) targets := by
    simpa only [targets,
      reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff] using hfloor
  rw [← hattach] at hfloor'
  exact Q'.le_trans' _ _ _ hfloor' hsumLe

/-- **Literal successful-event mass floor.**  At every positive cutoff, the
canonical observable recoupling row of the guarded extent-five state assigns
at least one quarter of its mass to choices that disconnect the marked
faces. -/
theorem reflectedBentGuardGraftLiteralObservableDisconnectionMass_quarter
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    oneQuarter ≤
      slabObservablePairedStrandDisconnectionMass D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) := by
  exact
    reflectedBentGuardGraftLiteralObservableDisconnectionMass_quarter_of_writtenLinks
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach rfl
      (attach_nodup_of_nodup _ (boundaryCompleteSlabLinks_nodup 5))
      (List.mem_attach _ _)

#print axioms reflectedBentGuardGraftLiteralObservableEncodedChoiceFromAtCutoff_success
#print axioms reflectedBentGuardGraftLiteralObservableWeightedTargetOfPinnedAtCutoff
#print axioms reflectedBentGuardGraftLiteralObservableDisconnectionMass_quarter

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccessfulMass
