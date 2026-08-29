/-
# Transport the reflected observable target to the disconnected assignment

Keep the pre-transport realization in its linked-list presentation, then
identify the complete linked list with the canonical full-slab realizer and
transport it to the actual observable source anchor.

Constructive contract: equality transport, anchor independence, and proved
assignment recursion only; no choice, `Classical`, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableTargetPackage

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableTargetPackage
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

abbrev LinkedPhysicalPairPackages
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink extent
      leftPhysical rightPhysical linked

theorem reflectedBentLinkedLeftRealization_eq :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
    (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      reflectedBentLeftFineWitness.1 reflectedBentRightFineWitness.1
      reflectedBentSwitchLeftAssignment_mem
      reflectedBentSwitchRightAssignment_mem
      reflectedBentSwitchLeftPhysical_bounded
      reflectedBentSwitchRightPhysical_bounded linkedList
      (reflectedBentSwitchTargetMembershipPackageFrom
        linkedList).target).leftAssignment =
          reflectedBentSwitchRealizedLeftAssignmentFrom linkedList := by
  intro linkedList
  rw [reflectedBentSwitchTargetMembershipPackageFrom_target]
  exact (reflectedBentSwitchRealizedLeftAssignmentFrom_eq_canonical
    linkedList).symm

structure TransportedLeftRealizationCertificate
    (K extent : Nat)
    (leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages₂ : slabPhysicalPairRecouplingPackages extent
        leftPhysical₂ rightPhysical₂ =
      LinkedPhysicalPairPackages extent
        leftPhysical₁ rightPhysical₁ linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages extent
        leftPhysical₁ rightPhysical₁ linkedList))
    (secondAnchor : SlabPhysicalPairCanonicalAnchor K extent
      leftPhysical₂ rightPhysical₂)
    (expected : SlabFusionWitnessAssignment) : Type where
  transported : TransportedTargetPackage
    (slabPhysicalPairRecouplingPackages extent
      leftPhysical₂ rightPhysical₂)
    (LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList)
    hpackages₂
  leftAssignment_eq :
    (secondAnchor.realize transported.target).leftAssignment = expected

theorem transportedTarget_eq_physicalTransport
    {extent : Nat}
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (rightPackages : List FiniteBistochasticQKernelPackage)
    (hpackages₁ : slabPhysicalPairRecouplingPackages extent
        leftPhysical₁ rightPhysical₁ = rightPackages)
    (hpackages₂ : slabPhysicalPairRecouplingPackages extent
        leftPhysical₂ rightPhysical₂ = rightPackages)
    (sourceTarget : TargetMembershipPackage rightPackages) :
    (transportedTargetPackage hpackages₂ sourceTarget).target =
      transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright
        (transportFiniteBistochasticTargetAssignment
          hpackages₁ sourceTarget.target) := by
  cases hleft
  cases hright
  have hproof : hpackages₂ = hpackages₁ := Subsingleton.elim _ _
  cases hproof
  rw [(transportedTargetPackage hpackages₁ sourceTarget).target_eq,
    transportedTargetPackage_sourceTarget hpackages₁ sourceTarget]
  rfl

theorem canonicalAnchor_realize_physicalTransport_left_eq
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (firstLeftAssignment firstRightAssignment :
      SlabFusionWitnessAssignment)
    (firstLeft_mem : firstLeftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstRight_mem : firstRightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstLeftBounded : SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded : SlabFaceLabellingBounded K extent rightPhysical₁)
    (second : SlabPhysicalPairCanonicalAnchor K extent
      leftPhysical₂ rightPhysical₂)
    (target : SlabPhysicalPairRecouplingTargetAssignment extent
      leftPhysical₁ rightPhysical₁) :
    (second.realize
      (transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright target)).leftAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem
        firstLeftBounded firstRightBounded target).leftAssignment := by
  cases hleft
  cases hright
  exact (slabPhysicalPairCanonicalTargetAssignmentsResult_anchor_independent
    K extent leftPhysical₁ rightPhysical₁
    second.leftAssignment second.rightAssignment
    firstLeftAssignment firstRightAssignment
    second.left_mem second.right_mem firstLeft_mem firstRight_mem
    second.leftBounded second.rightBounded target).1

def transportLinkedLeftRealizationCertificate
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hlinks : linkedList =
      (boundaryCompleteSlabLinks extent).attach)
    (hpackages₂ : slabPhysicalPairRecouplingPackages extent
        leftPhysical₂ rightPhysical₂ =
      LinkedPhysicalPairPackages extent
        leftPhysical₁ rightPhysical₁ linkedList)
    (sourceTargets : (links :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) →
        TargetMembershipPackage
          (LinkedPhysicalPairPackages extent
            leftPhysical₁ rightPhysical₁ links))
    (firstLeftAssignment firstRightAssignment :
      SlabFusionWitnessAssignment)
    (firstLeft_mem : firstLeftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstRight_mem : firstRightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstLeftBounded : SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded : SlabFaceLabellingBounded K extent rightPhysical₁)
    (secondAnchor : SlabPhysicalPairCanonicalAnchor K extent
      leftPhysical₂ rightPhysical₂)
    (expected : List {link //
      link ∈ boundaryCompleteSlabLinks extent} →
        SlabFusionWitnessAssignment)
    (linked : ∀ links,
      (slabPhysicalPairCanonicalTargetAssignmentsFrom K extent
        leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem
        firstLeftBounded firstRightBounded
        links (sourceTargets links).target).leftAssignment =
          expected links) :
    TransportedLeftRealizationCertificate K extent
      leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂
      linkedList hpackages₂ (sourceTargets linkedList) secondAnchor
      (expected linkedList) := by
  have hpackages₁ : slabPhysicalPairRecouplingPackages extent
      leftPhysical₁ rightPhysical₁ =
    LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList := by
    cases hlinks
    rfl
  let sourceTarget := sourceTargets linkedList
  let transported := transportedTargetPackage hpackages₂ sourceTarget
  refine
    { transported := transported
      leftAssignment_eq := ?_ }
  have htarget := transportedTarget_eq_physicalTransport
    hleft hright
    (LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList)
    hpackages₁ hpackages₂ sourceTarget
  have hanchor := canonicalAnchor_realize_physicalTransport_left_eq
    hleft hright
    firstLeftAssignment firstRightAssignment
    firstLeft_mem firstRight_mem
    firstLeftBounded firstRightBounded secondAnchor
    (transportFiniteBistochasticTargetAssignment
      hpackages₁ sourceTarget.target)
  have hlinked :
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem
        firstLeftBounded firstRightBounded
        (transportFiniteBistochasticTargetAssignment
          hpackages₁ sourceTarget.target)).leftAssignment =
        expected linkedList := by
    have hfamily := linked linkedList
    cases hlinks
    exact hfamily
  calc
    (secondAnchor.realize transported.target).leftAssignment =
        (secondAnchor.realize
          (transportSlabPhysicalPairRecouplingTargetAssignment
            hleft hright
            (transportFiniteBistochasticTargetAssignment
              hpackages₁ sourceTarget.target))).leftAssignment := by
      rw [htarget]
    _ = (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem
        firstLeftBounded firstRightBounded
        (transportFiniteBistochasticTargetAssignment
          hpackages₁ sourceTarget.target)).leftAssignment := hanchor
    _ = expected linkedList := hlinked

theorem reflectedBentSwitchLinkedList_eq_attach :
    reflectedBentSwitchLinkedList =
      (boundaryCompleteSlabLinks 5).attach := rfl

def reflectedBentObservableLeftRealization :
    TransportedLeftRealizationCertificate 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      reflectedBentSwitchRecouplingSource.1.1.1.1
      reflectedBentSwitchRecouplingSource.1.2.1.1
      reflectedBentSwitchLinkedList
      reflectedBentSwitchRecouplingPackages_eq
      (reflectedBentSwitchTargetMembershipPackageFrom
        reflectedBentSwitchLinkedList)
      reflectedBentSwitchRecouplingSource.anchor
      reflectedBentTargetMeasureIndexAssignment :=
  transportLinkedLeftRealizationCertificate
    reflectedBentSwitchRecouplingSource_leftPhysical.symm
    reflectedBentSwitchRecouplingSource_rightPhysical.symm
    reflectedBentSwitchLinkedList
    reflectedBentSwitchLinkedList_eq_attach
    reflectedBentSwitchRecouplingPackages_eq
    reflectedBentSwitchTargetMembershipPackageFrom
    reflectedBentLeftFineWitness.1 reflectedBentRightFineWitness.1
    reflectedBentSwitchLeftAssignment_mem
    reflectedBentSwitchRightAssignment_mem
    reflectedBentSwitchLeftPhysical_bounded
    reflectedBentSwitchRightPhysical_bounded
    reflectedBentSwitchRecouplingSource.anchor
    reflectedBentSwitchRealizedLeftAssignmentFrom
    reflectedBentLinkedLeftRealization_eq

#print axioms reflectedBentLinkedLeftRealization_eq
#print axioms transportedTarget_eq_physicalTransport
#print axioms canonicalAnchor_realize_physicalTransport_left_eq
#print axioms reflectedBentObservableLeftRealization

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge
