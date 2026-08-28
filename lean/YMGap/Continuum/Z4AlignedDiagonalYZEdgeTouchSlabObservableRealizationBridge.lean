/-
# Transport the aligned observable target to the disconnected assignment

Keep the pre-transport realization in its linked-list presentation, where
structural recursion is cheap.  A generic theorem, still polymorphic in the
extent, then identifies a complete linked list with the canonical full-slab
realizer and transports it to the actual observable source anchor.

Constructive contract: equality transport, anchor independence, and the
proved structural assignment recursion only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableTargetPackage

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableRealizationBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableTargetPackage
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

abbrev LinkedPhysicalPairPackages
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink extent
      leftPhysical rightPhysical linked

/-! ## 1. Cheap linked-list realization -/

theorem alignedDiagonalLinkedLeftRealization_eq :
    ∀ linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
      alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchLeftFineWitness.1
      alignedDiagonalSwitchRightFineWitness.1
      alignedDiagonalSwitchLeftAssignment_mem
      alignedDiagonalSwitchRightAssignment_mem
      alignedDiagonalSwitchLeftPhysical_bounded
      alignedDiagonalSwitchRightPhysical_bounded
      linkedList
      (alignedDiagonalSwitchTargetMembershipPackageFrom
        linkedList).target).leftAssignment =
          alignedDiagonalSwitchRealizedLeftAssignmentFrom linkedList := by
  intro linkedList
  rw [alignedDiagonalSwitchTargetMembershipPackageFrom_target]
  exact (alignedDiagonalSwitchRealizedLeftAssignmentFrom_eq_canonical
    linkedList).symm

/-! ## 2. Generic target and anchor transport -/

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
    (firstLeftBounded :
      SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded :
      SlabFaceLabellingBounded K extent rightPhysical₁)
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
    (firstLeftBounded :
      SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded :
      SlabFaceLabellingBounded K extent rightPhysical₁)
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

/-! ## 3. The actual observable source realization -/

theorem alignedDiagonalSwitchLinkedList_eq_attach :
    alignedDiagonalSwitchLinkedList =
      (boundaryCompleteSlabLinks 5).attach := rfl

def alignedDiagonalObservableLeftRealization :
    TransportedLeftRealizationCertificate 1 5
      alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchRecouplingSource.1.1.1.1
      alignedDiagonalSwitchRecouplingSource.1.2.1.1
      alignedDiagonalSwitchLinkedList
      alignedDiagonalSwitchRecouplingPackages_eq
      (alignedDiagonalSwitchTargetMembershipPackageFrom
        alignedDiagonalSwitchLinkedList)
      alignedDiagonalSwitchRecouplingSource.anchor
      alignedDiagonalTargetMeasureIndexAssignment :=
  transportLinkedLeftRealizationCertificate
    alignedDiagonalSwitchRecouplingSource_leftPhysical.symm
    alignedDiagonalSwitchRecouplingSource_rightPhysical.symm
    alignedDiagonalSwitchLinkedList
    alignedDiagonalSwitchLinkedList_eq_attach
    alignedDiagonalSwitchRecouplingPackages_eq
    alignedDiagonalSwitchTargetMembershipPackageFrom
    alignedDiagonalSwitchLeftFineWitness.1
    alignedDiagonalSwitchRightFineWitness.1
    alignedDiagonalSwitchLeftAssignment_mem
    alignedDiagonalSwitchRightAssignment_mem
    alignedDiagonalSwitchLeftPhysical_bounded
    alignedDiagonalSwitchRightPhysical_bounded
    alignedDiagonalSwitchRecouplingSource.anchor
    alignedDiagonalSwitchRealizedLeftAssignmentFrom
    alignedDiagonalLinkedLeftRealization_eq

#print axioms alignedDiagonalLinkedLeftRealization_eq
#print axioms transportedTarget_eq_physicalTransport
#print axioms canonicalAnchor_realize_physicalTransport_left_eq
#print axioms alignedDiagonalObservableLeftRealization

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableRealizationBridge
