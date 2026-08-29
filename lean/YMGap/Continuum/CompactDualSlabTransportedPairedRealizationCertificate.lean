/-
# Paired realization across a symbolic complete link list

Generalize the existing one-sided transported-realization certificate to both
replicas.  All recursion remains over an abstract complete linked list; the
caller supplies only its equality with the canonical attachment list and a
symbolic identification of both expected assignments.

Constructive contract: equality transport, anchor independence, and symbolic
list reasoning only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice

namespace YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

structure TransportedPairedRealizationCertificate
    (K extent : Nat)
    (leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling)
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
    (expectedLeft expectedRight : SlabFusionWitnessAssignment) : Type where
  transported : TransportedTargetPackage
    (slabPhysicalPairRecouplingPackages extent
      leftPhysical₂ rightPhysical₂)
    (LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList)
    hpackages₂
  leftAssignment_eq :
    (secondAnchor.realize transported.target).leftAssignment = expectedLeft
  rightAssignment_eq :
    (secondAnchor.realize transported.target).rightAssignment = expectedRight

def transportLinkedPairedRealizationCertificate
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hlinks : linkedList = (boundaryCompleteSlabLinks extent).attach)
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
    (expectedLeft expectedRight :
      List {link // link ∈ boundaryCompleteSlabLinks extent} →
        SlabFusionWitnessAssignment)
    (linked : ∀ links,
      let canonical := slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
        links (sourceTargets links).target
      expectedLeft links = canonical.leftAssignment ∧
        expectedRight links = canonical.rightAssignment) :
    TransportedPairedRealizationCertificate K extent
      leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂
      linkedList hpackages₂ (sourceTargets linkedList) secondAnchor
      (expectedLeft linkedList) (expectedRight linkedList) := by
  have hpackages₁ : slabPhysicalPairRecouplingPackages extent
      leftPhysical₁ rightPhysical₁ =
    LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList := by
    cases hlinks
    rfl
  let sourceTarget := sourceTargets linkedList
  let transported := transportedTargetPackage hpackages₂ sourceTarget
  have htarget := transportedTarget_eq_physicalTransport
    hleft hright
    (LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList)
    hpackages₁ hpackages₂ sourceTarget
  have hanchor := canonicalAnchor_realize_physicalTransport_assignments_eq
    hleft hright firstLeftAssignment firstRightAssignment
    firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
    secondAnchor
    (transportFiniteBistochasticTargetAssignment
      hpackages₁ sourceTarget.target)
  have hlinked :
      let first := slabPhysicalPairCanonicalTargetAssignmentsResult
        K extent leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
        (transportFiniteBistochasticTargetAssignment
          hpackages₁ sourceTarget.target)
      first.leftAssignment = expectedLeft linkedList ∧
        first.rightAssignment = expectedRight linkedList := by
    have hfamily := linked linkedList
    cases hlinks
    exact ⟨hfamily.1.symm, hfamily.2.symm⟩
  refine
    { transported := transported
      leftAssignment_eq := ?_
      rightAssignment_eq := ?_ }
  · rw [htarget]
    exact hanchor.1.trans hlinked.1
  · rw [htarget]
    exact hanchor.2.trans hlinked.2

#print axioms transportLinkedPairedRealizationCertificate

end YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate
