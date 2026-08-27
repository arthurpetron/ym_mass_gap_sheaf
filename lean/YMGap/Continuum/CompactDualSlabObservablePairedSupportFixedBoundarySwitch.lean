/-
# The paired-support switch stays inside a shared OS boundary fiber

The canonical two-replica move is a facewise transposition.  Therefore it
does not have to avoid the fixed-time interface: whenever the two replicas
already carry the same interface label, either branch of the transposition
returns that same label.  This is the boundary-fiber mechanism needed by the
conditional pairwise variance, where both half-states are conditioned on one
common boundary channel.

This module proves the pointwise fact, lifts it to arbitrary face lists and
the literal `centralFixedFaceIds`, and combines it with the existing accepted
whole-link auxiliary switch.  It constructs no posterior-variance fraction
and asserts no cutoff, volume, coupling, beta, or lattice-spacing uniformity.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget is used.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
import YMGap.Continuum.FiniteScopedFactorCoordinateReindex
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Equal inputs are fixed by either branch of a transposition -/

/-- If the two replicas agree at one face, the left output retains their
common label independently of the selected bit. -/
theorem twoReplicaFaceSwapLeft_eq_of_eq
    (selected : Nat → Bool) (left right : SlabLabelling) (faceId : Nat)
    (hagree : left faceId = right faceId) :
    twoReplicaFaceSwapLeft selected left right faceId = left faceId := by
  cases hselected : selected faceId <;>
    simp [twoReplicaFaceSwapLeft, hselected, hagree]

/-- If the two replicas agree at one face, the right output retains their
common label independently of the selected bit. -/
theorem twoReplicaFaceSwapRight_eq_of_eq
    (selected : Nat → Bool) (left right : SlabLabelling) (faceId : Nat)
    (hagree : left faceId = right faceId) :
    twoReplicaFaceSwapRight selected left right faceId = right faceId := by
  cases hselected : selected faceId <;>
    simp [twoReplicaFaceSwapRight, hselected, hagree]

/-! ## 2. Preservation of an arbitrary common coordinate fiber -/

/-- A facewise transposition preserves each replica's labels on every face
where the two inputs agree, and the two outputs still agree there. -/
theorem twoReplicaFaceSwap_preserves_agreement
    (faces : List Nat) (selected : Nat → Bool)
    (left right : SlabLabelling)
    (hagree : LabellingsAgreeUnder faces (fun id => id) left right) :
    LabellingsAgreeUnder faces (fun id => id) left
        (twoReplicaFaceSwapLeft selected left right) ∧
      LabellingsAgreeUnder faces (fun id => id) right
        (twoReplicaFaceSwapRight selected left right) ∧
      LabellingsAgreeUnder faces (fun id => id)
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) := by
  constructor
  · intro faceId hface
    exact twoReplicaFaceSwapLeft_eq_of_eq selected left right faceId
      (hagree faceId hface).symm
  constructor
  · intro faceId hface
    exact twoReplicaFaceSwapRight_eq_of_eq selected left right faceId
      (hagree faceId hface).symm
  · intro faceId hface
    have hleft := twoReplicaFaceSwapLeft_eq_of_eq
      selected left right faceId (hagree faceId hface).symm
    have hright := twoReplicaFaceSwapRight_eq_of_eq
      selected left right faceId (hagree faceId hface).symm
    exact hright.trans ((hagree faceId hface).trans hleft.symm)

/-! ## 3. The literal central fixed-time boundary -/

/-- Two reflected-slab labellings assembled with the same boundary channel
agree on every literal fixed-time face, independently of both half-states. -/
theorem assembledReplicas_agree_on_centralFixedFaces
    (half : Nat) (leftState rightState boundary : SlabLabelling)
    (leftUpper rightUpper : SlabLabelling) :
    LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
      (assembleReflectedSlabLabelling
        half leftState boundary leftUpper)
      (assembleReflectedSlabLabelling
        half rightState boundary rightUpper) := by
  intro faceId hface
  have hparts := mem_centralFixedFaceIds.mp hface
  rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2,
    assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]

/-- The canonical target-rooted support switch preserves a common central
fixed-time boundary even when its selected component crosses the interface. -/
theorem slabTwoReplicaCanonicalSupportSwap_preservesCentralBoundary
    (half targetFaceId : Nat) (left right : SlabLabelling)
    (hagree :
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        left right) :
    let selected := slabTwoReplicaSupportSwapMask
      (centralExtent half) left right targetFaceId
    LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id) left
        (twoReplicaFaceSwapLeft selected left right) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id) right
        (twoReplicaFaceSwapRight selected left right) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) := by
  dsimp only
  exact twoReplicaFaceSwap_preserves_agreement
    (centralFixedFaceIds half)
    (slabTwoReplicaSupportSwapMask
      (centralExtent half) left right targetFaceId)
    left right hagree

/-- In particular, two slab labellings assembled over the same boundary
channel remain in that channel after the canonical support switch. -/
theorem slabTwoReplicaCanonicalSupportSwap_assembled_preservesCentralBoundary
    (half targetFaceId : Nat)
    (leftState rightState boundary leftUpper rightUpper : SlabLabelling) :
    let left := assembleReflectedSlabLabelling
      half leftState boundary leftUpper
    let right := assembleReflectedSlabLabelling
      half rightState boundary rightUpper
    let selected := slabTwoReplicaSupportSwapMask
      (centralExtent half) left right targetFaceId
    LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id) left
        (twoReplicaFaceSwapLeft selected left right) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id) right
        (twoReplicaFaceSwapRight selected left right) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) := by
  dsimp only
  apply slabTwoReplicaCanonicalSupportSwap_preservesCentralBoundary
  exact assembledReplicas_agree_on_centralFixedFaces
    half leftState rightState boundary leftUpper rightUpper

/-! ## 4. Accepted observable switch inside one boundary fiber -/

/-- The named observable switch preserves a common fixed-time boundary at
the physical level. -/
theorem slabObservablePairSupportSwitch_preservesCentralBoundary
    (D : SlabPhysicalData) (half rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hagree :
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        pair.1.1.1 pair.2.1.1) :
    LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        pair.1.1.1
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId pair) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        pair.2.1.1
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId pair) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId pair)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId pair) := by
  unfold slabObservablePairSupportSwitchedLeftPhysical
    slabObservablePairSupportSwitchedRightPhysical
  exact twoReplicaFaceSwap_preserves_agreement
    (centralFixedFaceIds half)
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId)
    pair.1.1.1 pair.2.1.1 hagree

/-- The complete observable move has accepted auxiliary outputs and remains
inside the same central fixed-time physical boundary fiber. -/
theorem slabObservablePairSupportSwitch_accepted_in_centralBoundaryFiber
    (D : SlabPhysicalData) (half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hagree :
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
        pair.1.1.1 pair.2.1.1) :
    slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId pair ∈
        slabFineFusionWitnesses D
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId pair) ∧
      slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId pair ∈
        slabFineFusionWitnesses D
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId pair) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
          pair.1.1.1
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId pair) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
          pair.2.1.1
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId pair) ∧
      LabellingsAgreeUnder (centralFixedFaceIds half) (fun id => id)
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId pair)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId pair) := by
  have hboundary := slabObservablePairSupportSwitch_preservesCentralBoundary
    D half rootFaceId targetFaceId pair hagree
  have hleftAccepted :=
    slabObservablePairSupportSwitchedLeftAssignment_mem
      D rootFaceId targetFaceId htarget pair hpair
  have hrightAccepted :=
    slabObservablePairSupportSwitchedRightAssignment_mem
      D rootFaceId targetFaceId htarget pair hpair
  exact ⟨
    by simpa only [slabObservablePairSupportSwitchedLeftPhysical] using
      hleftAccepted,
    by simpa only [slabObservablePairSupportSwitchedRightPhysical] using
      hrightAccepted,
    hboundary.1, hboundary.2.1, hboundary.2.2⟩

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch.twoReplicaFaceSwap_preserves_agreement
#print axioms
  YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch.assembledReplicas_agree_on_centralFixedFaces
#print axioms
  YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch.slabTwoReplicaCanonicalSupportSwap_preservesCentralBoundary
#print axioms
  YMGap.Continuum.CompactDualSlabObservablePairedSupportFixedBoundarySwitch.slabObservablePairSupportSwitch_accepted_in_centralBoundaryFiber
