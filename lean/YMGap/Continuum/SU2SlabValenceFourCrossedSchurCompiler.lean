/-
# The degree-four crossed slab switch enters physical Schur transport

The geometric local-switch development already splits two accepted link
networks along mate-closed strand selections, swaps the selected parts, and
constructs accepted auxiliary witnesses for both crossed replicas at the
original cutoff.  Separately, the analytic development now converts an
accepted degree-four witness into a `FixedLeftCGChannel` and recouples two
channels whose external labels may differ.

This module joins those results.  A single proof-carrying record contains the
actual production inputs and selection certificates.  Its crossed auxiliary
fields give two explicit physical left channels, and their heterogeneous
Schur row is nonnegative and exactly normalized.

The construction is conditional on the supplied strand selection.  It does
not yet identify the selection law with the Cartan branching kernel, compare
Gibbs weights, prove an OS form bound, or take a continuum limit.

Constructive contract: Mathlib-free, exact finite data, no choice, no
`Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
import YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
import YMGap.Continuum.SU2PhysicalSchurHeterogeneousTwoReplicaTransport

namespace YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.CompactDualSlabSelectionComplement
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2PhysicalSchurHeterogeneousTwoReplicaTransport
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One proof-carrying production switch at a four-valent link -/

/-- All finite production data required to switch one four-valent link in two
replicas.  The selections are already certified mate-closed and face-constant
with the same face mask. -/
structure ValenceFourCrossReplicaSwitchData (K extent : Nat) where
  leftPhysical : SlabLabelling
  rightPhysical : SlabLabelling
  link : SlabLink
  leftAuxiliary : SlabLabelling
  rightAuxiliary : SlabLabelling
  leftAuxiliary_mem : leftAuxiliary ∈
    slabLinkFusionWitnesses K extent leftPhysical link
  rightAuxiliary_mem : rightAuxiliary ∈
    slabLinkFusionWitnesses K extent rightPhysical link
  mask : Nat → Bool
  leftBounded : SlabFaceLabellingBounded K extent leftPhysical
  rightBounded : SlabFaceLabellingBounded K extent rightPhysical
  leftSelection : SlabLinkPartnerClosedFaceSelection
    K extent leftPhysical link leftAuxiliary leftAuxiliary_mem
  rightSelection : SlabLinkPartnerClosedFaceSelection
    K extent rightPhysical link rightAuxiliary rightAuxiliary_mem
  leftConstant : ∀ copy, leftSelection.selected copy = mask copy.faceId
  rightConstant : ∀ copy, rightSelection.selected copy = mask copy.faceId
  degree_eq_four : (slabIncidentPlaqIds extent link).length = 4

/-- Physical field of the first crossed replica. -/
def crossedLeftPhysical {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) : SlabLabelling :=
  twoReplicaFaceSwapLeft D.mask D.leftPhysical D.rightPhysical

/-- Physical field of the second crossed replica. -/
def crossedRightPhysical {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) : SlabLabelling :=
  twoReplicaFaceSwapRight D.mask D.leftPhysical D.rightPhysical

/-- Production auxiliary field of the first crossed replica. -/
def crossedLeftAuxiliary {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) : SlabLabelling :=
  slabCrossReplicaLeftAuxiliary D.leftSelection D.rightSelection

/-- Production auxiliary field of the second crossed replica. -/
def crossedRightAuxiliary {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) : SlabLabelling :=
  slabCrossReplicaRightAuxiliary D.leftSelection D.rightSelection

theorem crossedLeftAuxiliary_mem {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    crossedLeftAuxiliary D ∈
      slabLinkFusionWitnesses K extent (crossedLeftPhysical D) D.link := by
  exact slabCrossReplicaLeftAuxiliary_mem
    D.mask D.leftBounded D.rightBounded D.leftSelection D.rightSelection
    D.leftConstant D.rightConstant

theorem crossedRightAuxiliary_mem {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    crossedRightAuxiliary D ∈
      slabLinkFusionWitnesses K extent (crossedRightPhysical D) D.link := by
  exact slabCrossReplicaRightAuxiliary_mem
    D.mask D.leftBounded D.rightBounded D.leftSelection D.rightSelection
    D.leftConstant D.rightConstant

/-! ## 2. Both production outputs become analytic left channels -/

def crossedLeftChannel {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    FixedLeftCGChannel
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 3) :=
  fixedLeftChannelOfSlabValenceFour K extent
    (crossedLeftPhysical D) D.link (crossedLeftAuxiliary D)
    D.degree_eq_four (crossedLeftAuxiliary_mem D)

def crossedRightChannel {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    FixedLeftCGChannel
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 3) :=
  fixedLeftChannelOfSlabValenceFour K extent
    (crossedRightPhysical D) D.link (crossedRightAuxiliary D)
    D.degree_eq_four (crossedRightAuxiliary_mem D)

theorem crossedLeftChannel_intermediate {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedLeftChannel D).intermediate = crossedLeftAuxiliary D 5 := by
  exact fixedLeftChannelOfSlabValenceFour_intermediate K extent
    (crossedLeftPhysical D) D.link (crossedLeftAuxiliary D)
    D.degree_eq_four (crossedLeftAuxiliary_mem D)

theorem crossedRightChannel_intermediate {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedRightChannel D).intermediate = crossedRightAuxiliary D 5 := by
  exact fixedLeftChannelOfSlabValenceFour_intermediate K extent
    (crossedRightPhysical D) D.link (crossedRightAuxiliary D)
    D.degree_eq_four (crossedRightAuxiliary_mem D)

/-- The first analytic intermediate label is the literal production sum of
the unselected left and selected right internal strand counts. -/
theorem crossedLeftChannel_intermediate_eq_cross_sum {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedLeftChannel D).intermediate =
      slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary D.leftSelection 5 +
        slabLinkPartnerClosedFaceSelectionSelectedAuxiliary
          D.rightSelection 5 := by
  rw [crossedLeftChannel_intermediate]
  unfold crossedLeftAuxiliary slabCrossReplicaLeftAuxiliary addEdgeLabelling
  rfl

/-- The second analytic intermediate label is the complementary production
sum. -/
theorem crossedRightChannel_intermediate_eq_cross_sum {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedRightChannel D).intermediate =
      slabLinkPartnerClosedFaceSelectionSelectedAuxiliary D.leftSelection 5 +
        slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary
          D.rightSelection 5 := by
  rw [crossedRightChannel_intermediate]
  unfold crossedRightAuxiliary slabCrossReplicaRightAuxiliary addEdgeLabelling
  rfl

/-! ## 3. The actual crossed link has a normalized Schur output row -/

/-- Right-associated target type for the first crossed replica. -/
abbrev CrossedLeftRightChannel {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  FixedRightCGChannel
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 3)

/-- Right-associated target type for the second crossed replica. -/
abbrev CrossedRightRightChannel {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  FixedRightCGChannel
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 3)

abbrev CrossedSchurTarget {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  CrossedLeftRightChannel D × CrossedRightRightChannel D

/-- Literal independently typed pair of right-associated analytic channels
available after the production switch. -/
def crossedSchurTargets {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    List (CrossedSchurTarget D) :=
  heterogeneousSchurTargets (crossedLeftChannel D) (crossedRightChannel D)

/-- Product Schur probability on the actual crossed production channels. -/
def crossedSchurKernelAt {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (target : CrossedSchurTarget D) : Q' :=
  heterogeneousSchurKernelAt
    (crossedLeftChannel D) (crossedRightChannel D) target

theorem crossedSchurTargets_nodup {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedSchurTargets D).Nodup := by
  exact heterogeneousSchurTargets_nodup
    (crossedLeftChannel D) (crossedRightChannel D)

theorem crossedSchurKernelAt_nonnegative {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (target : CrossedSchurTarget D) :
    (0 : Q') ≤ crossedSchurKernelAt D target := by
  exact heterogeneousSchurKernelAt_nonnegative
    (crossedLeftChannel D) (crossedRightChannel D) target

/-- **The actual crossed degree-four production link feeds an exact
normalized physical Schur row.** -/
theorem crossedSchurKernel_row_normalized {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    listQSum (crossedSchurKernelAt D) (crossedSchurTargets D) ≈ 1 := by
  exact heterogeneousSchurKernel_row_normalized
    (crossedLeftChannel D) (crossedRightChannel D)

def crossedSchurExpectation {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (observable : CrossedSchurTarget D → Q') : Q' :=
  heterogeneousSchurExpectation
    (crossedLeftChannel D) (crossedRightChannel D) observable

theorem crossedSchurExpectation_one {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    crossedSchurExpectation D (fun _ => 1) ≈ 1 := by
  exact heterogeneousSchurExpectation_one
    (crossedLeftChannel D) (crossedRightChannel D)

theorem crossedSchurExpectation_product {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (leftObservable : CrossedLeftRightChannel D → Q')
    (rightObservable : CrossedRightRightChannel D → Q') :
    crossedSchurExpectation D
        (fun target => leftObservable target.1 * rightObservable target.2) ≈
      physicalSchurExpectation (crossedLeftChannel D) leftObservable *
        physicalSchurExpectation (crossedRightChannel D) rightObservable := by
  exact heterogeneousSchurExpectation_product
    (crossedLeftChannel D) (crossedRightChannel D)
    leftObservable rightObservable

#print axioms crossedLeftAuxiliary_mem
#print axioms crossedRightAuxiliary_mem
#print axioms crossedLeftChannel
#print axioms crossedRightChannel
#print axioms crossedLeftChannel_intermediate
#print axioms crossedRightChannel_intermediate
#print axioms crossedLeftChannel_intermediate_eq_cross_sum
#print axioms crossedRightChannel_intermediate_eq_cross_sum
#print axioms crossedSchurTargets_nodup
#print axioms crossedSchurKernelAt_nonnegative
#print axioms crossedSchurKernel_row_normalized
#print axioms crossedSchurExpectation_one
#print axioms crossedSchurExpectation_product

end YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
