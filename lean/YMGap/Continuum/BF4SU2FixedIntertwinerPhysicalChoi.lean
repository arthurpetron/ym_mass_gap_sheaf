/-
# Genuine BF4 Choi refinement on the fixed-plane intertwiner carrier

The complete fine-intertwiner field contains lower, fixed-plane, and upper
link assignments.  It is therefore too large to serve directly as a common
source/target Gram channel: the lower and upper assignments belong to the
two half-amplitudes.  The cross-plane production factorization already
provides the correct split.

This module retains exactly the fixed-plane link-intertwiner assignment.
For each literal fixed face labelling it:

* enumerates the production witnesses on `centralFixedLinks`;
* assigns every witness the genuine fixed heat-kernel face factor;
* proves that their sum is exactly `centralBoundaryWeight`;
* pairs the witness with the fixed face labelling to form the common Choi
  channel; and
* proves that the resulting all-label weighted Gram is exactly the genuine
  corrected-slab reflected kernel.

The source/target amplitudes are not abstract arguments: they are precisely
`centralHalfAmplitude`.  The spatial insertion is not a placeholder: it is
the literal fixed-plane face factor before its SU(2) Haar multiplicity is
summed.

Honest scope: this is an exact finite-spacing identification and CP theorem.
It does not yet prove a spacing-uniform positive lower window for the fixed
face factor, a Mehler entry estimate, or the physical Perron identification.

## Axiom gate

Finite list algebra and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
import YMGap.Continuum.BF4RetainedSU2InterfaceGram

namespace YMGap.Continuum.BF4SU2FixedIntertwinerPhysicalChoi

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal fixed-plane SU(2) Haar fiber -/

/-- The production global-assignment list restricted to fixed-plane links. -/
def centralFixedFineIntertwinerCarrier
    (K half : Nat) (boundary : EdgeLabelling) :
    List SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentsOn
    K (centralExtent half)
    (assembleReflectedSlabLabelling
      half zeroEdgeLabelling boundary zeroEdgeLabelling)
    (centralFixedLinks half)

theorem centralFixedFineIntertwinerCarrier_length
    (K half : Nat) (boundary : EdgeLabelling) :
    (centralFixedFineIntertwinerCarrier K half boundary).length =
      slabLinkMultiplicityProductOn
        K (centralExtent half)
        (assembleReflectedSlabLabelling
          half zeroEdgeLabelling boundary zeroEdgeLabelling)
        (centralFixedLinks half) := by
  unfold centralFixedFineIntertwinerCarrier
    slabLinkMultiplicityProductOn
  exact slabFusionWitnessAssignmentsOn_length
    K (centralExtent half)
    (assembleReflectedSlabLabelling
      half zeroEdgeLabelling boundary zeroEdgeLabelling)
    (centralFixedLinks half)

def centralFixedFineIntertwinerRawWeight
    (_K _half : Nat) (_boundary : EdgeLabelling)
    (_witness : SlabFusionWitnessAssignment) : Q' :=
  1

private theorem listQSum_one_eqv_ofNat_length {A : Type} :
    ∀ items : List A,
      listQSum (fun _ => (1 : Q')) items ≈
        Q'.ofNat items.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _ :: tail => by
      simp only [listQSum, List.length_cons]
      refine Q'.eqv_trans _ (1 + Q'.ofNat tail.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _
          (listQSum_one_eqv_ofNat_length tail)
      · rw [Nat.add_comm tail.length 1]
        exact Q'.eqv_symm (Q'.ofNat_add_eqv 1 tail.length)

/-- The fixed-plane counting partition is exactly its production link
multiplicity. -/
theorem centralFixedFineIntertwinerPartition_eqv_linkMultiplicity
    (K half : Nat) (boundary : EdgeLabelling) :
    listQSum
        (centralFixedFineIntertwinerRawWeight K half boundary)
        (centralFixedFineIntertwinerCarrier K half boundary) ≈
      Q'.ofNat
        (slabLinkMultiplicityProductOn
          K (centralExtent half)
          (assembleReflectedSlabLabelling
            half zeroEdgeLabelling boundary zeroEdgeLabelling)
          (centralFixedLinks half)) := by
  unfold centralFixedFineIntertwinerRawWeight
  exact Q'.eqv_trans _ _ _
    (listQSum_one_eqv_ofNat_length
      (centralFixedFineIntertwinerCarrier K half boundary))
    (Q'.eqv_of_eq
      (congrArg Q'.ofNat
        (centralFixedFineIntertwinerCarrier_length
          K half boundary)))

/-! ## 2. Genuine interior spatial insertion -/

/-- The literal fixed-plane face factor carried by one accepted fixed-link
intertwiner assignment. -/
def centralFixedFineIntertwinerSpatialWeight
    (w : Q') (K half : Nat) (boundary : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) : Q' :=
  slabFaceFactorOn w K
      (assembleReflectedSlabLabelling
        half zeroEdgeLabelling boundary zeroEdgeLabelling)
      (centralFixedFaceIds half) *
    centralFixedFineIntertwinerRawWeight
      K half boundary witness

/-- Summing the genuine per-witness interior insertion reconstructs exactly
the fixed-interface weight in the production BF4 Gram. -/
theorem centralFixedFineIntertwinerSpatialWeight_total
    (w : Q') (K half : Nat) (boundary : EdgeLabelling) :
    listQSum
        (centralFixedFineIntertwinerSpatialWeight
          w K half boundary)
        (centralFixedFineIntertwinerCarrier K half boundary) ≈
      centralBoundaryWeight w K half boundary := by
  let fixedState :=
    assembleReflectedSlabLabelling
      half zeroEdgeLabelling boundary zeroEdgeLabelling
  let face :=
    slabFaceFactorOn w K fixedState
      (centralFixedFaceIds half)
  refine Q'.eqv_trans _
    (face *
      listQSum
        (centralFixedFineIntertwinerRawWeight K half boundary)
        (centralFixedFineIntertwinerCarrier K half boundary)) _ ?_ ?_
  · exact listQSum_mul_left
      face
      (centralFixedFineIntertwinerRawWeight K half boundary)
      (centralFixedFineIntertwinerCarrier K half boundary)
  · refine Q'.eqv_trans _
      (face *
        Q'.ofNat
          (slabLinkMultiplicityProductOn
            K (centralExtent half) fixedState
            (centralFixedLinks half))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left face _ _
        (centralFixedFineIntertwinerPartition_eqv_linkMultiplicity
          K half boundary)
    · unfold centralBoundaryWeight centralFixedWeight
      exact Q'.eqv_refl _

private theorem slabFaceFactorOn_nonnegative_all
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      (0 : Q') ≤ slabFaceFactorOn w K physical ids
  | [] => Q'.zero_le_one
  | id :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      apply Q'.mul_nonneg
      · by_cases hspin : physical id < K + 1
        · rw [coeffAt_heatKernelPacket hspin]
          exact coeffW_nonneg hw _
        · have hlarge : K < physical id := by omega
          rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
          exact Q'.le_refl' 0
      · exact slabFaceFactorOn_nonnegative_all
          hw K physical tail

theorem centralFixedFineIntertwinerSpatialWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) :
    (0 : Q') ≤
      centralFixedFineIntertwinerSpatialWeight
        w K half boundary witness := by
  unfold centralFixedFineIntertwinerSpatialWeight
    centralFixedFineIntertwinerRawWeight
  exact Q'.mul_nonneg _ _
    (slabFaceFactorOn_nonnegative_all
      hw K
      (assembleReflectedSlabLabelling
        half zeroEdgeLabelling boundary zeroEdgeLabelling)
      (centralFixedFaceIds half))
    Q'.zero_le_one

/-! ## 3. The common all-label Choi channel -/

abbrev CentralFixedFineIntertwinerChannel :=
  EdgeLabelling × SlabFusionWitnessAssignment

/-- Fixed face labels paired with every literal accepted fixed-link
intertwiner assignment. -/
def centralFixedFineIntertwinerChannels
    (K half : Nat) :
    List CentralFixedFineIntertwinerChannel :=
  (centralBoundaryChannels K half).flatMap
    (fun boundary =>
      (centralFixedFineIntertwinerCarrier K half boundary).map
        (fun witness => (boundary, witness)))

def centralFixedFineIntertwinerChannelWeight
    (w : Q') (K half : Nat)
    (channel : CentralFixedFineIntertwinerChannel) : Q' :=
  centralFixedFineIntertwinerSpatialWeight
    w K half channel.1 channel.2

/-- The genuine BF4 source/target half-amplitude, pulled back along the
all-label fixed-intertwiner channel. -/
def centralFixedFineIntertwinerHalfAmplitude
    (w : Q') (K half : Nat)
    (state : EdgeLabelling)
    (channel : CentralFixedFineIntertwinerChannel) : Q' :=
  centralHalfAmplitude w K half state channel.1

/-- The all-label Choi entry before the fixed intertwiner is integrated out. -/
def centralFixedFineIntertwinerChoiEntry
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  weightedGram
    (centralFixedFineIntertwinerChannels K half)
    (centralFixedFineIntertwinerChannelWeight w K half)
    (centralFixedFineIntertwinerHalfAmplitude w K half)
    left right

/-- Integrating the literal fixed-link intertwiner assignment recovers the
existing physical weighted Gram exactly. -/
theorem centralFixedFineIntertwinerChoiEntry_eq_weightedGram
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) :
    centralFixedFineIntertwinerChoiEntry
        w K half left right ≈
      weightedGram
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        left right := by
  unfold centralFixedFineIntertwinerChoiEntry
    centralFixedFineIntertwinerChannels
    centralFixedFineIntertwinerChannelWeight
    centralFixedFineIntertwinerHalfAmplitude
    weightedGram
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        listQSum
          (fun witness =>
            centralFixedFineIntertwinerSpatialWeight
                w K half boundary witness *
              (centralHalfAmplitude w K half left boundary *
                centralHalfAmplitude w K half right boundary))
          (centralFixedFineIntertwinerCarrier K half boundary))
      (centralBoundaryChannels K half)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
    apply listQSum_congr
    intro boundary
    rw [listQSum_map]
    exact Q'.eqv_refl _
  · apply listQSum_congr
    intro boundary
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (centralFixedFineIntertwinerSpatialWeight
          w K half boundary)
        (centralHalfAmplitude w K half left boundary *
          centralHalfAmplitude w K half right boundary)
        (centralFixedFineIntertwinerCarrier K half boundary))
      (Q'.mul_eqv_congr_right _ _ _
        (centralFixedFineIntertwinerSpatialWeight_total
          w K half boundary))

/-- **Exact physical identification.**  On the bounded endpoint carrier, the
genuine corrected-slab reflected kernel is the all-label fixed-intertwiner
Choi contraction. -/
theorem centralPhysicalReflectedKernel_eq_fixedIntertwinerChoi
    (w : Q') {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralPhysicalReflectedKernel w K half left right ≈
      centralFixedFineIntertwinerChoiEntry
        w K half left right := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      w hleft hright)
    (Q'.eqv_symm
      (centralFixedFineIntertwinerChoiEntry_eq_weightedGram
        w K half left right))

/-! ## 4. Finite complete positivity on the physical endpoint carrier -/

def centralFixedFineIntertwinerChoiQuadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling → Q') : Q' :=
  weightedGramQuadratic
    (centralHalfStates K half)
    (centralFixedFineIntertwinerChannels K half)
    (centralFixedFineIntertwinerChannelWeight w K half)
    (centralFixedFineIntertwinerHalfAmplitude w K half)
    coefficient

theorem centralFixedFineIntertwinerChoiQuadratic_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralFixedFineIntertwinerChoiQuadratic
        w K half coefficient := by
  unfold centralFixedFineIntertwinerChoiQuadratic
  exact weightedGramQuadratic_nonnegative
    (centralHalfStates K half)
    (centralFixedFineIntertwinerChannels K half)
    (centralFixedFineIntertwinerChannelWeight w K half)
    (centralFixedFineIntertwinerHalfAmplitude w K half)
    coefficient
    (fun channel _ =>
      centralFixedFineIntertwinerSpatialWeight_nonnegative
        hw K half channel.1 channel.2)

#print axioms centralFixedFineIntertwinerCarrier_length
#print axioms centralFixedFineIntertwinerPartition_eqv_linkMultiplicity
#print axioms centralFixedFineIntertwinerSpatialWeight_total
#print axioms centralFixedFineIntertwinerSpatialWeight_nonnegative
#print axioms centralFixedFineIntertwinerChoiEntry_eq_weightedGram
#print axioms centralPhysicalReflectedKernel_eq_fixedIntertwinerChoi
#print axioms centralFixedFineIntertwinerChoiQuadratic_nonnegative

end YMGap.Continuum.BF4SU2FixedIntertwinerPhysicalChoi
