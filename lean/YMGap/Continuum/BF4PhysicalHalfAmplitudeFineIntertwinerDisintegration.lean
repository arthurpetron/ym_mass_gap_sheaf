/-
# Exact lower-half fine-intertwiner disintegration of the BF4 amplitude

The physical BF4 half-amplitude is a lower-face heat factor multiplied by
the product of the SU(2) invariant-space multiplicities at all lower-half
links.  The production witness enumeration already realizes each local
multiplicity as a literal finite Haar fiber.

This file restricts that enumeration to `centralLowerLinks` and proves that
summing one copy of the lower-face factor over the resulting global
fine-intertwiner carrier is exactly `centralHalfAmplitude`.

This is the exact physical-identification half of the retained
Feynman--Kac bridge.  A common-carrier kinetic Harnack estimate still has to
compare the conditionally grouped entries; no positivity window is assumed
here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal lower-half fine-intertwiner carrier -/

/-- All accepted production intertwiner assignments on the lower-half link
list for one physical source/interface pair. -/
def centralLowerFineIntertwinerCarrier
    (K half : Nat)
    (source boundary : EdgeLabelling) :
    List SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentsOn
    K (centralExtent half)
    (assembleReflectedSlabLabelling
      half source boundary zeroEdgeLabelling)
    (centralLowerLinks half)

/-- Its cardinality is exactly the lower-link multiplicity in the physical
half-amplitude. -/
theorem centralLowerFineIntertwinerCarrier_length
    (K half : Nat)
    (source boundary : EdgeLabelling) :
    (centralLowerFineIntertwinerCarrier
        K half source boundary).length =
      slabLinkMultiplicityProductOn
        K (centralExtent half)
        (assembleReflectedSlabLabelling
          half source boundary zeroEdgeLabelling)
        (centralLowerLinks half) := by
  unfold centralLowerFineIntertwinerCarrier
    slabLinkMultiplicityProductOn
  exact slabFusionWitnessAssignmentsOn_length
    K (centralExtent half)
    (assembleReflectedSlabLabelling
      half source boundary zeroEdgeLabelling)
    (centralLowerLinks half)

/-- One Haar counting unit for every accepted lower-link assignment. -/
def centralLowerFineIntertwinerRawWeight
    (_K _half : Nat)
    (_source _boundary : EdgeLabelling)
    (_witness : SlabFusionWitnessAssignment) : Q' :=
  1

private theorem listQSum_one_eqv_ofNat_length
    {A : Type} :
    ∀ items : List A,
      listQSum (fun _ => (1 : Q')) items ≈
        Q'.ofNat items.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _ :: tail => by
      simp only [listQSum, List.length_cons]
      refine Q'.eqv_trans _
        (1 + Q'.ofNat tail.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _
          (listQSum_one_eqv_ofNat_length tail)
      · rw [Nat.add_comm tail.length 1]
        exact Q'.eqv_symm
          (Q'.ofNat_add_eqv 1 tail.length)

/-- The lower-half counting partition is the exact production
multiplicity. -/
theorem centralLowerFineIntertwinerPartition_eqv_linkMultiplicity
    (K half : Nat)
    (source boundary : EdgeLabelling) :
    listQSum
        (centralLowerFineIntertwinerRawWeight
          K half source boundary)
        (centralLowerFineIntertwinerCarrier
          K half source boundary) ≈
      Q'.ofNat
        (slabLinkMultiplicityProductOn
          K (centralExtent half)
          (assembleReflectedSlabLabelling
            half source boundary zeroEdgeLabelling)
          (centralLowerLinks half)) := by
  unfold centralLowerFineIntertwinerRawWeight
  exact Q'.eqv_trans _ _ _
    (listQSum_one_eqv_ofNat_length
      (centralLowerFineIntertwinerCarrier
        K half source boundary))
    (Q'.eqv_of_eq
      (congrArg Q'.ofNat
        (centralLowerFineIntertwinerCarrier_length
          K half source boundary)))

/-! ## 2. Exact conditional integration -/

/-- The literal lower-face heat factor carried by one accepted lower-link
intertwiner assignment. -/
def centralLowerFineIntertwinerContribution
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) : Q' :=
  slabFaceFactorOn w K
      (assembleReflectedSlabLabelling
        half source boundary zeroEdgeLabelling)
      (centralLowerFaceIds half) *
    centralLowerFineIntertwinerRawWeight
      K half source boundary witness

/-- Summing the genuine lower-half fine-intertwiner fiber reconstructs
`centralHalfAmplitude` exactly. -/
theorem centralLowerFineIntertwinerContribution_total
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) :
    listQSum
        (centralLowerFineIntertwinerContribution
          w K half source boundary)
        (centralLowerFineIntertwinerCarrier
          K half source boundary) ≈
      centralHalfAmplitude
        w K half source boundary := by
  let assembled :=
    assembleReflectedSlabLabelling
      half source boundary zeroEdgeLabelling
  let face :=
    slabFaceFactorOn w K assembled
      (centralLowerFaceIds half)
  refine Q'.eqv_trans _
    (face *
      listQSum
        (centralLowerFineIntertwinerRawWeight
          K half source boundary)
        (centralLowerFineIntertwinerCarrier
          K half source boundary)) _ ?_ ?_
  · exact listQSum_mul_left
      face
      (centralLowerFineIntertwinerRawWeight
        K half source boundary)
      (centralLowerFineIntertwinerCarrier
        K half source boundary)
  · refine Q'.eqv_trans _
      (face *
        Q'.ofNat
          (slabLinkMultiplicityProductOn
            K (centralExtent half) assembled
            (centralLowerLinks half))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left face _ _
        (centralLowerFineIntertwinerPartition_eqv_linkMultiplicity
          K half source boundary)
    · unfold centralHalfAmplitude centralLowerFactor
      exact Q'.eqv_refl _

private theorem slabFaceFactorOn_nonnegative_all
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      (0 : Q') ≤
        slabFaceFactorOn w K physical ids
  | [] => Q'.zero_le_one
  | id :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      apply Q'.mul_nonneg
      · by_cases hspin : physical id < K + 1
        · rw [coeffAt_heatKernelPacket hspin]
          exact coeffW_nonneg hw _
        · have hlarge : K < physical id := by
            omega
          rw [coeffAt_of_gt
            (heatKernelPacket K w) hlarge]
          exact Q'.le_refl' 0
      · exact slabFaceFactorOn_nonnegative_all
          hw K physical tail

/-- Every literal conditional contribution is nonnegative for a
nonnegative heat nome. -/
theorem centralLowerFineIntertwinerContribution_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (source boundary : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) :
    (0 : Q') ≤
      centralLowerFineIntertwinerContribution
        w K half source boundary witness := by
  unfold centralLowerFineIntertwinerContribution
    centralLowerFineIntertwinerRawWeight
  exact Q'.mul_nonneg _ _
    (slabFaceFactorOn_nonnegative_all
      hw K
      (assembleReflectedSlabLabelling
        half source boundary zeroEdgeLabelling)
      (centralLowerFaceIds half))
    Q'.zero_le_one

end YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration.centralLowerFineIntertwinerCarrier_length
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration.centralLowerFineIntertwinerPartition_eqv_linkMultiplicity
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration.centralLowerFineIntertwinerContribution_total
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeFineIntertwinerDisintegration.centralLowerFineIntertwinerContribution_nonnegative
