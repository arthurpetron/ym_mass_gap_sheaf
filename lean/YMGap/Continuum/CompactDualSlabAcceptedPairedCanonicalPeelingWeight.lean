/-
# Weight telescoping along canonical accepted paired peeling

Each deterministic accepted paired peel changes exactly one replica.  The
existing component-payment theorem bounds that replica's source weight by
`anchorFaceCoefficient ^ peelSize` times its lowered weight.  Nonnegativity
of the unchanged replica therefore gives the same inequality for the exact
two-replica product weight.

Iterating this one-step inequality along the canonical trace yields one power
whose exponent is the trace's total removed physical multiplicity.  This is
the pointwise heat payment.  The adaptive entropy carrier is deliberately not
multiplied in here: summing over admissible complete traces is the next finite
combinatorial theorem.

Constructive contract: exact rational order, finite powers, and well-founded
recursion on physical mass only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact anchor weight of an accepted pair -/

/-- Product of the two literal expanded-source weights on the closed accepted
paired carrier. -/
def slabAcceptedTwoReplicaStateWeight
    (cutoff half : Nat)
    (state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) : Q' :=
  slabExpandedFineEntryWeight
      (anchorSlabPhysicalData cutoff half) state.1 *
    slabExpandedFineEntryWeight
      (anchorSlabPhysicalData cutoff half) state.2

/-- Every accepted paired state has nonnegative weight at the production
anchor. -/
theorem slabAcceptedTwoReplicaStateWeight_nonnegative
    (cutoff half : Nat)
    (state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) :
    (0 : Q') ≤ slabAcceptedTwoReplicaStateWeight cutoff half state := by
  exact Q'.mul_nonneg _ _
    (slabExpandedFineEntryWeight_anchor_nonnegative
      cutoff half state.1)
    (slabExpandedFineEntryWeight_anchor_nonnegative
      cutoff half state.2)

/-! ## 2. One deterministic component payment -/

/-- One selected accepted paired peel pays the exact one-copy anchor power.
The other replica is unchanged and nonnegative. -/
theorem SlabAcceptedPairedPeelChoice.sourceWeight_le
    (cutoff half : Nat)
    {state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)}
    (choice : SlabAcceptedPairedPeelChoice
      (anchorSlabPhysicalData cutoff half) state) :
    slabAcceptedTwoReplicaStateWeight cutoff half state ≤
      anchorFaceCoefficient ^ choice.peelSize *
        slabAcceptedTwoReplicaStateWeight
          cutoff half choice.lowerState := by
  cases choice with
  | left faceId hface hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        (anchorSlabPhysicalData cutoff half)
        faceId hface state.1 hpositive
      have hsource :=
        SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le
          cutoff half seed
            (SlabExpandedFineSourceEntry.physical_bounded state.1)
      have hright := slabExpandedFineEntryWeight_anchor_nonnegative
        cutoff half state.2
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hsource hright
      refine Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _
        ((anchorFaceCoefficient ^
            (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length *
              slabExpandedFineEntryWeight
                (anchorSlabPhysicalData cutoff half)
                (acceptedExpandedSourceLowerAt
                  (anchorSlabPhysicalData cutoff half)
                  faceId hface state.1 hpositive)) *
            slabExpandedFineEntryWeight
              (anchorSlabPhysicalData cutoff half) state.2) _
        (Q'.eqv_refl _) (Q'.mul_assoc_eqv _ _ _)
  | right faceId hface hleftZero hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        (anchorSlabPhysicalData cutoff half)
        faceId hface state.2 hpositive
      have hsource :=
        SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le
          cutoff half seed
            (SlabExpandedFineSourceEntry.physical_bounded state.2)
      have hleft := slabExpandedFineEntryWeight_anchor_nonnegative
        cutoff half state.1
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hsource hleft
      refine Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _
        ((slabExpandedFineEntryWeight
            (anchorSlabPhysicalData cutoff half) state.1 *
              anchorFaceCoefficient ^
                (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length) *
            slabExpandedFineEntryWeight
              (anchorSlabPhysicalData cutoff half)
              (acceptedExpandedSourceLowerAt
                (anchorSlabPhysicalData cutoff half)
                faceId hface state.2 hpositive)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((anchorFaceCoefficient ^
            (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length *
              slabExpandedFineEntryWeight
                (anchorSlabPhysicalData cutoff half) state.1) *
            slabExpandedFineEntryWeight
              (anchorSlabPhysicalData cutoff half)
              (acceptedExpandedSourceLowerAt
                (anchorSlabPhysicalData cutoff half)
                faceId hface state.2 hpositive)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _

/-! ## 3. Telescope through the complete canonical trace -/

/-- The exact pointwise heat payment along the complete deterministic trace.
The exponent is the sum of all physical strand copies actually removed. -/
theorem slabAcceptedPairCanonicalPeeling_sourceWeight_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) :
    let result := slabAcceptedPairCanonicalPeeling
      (anchorSlabPhysicalData cutoff half) faces hphysical state
    slabAcceptedTwoReplicaStateWeight cutoff half state ≤
      anchorFaceCoefficient ^
          slabAcceptedPairedPeelTraceMass result.2 *
        slabAcceptedTwoReplicaStateWeight cutoff half result.1 := by
  change slabAcceptedTwoReplicaStateWeight cutoff half state ≤
    anchorFaceCoefficient ^
        slabAcceptedPairedPeelTraceMass
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical state).2 *
      slabAcceptedTwoReplicaStateWeight cutoff half
        (slabAcceptedPairCanonicalPeeling
          (anchorSlabPhysicalData cutoff half)
          faces hphysical state).1
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  · rename_i choice hchoice
    have hstep := SlabAcceptedPairedPeelChoice.sourceWeight_le
      cutoff half choice
    have htail := slabAcceptedPairCanonicalPeeling_sourceWeight_le
      cutoff half faces hphysical choice.lowerState
    have hfactor : (0 : Q') ≤ anchorFaceCoefficient ^ choice.peelSize :=
      Q'.pow_nonneg anchorFaceCoefficient (by decide) choice.peelSize
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ htail hfactor
    refine Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
    unfold slabAcceptedPairedPeelTraceMass
    simp only [listNatWeight,
      slabAcceptedPairedPeelChoiceRecord_peelSize]
    exact Q'.eqv_trans _
      ((anchorFaceCoefficient ^ choice.peelSize *
          anchorFaceCoefficient ^
            slabAcceptedPairedPeelTraceMass
              (slabAcceptedPairCanonicalPeeling
                (anchorSlabPhysicalData cutoff half)
                faces hphysical choice.lowerState).2) *
        slabAcceptedTwoReplicaStateWeight cutoff half
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical choice.lowerState).1) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (Q'.pow_add_eqv
          anchorFaceCoefficient choice.peelSize
            (slabAcceptedPairedPeelTraceMass
              (slabAcceptedPairCanonicalPeeling
                (anchorSlabPhysicalData cutoff half)
                faces hphysical choice.lowerState).2))))
termination_by
  slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight.slabAcceptedTwoReplicaStateWeight_nonnegative
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight.SlabAcceptedPairedPeelChoice.sourceWeight_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight.slabAcceptedPairCanonicalPeeling_sourceWeight_le
