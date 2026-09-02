/-
# Arbitrary-coupling weight telescope for accepted paired peeling

The accepted canonical paired peeling is independent of the coupling.  At an
arbitrary rational `0 < w < 1`, every selected component now has a proved
two-rate comparison: the high-spin exterior pays the strict anchor factor and
the finite-core remainder pays the explicit coarse factor two.  This module
lifts that one-replica comparison to the paired product and telescopes the
result through the complete deterministic accepted path.

The recursively accumulated payment is explicit and source-dependent.  This
module does not yet sum the inverse source fibers or prove that the resulting
aggregate rate is contractive.

Constructive contract: exact rational order and well-founded recursion on
physical mass only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPeelWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Exact arbitrary-coupling paired weight -/

/-- Product of the two literal expanded-source weights on the accepted paired
carrier at the coupling stored in `D`. -/
def slabAcceptedTwoReplicaStateWeight
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) : Q' :=
  slabExpandedFineEntryWeight D state.1 *
    slabExpandedFineEntryWeight D state.2

/-- Every accepted expanded source has nonnegative literal weight whenever
the stored coupling is nonnegative. -/
theorem slabExpandedFineEntryWeight_nonnegative
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) :
    (0 : Q') <= slabExpandedFineEntryWeight D entry := by
  cases D with
  | mk coupling coupling_nonnegative cutoff half =>
      exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        coupling_nonnegative cutoff half entry.1.1 entry.1.2

/-- Hence every accepted paired state has nonnegative product weight. -/
theorem slabAcceptedTwoReplicaStateWeight_nonnegative
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    (0 : Q') <= slabAcceptedTwoReplicaStateWeight D state := by
  exact Q'.mul_nonneg _ _
    (slabExpandedFineEntryWeight_nonnegative D state.1)
    (slabExpandedFineEntryWeight_nonnegative D state.2)

/-! ## 2. Explicit cost of one deterministic selected component -/

def slabAcceptedPairedPeelChoiceExteriorPeelSizeAt
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) : Nat :=
  match choice with
  | .left faceId hface hpositive =>
      acceptedExpandedSourceExteriorPeelSizeAt
        D threshold faceId hface state.1 hpositive
  | .right faceId hface _ hpositive =>
      acceptedExpandedSourceExteriorPeelSizeAt
        D threshold faceId hface state.2 hpositive

def slabAcceptedPairedPeelChoiceCoreResidualSizeAt
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) : Nat :=
  match choice with
  | .left faceId hface hpositive =>
      acceptedExpandedSourceCoreResidualSizeAt
        D threshold faceId hface state.1 hpositive
  | .right faceId hface _ hpositive =>
      acceptedExpandedSourceCoreResidualSizeAt
        D threshold faceId hface state.2 hpositive

/-- Literal two-rate multiplier paid by one selected accepted component. -/
def slabAcceptedPairedPeelChoiceHighSpinPaymentRate
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) : Q' :=
  anchorFaceCoefficient ^
      slabAcceptedPairedPeelChoiceExteriorPeelSizeAt threshold choice *
    (Q'.ofNat 2) ^
      slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice

theorem slabAcceptedPairedPeelChoiceHighSpinPaymentRate_nonnegative
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) :
    (0 : Q') <=
      slabAcceptedPairedPeelChoiceHighSpinPaymentRate threshold choice := by
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg anchorFaceCoefficient (by decide) _)
    (Q'.pow_nonneg (Q'.ofNat 2) (by decide) _)

/-- One selected paired peel pays its arbitrary-coupling two-rate multiplier;
the unchanged replica is carried through by nonnegativity. -/
theorem SlabAcceptedPairedPeelChoice.sourceWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedTwoReplicaStateWeight D state <=
      slabAcceptedPairedPeelChoiceHighSpinPaymentRate
          (anchorPaidExteriorThreshold D.coupling) choice *
        slabAcceptedTwoReplicaStateWeight D choice.lowerState := by
  cases choice with
  | left faceId hface hpositive =>
      have hsource := slabExpandedFineEntryWeight_lowerAt_le
        D hw0 hw1 faceId hface state.1 hpositive
      have hright := slabExpandedFineEntryWeight_nonnegative D state.2
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hsource hright
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
  | right faceId hface hleftZero hpositive =>
      have hsource := slabExpandedFineEntryWeight_lowerAt_le
        D hw0 hw1 faceId hface state.2 hpositive
      have hleft := slabExpandedFineEntryWeight_nonnegative D state.1
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hsource hleft
      refine Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _
        ((slabExpandedFineEntryWeight D state.1 *
            (anchorFaceCoefficient ^
                acceptedExpandedSourceExteriorPeelSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive *
              (Q'.ofNat 2) ^
                acceptedExpandedSourceCoreResidualSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive)) *
          slabExpandedFineEntryWeight D
            (acceptedExpandedSourceLowerAt
              D faceId hface state.2 hpositive)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        (((anchorFaceCoefficient ^
                acceptedExpandedSourceExteriorPeelSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive *
              (Q'.ofNat 2) ^
                acceptedExpandedSourceCoreResidualSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive) *
            slabExpandedFineEntryWeight D state.1) *
          slabExpandedFineEntryWeight D
            (acceptedExpandedSourceLowerAt
              D faceId hface state.2 hpositive)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _)

/-! ## 3. Complete accepted-path telescope -/

/-- The accepted terminal state paired with the product of every explicit
two-rate multiplier paid along the deterministic path. -/
abbrev SlabAcceptedPairedHighSpinWeightedPeelingOutput
    (D : SlabPhysicalData) := SlabAcceptedTwoReplicaState D × Q'

/-- Run the same deterministic accepted recursion while accumulating the
literal arbitrary-coupling step multipliers. -/
def slabAcceptedPairCanonicalHighSpinWeightedPeeling
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    (state : SlabAcceptedTwoReplicaState D) ->
      SlabAcceptedPairedHighSpinWeightedPeelingOutput D
  | state =>
      match slabAcceptedPairCanonicalChoice? D state faces hphysical with
      | none => (state, 1)
      | some choice =>
          let tail := slabAcceptedPairCanonicalHighSpinWeightedPeeling
            D threshold faces hphysical choice.lowerState
          (tail.1,
            slabAcceptedPairedPeelChoiceHighSpinPaymentRate threshold choice *
              tail.2)
termination_by state => slabAcceptedTwoReplicaStateMass state
decreasing_by
  exact choice.lowerState_mass_lt

/-- The terminal state of the weighted recursion vanishes in both replicas
on every scanned face. -/
theorem slabAcceptedPairCanonicalHighSpinWeightedPeeling_final_zero
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall faceId, faceId ∈ faces ->
      let result := slabAcceptedPairCanonicalHighSpinWeightedPeeling
        D threshold faces hphysical state
      result.1.1.1.1 faceId = 0 ∧
        result.1.2.1.1 faceId = 0 := by
  change forall faceId, faceId ∈ faces ->
    (slabAcceptedPairCanonicalHighSpinWeightedPeeling
      D threshold faces hphysical state).1.1.1.1 faceId = 0 ∧
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling
        D threshold faces hphysical state).1.2.1.1 faceId = 0
  rw [slabAcceptedPairCanonicalHighSpinWeightedPeeling]
  split
  · rename_i hchoice
    intro faceId hface
    exact (slabAcceptedPairCanonicalChoice?_eq_none_iff
      D state faces hphysical).mp hchoice faceId hface
  · rename_i choice hchoice
    exact slabAcceptedPairCanonicalHighSpinWeightedPeeling_final_zero
      D threshold faces hphysical choice.lowerState
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- Scanning the complete physical carrier makes both accepted terminal
physical fields extensionally equal to the literal vacuum labelling. -/
theorem slabAcceptedPairCanonicalHighSpinWeightedPeeling_physical_eq_zero
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinWeightedPeeling
      D threshold D.faceEdges
        (fun faceId hface => by
          simpa only [SlabPhysicalData.faceEdges] using hface)
        state
    result.1.1.1.1 = zeroEdgeLabelling ∧
      result.1.2.1.1 = zeroEdgeLabelling := by
  let hphysical : forall faceId, faceId ∈ D.faceEdges ->
      faceId ∈ slabPhysicalFaceEdges D.extent := fun faceId hface => by
    simpa only [SlabPhysicalData.faceEdges] using hface
  let result := slabAcceptedPairCanonicalHighSpinWeightedPeeling
    D threshold D.faceEdges hphysical state
  have hfinal := slabAcceptedPairCanonicalHighSpinWeightedPeeling_final_zero
    D threshold D.faceEdges hphysical state
  constructor
  · funext faceId
    by_cases hface : faceId ∈ D.faceEdges
    · simpa only [result, zeroEdgeLabelling] using (hfinal faceId hface).1
    · have hmem := acceptedExpandedSourcePhysical_mem result.1.1
      have hzero := (boundedEdgeLabellings_sound D.cutoff D.faceEdges
        result.1.1.1.1 hmem).2 faceId hface
      simpa only [zeroEdgeLabelling] using hzero
  · funext faceId
    by_cases hface : faceId ∈ D.faceEdges
    · simpa only [result, zeroEdgeLabelling] using (hfinal faceId hface).2
    · have hmem := acceptedExpandedSourcePhysical_mem result.1.2
      have hzero := (boundedEdgeLabellings_sound D.cutoff D.faceEdges
        result.1.2.1.1 hmem).2 faceId hface
      simpa only [zeroEdgeLabelling] using hzero

/-- The literal accepted paired weight telescopes through the complete path
to its actual accepted terminal state with the exact recursive payment. -/
theorem slabAcceptedPairCanonicalHighSpinWeightedPeeling_sourceWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinWeightedPeeling
      D (anchorPaidExteriorThreshold D.coupling) faces hphysical state
    slabAcceptedTwoReplicaStateWeight D state <=
      result.2 * slabAcceptedTwoReplicaStateWeight D result.1 := by
  change slabAcceptedTwoReplicaStateWeight D state <=
    (slabAcceptedPairCanonicalHighSpinWeightedPeeling
      D (anchorPaidExteriorThreshold D.coupling)
        faces hphysical state).2 *
      slabAcceptedTwoReplicaStateWeight D
        (slabAcceptedPairCanonicalHighSpinWeightedPeeling
          D (anchorPaidExteriorThreshold D.coupling)
            faces hphysical state).1
  rw [slabAcceptedPairCanonicalHighSpinWeightedPeeling]
  split
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  · rename_i choice hchoice
    have hstep := SlabAcceptedPairedPeelChoice.sourceWeight_le
      D hw0 hw1 choice
    have htail :=
      slabAcceptedPairCanonicalHighSpinWeightedPeeling_sourceWeight_le
      D hw0 hw1 faces hphysical choice.lowerState
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ htail
      (slabAcceptedPairedPeelChoiceHighSpinPaymentRate_nonnegative
        (anchorPaidExteriorThreshold D.coupling) choice)
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

#print axioms slabAcceptedTwoReplicaStateWeight
#print axioms slabExpandedFineEntryWeight_nonnegative
#print axioms slabAcceptedPairedPeelChoiceHighSpinPaymentRate
#print axioms SlabAcceptedPairedPeelChoice.sourceWeight_le
#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling
#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling_final_zero
#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling_physical_eq_zero
#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling_sourceWeight_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
