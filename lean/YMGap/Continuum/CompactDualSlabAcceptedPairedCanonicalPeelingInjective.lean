/-
# Injectivity of complete canonical paired-peeling output

A trace is multiplicity faithful only if its terminal pair and recorded words
determine the original pair.  The one-step adaptive decoder already proves
this for one selected component at a common root and common lowered target.

This module first lifts that decoder through the left/right paired carrier.
Equality of the side, root, adaptive code, and lowered pair reconstructs the
source pair.  It then runs that argument backward through the complete
canonical trace.  Consequently

  initial state |-> (terminal state, complete trace)

is injective for every fixed ordered physical-face list.

Constructive contract: explicit adaptive reconstruction and well-founded
induction on the sum of two pair masses only; no choice, `Classical`, `sorry`,
or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. One-step paired reconstruction -/

private theorem acceptedPairLeftPeel_source_eq
    (D : SlabPhysicalData)
    {leftState rightState : SlabAcceptedTwoReplicaState D}
    {leftFaceId rightFaceId : Nat}
    (leftFaceMem : leftFaceId ∈ slabPhysicalFaceEdges D.extent)
    (rightFaceMem : rightFaceId ∈ slabPhysicalFaceEdges D.extent)
    (leftPositive : 0 < leftState.1.1.1 leftFaceId)
    (rightPositive : 0 < rightState.1.1.1 rightFaceId)
    (hroot : leftFaceId = rightFaceId)
    (hcode :
      componentAdaptiveEntropyCode
          (acceptedExpandedSourceRootSeed
            D leftFaceId leftFaceMem leftState.1 leftPositive) =
        componentAdaptiveEntropyCode
          (acceptedExpandedSourceRootSeed
            D rightFaceId rightFaceMem rightState.1 rightPositive))
    (hlower :
      slabAcceptedTwoReplicaStateLowerLeftAt
          leftState leftFaceId leftFaceMem leftPositive =
        slabAcceptedTwoReplicaStateLowerLeftAt
          rightState rightFaceId rightFaceMem rightPositive) :
    leftState = rightState := by
  let leftSeed := acceptedExpandedSourceRootSeed
    D leftFaceId leftFaceMem leftState.1 leftPositive
  let rightSeed := acceptedExpandedSourceRootSeed
    D rightFaceId rightFaceMem rightState.1 rightPositive
  have hseedRoot : leftSeed.root.faceId = rightSeed.root.faceId := by
    simpa [leftSeed, rightSeed, acceptedExpandedSourceRootSeed] using hroot
  have hlowerPhysical :
      SlabFusionWitnessFaceStrandSeed.lowerPhysical leftSeed =
        SlabFusionWitnessFaceStrandSeed.lowerPhysical rightSeed := by
    change
      (acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.1 leftPositive).1.1 =
        (acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.1 rightPositive).1.1
    exact congrArg
      (fun state : SlabAcceptedTwoReplicaState D => state.1.1.1) hlower
  have hlowerAssignment :
      SlabFusionWitnessFaceStrandSeed.lowerAssignment leftSeed =
        SlabFusionWitnessFaceStrandSeed.lowerAssignment rightSeed := by
    change
      (acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.1 leftPositive).1.2 =
        (acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.1 rightPositive).1.2
    exact congrArg
      (fun state : SlabAcceptedTwoReplicaState D => state.1.1.2) hlower
  have hsource := componentAdaptiveEntropyCode_eq_sourceData_eq
    leftSeed rightSeed hseedRoot hlowerPhysical hlowerAssignment hcode
  have hother : leftState.2 = rightState.2 := by
    change
      (acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.1 leftPositive,
        leftState.2) =
      (acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.1 rightPositive,
        rightState.2) at hlower
    have hparts :
        acceptedExpandedSourceLowerAt
              D leftFaceId leftFaceMem leftState.1 leftPositive =
            acceptedExpandedSourceLowerAt
              D rightFaceId rightFaceMem rightState.1 rightPositive ∧
          leftState.2 = rightState.2 := by
      simpa only [Prod.mk.injEq] using hlower
    exact hparts.2
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hsource.1 hsource.2
  · exact hother

private theorem acceptedPairRightPeel_source_eq
    (D : SlabPhysicalData)
    {leftState rightState : SlabAcceptedTwoReplicaState D}
    {leftFaceId rightFaceId : Nat}
    (leftFaceMem : leftFaceId ∈ slabPhysicalFaceEdges D.extent)
    (rightFaceMem : rightFaceId ∈ slabPhysicalFaceEdges D.extent)
    (leftPositive : 0 < leftState.2.1.1 leftFaceId)
    (rightPositive : 0 < rightState.2.1.1 rightFaceId)
    (hroot : leftFaceId = rightFaceId)
    (hcode :
      componentAdaptiveEntropyCode
          (acceptedExpandedSourceRootSeed
            D leftFaceId leftFaceMem leftState.2 leftPositive) =
        componentAdaptiveEntropyCode
          (acceptedExpandedSourceRootSeed
            D rightFaceId rightFaceMem rightState.2 rightPositive))
    (hlower :
      slabAcceptedTwoReplicaStateLowerRightAt
          leftState leftFaceId leftFaceMem leftPositive =
        slabAcceptedTwoReplicaStateLowerRightAt
          rightState rightFaceId rightFaceMem rightPositive) :
    leftState = rightState := by
  let leftSeed := acceptedExpandedSourceRootSeed
    D leftFaceId leftFaceMem leftState.2 leftPositive
  let rightSeed := acceptedExpandedSourceRootSeed
    D rightFaceId rightFaceMem rightState.2 rightPositive
  have hseedRoot : leftSeed.root.faceId = rightSeed.root.faceId := by
    simpa [leftSeed, rightSeed, acceptedExpandedSourceRootSeed] using hroot
  have hlowerPhysical :
      SlabFusionWitnessFaceStrandSeed.lowerPhysical leftSeed =
        SlabFusionWitnessFaceStrandSeed.lowerPhysical rightSeed := by
    change
      (acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.2 leftPositive).1.1 =
        (acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.2 rightPositive).1.1
    exact congrArg
      (fun state : SlabAcceptedTwoReplicaState D => state.2.1.1) hlower
  have hlowerAssignment :
      SlabFusionWitnessFaceStrandSeed.lowerAssignment leftSeed =
        SlabFusionWitnessFaceStrandSeed.lowerAssignment rightSeed := by
    change
      (acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.2 leftPositive).1.2 =
        (acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.2 rightPositive).1.2
    exact congrArg
      (fun state : SlabAcceptedTwoReplicaState D => state.2.1.2) hlower
  have hsource := componentAdaptiveEntropyCode_eq_sourceData_eq
    leftSeed rightSeed hseedRoot hlowerPhysical hlowerAssignment hcode
  have hother : leftState.1 = rightState.1 := by
    change
      (leftState.1,
        acceptedExpandedSourceLowerAt
          D leftFaceId leftFaceMem leftState.2 leftPositive) =
      (rightState.1,
        acceptedExpandedSourceLowerAt
          D rightFaceId rightFaceMem rightState.2 rightPositive) at hlower
    have hparts :
        leftState.1 = rightState.1 ∧
          acceptedExpandedSourceLowerAt
              D leftFaceId leftFaceMem leftState.2 leftPositive =
            acceptedExpandedSourceLowerAt
              D rightFaceId rightFaceMem rightState.2 rightPositive := by
      simpa only [Prod.mk.injEq] using hlower
    exact hparts.1
  apply Prod.ext
  · exact hother
  · apply Subtype.ext
    exact Prod.ext hsource.1 hsource.2

/-- Equal one-step records and equal lowered paired states reconstruct equal
source paired states. -/
theorem SlabAcceptedPairedPeelChoice.sourceState_eq_of_record_eq_of_lower_eq
    {D : SlabPhysicalData}
    {leftState rightState : SlabAcceptedTwoReplicaState D}
    (leftChoice : SlabAcceptedPairedPeelChoice D leftState)
    (rightChoice : SlabAcceptedPairedPeelChoice D rightState)
    (hrecord : slabAcceptedPairedPeelChoiceRecord leftChoice =
      slabAcceptedPairedPeelChoiceRecord rightChoice)
    (hlower : leftChoice.lowerState = rightChoice.lowerState) :
    leftState = rightState := by
  cases leftChoice with
  | left leftFaceId leftFaceMem leftPositive =>
      cases rightChoice with
      | left rightFaceId rightFaceMem rightPositive =>
          have hroot : leftFaceId = rightFaceId := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.rootFaceId hrecord
          have hcode :
              componentAdaptiveEntropyCode
                  (acceptedExpandedSourceRootSeed
                    D leftFaceId leftFaceMem leftState.1 leftPositive) =
                componentAdaptiveEntropyCode
                  (acceptedExpandedSourceRootSeed
                    D rightFaceId rightFaceMem rightState.1 rightPositive) := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.code hrecord
          exact acceptedPairLeftPeel_source_eq D
            leftFaceMem rightFaceMem leftPositive rightPositive
            hroot hcode hlower
      | right rightFaceId rightFaceMem rightLeftZero rightPositive =>
          have hside : true = false := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.left hrecord
          cases hside
  | right leftFaceId leftFaceMem leftLeftZero leftPositive =>
      cases rightChoice with
      | left rightFaceId rightFaceMem rightPositive =>
          have hside : false = true := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.left hrecord
          cases hside
      | right rightFaceId rightFaceMem rightLeftZero rightPositive =>
          have hroot : leftFaceId = rightFaceId := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.rootFaceId hrecord
          have hcode :
              componentAdaptiveEntropyCode
                  (acceptedExpandedSourceRootSeed
                    D leftFaceId leftFaceMem leftState.2 leftPositive) =
                componentAdaptiveEntropyCode
                  (acceptedExpandedSourceRootSeed
                    D rightFaceId rightFaceMem rightState.2 rightPositive) := by
            simpa only [slabAcceptedPairedPeelChoiceRecord] using
              congrArg SlabAcceptedPairedPeelRecord.code hrecord
          exact acceptedPairRightPeel_source_eq D
            leftFaceMem rightFaceMem leftPositive rightPositive
            hroot hcode hlower

/-! ## 2. Backward reconstruction through the complete trace -/

/-- For a fixed ordered physical-face list, terminal state plus complete trace
is an injective code for the initial accepted paired state. -/
theorem slabAcceptedPairCanonicalPeeling_injective
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    ∀ leftState rightState : SlabAcceptedTwoReplicaState D,
      slabAcceptedPairCanonicalPeeling D faces hphysical leftState =
          slabAcceptedPairCanonicalPeeling D faces hphysical rightState →
        leftState = rightState
  | leftState, rightState, hout => by
      cases hleft : slabAcceptedPairCanonicalChoice?
          D leftState faces hphysical with
      | none =>
          cases hright : slabAcceptedPairCanonicalChoice?
              D rightState faces hphysical with
          | none =>
              have hleftOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical leftState =
                    (leftState, ([] : List SlabAcceptedPairedPeelRecord)) := by
                rw [slabAcceptedPairCanonicalPeeling, hleft]
              have hrightOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical rightState =
                    (rightState, ([] : List SlabAcceptedPairedPeelRecord)) := by
                rw [slabAcceptedPairCanonicalPeeling, hright]
              have hout' :
                  (leftState, ([] : List SlabAcceptedPairedPeelRecord)) =
                    (rightState, []) := by
                rw [← hleftOut, ← hrightOut]
                exact hout
              exact congrArg Prod.fst hout'
          | some rightChoice =>
              have hleftOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical leftState =
                    (leftState, ([] : List SlabAcceptedPairedPeelRecord)) := by
                rw [slabAcceptedPairCanonicalPeeling, hleft]
              have hrightOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical rightState =
                    ((slabAcceptedPairCanonicalPeeling D faces hphysical
                        rightChoice.lowerState).1,
                      slabAcceptedPairedPeelChoiceRecord rightChoice ::
                        (slabAcceptedPairCanonicalPeeling D faces hphysical
                          rightChoice.lowerState).2) := by
                rw [slabAcceptedPairCanonicalPeeling, hright]
              have htrace := congrArg Prod.snd hout
              have himpossible : ([] : List SlabAcceptedPairedPeelRecord) =
                  slabAcceptedPairedPeelChoiceRecord rightChoice ::
                    (slabAcceptedPairCanonicalPeeling D faces hphysical
                      rightChoice.lowerState).2 := by
                rw [hleftOut, hrightOut] at htrace
                exact htrace
              cases himpossible
      | some leftChoice =>
          cases hright : slabAcceptedPairCanonicalChoice?
              D rightState faces hphysical with
          | none =>
              have hleftOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical leftState =
                    ((slabAcceptedPairCanonicalPeeling D faces hphysical
                        leftChoice.lowerState).1,
                      slabAcceptedPairedPeelChoiceRecord leftChoice ::
                        (slabAcceptedPairCanonicalPeeling D faces hphysical
                          leftChoice.lowerState).2) := by
                rw [slabAcceptedPairCanonicalPeeling, hleft]
              have hrightOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical rightState =
                    (rightState, ([] : List SlabAcceptedPairedPeelRecord)) := by
                rw [slabAcceptedPairCanonicalPeeling, hright]
              have htrace := congrArg Prod.snd hout
              have himpossible :
                  slabAcceptedPairedPeelChoiceRecord leftChoice ::
                      (slabAcceptedPairCanonicalPeeling D faces hphysical
                        leftChoice.lowerState).2 = [] := by
                rw [hleftOut, hrightOut] at htrace
                exact htrace
              cases himpossible
          | some rightChoice =>
              have hleftOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical leftState =
                    ((slabAcceptedPairCanonicalPeeling D faces hphysical
                        leftChoice.lowerState).1,
                      slabAcceptedPairedPeelChoiceRecord leftChoice ::
                        (slabAcceptedPairCanonicalPeeling D faces hphysical
                          leftChoice.lowerState).2) := by
                rw [slabAcceptedPairCanonicalPeeling, hleft]
              have hrightOut :
                  slabAcceptedPairCanonicalPeeling
                      D faces hphysical rightState =
                    ((slabAcceptedPairCanonicalPeeling D faces hphysical
                        rightChoice.lowerState).1,
                      slabAcceptedPairedPeelChoiceRecord rightChoice ::
                        (slabAcceptedPairCanonicalPeeling D faces hphysical
                          rightChoice.lowerState).2) := by
                rw [slabAcceptedPairCanonicalPeeling, hright]
              have hout' :
                  ((slabAcceptedPairCanonicalPeeling D faces hphysical
                      leftChoice.lowerState).1,
                    slabAcceptedPairedPeelChoiceRecord leftChoice ::
                      (slabAcceptedPairCanonicalPeeling D faces hphysical
                        leftChoice.lowerState).2) =
                  ((slabAcceptedPairCanonicalPeeling D faces hphysical
                      rightChoice.lowerState).1,
                    slabAcceptedPairedPeelChoiceRecord rightChoice ::
                      (slabAcceptedPairCanonicalPeeling D faces hphysical
                        rightChoice.lowerState).2) := by
                rw [hleftOut, hrightOut] at hout
                exact hout
              have hfinal := congrArg Prod.fst hout'
              have htrace := congrArg Prod.snd hout'
              have hrecord := (List.cons.inj htrace).1
              have htailTrace := (List.cons.inj htrace).2
              have htailOutput :
                  slabAcceptedPairCanonicalPeeling D faces hphysical
                      leftChoice.lowerState =
                    slabAcceptedPairCanonicalPeeling D faces hphysical
                      rightChoice.lowerState :=
                Prod.ext hfinal htailTrace
              have hlower := slabAcceptedPairCanonicalPeeling_injective
                D faces hphysical leftChoice.lowerState
                  rightChoice.lowerState htailOutput
              exact
                SlabAcceptedPairedPeelChoice.sourceState_eq_of_record_eq_of_lower_eq
                  leftChoice rightChoice hrecord hlower
termination_by leftState rightState =>
  slabAcceptedTwoReplicaStateMass leftState +
    slabAcceptedTwoReplicaStateMass rightState
decreasing_by
  have hleftMass := leftChoice.lowerState_mass_lt
  have hrightMass := rightChoice.lowerState_mass_lt
  omega

/-- Every duplicate-free finite fiber over one complete terminal/trace output
contains at most one initial accepted pair. -/
theorem slabAcceptedPairCanonicalPeeling_fixedOutput_length_le_one
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (output : SlabAcceptedPairedCanonicalPeelingOutput D)
    (sources : List (SlabAcceptedTwoReplicaState D))
    (hsources : sources.Nodup)
    (houtput : ∀ source, source ∈ sources →
      slabAcceptedPairCanonicalPeeling D faces hphysical source = output) :
    sources.length ≤ 1 := by
  cases sources with
  | nil =>
      change 0 ≤ 1
      exact Nat.zero_le 1
  | cons first rest =>
      cases rest with
      | nil => exact Nat.le_refl 1
      | cons second tail =>
          have hfirstOutput := houtput first List.mem_cons_self
          have hsecondOutput := houtput second
            (List.mem_cons_of_mem first List.mem_cons_self)
          have hsameOutput :
              slabAcceptedPairCanonicalPeeling D faces hphysical first =
                slabAcceptedPairCanonicalPeeling
                  D faces hphysical second :=
            hfirstOutput.trans hsecondOutput.symm
          have hsource := slabAcceptedPairCanonicalPeeling_injective
            D faces hphysical first second hsameOutput
          have hnotMem := (List.nodup_cons.mp hsources).1
          exfalso
          apply hnotMem
          rw [hsource]
          exact List.mem_cons_self

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective.SlabAcceptedPairedPeelChoice.sourceState_eq_of_record_eq_of_lower_eq
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective.slabAcceptedPairCanonicalPeeling_injective
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective.slabAcceptedPairCanonicalPeeling_fixedOutput_length_le_one
