/-
# Terminating canonical paired-component peeling

The deterministic accepted step has a strict natural-number measure.  This
module performs the resulting well-founded recursion and retains the exact
inverse data of every step: selected root face, selected replica, peel size,
and the adaptive component entropy code.

The output state is terminal on the fixed face list.  Every recorded peel
size is positive, and the sum of all recorded sizes telescopes exactly:

  mass(final) + totalPeelSize(trace) = mass(initial).

Thus the local component-removal compiler is now an actual finite canonical
process, not merely a one-step relation.

Constructive contract: well-founded recursion on explicit physical mass and
finite trace data only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Multiplicity-faithful step records -/

/-- The nondependent data retained from one selected component peel.  `left`
is true for the first replica and false for the second. -/
structure SlabAcceptedPairedPeelRecord : Type where
  rootFaceId : Nat
  left : Bool
  peelSize : Nat
  code : ComponentAdaptiveEntropyCode
deriving DecidableEq

/-- Erase one dependent accepted choice to its complete finite inverse code. -/
def slabAcceptedPairedPeelChoiceRecord
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    SlabAcceptedPairedPeelRecord :=
  match choice with
  | .left faceId hface hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.1 hpositive
      { rootFaceId := faceId
        left := true
        peelSize := choice.peelSize
        code := componentAdaptiveEntropyCode seed }
  | .right faceId hface _ hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.2 hpositive
      { rootFaceId := faceId
        left := false
        peelSize := choice.peelSize
        code := componentAdaptiveEntropyCode seed }

@[simp] theorem slabAcceptedPairedPeelChoiceRecord_peelSize
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    (slabAcceptedPairedPeelChoiceRecord choice).peelSize =
      choice.peelSize := by
  cases choice <;> rfl

/-- A recorded code is admitted by the adaptive carrier at its stored root
and stored peel size. -/
def SlabAcceptedPairedPeelRecord.Valid
    (extent : Nat) (record : SlabAcceptedPairedPeelRecord) : Prop :=
  record.code ∈ componentAdaptiveEntropyCarrier
    extent record.rootFaceId record.peelSize

/-- The record emitted by every actual accepted choice is carrier-valid. -/
theorem slabAcceptedPairedPeelChoiceRecord_valid
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    (slabAcceptedPairedPeelChoiceRecord choice).Valid D.extent := by
  cases choice with
  | left faceId hface hpositive =>
      exact componentAdaptiveEntropyCode_mem_carrier
        (acceptedExpandedSourceRootSeed
          D faceId hface state.1 hpositive)
  | right faceId hface _ hpositive =>
      exact componentAdaptiveEntropyCode_mem_carrier
        (acceptedExpandedSourceRootSeed
          D faceId hface state.2 hpositive)

/-- Total physical multiplicity removed by a recorded trace. -/
def slabAcceptedPairedPeelTraceMass
    (trace : List SlabAcceptedPairedPeelRecord) : Nat :=
  listNatWeight SlabAcceptedPairedPeelRecord.peelSize trace

/-! ## 2. The finite output carrier -/

/-- The computed final accepted pair and its forward chronological trace. -/
abbrev SlabAcceptedPairedCanonicalPeelingOutput
    (D : SlabPhysicalData) :=
  SlabAcceptedTwoReplicaState D × List SlabAcceptedPairedPeelRecord

/-! ## 3. Well-founded canonical iteration -/

/-- Repeatedly apply the unique deterministic step until both replicas vanish
on the fixed face list.  Termination is by strict total pair-mass descent. -/
def slabAcceptedPairCanonicalPeeling
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    (state : SlabAcceptedTwoReplicaState D) →
      SlabAcceptedPairedCanonicalPeelingOutput D
  | state =>
      match slabAcceptedPairCanonicalChoice? D state faces hphysical with
      | none =>
          (state, [])
      | some choice =>
          let tail := slabAcceptedPairCanonicalPeeling
            D faces hphysical choice.lowerState
          (tail.1, slabAcceptedPairedPeelChoiceRecord choice :: tail.2)
termination_by state => slabAcceptedTwoReplicaStateMass state
decreasing_by
  exact choice.lowerState_mass_lt

/-! ## 4. Contracted consequences -/

/-- The final state vanishes in both replicas at every fixed face. -/
theorem slabAcceptedPairCanonicalPeeling_final_zero
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (faceId : Nat), faceId ∈ faces →
      let result := slabAcceptedPairCanonicalPeeling
        D faces hphysical state
      result.1.1.1.1 faceId = 0 ∧
        result.1.2.1.1 faceId = 0 := by
  change ∀ (faceId : Nat), faceId ∈ faces →
    (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).1.1.1.1 faceId = 0 ∧
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).1.2.1.1 faceId = 0
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · rename_i hchoice
    intro faceId hface
    exact (slabAcceptedPairCanonicalChoice?_eq_none_iff
      D state faces hphysical).mp hchoice faceId hface
  · rename_i choice hchoice
    exact slabAcceptedPairCanonicalPeeling_final_zero
      D faces hphysical choice.lowerState
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- Every step in the computed trace has positive removed multiplicity. -/
theorem slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalPeeling
      D faces hphysical state
    ∀ record, record ∈ result.2 → 0 < record.peelSize := by
  change ∀ record,
    record ∈ (slabAcceptedPairCanonicalPeeling
      D faces hphysical state).2 → 0 < record.peelSize
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro record hmem
    cases hmem
  · rename_i choice hchoice
    intro record hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · subst record
      simpa using choice.peelSize_pos
    · exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
        D faces hphysical choice.lowerState record htail
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- Every code in the computed trace belongs to its stored adaptive carrier. -/
theorem slabAcceptedPairCanonicalPeeling_trace_valid
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ record,
      record ∈ (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).2 → record.Valid D.extent := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro record hmem
    cases hmem
  · rename_i choice hchoice
    intro record hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · subst record
      exact slabAcceptedPairedPeelChoiceRecord_valid choice
    · exact slabAcceptedPairCanonicalPeeling_trace_valid
        D faces hphysical choice.lowerState record htail
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- The recorded peel sizes telescope exactly against total pair mass. -/
theorem slabAcceptedPairCanonicalPeeling_mass_telescope
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalPeeling
      D faces hphysical state
    slabAcceptedTwoReplicaStateMass result.1 +
        slabAcceptedPairedPeelTraceMass result.2 =
      slabAcceptedTwoReplicaStateMass state := by
  change
    slabAcceptedTwoReplicaStateMass
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical state).1 +
        slabAcceptedPairedPeelTraceMass
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical state).2 =
      slabAcceptedTwoReplicaStateMass state
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · rfl
  · rename_i choice hchoice
    have hhead := choice.lowerState_mass_add_peelSize
    have htail := slabAcceptedPairCanonicalPeeling_mass_telescope
      D faces hphysical choice.lowerState
    unfold slabAcceptedPairedPeelTraceMass at htail ⊢
    simp only [listNatWeight,
      slabAcceptedPairedPeelChoiceRecord_peelSize]
    omega
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

private theorem trace_length_le_mass_of_positive :
    ∀ trace : List SlabAcceptedPairedPeelRecord,
      (∀ record, record ∈ trace → 0 < record.peelSize) →
      trace.length ≤ slabAcceptedPairedPeelTraceMass trace
  | [], _ => Nat.le_refl 0
  | head :: tail, hpositive => by
      have hhead := hpositive head List.mem_cons_self
      have htail := trace_length_le_mass_of_positive tail
        (fun record hmem =>
          hpositive record (List.mem_cons_of_mem head hmem))
      unfold slabAcceptedPairedPeelTraceMass at htail ⊢
      simp only [List.length_cons, listNatWeight]
      omega

/-- A canonical trace contains no more steps than the initial pair mass. -/
theorem slabAcceptedPairCanonicalPeeling_trace_length_le_mass
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalPeeling
      D faces hphysical state
    result.2.length ≤ slabAcceptedTwoReplicaStateMass state := by
  change
    (slabAcceptedPairCanonicalPeeling
      D faces hphysical state).2.length ≤
        slabAcceptedTwoReplicaStateMass state
  have hpositive := slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
    D faces hphysical state
  have hlength := trace_length_le_mass_of_positive
    (slabAcceptedPairCanonicalPeeling
      D faces hphysical state).2 hpositive
  have htelescope := slabAcceptedPairCanonicalPeeling_mass_telescope
    D faces hphysical state
  omega

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairedPeelChoiceRecord
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairCanonicalPeeling
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairCanonicalPeeling_final_zero
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairCanonicalPeeling_trace_valid
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairCanonicalPeeling_mass_telescope
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling.slabAcceptedPairCanonicalPeeling_trace_length_le_mass
