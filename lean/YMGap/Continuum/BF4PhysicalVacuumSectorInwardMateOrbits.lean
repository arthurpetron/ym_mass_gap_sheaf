/-
# Exact inward-mate orbits and the cutoff-two geometric separation test

Two inward moves preserve zero and one and lower every other label by two.
Thus after `2*n` moves, labels bounded by `2*n+1` are exactly their parities.
A cube-supported state with common face parity reaches the vacuum at the
explicit time `2*(K/2) + state 0 % 2 <= K+1`. This is an all-cutoff formula
for the literal mate map, with no kernel or analytic hypothesis.

The map commutes with lower restriction, so it is exactly the endpoint map
of the existing successful full-slab sources. On the independently certified
65-state vacuum sector at cutoff two and coupling 1/2, every doubled subset
maps to the fundamental cube and that cube maps to zero. Consequently every
observable invariant under ALL these potential mates is constant there.

The successor `BF4PhysicalVacuumSectorCubeClassification` identifies the
all-cutoff canonical sector with this bounded common-parity family and proves
positive physical OS support for every mate, for w > 0, K >= 1, extent one.
OPEN: positive successful-source traffic for every required move and uniform
weighted norm control. The orbit formulas alone give neither a completed gap
nor any continuum/Clay conclusion.

No new analytic field, axiom, sorry, classical choice, noncomputable code,
native_decide, or enlarged elaboration limit is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

local infix:50 " ≈ " => Q'.eqv

/-- Two moves are a parity-preserving descent, not strict one-step spin descent. -/
theorem evenInwardMateLabel_twice (spin : Nat) :
    evenInwardMateLabel (evenInwardMateLabel spin) =
      if spin < 2 then spin else spin - 2 := by
  unfold evenInwardMateLabel
  by_cases hzero : spin = 0
  · subst spin; decide
  · rw [if_neg hzero]
    by_cases hone : spin = 1
    · subst spin; decide
    · rw [if_neg (by omega), if_neg (by omega)]
      omega

def inwardLabelOrbit : Nat → Nat → Nat
  | 0, spin => spin
  | steps + 1, spin => inwardLabelOrbit steps (evenInwardMateLabel spin)

/-- Exact terminal phase after an even number of moves. -/
theorem inwardLabelOrbit_even (pairs spin : Nat)
    (hspin : spin ≤ 2 * pairs + 1) :
    inwardLabelOrbit (2 * pairs) spin = spin % 2 := by
  induction pairs generalizing spin with
  | zero =>
      change spin = spin % 2
      omega
  | succ pairs ih =>
      rw [show 2 * (pairs + 1) = 2 * pairs + 2 by omega]
      change inwardLabelOrbit (2 * pairs)
        (evenInwardMateLabel (evenInwardMateLabel spin)) = spin % 2
      rw [evenInwardMateLabel_twice]
      by_cases hsmall : spin < 2
      · rw [if_pos hsmall]
        exact ih spin (by omega)
      · rw [if_neg hsmall, ih (spin - 2) (by omega)]
        omega

def cubeInwardOrbit : Nat → EdgeLabelling → EdgeLabelling
  | 0, state => state
  | steps + 1, state => cubeInwardOrbit steps
      (centralLowerCubeEvenInwardMatePhysical state)

theorem cubeInwardOrbit_on_cube (steps : Nat) (state : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    cubeInwardOrbit steps state id = inwardLabelOrbit steps (state id) := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      simp only [cubeInwardOrbit, ih,
        centralLowerCubeEvenInwardMatePhysical_on_cube _ hid, inwardLabelOrbit]

theorem cubeInwardOrbit_off_cube (steps : Nat) (state : EdgeLabelling)
    {id : Nat} (hid : id ∉ centralLowerCubeFaceIds) :
    cubeInwardOrbit steps state id = state id := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      simp only [cubeInwardOrbit, ih,
        centralLowerCubeEvenInwardMatePhysical_off_cube _ hid]

theorem cubeInwardOrbit_succ_last (steps : Nat) (state : EdgeLabelling) :
    cubeInwardOrbit (steps + 1) state =
      centralLowerCubeEvenInwardMatePhysical (cubeInwardOrbit steps state) := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      exact ih (centralLowerCubeEvenInwardMatePhysical state)

/-- The limiting two-cycle retains exterior labels and the entire cube parity pattern. -/
def cubeParityCore (state : EdgeLabelling) : EdgeLabelling :=
  fun id => if id ∈ centralLowerCubeFaceIds then state id % 2 else state id

theorem cubeInwardOrbit_even_eq_parityCore (pairs : Nat) (state : EdgeLabelling)
    (hbound : ∀ id, id ∈ centralLowerCubeFaceIds → state id ≤ 2 * pairs + 1) :
    cubeInwardOrbit (2 * pairs) state = cubeParityCore state := by
  funext id
  by_cases hid : id ∈ centralLowerCubeFaceIds
  · simp only [cubeParityCore, if_pos hid, cubeInwardOrbit_on_cube _ _ hid]
    exact inwardLabelOrbit_even pairs (state id) (hbound id hid)
  · simp only [cubeParityCore, if_neg hid, cubeInwardOrbit_off_cube _ _ hid]

/-- A label condition, not an assertion about the all-cutoff physical sector. -/
def CubeSupportedCommonParity (state : EdgeLabelling) : Prop :=
  (∀ id, id ∉ centralLowerCubeFaceIds → state id = 0) ∧
  (∀ id, id ∈ centralLowerCubeFaceIds → state id % 2 = state 0 % 2)

/-- Explicit root-hitting time; no existential witness is erased. -/
def cubeInwardRootTime (K : Nat) (state : EdgeLabelling) : Nat :=
  2 * (K / 2) + state 0 % 2

theorem cubeInwardRootTime_le (K : Nat) (state : EdgeLabelling) :
    cubeInwardRootTime K state ≤ K + 1 := by
  unfold cubeInwardRootTime
  omega

/-- All-cutoff geometric contraction of the common-parity cube family. -/
theorem cubeInwardOrbit_rootTime_eq_zero (K : Nat) (state : EdgeLabelling)
    (hbound : ∀ id, id ∈ centralLowerCubeFaceIds → state id ≤ K)
    (hstate : CubeSupportedCommonParity state) :
    cubeInwardOrbit (cubeInwardRootTime K state) state = zeroEdgeLabelling := by
  have hcore := cubeInwardOrbit_even_eq_parityCore (K / 2) state
    (fun id hid => by have := hbound id hid; omega)
  have hphase : state 0 % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases heven : state 0 % 2 = 0
  · unfold cubeInwardRootTime
    rw [heven, Nat.add_zero, hcore]
    funext id
    by_cases hid : id ∈ centralLowerCubeFaceIds
    · simp [cubeParityCore, hid, hstate.2 id hid, heven, zeroEdgeLabelling]
    · simp [cubeParityCore, hid, hstate.1 id hid, zeroEdgeLabelling]
  · have hodd : state 0 % 2 = 1 := by omega
    unfold cubeInwardRootTime
    rw [hodd, cubeInwardOrbit_succ_last, hcore]
    funext id
    by_cases hid : id ∈ centralLowerCubeFaceIds
    · simp [centralLowerCubeEvenInwardMatePhysical, cubeParityCore,
        hid, hstate.2 id hid, hodd, evenInwardMateLabel, zeroEdgeLabelling]
    · simp [centralLowerCubeEvenInwardMatePhysical, cubeParityCore,
        hid, hstate.1 id hid, zeroEdgeLabelling]

/-- This is the literal lower-state map of the existing successful sources. -/
theorem targetLower_eq_mate_sourceLower {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    targetLower source = centralLowerCubeEvenInwardMatePhysical (sourceLower source) := by
  funext id
  change centralLowerRestriction 0
      (centralLowerCubeEvenInwardMatePhysical source.physical) id =
    centralLowerCubeEvenInwardMatePhysical
      (centralLowerRestriction 0 source.physical) id
  by_cases hcube : id ∈ centralLowerCubeFaceIds
  · have hlower := centralLowerCubeFaceIds_subset_lower id hcube
    simp [centralLowerRestriction, centralLowerCubeEvenInwardMatePhysical, hcube, hlower]
  · by_cases hlower : id ∈ centralLowerFaceIds 0 <;>
      simp [centralLowerRestriction, centralLowerCubeEvenInwardMatePhysical, hcube, hlower]

/-! ## The exact finite sector: potential mates have no invisible observable -/

theorem inwardMate_fundamental_eq_zero :
    centralLowerCubeEvenInwardMatePhysical centralLowerCubeState = zeroEdgeLabelling := by
  funext id
  by_cases hid : id ∈ centralLowerCubeFaceIds <;>
    simp [centralLowerCubeEvenInwardMatePhysical, centralLowerCubeState, componentLabel,
      evenInwardMateLabel, hid, zeroEdgeLabelling]

theorem inwardMate_doubledSubset_eq_fundamental {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoDoubledCubeSubsetStates) :
    centralLowerCubeEvenInwardMatePhysical state = centralLowerCubeState := by
  have hs := (mem_cutoffTwoDoubledCubeSubsetStates_iff state).mp hstate
  funext id
  by_cases hid : id ∈ centralLowerCubeFaceIds
  · rcases hs.1 id hid with hlabel | hlabel <;>
      simp [centralLowerCubeEvenInwardMatePhysical, centralLowerCubeState, componentLabel,
        evenInwardMateLabel, hid, hlabel]
  · simp [centralLowerCubeEvenInwardMatePhysical, centralLowerCubeState, componentLabel,
      hid, hs.2 id hid]

/-- The potential mate never leaves the certified 65-state set. -/
theorem cutoffTwo_mate_mem {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    centralLowerCubeEvenInwardMatePhysical state ∈ cutoffTwoCubeSectorStates := by
  rcases List.mem_cons.mp hstate with heq | hsubset
  · subst state
    rw [inwardMate_fundamental_eq_zero]
    exact YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates
  · rw [inwardMate_doubledSubset_eq_fundamental hsubset]
    exact List.mem_cons_self

/-- Every potential-mate invariant is constant on all 65 states, not just on parity. -/
theorem cutoffTwo_mate_invariant_constant (coefficient : EdgeLabelling → Q')
    (hinvariant : ∀ state, state ∈ cutoffTwoCubeSectorStates →
      coefficient state ≈ coefficient (centralLowerCubeEvenInwardMatePhysical state))
    {state : EdgeLabelling} (hstate : state ∈ cutoffTwoCubeSectorStates) :
    coefficient state ≈ coefficient zeroEdgeLabelling := by
  have hhub := hinvariant centralLowerCubeState List.mem_cons_self
  rw [inwardMate_fundamental_eq_zero] at hhub
  rcases List.mem_cons.mp hstate with heq | hsubset
  · subst state; exact hhub
  · have hs := hinvariant state hstate
    rw [inwardMate_doubledSubset_eq_fundamental hsubset] at hs
    exact Q'.eqv_trans _ _ _ hs hhub

/-- Same statement on the canonical finite vacuum component at coupling 1/2.
The invariance premise covers all potential mates, not merely positive selected traffic. -/
theorem canonicalCutoffTwo_mate_invariant_constant (coefficient : EdgeLabelling → Q')
    (hinvariant : ∀ state, state ∈ centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0 →
      coefficient state ≈ coefficient (centralLowerCubeEvenInwardMatePhysical state))
    {state : EdgeLabelling} (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      cutoffTwoHalfCoupling (by decide) 2 0) :
    coefficient state ≈ coefficient zeroEdgeLabelling := by
  apply cutoffTwo_mate_invariant_constant coefficient
    (fun state hs => hinvariant state
      ((centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff state).mpr hs))
  exact (centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff state).mp hstate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.evenInwardMateLabel_twice
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.inwardLabelOrbit_even
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.cubeInwardOrbit_even_eq_parityCore
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.cubeInwardRootTime_le
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.cubeInwardOrbit_rootTime_eq_zero
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.targetLower_eq_mate_sourceLower
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.inwardMate_fundamental_eq_zero
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.inwardMate_doubledSubset_eq_fundamental
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.cutoffTwo_mate_mem
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.cutoffTwo_mate_invariant_constant
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits.canonicalCutoffTwo_mate_invariant_constant
