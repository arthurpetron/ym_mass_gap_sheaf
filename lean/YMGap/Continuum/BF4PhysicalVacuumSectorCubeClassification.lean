/-
# Exact all-cutoff classification of the physical vacuum component

At slab extent one, positive w and K >= 1, the canonical vacuum sector is
exactly the bounded cube-supported common-parity family. The previously
proved containment is complemented here by the explicit difference-boundary
OS edges: the literal inward orbit stays inside the positive carrier, reaches
vacuum in at most K+1 moves, and every step has a positive physical weight.

Mate-invariant observables are consequently constant on this sector at every
cutoff. This is qualitative separation on the original OS object, not a
cutoff-uniform Poincare bound or successful-source traffic coverage. Those
quantitative obligations, completed gap, and continuum/Clay target stay open.
-/

import YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
import YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- An edge may be supplied in either direction because the actual finite
support graph is explicitly symmetric. No new graph is introduced. -/
theorem vacuumSector_mem_of_incoming_kernel (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) {source target : EdgeLabelling}
    (hs : source ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0)
    (ht : target ∈ centralPositiveHalfStates w hw K 0)
    (hp : (0 : Q') < centralPhysicalReflectedKernel w K 0 target source) :
    target ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0 := by
  obtain ⟨sourceIndex, hsourceIndex, hsourceEq⟩ := List.mem_map.mp hs
  obtain ⟨targetIndex, htargetIndex, htargetEq⟩ := centralPhysicalFiniteStateAt_exists w hw K 0 ht
  have hedge := centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos w hw K 0
    htargetEq hsourceEq hp
  have hreverse : centralPhysicalFiniteSupportAdjacentB w hw K 0 sourceIndex targetIndex = true := by
    rw [centralPhysicalFiniteSupportAdjacentB_symmetric w hw K 0 sourceIndex targetIndex]
    exact hedge
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index w hw K 0
    (rootComponent_closed_under_edge _ (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K 0)
      (zero_mem_centralPhysicalFiniteIndexCarrier w hw K 0) hsourceIndex
      (List.mem_range.mpr htargetIndex) hreverse) htargetEq

theorem cubeSupported_sector_of_mate {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hm : centralLowerCubeEvenInwardMatePhysical state ∈
      centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 :=
  vacuumSector_mem_of_incoming_kernel w (Q'.le_of_lt hw) K hm
    (cubeSupported_mem_positiveHalfStates hw K hK state (fun face _ => hb face) hz)
    (difference_kernel_pos hw K hK state (fun face _ => hb face) hz)

private theorem sector_of_orbit {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (steps : Nat) (state : EdgeLabelling)
    (hb : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hfinal : cubeInwardOrbit steps state ∈
      centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 := by
  induction steps generalizing state with
  | zero => exact hfinal
  | succ steps ih =>
      apply cubeSupported_sector_of_mate hw K hK state hb hz
      apply ih _ (cubeMate_bounded K hK state hb) _ hfinal
      intro face hf
      rw [centralLowerCubeEvenInwardMatePhysical_off_cube state hf, hz face hf]

theorem cubeSupportedCommonParity_mem_sector {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hc : CubeSupportedCommonParity state) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 := by
  apply sector_of_orbit hw K hK (cubeInwardRootTime K state) state
    (cubeSupported_bounded K state hb hc.1) hc.1
  rw [cubeInwardOrbit_rootTime_eq_zero K state hb hc]
  exact zeroEdgeLabelling_mem_centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0

theorem vacuumSector_cubeBounded (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0) :
    ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K := by
  have hhalf := centralPhysicalFiniteVacuumSectorState_mem_halfStates w hw K 0 hs
  intro face hf
  exact Nat.le_of_lt_succ ((boundedEdgeLabellings_sound K (centralLowerFaceIds 0) state hhalf).1
    face (centralLowerCubeFaceIds_subset_lower face hf))

/-- Exact canonical sector, all cutoffs K >= 1 and every positive rational w. -/
theorem vacuumSector_iff_cubeSupportedCommonParity {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 ↔
      (∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) ∧
        CubeSupportedCommonParity state := by
  constructor
  · intro hs
    exact ⟨vacuumSector_cubeBounded w (Q'.le_of_lt hw) K hs,
      vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw) K hs⟩
  · rintro ⟨hb, hc⟩
    exact cubeSupportedCommonParity_mem_sector hw K hK state hb hc

/-- The canonical sector sets are nested with representation cutoff. This
does not assert isometry, kernel compatibility, or norm convergence. -/
theorem vacuumSector_cutoff_mono {w : Q'} (hw : (0 : Q') < w)
    (K L : Nat) (hK : 1 ≤ K) (hKL : K ≤ L) {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) L 0 := by
  have hc := (vacuumSector_iff_cubeSupportedCommonParity hw K hK state).mp hs
  exact cubeSupportedCommonParity_mem_sector hw L (Nat.le_trans hK hKL) state
    (fun face hf => Nat.le_trans (hc.1 face hf) hKL) hc.2

/-- Positive coupling changes weights, but not this extent-one sector's
state set. This is not a coupling-uniform spectral estimate. -/
theorem vacuumSector_mem_coupling_iff {w v : Q'} (hw : (0 : Q') < w) (hv : (0 : Q') < v)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 ↔
      state ∈ centralPhysicalFiniteVacuumSectorStates v (Q'.le_of_lt hv) K 0 :=
  (vacuumSector_iff_cubeSupportedCommonParity hw K hK state).trans
    (vacuumSector_iff_cubeSupportedCommonParity hv K hK state).symm

theorem vacuumSector_inwardMate_mem {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    centralLowerCubeEvenInwardMatePhysical state ∈
      centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 := by
  have hc := vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw) K hs
  have hb := vacuumSector_cubeBounded w (Q'.le_of_lt hw) K hs
  have hmateBound := cubeMate_bounded K hK state (cubeSupported_bounded K state hb hc.1)
  have hmateHalf := cubeMate_mem_halfStates K hK state (cubeSupported_bounded K state hb hc.1) hc.1
  have hne : ¬ centralPhysicalReflectedKernel w K 0 state
      (centralLowerCubeEvenInwardMatePhysical state) ≈ 0 := by
    intro hz
    exact (Int.not_lt_of_ge (Q'.le_of_eqv hz)) (difference_kernel_pos hw K hK state hb hc.1)
  apply cubeSupportedCommonParity_mem_sector hw K hK _ (fun face _ => hmateBound face)
  exact kernel_preserves_cubeSupportedCommonParity w K state _
    (centralPhysicalFiniteVacuumSectorState_mem_halfStates w (Q'.le_of_lt hw) K 0 hs)
    hmateHalf hne hc

theorem vacuumSector_orbit_mem {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (steps : Nat) {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    cubeInwardOrbit steps state ∈
      centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 := by
  induction steps generalizing state with
  | zero => exact hs
  | succ steps ih => exact ih (vacuumSector_inwardMate_mem hw K hK hs)

/-- Every successive pair on the computed orbit has a genuine positive OS
entry. The explicit state-dependent lower bound is differencePhysicalWeight. -/
theorem vacuumSector_orbit_edge_pos {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (steps : Nat) {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
      (cubeInwardOrbit steps state) (cubeInwardOrbit (steps + 1) state) := by
  rw [cubeInwardOrbit_succ_last]
  have hhere := vacuumSector_orbit_mem hw K hK steps hs
  exact difference_kernel_pos hw K hK _
    (vacuumSector_cubeBounded w (Q'.le_of_lt hw) K hhere)
    (vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw) K hhere).1

theorem vacuumSector_mateInvariant_constant {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (coefficient : EdgeLabelling → Q')
    (hi : ∀ state, state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 →
      coefficient state ≈ coefficient (centralLowerCubeEvenInwardMatePhysical state))
    {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0) :
    coefficient state ≈ coefficient zeroEdgeLabelling := by
  have horbit : ∀ steps, coefficient state ≈ coefficient (cubeInwardOrbit steps state) := by
    intro steps
    induction steps with
    | zero => exact Q'.eqv_refl _
    | succ steps ih =>
        rw [cubeInwardOrbit_succ_last]
        exact Q'.eqv_trans _ _ _ ih (hi _ (vacuumSector_orbit_mem hw K hK steps hs))
  have hfinal := horbit (cubeInwardRootTime K state)
  rw [vacuumSector_inwardOrbit_reaches_zero w (Q'.le_of_lt hw) K hs] at hfinal
  exact hfinal

end YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_mem_of_incoming_kernel
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.cubeSupported_sector_of_mate
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.cubeSupportedCommonParity_mem_sector
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_cubeBounded
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_iff_cubeSupportedCommonParity
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_cutoff_mono
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_mem_coupling_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_inwardMate_mem
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_orbit_mem
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_orbit_edge_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification.vacuumSector_mateInvariant_constant
