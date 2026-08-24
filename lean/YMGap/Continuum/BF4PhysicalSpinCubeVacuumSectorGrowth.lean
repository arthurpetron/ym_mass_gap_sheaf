/-
# Linear growth of the canonical BF4 vacuum sector

At cutoff `K`, the positive support ray supplies the `K + 1` closed cube
states with labels `0, ..., K`.  Each state has a direct strictly positive raw
kernel edge from the vacuum, so its finite-carrier index lies in the rooted
vacuum component.  Evaluation on one named cube face makes these states
pairwise distinct.  A constructive finite-list injection therefore proves
that the literal canonical vacuum-sector state count is at least `K + 1`.

This is a representation-cutoff carrier-growth theorem at half-extent zero.
It is not a thermodynamic-volume statement and, by itself, is not a spectral
gap estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.FiniteBoolGraphSimplePaths

namespace YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Every admitted spin cube lies in the rooted component -/

theorem centralLowerSpinCubeState_mem_vacuumSector
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    centralLowerSpinCubeState spin ∈
      centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) K 0 := by
  have hpositive :=
    centralLowerSpinCubeState_mem_centralPositiveHalfStates hw hspin
  obtain ⟨spinIndex, hspinIndex, hstateAt⟩ :=
    centralPhysicalFiniteStateAt_exists
      w (Q'.le_of_lt hw) K 0 hpositive
  have hrootSpin :
      centralPhysicalFiniteSupportAdjacentB
        w (Q'.le_of_lt hw) K 0 0 spinIndex = true :=
    centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
      w (Q'.le_of_lt hw) K 0
      (centralPhysicalFiniteStateAt_zero_eq_vacuum
        w (Q'.le_of_lt hw) K 0)
      hstateAt
      (centralPhysicalReflectedKernel_vacuum_spinCube_pos hw hspin)
  have hspinSector : spinIndex ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        w (Q'.le_of_lt hw) K 0)
      (zero_mem_centralPhysicalFiniteIndexCarrier
        w (Q'.le_of_lt hw) K 0)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (List.mem_range.mpr hspinIndex)
      hrootSpin
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    w (Q'.le_of_lt hw) K 0 hspinSector hstateAt

/-! ## 2. The explicit finite ray is duplicate-free -/

/-- The complete list of cutoff-admitted closed spin cubes. -/
def centralLowerSpinCubeStates (K : Nat) : List EdgeLabelling :=
  (List.range (K + 1)).map centralLowerSpinCubeState

theorem centralLowerSpinCubeStates_length (K : Nat) :
    (centralLowerSpinCubeStates K).length = K + 1 := by
  simp [centralLowerSpinCubeStates]

private theorem nodup_map_of_injective
    {A B : Type} (map : A → B)
    (hinjective : Function.Injective map) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective heq) ▸ hitem)

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem centralLowerSpinCubeStates_nodup (K : Nat) :
    (centralLowerSpinCubeStates K).Nodup := by
  unfold centralLowerSpinCubeStates
  exact nodup_map_of_injective centralLowerSpinCubeState
    centralLowerSpinCubeState_injective (rangeNodupLocal _)

theorem centralLowerSpinCubeStates_subset_vacuumSector
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ∀ state, state ∈ centralLowerSpinCubeStates K →
      state ∈ centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) K 0 := by
  intro state hstate
  obtain ⟨spin, hspinRange, rfl⟩ := List.mem_map.mp hstate
  exact centralLowerSpinCubeState_mem_vacuumSector hw
    (by
      have hlt := List.mem_range.mp hspinRange
      omega)

/-! ## 3. Faithful natural-number codes for finite counting -/

/-- Faithful numerical codes of the cutoff-admitted spin cubes. -/
def centralLowerSpinCubeCodes (K : Nat) : List Nat :=
  (List.range (K + 1)).map fun spin =>
    bf4StateCode K 0 (centralLowerSpinCubeState spin)

/-- Numerical codes of all states in the canonical rooted component. -/
def centralPhysicalFiniteVacuumSectorStateCodes
    (w : Q') (hw : (0 : Q') <= w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorStates w hw K 0).map
    (bf4StateCode K 0)

theorem centralLowerSpinCubeCodes_length (K : Nat) :
    (centralLowerSpinCubeCodes K).length = K + 1 := by
  simp [centralLowerSpinCubeCodes]

theorem centralLowerSpinCubeCodes_nodup (K : Nat) :
    (centralLowerSpinCubeCodes K).Nodup := by
  unfold centralLowerSpinCubeCodes
  apply nodup_map_of_injOn
  · exact rangeNodupLocal _
  · intro left hleft right hright hcode
    have hleftLe : left <= K := by
      have hlt := List.mem_range.mp hleft
      omega
    have hrightLe : right <= K := by
      have hlt := List.mem_range.mp hright
      omega
    have hstateEq := bf4StateCode_injective_on_centralHalfStates
      (centralLowerSpinCubeState_mem_centralHalfStates hleftLe)
      (centralLowerSpinCubeState_mem_centralHalfStates hrightLe)
      hcode
    exact centralLowerSpinCubeState_injective hstateEq

theorem centralLowerSpinCubeCodes_subset_vacuumSectorStateCodes
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ∀ code, code ∈ centralLowerSpinCubeCodes K →
      code ∈ centralPhysicalFiniteVacuumSectorStateCodes
        w (Q'.le_of_lt hw) K := by
  intro code hcode
  obtain ⟨spin, hspinRange, rfl⟩ := List.mem_map.mp hcode
  unfold centralPhysicalFiniteVacuumSectorStateCodes
  apply List.mem_map.mpr
  refine ⟨centralLowerSpinCubeState spin, ?_, rfl⟩
  exact centralLowerSpinCubeState_mem_vacuumSector hw
    (by
      have hlt := List.mem_range.mp hspinRange
      omega)

/-! ## 4. Quantitative rooted-carrier growth -/

/-- The canonical rooted vacuum component contains at least one distinct
state for each label admitted by cutoff `K`. -/
theorem centralPhysicalFiniteVacuumSectorIndices_length_ge_cutoff_succ
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    K + 1 <=
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0).length := by
  have hlength := FiniteListBound.nodup_subset_length_le
    (centralLowerSpinCubeCodes K)
    (centralPhysicalFiniteVacuumSectorStateCodes
      w (Q'.le_of_lt hw) K)
    (centralLowerSpinCubeCodes_nodup K)
    (centralLowerSpinCubeCodes_subset_vacuumSectorStateCodes hw K)
  rw [centralLowerSpinCubeCodes_length] at hlength
  unfold centralPhysicalFiniteVacuumSectorStateCodes
    centralPhysicalFiniteVacuumSectorStates at hlength
  simpa only [List.length_map] using hlength

end YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralLowerSpinCubeState_mem_vacuumSector
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralLowerSpinCubeStates_nodup
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralLowerSpinCubeStates_subset_vacuumSector
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralLowerSpinCubeCodes_nodup
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralLowerSpinCubeCodes_subset_vacuumSectorStateCodes
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth.centralPhysicalFiniteVacuumSectorIndices_length_ge_cutoff_succ
