/-
# A full-sector routing with direct spin-cube root spokes

The generic finite vacuum-sector routing is constructive but does not preserve
the explicit spin-cube geometry.  This module modifies only paths whose source
is an excited spin cube and whose target is the vacuum root: those paths use
the literal one-edge positive spoke.  Every other ordered endpoint pair uses
the existing canonical simple path.

The resulting routing is defined on the complete finite vacuum sector and is
vertex-simple.  Each excited spin cube has itself as terminal root source, so
the ray assignment is injective and its direct demand is already controlled by
the uniform return-floor theorem.  Off-ray routes remain canonical and no
uniform bound on their collisions or resistance traffic is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.FiniteBoolGraphSimplePaths

private def firstMappedPreimageOrLocal
    (map : Nat → Nat) (fallback target : Nat) : List Nat → Nat
  | [] => fallback
  | head :: tail =>
      if map head = target then head
      else firstMappedPreimageOrLocal map fallback target tail

private theorem firstMappedPreimageOrLocal_mem_of_mem_map
    (map : Nat → Nat) (fallback target : Nat) :
    ∀ items : List Nat,
      target ∈ items.map map →
        firstMappedPreimageOrLocal map fallback target items ∈ items
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : map head = target
      · simp only [firstMappedPreimageOrLocal, hhead, if_true]
        exact List.mem_cons_self
      · simp only [firstMappedPreimageOrLocal, hhead, if_false]
        apply List.mem_cons_of_mem head
        apply firstMappedPreimageOrLocal_mem_of_mem_map
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with htargetHead | htargetTail
        · exact False.elim (hhead htargetHead.symm)
        · exact htargetTail

private theorem map_firstMappedPreimageOrLocal_eq_of_mem_map
    (map : Nat → Nat) (fallback target : Nat) :
    ∀ items : List Nat,
      target ∈ items.map map →
        map (firstMappedPreimageOrLocal map fallback target items) = target
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : map head = target
      · simp only [firstMappedPreimageOrLocal, hhead, if_true]
      · simp only [firstMappedPreimageOrLocal, hhead, if_false]
        apply map_firstMappedPreimageOrLocal_eq_of_mem_map
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with htargetHead | htargetTail
        · exact False.elim (hhead htargetHead.symm)
        · exact htargetTail

private theorem cast_centralLowerSpinCubeToVacuumSpoke_eq_of_offset_eq
    {w : Q'} (hw : (0 : Q') < w) {K chosen offset : Nat}
    (hchosen : chosen = offset)
    (hindex : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K chosen =
      centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
    (hchosenBound : chosen + 1 ≤ K)
    (hoffsetBound : offset + 1 ≤ K) :
    Eq.mp
        (congrArg
          (fun start =>
            PositiveKernelChainIn
              (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
              (centralPhysicalFiniteVacuumSectorIndices
                w (Q'.le_of_lt hw) K 0)
              start 0)
          hindex)
        (centralLowerSpinCubeToVacuumSpoke hw hchosenBound) =
      centralLowerSpinCubeToVacuumSpoke hw hoffsetBound := by
  subst chosen
  rfl

/-! ## 1. Direct-ray / canonical-residual path selection -/

/-- A root-directed path that uses the literal spoke exactly on the excited
spin-cube ray and the canonical simple path everywhere else.  Keeping the
target definitionally equal to zero isolates the dependent source cast. -/
def centralLowerExcitedSpinCubeRayDirectPathToVacuum
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (left : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
      left 0 := by
  by_cases hray : left ∈
      centralLowerExcitedSpinCubeIndices w (Q'.le_of_lt hw) K
  · let offset := firstMappedPreimageOrLocal
      (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
      0 left (List.range K)
    have hoffset : offset ∈ List.range K :=
      firstMappedPreimageOrLocal_mem_of_mem_map
        (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
        0 left (List.range K) hray
    have hleftEq : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset = left :=
      map_firstMappedPreimageOrLocal_eq_of_mem_map
        (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
        0 left (List.range K) hray
    exact Eq.mp
      (congrArg
        (fun start =>
          PositiveKernelChainIn
            (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
            (centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw) K 0)
            start 0)
        hleftEq)
      (centralLowerSpinCubeToVacuumSpoke hw
        (by
          have hoffsetLt := List.mem_range.mp hoffset
          omega))
  · exact centralPhysicalFiniteVacuumSectorSimplePositivePath
      w (Q'.le_of_lt hw) K 0 left 0 hleft
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)

/-- The full ordered-pair routing: root-directed ray paths use the direct
spokes; every non-root target retains the canonical simple path. -/
def centralLowerExcitedSpinCubeRayDirectRootPath
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
      left right := by
  by_cases hroot : right = 0
  · exact Eq.mp
      (congrArg
        (fun target =>
          PositiveKernelChainIn
            (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
            (centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw) K 0)
            left target)
        hroot.symm)
      (centralLowerExcitedSpinCubeRayDirectPathToVacuum hw K left hleft)
  · exact centralPhysicalFiniteVacuumSectorSimplePositivePath
      w (Q'.le_of_lt hw) K 0 left right hleft hright

def centralLowerExcitedSpinCubeRayDirectRootRoutingAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K where
  path := centralLowerExcitedSpinCubeRayDirectRootPath hw K

theorem centralLowerExcitedSpinCubeRayDirectPathToVacuum_ray_eq
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hindex : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0) :
    centralLowerExcitedSpinCubeRayDirectPathToVacuum hw K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) hindex =
      centralLowerSpinCubeToVacuumSpoke hw
        (show offset + 1 ≤ K by omega) := by
  unfold centralLowerExcitedSpinCubeRayDirectPathToVacuum
  have hray : centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset ∈
        centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K := by
    apply List.mem_map.mpr
    exact ⟨offset, List.mem_range.mpr hoffset, rfl⟩
  rw [dif_pos hray]
  let chosen := firstMappedPreimageOrLocal
    (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
    0
    (centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset)
    (List.range K)
  have hchosenMem : chosen ∈ List.range K :=
    firstMappedPreimageOrLocal_mem_of_mem_map
      (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
      0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
      (List.range K) hray
  have hchosenLt : chosen < K := List.mem_range.mp hchosenMem
  have hchosenIndex : centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K chosen =
        centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset :=
    map_firstMappedPreimageOrLocal_eq_of_mem_map
      (centralLowerExcitedSpinCubeIndex w (Q'.le_of_lt hw) K)
      0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
      (List.range K) hray
  have hchosen : chosen = offset :=
    centralLowerExcitedSpinCubeIndex_injective_on
      hw hchosenLt hoffset hchosenIndex
  exact cast_centralLowerSpinCubeToVacuumSpoke_eq_of_offset_eq
    hw hchosen hchosenIndex (by omega) (by omega)

theorem centralLowerExcitedSpinCubeRayDirectRootPath_ray_eq
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hindex : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
    (hzero : 0 ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    centralLowerExcitedSpinCubeRayDirectRootPath hw K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 hindex hzero =
      centralLowerSpinCubeToVacuumSpoke hw
        (show offset + 1 ≤ K by omega) := by
  unfold centralLowerExcitedSpinCubeRayDirectRootPath
  rw [dif_pos rfl]
  exact centralLowerExcitedSpinCubeRayDirectPathToVacuum_ray_eq
    hw hoffset hindex

theorem centralLowerExcitedSpinCubeRayDirectRootRoutingAt_path_ray_eq
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hindex : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
    (hzero : 0 ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K).path
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 hindex hzero =
      centralLowerSpinCubeToVacuumSpoke hw
        (show offset + 1 ≤ K by omega) :=
  centralLowerExcitedSpinCubeRayDirectRootPath_ray_eq
    hw hoffset hindex hzero

/-! ## 2. Vertex-simple full-sector routing -/

private theorem canonicalSimplePositivePath_vertices_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (PositiveKernelChainIn.vertices
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 left right hleft hright)).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorSimplePositivePath
  rw [BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.vertices_ofSupportedWalk]
  exact (centralPhysicalFiniteVacuumSectorSimpleWalk
    w hw K 0 left right hleft hright).nodup

theorem centralLowerExcitedSpinCubeRayDirectPathToVacuum_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) (K left : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0) :
    (PositiveKernelChainIn.vertices
      (centralLowerExcitedSpinCubeRayDirectPathToVacuum
        hw K left hleft)).Nodup := by
  by_cases hray : left ∈
      centralLowerExcitedSpinCubeIndices w (Q'.le_of_lt hw) K
  · obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hray
    have hoffsetLt := List.mem_range.mp hoffset
    rw [centralLowerExcitedSpinCubeRayDirectPathToVacuum_ray_eq
      hw hoffsetLt]
    simp only [centralLowerSpinCubeToVacuumSpoke,
      PositiveKernelChainIn.vertices]
    exact List.nodup_cons.mpr
      ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact centralLowerExcitedSpinCubeIndex_ne_zero hw hoffsetLt,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
  · unfold centralLowerExcitedSpinCubeRayDirectPathToVacuum
    rw [dif_neg hray]
    exact canonicalSimplePositivePath_vertices_nodup _ _

theorem centralLowerExcitedSpinCubeRayDirectRootPath_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) (K left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0) :
    (PositiveKernelChainIn.vertices
      (centralLowerExcitedSpinCubeRayDirectRootPath
        hw K left right hleft hright)).Nodup := by
  by_cases hroot : right = 0
  · subst right
    unfold centralLowerExcitedSpinCubeRayDirectRootPath
    rw [dif_pos rfl]
    exact centralLowerExcitedSpinCubeRayDirectPathToVacuum_vertices_nodup
      hw K left hleft
  · unfold centralLowerExcitedSpinCubeRayDirectRootPath
    rw [dif_neg hroot]
    exact canonicalSimplePositivePath_vertices_nodup hleft hright

theorem centralLowerExcitedSpinCubeRayDirectRootRoutingAt_path_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) (K left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0) :
    (PositiveKernelChainIn.vertices
      ((centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K).path
        left right hleft hright)).Nodup :=
  centralLowerExcitedSpinCubeRayDirectRootPath_vertices_nodup
    hw K left right hleft hright

/-! ## 3. Literal terminal assignment on the ray -/

theorem centralLowerExcitedSpinCubeRayDirectRootRoutingAt_terminalSource_eq
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset)
        (centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K _
          (List.mem_map.mpr
            ⟨offset, List.mem_range.mpr hoffset, rfl⟩)) =
      centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
  rw [centralLowerExcitedSpinCubeRayDirectRootRoutingAt_path_ray_eq
    hw hoffset]
  rfl

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting.centralLowerExcitedSpinCubeRayDirectRootPath_ray_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting.centralLowerExcitedSpinCubeRayDirectRootPath_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting.centralLowerExcitedSpinCubeRayDirectRootRoutingAt_path_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting.centralLowerExcitedSpinCubeRayDirectRootRoutingAt_terminalSource_eq
