/-
# Exact ray/off-ray split of the direct-spoke terminal fibers

The direct-spoke routing fixes every excited spin-cube ray state as its own
terminal source.  This module turns that pointwise fact into a fiber theorem:
the ray part of the terminal fiber over an explicit spin-cube spoke is exactly
one state, namely that spin cube.  Every additional state in the fiber lies in
the literal off-ray carrier.

This isolates the remaining terminal-spoke collision problem without assuming
that its off-ray part is small.  No cutoff-independent off-ray demand bound,
preceding-edge resistance estimate, cofinal gap, scaling limit, continuum
measure, OS/GNS reconstruction, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSumPerm_local {Item : Type} (value : Item → Q') :
    ∀ {left right : List Item}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSumPerm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSumPerm_local value hleft)
        (listQSumPerm_local value hright)

/-! ## 1. The ray state belongs to its own terminal fiber -/

theorem centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ∈
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) := by
  apply
    mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mpr
  let hindex := centralLowerExcitedSpinCubeIndices_subset_vacuumSector
    hw K _
      (List.mem_map.mpr
        ⟨offset, List.mem_range.mpr hoffset, rfl⟩)
  refine ⟨hindex,
    centralLowerExcitedSpinCubeIndex_ne_zero hw hoffset, ?_⟩
  exact
    centralLowerExcitedSpinCubeRayDirectRootRoutingAt_terminalSource_eq
      hw hoffset

/-- Two ray states can share a terminal spin-cube spoke only when their spin
offsets are equal. -/
theorem centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber_iff
    {w : Q'} (hw : (0 : Q') < w) {K leftOffset rightOffset : Nat}
    (hleft : leftOffset < K) (hright : rightOffset < K) :
    centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K leftOffset ∈
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K rightOffset) ↔
      leftOffset = rightOffset := by
  constructor
  · intro hmem
    obtain ⟨hindex, _hne, hterminal⟩ :=
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp
        hmem
    have hself :
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
            (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K leftOffset)
            hindex =
          centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K leftOffset := by
      simpa only using
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt_terminalSource_eq
          hw hleft)
    exact centralLowerExcitedSpinCubeIndex_injective_on
      hw hleft hright (hself.symm.trans hterminal)
  · intro heq
    subst rightOffset
    exact centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber
      hw hleft

/-! ## 2. Literal ray and off-ray subfibers -/

def centralLowerExcitedSpinCubeDirectRootTerminalRayFiber
    {w : Q'} (hw : (0 : Q') < w) (K source : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
      (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K) source).filter
    (centralLowerExcitedSpinCubeRayMembershipTest
      w (Q'.le_of_lt hw) K)

def centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber
    {w : Q'} (hw : (0 : Q') < w) (K source : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
      (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K) source).filter
    (fun state =>
      !(centralLowerExcitedSpinCubeRayMembershipTest
        w (Q'.le_of_lt hw) K state))

theorem mem_centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber_iff
    {w : Q'} (hw : (0 : Q') < w) {K source state : Nat} :
    state ∈ centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber
        hw K source ↔
      state ∈ centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K) source ∧
        state ∈ centralLowerExcitedSpinCubeOffRayIndices
          w (Q'.le_of_lt hw) K := by
  constructor
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    obtain ⟨hsector, _hne, _hterminal⟩ :=
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp
        hparts.1
    exact ⟨hparts.1, List.mem_filter.mpr ⟨hsector, hparts.2⟩⟩
  · rintro ⟨hterminal, hoffRay⟩
    have hoffRayParts := List.mem_filter.mp hoffRay
    exact List.mem_filter.mpr ⟨hterminal, hoffRayParts.2⟩

/-! ## 3. Exactly one ray occupant per explicit spoke -/

theorem centralLowerExcitedSpinCubeDirectRootTerminalRayFiber_perm_singleton
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    (centralLowerExcitedSpinCubeDirectRootTerminalRayFiber hw K
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)).Perm
      [centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset] := by
  apply perm_of_nodup_mem_iff
  · unfold centralLowerExcitedSpinCubeDirectRootTerminalRayFiber
    exact List.filter_sublist.nodup
      (List.filter_sublist.nodup
        (centralPhysicalFiniteVacuumSectorIndices_nodup
          w (Q'.le_of_lt hw) K 0))
  · exact List.nodup_cons.mpr
      ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro state
    constructor
    · intro hmem
      have hparts := List.mem_filter.mp hmem
      have hray : state ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K := by
        simpa only [centralLowerExcitedSpinCubeRayMembershipTest,
          decide_eq_true_eq] using hparts.2
      obtain ⟨otherOffset, hotherMem, rfl⟩ := List.mem_map.mp hray
      have hother : otherOffset < K := List.mem_range.mp hotherMem
      have heq :=
        (centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber_iff
          hw hother hoffset).mp hparts.1
      subst otherOffset
      exact List.mem_cons_self
    · intro hmem
      have hstate : state = centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset := List.mem_singleton.mp hmem
      subst state
      apply List.mem_filter.mpr
      refine ⟨
        centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber
          hw hoffset, ?_⟩
      simp only [centralLowerExcitedSpinCubeRayMembershipTest,
        decide_eq_true_eq]
      exact List.mem_map.mpr
        ⟨offset, List.mem_range.mpr hoffset, rfl⟩

/-- Every terminal-fiber occupant other than the distinguished ray state lies
in the literal off-ray subfiber. -/
theorem mem_directRootTerminalFiber_eq_ray_or_mem_offRayFiber
    {w : Q'} (hw : (0 : Q') < w) {K offset state : Nat}
    (hoffset : offset < K)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset)) :
    state = centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ∨
      state ∈ centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber
        hw K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) := by
  by_cases hray : state ∈ centralLowerExcitedSpinCubeIndices
      w (Q'.le_of_lt hw) K
  · obtain ⟨otherOffset, hotherMem, rfl⟩ := List.mem_map.mp hray
    have hother : otherOffset < K := List.mem_range.mp hotherMem
    have heq :=
      (centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber_iff
        hw hother hoffset).mp hstate
    subst otherOffset
    exact Or.inl rfl
  · apply Or.inr
    apply
      (mem_centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber_iff
        hw).mpr
    refine ⟨hstate, ?_⟩
    obtain ⟨hsector, _hne, _hterminal⟩ :=
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp
        hstate
    apply List.mem_filter.mpr
    refine ⟨hsector, ?_⟩
    unfold centralLowerExcitedSpinCubeRayMembershipTest
    rw [decide_eq_false_iff_not.mpr hray]
    rfl

/-! ## 4. Exact direct-demand / off-ray-demand decomposition -/

theorem directRootTerminalFiber_listQSum_eqv_self_add_offRay
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (value : Nat → Q') :
    listQSum value
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset)) ≈
      value (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) +
        listQSum value
          (centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber
            hw K
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K offset)) := by
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let fiber := centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K) source
  let test := centralLowerExcitedSpinCubeRayMembershipTest
    w (Q'.le_of_lt hw) K
  have hpartition : listQSum value fiber ≈
      listQSum value (fiber.filter test) +
        listQSum value (fiber.filter (fun state => !(test state))) :=
    listQSum_filter_partition value test fiber
  have hperm : (fiber.filter test).Perm [source] := by
    simpa only [source, fiber, test,
      centralLowerExcitedSpinCubeDirectRootTerminalRayFiber] using
      (centralLowerExcitedSpinCubeDirectRootTerminalRayFiber_perm_singleton
        hw hoffset)
  have hray : listQSum value (fiber.filter test) ≈ value source :=
    Q'.eqv_trans _ _ _
      (listQSumPerm_local value hperm)
      (Q'.eqv_of_eq (Q'.add_zero' (value source)))
  exact Q'.eqv_trans _ _ _ hpartition
    (Q'.add_eqv_congr_right _ _ _ hray)

/-- The resistance demand contributed by the genuinely off-ray occupants of
one selected terminal spoke. -/
def centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
    {w : Q'} (hw : (0 : Q') < w) (K source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0) : Q' :=
  listQSum
    (fun state =>
      let singleDemand :=
        centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 state *
          Q'.recipPos
            (centralPhysicalFiniteKernel
              w (Q'.le_of_lt hw) K 0 source 0)
            hpositive
      singleDemand + singleDemand)
    (centralLowerExcitedSpinCubeDirectRootTerminalOffRayFiber
      hw K source)

/-- The one distinguished ray occupant's contribution, using the same
positivity witness as the full terminal-fiber demand. -/
def centralLowerExcitedSpinCubeDirectRootTerminalSelfResistanceDemand
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0) : Q' :=
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let singleDemand :=
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 source *
      Q'.recipPos
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0)
        hpositive
  singleDemand + singleDemand

theorem directRootTerminalSelfResistanceDemand_eq_direct
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0) :
    centralLowerExcitedSpinCubeDirectRootTerminalSelfResistanceDemand
        hw hpositive =
      centralLowerExcitedSpinCubeDirectRootResistanceDemand
        hw hoffset := by
  rfl

theorem directRootTerminalFiberResistanceDemand_eqv_self_add_offRay
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) hpositive ≈
      centralLowerExcitedSpinCubeDirectRootTerminalSelfResistanceDemand
          hw hpositive +
        centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
          hw K
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) hpositive := by
  unfold
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
    centralLowerExcitedSpinCubeDirectRootTerminalSelfResistanceDemand
    centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
  exact directRootTerminalFiber_listQSum_eqv_self_add_offRay
    hw hoffset _

theorem directRootTerminalFiberResistanceDemand_eqv_direct_add_offRay
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) hpositive ≈
      centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset +
        centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
          hw K
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) hpositive := by
  exact Q'.eqv_trans _ _ _
    (directRootTerminalFiberResistanceDemand_eqv_self_add_offRay
      hw hoffset hpositive)
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_of_eq
        (directRootTerminalSelfResistanceDemand_eq_direct
          hw hoffset hpositive)))

/-- At the concrete strong-coupling anchor, the whole demand on an explicit
ray spoke is bounded by the proved direct-ray constant plus only its off-ray
fiber demand. -/
theorem anchorDirectRootTerminalFiberResistanceDemand_le_uniformBound_add_offRay
    {K offset : Nat} (hoffset : offset < K) :
    let source := centralLowerExcitedSpinCubeIndex
      anchorCoupling (by decide) K offset
    let hpositive : (0 : Q') <
        centralPhysicalFiniteKernel anchorCoupling (by decide) K 0 source 0 :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos (by decide)
        (by omega)
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt
          (w := anchorCoupling) (by decide) K)
        source hpositive ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
          anchorCentralSpinCubeCofinalRayCapacity.delta_pos +
        centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
          (w := anchorCoupling) (by decide) K source hpositive := by
  let source := centralLowerExcitedSpinCubeIndex
    anchorCoupling (by decide) K offset
  let hpositive : (0 : Q') <
      centralPhysicalFiniteKernel anchorCoupling (by decide) K 0 source 0 :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos (by decide)
      (by omega)
  have hsplit :=
    directRootTerminalFiberResistanceDemand_eqv_direct_add_offRay
      (w := anchorCoupling) (by decide) hoffset hpositive
  have hdirect := anchorDirectRootResistanceDemand_le_uniformBound hoffset
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add hdirect
      (Q'.le_refl'
        (centralLowerExcitedSpinCubeDirectRootTerminalOffRayResistanceDemand
          (w := anchorCoupling) (by decide) K source hpositive)))

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.centralLowerExcitedSpinCubeIndex_mem_directRootTerminalFiber_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.centralLowerExcitedSpinCubeDirectRootTerminalRayFiber_perm_singleton
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.mem_directRootTerminalFiber_eq_ray_or_mem_offRayFiber
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.directRootTerminalFiberResistanceDemand_eqv_direct_add_offRay
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber.anchorDirectRootTerminalFiberResistanceDemand_le_uniformBound_add_offRay
