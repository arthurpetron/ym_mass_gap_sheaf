/-
# No common terminal spoke under cofinal bounded BF4 route sharing

The cutoff-two mass-amortized pilot routes every non-vacuum state through one
hub and then into the vacuum.  This module proves why that terminal pattern
cannot be the cofinal bounded-sharing producer.

At cutoff `K`, the explicit excited spin-cube ray supplies `K` distinct
non-vacuum states.  If every non-vacuum route has the same terminal source,
then every one of those states uses the same final directed edge into the
vacuum.  The existing uniform sharing ceiling would therefore have to be at
least `K` for every sufficiently large `K`, contradicting its fixed rational
value.

Only the *common terminal source* strategy is ruled out.  Internal hubs may
still be useful, provided the cofinal construction distributes the terminal
root spokes.  No routing producer, congestion bound, gap, continuum limit, or
Clay conclusion is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCommonTerminalBoundedSharingNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. A common terminal edge contains the full spin-cube ray -/

theorem centralLowerExcitedSpinCubeIndices_subset_commonTerminalEdgeUsers
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw)
    (terminalSource : ∀ K, family.start ≤ K → Nat)
    (allNonzeroRoutesHaveCommonTerminal :
      ∀ K, (hK : family.start ≤ K) →
        ∀ state,
          (hstate : state ∈
            centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw) K 0) →
          state ≠ 0 →
          centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
              (family.routing K hK) state hstate =
            terminalSource K hK)
    (K : Nat) (hK : family.start ≤ K) :
    ∀ state,
      state ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K →
        state ∈
          centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
            (family.routing K hK) (terminalSource K hK) 0 := by
  intro state hspin
  have hnonzero :=
    centralLowerExcitedSpinCubeIndices_subset_nonzeroSector
      hw K state hspin
  have hparts :=
    mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff.mp hnonzero
  apply
    mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mpr
  refine ⟨hparts.1, ?_⟩
  have hedge :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
      (family.routing K hK) state hparts.1 hparts.2
  rw [allNonzeroRoutesHaveCommonTerminal K hK state hparts.1 hparts.2]
    at hedge
  exact hedge

/-! ## 2. Linear sharing demand and the cofinal contradiction -/

theorem cutoff_le_sharingBound_of_commonTerminal
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw)
    (terminalSource : ∀ K, family.start ≤ K → Nat)
    (allNonzeroRoutesHaveCommonTerminal :
      ∀ K, (hK : family.start ≤ K) →
        ∀ state,
          (hstate : state ∈
            centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw) K 0) →
          state ≠ 0 →
          centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
              (family.routing K hK) state hstate =
            terminalSource K hK)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat K ≤ family.sharingBound := by
  have hlength :
      (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K).length ≤
        (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
          (family.routing K hK) (terminalSource K hK) 0).length :=
    FiniteListBound.nodup_subset_length_le _ _
      (centralLowerExcitedSpinCubeIndices_nodup hw K)
      (centralLowerExcitedSpinCubeIndices_subset_commonTerminalEdgeUsers
        family terminalSource allNonzeroRoutesHaveCommonTerminal K hK)
  rw [centralLowerExcitedSpinCubeIndices_length] at hlength
  exact Q'.le_trans' _ _ _
    (Q'.ofNat_le_ofNat hlength)
    (family.edgeUsers_cardinality_le
      K hK (terminalSource K hK) 0)

private theorem q_lt_of_lt_of_le_local
    {left middle right : Q'}
    (hleft : left < middle) (hright : middle ≤ right) :
    left < right := by
  have hleftCross :
      left.num * (middle.den : Int) <
        middle.num * (left.den : Int) :=
    hleft
  have hrightCross :
      middle.num * (right.den : Int) ≤
        right.num * (middle.den : Int) :=
    hright
  show
    left.num * (right.den : Int) <
      right.num * (left.den : Int)
  have hfirst :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (middle.num * (left.den : Int)) * (right.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right hleftCross
      (by
        exact_mod_cast right.den_pos :
          (0 : Int) < (right.den : Int))
    have hreorder :
        (left.num * (middle.den : Int)) * (right.den : Int) =
          (left.num * (right.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (middle.den : Int) (right.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (middle.num * (left.den : Int)) * (right.den : Int) ≤
        (right.num * (left.den : Int)) * (middle.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hrightCross
      (by
        exact_mod_cast Nat.le_of_lt left.den_pos :
          (0 : Int) ≤ (left.den : Int))
    have hleftReorder :
        (middle.num * (right.den : Int)) * (left.den : Int) =
          (middle.num * (left.den : Int)) * (right.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (right.den : Int) (left.den : Int)]
    have hrightReorder :
        (right.num * (middle.den : Int)) * (left.den : Int) =
          (right.num * (left.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (middle.den : Int) (left.den : Int)]
    rw [hleftReorder, hrightReorder] at hscaled
    exact hscaled
  have hproduct :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (right.num * (left.den : Int)) * (middle.den : Int) :=
    Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hproduct
    (by
      exact_mod_cast Nat.le_of_lt middle.den_pos :
        (0 : Int) ≤ (middle.den : Int))

/-- Constructive Archimedean witness used to exceed the fixed sharing bound. -/
private theorem sharingBound_lt_successorNumerator (bound : Q') :
    bound < Q'.ofNat (bound.num.toNat + 1) := by
  have hdenOne : (1 : Int) ≤ (bound.den : Int) := by
    exact_mod_cast bound.den_pos
  have hnumLe :
      bound.num ≤ (bound.num.toNat : Int) :=
    Int.self_le_toNat bound.num
  have hmultiplierNonnegative :
      (0 : Int) ≤ (bound.num.toNat : Int) + 1 := by
    have hcastNonnegative :
        (0 : Int) ≤ (bound.num.toNat : Int) :=
      Int.natCast_nonneg _
    omega
  have hmul :
      ((bound.num.toNat : Int) + 1) * (1 : Int) ≤
        ((bound.num.toNat : Int) + 1) * (bound.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hdenOne hmultiplierNonnegative
  rw [Int.mul_one] at hmul
  show
    bound.num *
        ((Q'.ofNat (bound.num.toNat + 1)).den : Int) <
      (Q'.ofNat (bound.num.toNat + 1)).num *
        (bound.den : Int)
  have hden :
      (Q'.ofNat (bound.num.toNat + 1)).den = 1 :=
    rfl
  have hnum :
      (Q'.ofNat (bound.num.toNat + 1)).num =
        ((bound.num.toNat + 1 : Nat) : Int) :=
    rfl
  rw [hden, hnum]
  push_cast
  push_cast at hmul
  omega

/-- A cofinal bounded-sharing routing cannot send every non-vacuum route
through one cutoff-dependent terminal root spoke. -/
theorem boundedSharing_has_no_commonTerminal
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw)
    (terminalSource : ∀ K, family.start ≤ K → Nat)
    (allNonzeroRoutesHaveCommonTerminal :
      ∀ K, (hK : family.start ≤ K) →
        ∀ state,
          (hstate : state ∈
            centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw) K 0) →
          state ≠ 0 →
          centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
              (family.routing K hK) state hstate =
            terminalSource K hK) :
    False := by
  let K := max family.start (family.sharingBound.num.toNat + 1)
  have hK : family.start ≤ K :=
    Nat.le_max_left _ _
  have hsuccessorK : family.sharingBound.num.toNat + 1 ≤ K :=
    Nat.le_max_right _ _
  have hcutoffLe : Q'.ofNat K ≤ family.sharingBound :=
    cutoff_le_sharingBound_of_commonTerminal
      family terminalSource allNonzeroRoutesHaveCommonTerminal K hK
  have hboundLt : family.sharingBound < Q'.ofNat K :=
    q_lt_of_lt_of_le_local
      (sharingBound_lt_successorNumerator family.sharingBound)
      (Q'.ofNat_le_ofNat hsuccessorK)
  exact (Int.not_lt_of_ge hcutoffLe) hboundLt

end YMGap.Continuum.BF4PhysicalVacuumSectorCommonTerminalBoundedSharingNoGo

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCommonTerminalBoundedSharingNoGo.centralLowerExcitedSpinCubeIndices_subset_commonTerminalEdgeUsers
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCommonTerminalBoundedSharingNoGo.cutoff_le_sharingBound_of_commonTerminal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCommonTerminalBoundedSharingNoGo.boundedSharing_has_no_commonTerminal
