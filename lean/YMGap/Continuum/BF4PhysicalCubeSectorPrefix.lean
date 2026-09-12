/-
# Literal finite-cylinder approximations to the physical sector indicator

Each prefix is the existing canonical sector presentation with every
coefficient equal to one. Distinct sector states cannot match the same
lower labelling, so its value is exactly a zero/one indicator, not a bound
by the growing number of states. On its finite half-state carrier this
indicator equals the cutoff-independent physical sector event.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorIndicator
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

namespace YMGap.Continuum.BF4PhysicalCubeSectorPrefix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeSectorIndicator
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "indices" => centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide)
local notation "stateAt" => centralPhysicalFiniteStateAt anchorCoupling (by decide)

def sectorPrefix (K : Nat) : CentralPhysicalVacuumSectorCylinderPresentation anchorCoupling (by decide) 0 where
  base := K
  coefficient := fun _ => 1

def prefixB (K : Nat) (state : EdgeLabelling) : Bool :=
  (indices K 0).any (fun i => labellingsAgreeOnB (centralLowerFaceIds 0) state (stateAt K 0 i))

def prefixObservable (K : Nat) : CentralPhysicalUnitObservable where
  value state := if prefixB K state then 1 else 0
  nonnegative := fun state => by cases prefixB K state <;> decide
  le_one := fun state => by cases prefixB K state <;> decide

private theorem match_unique (K : Nat) (state : EdgeLabelling) {i j : Nat}
    (hi : i ∈ indices K 0) (hj : j ∈ indices K 0)
    (hmi : labellingsAgreeOnB (centralLowerFaceIds 0) state (stateAt K 0 i) = true)
    (hmj : labellingsAgreeOnB (centralLowerFaceIds 0) state (stateAt K 0 j) = true) : i = j := by
  have hil := centralPhysicalFiniteVacuumSectorIndex_lt anchorCoupling (by decide) K 0 hi
  have hjl := centralPhysicalFiniteVacuumSectorIndex_lt anchorCoupling (by decide) K 0 hj
  have hbi := (mem_centralPositiveHalfStates_iff.mp
    (centralPhysicalFiniteStateAt_mem_positive anchorCoupling (by decide) K 0 hil)).1
  have hbj := (mem_centralPositiveHalfStates_iff.mp
    (centralPhysicalFiniteStateAt_mem_positive anchorCoupling (by decide) K 0 hjl)).1
  apply centralPhysicalFiniteStateAt_injective_of_lt hil hjl
  apply eq_of_labellingsAgreeOnB_of_bounded hbi hbj
  apply (labellingsAgreeOnB_true_iff _ _ _).mpr
  intro face hf
  exact ((labellingsAgreeOnB_true_iff _ _ _).mp hmi face hf).symm.trans
    ((labellingsAgreeOnB_true_iff _ _ _).mp hmj face hf)

private theorem unique_indicator_sum {A : Type} (test : A → Bool) : ∀ items : List A,
    items.Nodup →
    (∀ a, a ∈ items → ∀ b, b ∈ items → test a = true → test b = true → a = b) →
    listQSum (fun a => if test a then (1 : Q') else 0) items ≈
      (if items.any test then 1 else 0)
  | [], _, _ => Q'.eqv_refl 0
  | a :: rest, hnodup, hunique => by
      have hn := List.nodup_cons.mp hnodup
      cases ha : test a with
      | false =>
          simp only [listQSum, List.any_cons, ha, Bool.false_or, Bool.false_eq_true, if_false]
          exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
            (unique_indicator_sum test rest hn.2 (fun b hb c hc =>
              hunique b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)))
      | true =>
          have hz : listQSum (fun b => if test b then (1 : Q') else 0) rest ≈ 0 := by
            refine Q'.eqv_trans _ (listQSum (fun _ : A => (0 : Q')) rest) _ ?_ (listQSum_zero rest)
            apply listQSum_congr_on
            intro b hb
            have hfalse : test b = false := by
              cases htest : test b with
              | false => rfl
              | true =>
                  have heq := hunique a List.mem_cons_self b (List.mem_cons_of_mem a hb) ha htest
                  exact False.elim (hn.1 (heq ▸ hb))
            rw [hfalse]
            exact Q'.eqv_refl 0
          simp only [listQSum, List.any_cons, ha, Bool.true_or, if_true]
          exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))

/-- The growing cylinder sum is still a unit indicator, globally. -/
theorem sectorPrefix_value (K : Nat) (state : EdgeLabelling) :
    (sectorPrefix K).toLinearObservable.value state ≈ (prefixObservable K).value state := by
  refine Q'.eqv_trans _ _ _ (centralPhysicalStateCylinderLinearCombination_value
    0 (stateAt K 0) (fun _ => 1) state (indices K 0)) ?_
  exact unique_indicator_sum _ _
    (centralPhysicalFiniteVacuumSectorIndices_nodup anchorCoupling (by decide) K 0)
    (fun i hi j hj => match_unique K state hi hj)

theorem prefixB_iff_finiteSector (K : Nat) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0) :
    prefixB K state = true ↔
      state ∈ centralPhysicalFiniteVacuumSectorStates anchorCoupling (by decide) K 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, hmatch⟩ := List.any_eq_true.mp h
    have hsector := centralPhysicalFiniteVacuumSectorState_mem_of_index
      anchorCoupling (by decide) K 0 hi rfl
    have hbounded := centralPhysicalFiniteVacuumSectorState_mem_halfStates
      anchorCoupling (by decide) K 0 hsector
    have heq := eq_of_labellingsAgreeOnB_of_bounded hs hbounded hmatch
    exact heq ▸ hsector
  · intro h
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
    apply List.any_eq_true.mpr
    refine ⟨i, hi, ?_⟩
    rw [heq]
    exact labellingsAgreeOnB_self _ _

theorem prefixB_eq_sectorB (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0) : prefixB K state = cubeSectorB state := by
  have hiff := (prefixB_iff_finiteSector K state hs).trans
    (cubeSectorB_iff_finiteSector (w := anchorCoupling) (by decide) K hK state hs).symm
  cases hp : prefixB K state <;> cases hc : cubeSectorB state <;> simp_all

/-- Exact agreement on the retained core; the later tail proof can use the
fixed envelope one, independent of the prefix's number of states. -/
theorem sectorPrefix_value_on_core (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0) :
    (sectorPrefix K).toLinearObservable.value state ≈ cubeSectorIndicator state := by
  have h := sectorPrefix_value K state
  change (sectorPrefix K).toLinearObservable.value state ≈ (if prefixB K state then 1 else 0) at h
  rw [prefixB_eq_sectorB K hK state hs] at h
  exact h

end YMGap.Continuum.BF4PhysicalCubeSectorPrefix

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.sectorPrefix
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.prefixB
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.prefixObservable
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.sectorPrefix_value
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.prefixB_iff_finiteSector
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.prefixB_eq_sectorB
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorPrefix.sectorPrefix_value_on_core
