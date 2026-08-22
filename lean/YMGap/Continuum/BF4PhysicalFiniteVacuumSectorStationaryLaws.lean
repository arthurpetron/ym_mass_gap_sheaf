/-
# Stationary row laws on every finite BF4 vacuum sector

The canonical vacuum component is closed under the physical reflected kernel,
but the finite Poincare argument needs the resulting restricted row law in
exact rational form.  This module proves that the normalized joint kernel,
summed only over the canonical component, has row mass equal to the genuine
physical stationary weight.

The proof first recodes the complete positive-row carrier by finite indices.
Filtering to the root component loses only entries already proved to vanish by
component closure.  A small constructive reordering lemma identifies the
root-component list with the corresponding filtered carrier without assuming
that their enumerations have the same order.

The total stationary mass of the component is also strictly positive because
it contains the vacuum index and every retained weight is strictly positive.
These are finite stationary laws, not yet a quantitative Poincare estimate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive finite-list sum helpers -/

private theorem listQSum_filter_eq_of_zero_local
    {State : Type} (value : State → Q') (predicate : State → Bool) :
    ∀ states : List State,
      (∀ state, state ∈ states → predicate state = false → value state ≈ 0) →
      listQSum value (states.filter predicate) ≈ listQSum value states
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hhead : predicate head with
      | false =>
          simp only [List.filter_cons, hhead, Bool.false_eq_true,
            if_false, listQSum]
          have hz := hzero head List.mem_cons_self hhead
          have ht := listQSum_filter_eq_of_zero_local value predicate tail
            (fun state hstate =>
              hzero state (List.mem_cons_of_mem head hstate))
          exact Q'.eqv_trans _ _ _ ht
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr' (Q'.eqv_symm hz) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hhead, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local value predicate tail
              (fun state hstate =>
                hzero state (List.mem_cons_of_mem head hstate)))

private theorem range_nodup_local (bound : Nat) :
    (List.range bound).Nodup := by
  induction bound with
  | zero => exact List.nodup_nil
  | succ bound ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

private theorem listQSum_eqv_of_nodup_same_members_nonnegative
    {State : Type} [DecidableEq State]
    (value : State → Q') (left right : List State)
    (hleft : left.Nodup) (hright : right.Nodup)
    (hmembers : ∀ state, state ∈ left ↔ state ∈ right)
    (hnonnegative : ∀ state, (0 : Q') ≤ value state) :
    listQSum value left ≈ listQSum value right := by
  have hleftRight : listQSum value left ≤ listQSum value right :=
    listQSum_le_of_injective left right value value (fun state => state)
      hleft
      (fun state hstate => (hmembers state).mp hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  have hrightLeft : listQSum value right ≤ listQSum value left :=
    listQSum_le_of_injective right left value value (fun state => state)
      hright
      (fun state hstate => (hmembers state).mpr hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  exact Int.le_antisymm hleftRight hrightLeft

private theorem listQSum_member_le_nonnegative_local
    {State : Type} (value : State → Q')
    (hnonnegative : ∀ state, (0 : Q') ≤ value state) :
    ∀ (states : List State) {state : State},
      state ∈ states → value state ≤ listQSum value states
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, state, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst state
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hnonnegative item))
      · have ih := listQSum_member_le_nonnegative_local
          value hnonnegative tail htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg _ _ (hnonnegative head))
            (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
        exact Q'.le_trans' _ _ _ ih htailLe

/-! ## 2. The complete indexed row has the physical marginal mass -/

/-- Summing an indexed normalized-joint row over the complete positive-row
carrier gives its exact physical stationary marginal. -/
theorem centralPhysicalFiniteKernel_fullRowSum_eqv_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source <
      centralPhysicalFiniteCarrierSize w hw cutoff half) :
    listQSum
        (centralPhysicalFiniteKernel w hw cutoff half source)
        (List.range
          (centralPhysicalFiniteCarrierSize w hw cutoff half)) ≈
      centralPhysicalFiniteWeight w hw cutoff half source := by
  let states := centralPositiveHalfStates w hw cutoff half
  let sourceState :=
    centralPhysicalFiniteStateAt w hw cutoff half source
  have hsourcePositive : sourceState ∈ states := by
    exact centralPhysicalFiniteStateAt_mem_positive
      w hw cutoff half hsource
  have hsourceHalf : sourceState ∈ centralHalfStates cutoff half :=
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
  have hfilter :
      listQSum
          (centralNormalizedPhysicalReflectedKernel
            w hw cutoff half sourceState)
          states ≈
        listQSum
          (centralNormalizedPhysicalReflectedKernel
            w hw cutoff half sourceState)
          (centralHalfStates cutoff half) := by
    unfold states centralPositiveHalfStates
    apply listQSum_filter_eq_of_zero_local
    intro target htarget hfalse
    apply centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
      hsourceHalf htarget
    simpa only [decide_eq_false_iff_not] using hfalse
  change
    listQSum
        (fun target =>
          centralNormalizedPhysicalReflectedKernel
            w hw cutoff half sourceState
            (finiteListStateAt states zeroEdgeLabelling target))
        (List.range states.length) ≈
      centralPhysicalRowMarginal w hw cutoff half sourceState
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states zeroEdgeLabelling
        (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half sourceState)))
    hfilter

/-! ## 3. Restriction to the closed canonical component -/

private theorem centralPhysicalFiniteKernel_eqv_zero_of_sector_complement
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteKernel w hw cutoff half source target ≈ 0 := by
  have hraw := centralPhysicalFiniteVacuumSector_rowClosed
    w hw cutoff half hsource htarget houtside
  unfold centralPhysicalFiniteRawKernel at hraw
  unfold centralPhysicalFiniteKernel
    centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.eqv_trans _
    (0 * Q'.recipPos
      (slabParametricKPhysicalPartition
        w cutoff (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw cutoff (centralExtent half))) _
    (Q'.mul_eqv_congr_right _ _ _ hraw)
    (Q'.zero_mul_eqv _)

/-- Exact stationarity of every row after restriction to the canonical vacuum
component.  The component's joint-kernel row mass is its genuine physical
stationary weight. -/
theorem centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    listQSum
        (centralPhysicalFiniteKernel w hw cutoff half source)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) ≈
      centralPhysicalFiniteWeight w hw cutoff half source := by
  let sector :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let full := List.range
    (centralPhysicalFiniteCarrierSize w hw cutoff half)
  let inside := full.filter (fun index => decide (index ∈ sector))
  let value := centralPhysicalFiniteKernel w hw cutoff half source
  have hsectorInside : listQSum value sector ≈ listQSum value inside := by
    apply listQSum_eqv_of_nodup_same_members_nonnegative
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw cutoff half
    · exact List.filter_sublist.nodup
        (range_nodup_local
          (centralPhysicalFiniteCarrierSize w hw cutoff half))
    · intro index
      constructor
      · intro hindex
        apply List.mem_filter.mpr
        exact ⟨List.mem_range.mpr
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw cutoff half hindex), decide_eq_true hindex⟩
      · intro hindex
        have hparts := List.mem_filter.mp hindex
        simpa only [decide_eq_true_eq] using hparts.2
    · intro index
      unfold value centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        hw cutoff half _ _
  have hinsideFull : listQSum value inside ≈ listQSum value full := by
    unfold inside
    apply listQSum_filter_eq_of_zero_local
    intro target htarget hfalse
    apply centralPhysicalFiniteKernel_eqv_zero_of_sector_complement
      hsource (List.mem_range.mp htarget)
    simpa only [decide_eq_false_iff_not] using hfalse
  exact Q'.eqv_trans _ _ _ hsectorInside
    (Q'.eqv_trans _ _ _ hinsideFull
      (centralPhysicalFiniteKernel_fullRowSum_eqv_weight
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hsource)))

/-- The canonical component has strictly positive total stationary mass. -/
theorem centralPhysicalFiniteVacuumSectorWeightSum_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      listQSum
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) := by
  let sector :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  have hzero : 0 ∈ sector :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w hw cutoff half
  have hrootPos : (0 : Q') <
      centralPhysicalFiniteWeight w hw cutoff half 0 :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hzero
  have hrootLe :
      centralPhysicalFiniteWeight w hw cutoff half 0 ≤
        listQSum
          (centralPhysicalFiniteWeight w hw cutoff half) sector :=
    listQSum_member_le_nonnegative_local
      (centralPhysicalFiniteWeight w hw cutoff half)
      (fun index => centralPhysicalRowMarginal_nonnegative
        hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half index))
      sector hzero
  exact Q'.pos_of_lt_of_le hrootPos hrootLe

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws.centralPhysicalFiniteKernel_fullRowSum_eqv_weight
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws.centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws.centralPhysicalFiniteVacuumSectorWeightSum_pos
