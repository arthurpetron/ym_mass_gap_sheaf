/-
# Conditioning commutes with BF4 density powers on the vacuum component

For a closed component `S` of stationary mass `m`, the conditioned weight and
density are

    pi_S(x) = pi(x) / m,        k_S(x,y) = m * k(x,y).

The reciprocal factors cancel at every intermediate state.  If the original
density has no transition from `S` to its complement, then every positive-
length weighted density power satisfies

    k_S^[n](x,y) = m * k^[n](x,y)             (x,y in S).

This file proves that identity first for arbitrary finite lists and then for
the actual graph-defined BF4 vacuum component.  It is the exact algebra needed
to restrict a future physical time-slice factorization to the selected sector
without accumulating a component-mass defect at each convolution.

The theorem does not construct a strict local contraction or a density-power
factorization of the physical slab.  No thermodynamic or continuum limit is
constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
import YMGap.Continuum.BF4StationaryDensityBufferSplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive finite-list restriction helpers -/

private theorem permOfNodupMemIff_local {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := permOfNodupMemIff_local tail (before ++ after)
        hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
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
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem listQSum_filter_eq_of_zero_local
    {State : Type} (value : State → Q') (predicate : State → Bool) :
    ∀ states : List State,
      (∀ state, state ∈ states → predicate state = false →
        value state ≈ 0) →
      listQSum value (states.filter predicate) ≈
        listQSum value states
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

/-- Deleting a closed-component complement from a finite sum changes
nothing.  The component list may have a different order from the full-list
filter. -/
theorem listQSum_sector_eq_full_of_zero
    {State : Type} [DecidableEq State]
    (full sector : List State) (value : State → Q')
    (hfullNodup : full.Nodup) (hsectorNodup : sector.Nodup)
    (hsubset : ∀ state, state ∈ sector → state ∈ full)
    (hzero : ∀ state, state ∈ full → state ∉ sector →
      value state ≈ 0) :
    listQSum value sector ≈ listQSum value full := by
  let inside := full.filter (fun state => decide (state ∈ sector))
  have hinsideNodup : inside.Nodup :=
    List.filter_sublist.nodup hfullNodup
  have hmembers : ∀ state, state ∈ sector ↔ state ∈ inside := by
    intro state
    constructor
    · intro hstate
      exact List.mem_filter.mpr
        ⟨hsubset state hstate, decide_eq_true hstate⟩
    · intro hstate
      have hparts := List.mem_filter.mp hstate
      simpa only [decide_eq_true_eq] using hparts.2
  have hperm : sector.Perm inside :=
    permOfNodupMemIff_local sector inside
      hsectorNodup hinsideNodup hmembers
  refine Q'.eqv_trans _ (listQSum value inside) _
    (listQSum_perm_local value hperm) ?_
  unfold inside
  apply listQSum_filter_eq_of_zero_local
  intro state hstate hfalse
  apply hzero state hstate
  simpa only [decide_eq_false_iff_not] using hfalse

/-! ## 2. Generic conditioning-power theorem -/

/-- Positive-mass conditioning commutes exactly with every positive-length
weighted density power on a closed finite component. -/
theorem finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower
    {State : Type} [DecidableEq State]
    (full sector : List State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q')
    (fullDensity conditionedDensity : State → State → Q')
    (hfullNodup : full.Nodup) (hsectorNodup : sector.Nodup)
    (hsubset : ∀ state, state ∈ sector → state ∈ full)
    (hclosed : ∀ source target,
      source ∈ sector → target ∈ full → target ∉ sector →
        fullDensity source target ≈ 0)
    (hscale : ∀ source target,
      source ∈ sector → target ∈ sector →
        conditionedDensity source target ≈
          mass * fullDensity source target) :
    ∀ steps source target,
      source ∈ sector → target ∈ sector →
        finiteWeightedDensityPower sector
            (finiteCarrierMassNormalizedWeight mass mass_pos weight)
            conditionedDensity steps source target ≈
          mass * finiteWeightedDensityPower full weight fullDensity
            steps source target
  | 0, source, target, hsource, htarget =>
      hscale source target hsource htarget
  | steps + 1, source, target, hsource, htarget => by
      let normalizedWeight :=
        finiteCarrierMassNormalizedWeight mass mass_pos weight
      let sectorPower :=
        finiteWeightedDensityPower sector normalizedWeight
          conditionedDensity steps
      let fullPower :=
        finiteWeightedDensityPower full weight fullDensity steps
      let value : State → Q' := fun middle =>
        (weight middle * fullDensity source middle) *
          fullPower middle target
      have hterm : ∀ middle, middle ∈ sector →
          (normalizedWeight middle * conditionedDensity source middle) *
              sectorPower middle target ≈
            mass * value middle := by
        intro middle hmiddle
        have hleft := hscale source middle hsource hmiddle
        have hright :=
          finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower
            full sector mass mass_pos weight fullDensity conditionedDensity
            hfullNodup hsectorNodup hsubset hclosed hscale
            steps middle target hmiddle htarget
        have hweightMass : normalizedWeight middle * mass ≈
            weight middle :=
          finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
            mass mass_pos weight middle
        refine Q'.eqv_trans _
          ((normalizedWeight middle *
              (mass * fullDensity source middle)) *
            (mass * fullPower middle target)) _ ?_ ?_
        · refine Q'.eqv_trans _
            ((normalizedWeight middle *
                (mass * fullDensity source middle)) *
              sectorPower middle target) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_left _ _ _ hleft)
          · exact Q'.mul_eqv_congr_left _ _ _ hright
        refine Q'.eqv_trans _
          (((normalizedWeight middle * mass) *
              fullDensity source middle) *
            (mass * fullPower middle target)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (normalizedWeight middle) mass
                (fullDensity source middle)))
        refine Q'.eqv_trans _
          ((weight middle * fullDensity source middle) *
            (mass * fullPower middle target)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hweightMass)
        change
          (weight middle * fullDensity source middle) *
              (mass * fullPower middle target) ≈
            mass *
              ((weight middle * fullDensity source middle) *
                fullPower middle target)
        let left := weight middle * fullDensity source middle
        let right := fullPower middle target
        refine Q'.eqv_trans _ ((left * mass) * right) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv left mass right)) ?_
        refine Q'.eqv_trans _ ((mass * left) * right) _ ?_
          (Q'.mul_assoc_eqv mass left right)
        exact Q'.mul_eqv_congr_right _ _ right
          (Q'.mul_comm_eqv left mass)
      have hsectorSum :
          listQSum
              (fun middle =>
                (normalizedWeight middle *
                    conditionedDensity source middle) *
                  sectorPower middle target)
              sector ≈
            mass * listQSum value sector := by
        refine Q'.eqv_trans _
          (listQSum (fun middle => mass * value middle) sector) _ ?_ ?_
        · apply listQSum_congr_on
          exact hterm
        · exact listQSum_mul_left mass value sector
      have hvalueZero : ∀ middle,
          middle ∈ full → middle ∉ sector →
            value middle ≈ 0 := by
        intro middle hmiddleFull hmiddleOutside
        unfold value
        refine Q'.eqv_trans _
          ((weight middle * 0) * fullPower middle target) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (hclosed source middle hsource hmiddleFull hmiddleOutside))
        exact Q'.eqv_trans _ (0 * fullPower middle target) _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
          (Q'.zero_mul_eqv _)
      have hrestrict : listQSum value sector ≈ listQSum value full :=
        listQSum_sector_eq_full_of_zero full sector value
          hfullNodup hsectorNodup hsubset hvalueZero
      unfold finiteWeightedDensityPower
      unfold finiteWeightedDensityCompose
      exact Q'.eqv_trans _ _ _ hsectorSum
        (Q'.mul_eqv_congr_left mass _ _ hrestrict)

/-! ## 3. The actual finite BF4 vacuum component -/

/-- The full physical conditional density expressed on the complete finite
index carrier. -/
def centralPhysicalFiniteFullDensity
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source target : Nat) : Q' :=
  centralPhysicalConditionalDensity w hw cutoff half
    (centralPhysicalFiniteStateAt w hw cutoff half source)
    (centralPhysicalFiniteStateAt w hw cutoff half target)

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

/-- The full indexed physical density has no transition from the canonical
vacuum component to its complement. -/
theorem centralPhysicalFiniteFullDensity_eqv_zero_of_sector_complement
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteFullDensity w hw cutoff half source target ≈
      0 := by
  have htargetLt : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half :=
    List.mem_range.mp htarget
  have hraw := centralPhysicalFiniteVacuumSector_rowClosed
    w hw cutoff half hsource htargetLt houtside
  have hsourcePos :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have htargetState := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half htargetLt
  have htargetPos := (mem_centralPositiveHalfStates_iff.mp htargetState).2
  change (0 : Q') < centralPhysicalRowMarginal w hw cutoff half
      (centralPhysicalFiniteStateAt w hw cutoff half source) at hsourcePos
  unfold centralPhysicalFiniteFullDensity
  rw [centralPhysicalConditionalDensity_eq_divPos htargetPos]
  rw [centralPhysicalConditionalKernel_eq_divPos hsourcePos]
  have hnormalized :
      centralNormalizedPhysicalReflectedKernel w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source)
          (centralPhysicalFiniteStateAt w hw cutoff half target) ≈ 0 := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    unfold centralPhysicalFiniteRawKernel at hraw
    refine Q'.eqv_trans _
      (0 * Q'.recipPos
        (slabParametricKPhysicalPartition
          w cutoff (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw cutoff (centralExtent half))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hraw
    · exact Q'.zero_mul_eqv _
  have hconditional :
      Q'.divPos
          (centralNormalizedPhysicalReflectedKernel w hw cutoff half
            (centralPhysicalFiniteStateAt w hw cutoff half source)
            (centralPhysicalFiniteStateAt w hw cutoff half target))
          (centralPhysicalRowMarginal w hw cutoff half
            (centralPhysicalFiniteStateAt w hw cutoff half source))
          hsourcePos ≈ 0 := by
    unfold Q'.divPos
    refine Q'.eqv_trans _
      (0 * Q'.recipPos
        (centralPhysicalRowMarginal w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source))
        hsourcePos) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hnormalized
    · exact Q'.zero_mul_eqv _
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (centralPhysicalRowMarginal w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half target))
      htargetPos) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hconditional
  · exact Q'.zero_mul_eqv _

/-- **Actual BF4 conditioning-power identity.**  On the canonical vacuum
component, every positive-length conditioned density power is exactly the
component mass times the corresponding full indexed physical density power.
-/
theorem centralPhysicalFiniteVacuumSectorConditionedDensityPower_eqv_mass_mul_fullPower
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half steps source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedDensityPower
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half)
        steps source target ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        finiteWeightedDensityPower
          (centralPhysicalFiniteIndexCarrier w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half)
          (centralPhysicalFiniteFullDensity w hw cutoff half)
          steps source target := by
  apply finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower
    (centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteFullDensity w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
      w hw cutoff half)
  · exact range_nodup_local _
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw cutoff half
  · intro state hstate
    exact rootComponent_subset
      (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
      (zero_mem_centralPhysicalFiniteIndexCarrier w hw cutoff half) hstate
  · intro first middle hfirst hmiddle houtside
    exact centralPhysicalFiniteFullDensity_eqv_zero_of_sector_complement
      hfirst hmiddle houtside
  · intro first last hfirst hlast
    exact
      centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
        hfirst hlast
  · exact hsource
  · exact htarget

end YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower.listQSum_sector_eq_full_of_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower.finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower.centralPhysicalFiniteFullDensity_eqv_zero_of_sector_complement
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower.centralPhysicalFiniteVacuumSectorConditionedDensityPower_eqv_mass_mul_fullPower
