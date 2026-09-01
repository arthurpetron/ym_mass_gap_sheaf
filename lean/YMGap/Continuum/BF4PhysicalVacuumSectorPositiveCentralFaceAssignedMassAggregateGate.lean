/-
# Aggregate feasibility gate for the assigned central-face mass

The assigned-spin observable branch compares the stationary mass of every
repaired face-label fiber with the stationary weight of one displayed spin
cube.  Before trying to prove that comparison uniformly in the cutoff, this
module records its aggregate necessary condition.

At every positive cutoff, the assigned observables over spins `1,...,K`
partition the displayed non-vacuum event: failure to agree with the vacuum on
the central lower face.  Their stationary means therefore sum exactly to the
stationary mass of that event.  Meanwhile the comparison weights sum exactly
to the already defined excited spin-cube ray mass.  Consequently either the
sharp finite ratio ceiling or any cofinal ratio producer bounds the displayed
non-vacuum mass by the same multiple of the ray mass.

This is a feasibility gate, not a proof that a cutoff-independent ratio exists.
In particular, no lower bound on the displayed non-vacuum mass, decay of the
ray mass, congestion certificate, finite gap, physical scaling, continuum
theory, or Clay conclusion is proved here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Nat := Nat.decEq

/-! ## 1. Pointwise partition of the displayed non-vacuum event -/

/-- The event that the state is not the displayed vacuum on the central lower
face used by the assigned-spin routing.  On the bounded physical carrier this
is the ordinary non-vacuum event; the present module only needs the displayed
form of the predicate. -/
def positiveCentralFaceDisplayedNonvacuumIndicator
    (state : EdgeLabelling) : Q' :=
  if labellingsAgreeOnB
      (centralLowerFaceIds 0) state zeroEdgeLabelling then 0 else 1

private theorem listQSum_single_indicator_eqv
    {A : Type} [DecidableEq A]
    (selected : A) (value : A → Q') :
    ∀ items : List A, items.Nodup → selected ∈ items →
      listQSum
          (fun item => if item = selected then value item else 0)
          items ≈ value selected
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : head = selected
      · subst head
        have hselectedTail : selected ∉ tail := hparts.1
        have htailZero : listQSum
            (fun item => if item = selected then value item else 0)
            tail ≈ 0 := by
          exact Q'.eqv_trans _
            (listQSum (fun _ => (0 : Q')) tail) _
            (listQSum_congr_on _ _ tail (fun item hitem => by
              rw [if_neg]
              exact Q'.eqv_refl 0
              intro heq
              exact hselectedTail (heq ▸ hitem)))
            (listQSum_zero tail)
        simp only [listQSum]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have htail : selected ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left
            (fun heq => hhead heq.symm)
        simp only [listQSum, if_neg hhead]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left 0 _ _
            (listQSum_single_indicator_eqv
              selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

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

private theorem listQSum_succ_indicator_eqv_one
    {K value : Nat} (hvaluePos : 0 < value) (hvalueLe : value ≤ K) :
    listQSum
        (fun offset => if value = offset + 1 then (1 : Q') else 0)
        (List.range K) ≈ 1 := by
  let selected := value - 1
  have hselected : selected < K := by
    unfold selected
    exact Nat.lt_of_lt_of_le
      (Nat.sub_lt hvaluePos (by decide)) hvalueLe
  refine Q'.eqv_trans _
    (listQSum
      (fun offset => if offset = selected then (1 : Q') else 0)
      (List.range K)) _ ?_ ?_
  · apply listQSum_congr_on
    intro offset _hoffset
    by_cases hvalue : value = offset + 1
    · have hoffset : offset = selected := by
        unfold selected
        rw [hvalue]
        exact (Nat.add_sub_cancel offset 1).symm
      rw [if_pos hvalue, if_pos hoffset]
      exact Q'.eqv_refl 1
    · have hoffset : offset ≠ selected := by
        intro heq
        unfold selected at heq
        apply hvalue
        rw [heq]
        exact (Nat.sub_add_cancel hvaluePos).symm
      rw [if_neg hvalue, if_neg hoffset]
      exact Q'.eqv_refl 0
  · exact listQSum_single_indicator_eqv
      selected (fun _ => (1 : Q')) (List.range K)
      (rangeNodupLocal K) (List.mem_range.mpr hselected)

/-- The repaired spin labels `1,...,K` form a pointwise partition of the
displayed non-vacuum event. -/
theorem positiveCentralFaceAssignedIndicator_sum_eqv_nonvacuum
    {K : Nat} (hK : 1 ≤ K) (state : EdgeLabelling) :
    listQSum
        (fun offset =>
          positiveCentralFaceAssignedIndicator K (offset + 1) state)
        (List.range K) ≈
      positiveCentralFaceDisplayedNonvacuumIndicator state := by
  unfold positiveCentralFaceAssignedIndicator
    positiveCentralFaceDisplayedNonvacuumIndicator
  cases hagree : labellingsAgreeOnB
      (centralLowerFaceIds 0) state zeroEdgeLabelling
  · simp only [Bool.false_eq_true, if_false]
    exact listQSum_succ_indicator_eqv_one
      positiveCentralFaceTerminalSpin_pos
      (positiveCentralFaceTerminalSpin_le hK)
  · simp only [if_true]
    exact listQSum_zero (List.range K)

/-! ## 2. Exact stationary-mass partition -/

/-- Sum of the stationary means of all repaired assigned-spin observables at
one finite cutoff. -/
def positiveCentralFaceAssignedStationaryMassSum
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum
    (fun offset =>
      centralPhysicalStationaryMean w hw K 0
        (positiveCentralFaceAssignedUnitObservable
          K (offset + 1)).value)
    (List.range K)

/-- Stationary mass of failure to agree with the vacuum on the displayed
central lower face. -/
def positiveCentralFaceDisplayedNonvacuumStationaryMass
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  centralPhysicalStationaryMean w hw K 0
    positiveCentralFaceDisplayedNonvacuumIndicator

/-- Summing the assigned-spin stationary means recovers exactly the displayed
non-vacuum stationary mass. -/
theorem positiveCentralFaceAssignedStationaryMassSum_eqv_nonvacuum
    (w : Q') (hw : (0 : Q') ≤ w) {K : Nat} (hK : 1 ≤ K) :
    positiveCentralFaceAssignedStationaryMassSum w hw K ≈
      positiveCentralFaceDisplayedNonvacuumStationaryMass w hw K := by
  let states := centralPositiveHalfStates w hw K 0
  let marginal := centralPhysicalRowMarginal w hw K 0
  unfold positiveCentralFaceAssignedStationaryMassSum
    positiveCentralFaceDisplayedNonvacuumStationaryMass
    centralPhysicalStationaryMean
  change listQSum
      (fun offset => listQSum
        (fun state => marginal state *
          positiveCentralFaceAssignedIndicator K (offset + 1) state)
        states)
      (List.range K) ≈
    listQSum
      (fun state => marginal state *
        positiveCentralFaceDisplayedNonvacuumIndicator state)
      states
  refine Q'.eqv_trans _
    (listQSum
      (fun state => listQSum
        (fun offset => marginal state *
          positiveCentralFaceAssignedIndicator K (offset + 1) state)
        (List.range K))
      states) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_swap
      (fun offset state => marginal state *
        positiveCentralFaceAssignedIndicator K (offset + 1) state)
      (List.range K) states)
  · apply listQSum_congr_on
    intro state _hstate
    refine Q'.eqv_trans _
      (marginal state * listQSum
        (fun offset =>
          positiveCentralFaceAssignedIndicator K (offset + 1) state)
        (List.range K)) _ ?_ ?_
    · exact listQSum_mul_left
        (marginal state)
        (fun offset =>
          positiveCentralFaceAssignedIndicator K (offset + 1) state)
        (List.range K)
    · exact Q'.mul_eqv_congr_left (marginal state) _ _
        (positiveCentralFaceAssignedIndicator_sum_eqv_nonvacuum hK state)

/-! ## 3. Identification with the actual vacuum-mass complement -/

/-- The complementary displayed-vacuum point indicator. -/
def positiveCentralFaceDisplayedVacuumIndicator
    (state : EdgeLabelling) : Q' :=
  if labellingsAgreeOnB
      (centralLowerFaceIds 0) state zeroEdgeLabelling then 1 else 0

private theorem positiveCentralFaceDisplayedIndicators_add_eqv_one
    (state : EdgeLabelling) :
    positiveCentralFaceDisplayedNonvacuumIndicator state +
        positiveCentralFaceDisplayedVacuumIndicator state ≈ 1 := by
  unfold positiveCentralFaceDisplayedNonvacuumIndicator
    positiveCentralFaceDisplayedVacuumIndicator
  cases labellingsAgreeOnB
      (centralLowerFaceIds 0) state zeroEdgeLabelling
  · exact Q'.eqv_of_eq (Q'.add_zero' 1)
  · exact Q'.eqv_of_eq (Q'.zero_add' 1)

private theorem zeroEdgeLabelling_mem_bounded_local
    (K : Nat) :
    zeroEdgeLabelling ∈
      boundedEdgeLabellings K (centralLowerFaceIds 0) := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    simp [zeroEdgeLabelling]
  · intro _ _
    rfl

private theorem listQSum_displayedVacuum_zero_of_not_mem
    (K : Nat) (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ boundedEdgeLabellings K (centralLowerFaceIds 0)) →
      zeroEdgeLabelling ∉ items →
      listQSum
          (fun item =>
            value item *
              positiveCentralFaceDisplayedVacuumIndicator item)
          items ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hcarrier, hnot => by
      have hheadBounded := hcarrier head List.mem_cons_self
      have htailCarrier : ∀ item, item ∈ tail →
          item ∈ boundedEdgeLabellings K (centralLowerFaceIds 0) :=
        fun item hitem =>
          hcarrier item (List.mem_cons_of_mem head hitem)
      have hzeroTail : zeroEdgeLabelling ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hagreeNe : labellingsAgreeOnB
          (centralLowerFaceIds 0) head zeroEdgeLabelling ≠ true := by
        intro hagree
        have hsame := eq_of_labellingsAgreeOnB_of_bounded
          hheadBounded (zeroEdgeLabelling_mem_bounded_local K) hagree
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum]
      unfold positiveCentralFaceDisplayedVacuumIndicator
      rw [if_neg hagreeNe]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_zero_eqv (value head))
          (listQSum_displayedVacuum_zero_of_not_mem
            K value tail htailCarrier hzeroTail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_displayedVacuum_of_mem_nodup
    (K : Nat) (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ boundedEdgeLabellings K (centralLowerFaceIds 0)) →
      items.Nodup → zeroEdgeLabelling ∈ items →
      listQSum
          (fun item =>
            value item *
              positiveCentralFaceDisplayedVacuumIndicator item)
          items ≈ value zeroEdgeLabelling
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hcarrier, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        have hself := labellingsAgreeOnB_self
          (centralLowerFaceIds 0) zeroEdgeLabelling
        simp only [listQSum]
        unfold positiveCentralFaceDisplayedVacuumIndicator
        rw [if_pos hself]
        exact Q'.eqv_trans _ (value zeroEdgeLabelling + 0) _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv (value zeroEdgeLabelling))
            (listQSum_displayedVacuum_zero_of_not_mem
              K value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem zeroEdgeLabelling hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value zeroEdgeLabelling)))
      · have hheadBounded := hcarrier head List.mem_cons_self
        have hagreeNe : labellingsAgreeOnB
            (centralLowerFaceIds 0) head zeroEdgeLabelling ≠ true := by
          intro hagree
          have hsame := eq_of_labellingsAgreeOnB_of_bounded
            hheadBounded (zeroEdgeLabelling_mem_bounded_local K) hagree
          subst head
          exact hparts.1 htail
        simp only [listQSum]
        unfold positiveCentralFaceDisplayedVacuumIndicator
        rw [if_neg hagreeNe]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv (value head))
            (listQSum_displayedVacuum_of_mem_nodup
              K value tail
              (fun item hitem =>
                hcarrier item (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq
            (Q'.zero_add' (value zeroEdgeLabelling)))

private theorem centralPhysicalStationaryMean_displayedVacuum
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralPhysicalStationaryMean w hw K 0
        positiveCentralFaceDisplayedVacuumIndicator ≈
      centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling := by
  unfold centralPhysicalStationaryMean
  exact listQSum_displayedVacuum_of_mem_nodup
    K (centralPhysicalRowMarginal w hw K 0)
    (centralPositiveHalfStates w hw K 0)
    (fun item hitem =>
      (mem_centralPositiveHalfStates_iff.mp hitem).1)
    (centralPositiveHalfStates_nodup w hw K 0)
    (zeroEdgeLabelling_mem_centralPositiveHalfStates hw K 0)

private theorem centralPhysicalStationaryMean_add_local
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (left right : EdgeLabelling → Q') :
    centralPhysicalStationaryMean
        w hw K 0 (fun state => left state + right state) ≈
      centralPhysicalStationaryMean w hw K 0 left +
        centralPhysicalStationaryMean w hw K 0 right := by
  let states := centralPositiveHalfStates w hw K 0
  let marginal := centralPhysicalRowMarginal w hw K 0
  unfold centralPhysicalStationaryMean
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        marginal state * left state + marginal state * right state)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _hstate
    exact Q'.mul_add_eqv
      (marginal state) (left state) (right state)
  · exact listQSum_add
      (fun state => marginal state * left state)
      (fun state => marginal state * right state)
      states

/-- The displayed non-vacuum stationary mass is exactly complementary to the
actual normalized physical vacuum row marginal. -/
theorem positiveCentralFaceDisplayedNonvacuumStationaryMass_add_vacuumMass_eqv_one
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    positiveCentralFaceDisplayedNonvacuumStationaryMass w hw K +
        centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling ≈
      1 := by
  refine Q'.eqv_trans _
    (positiveCentralFaceDisplayedNonvacuumStationaryMass w hw K +
      centralPhysicalStationaryMean w hw K 0
        positiveCentralFaceDisplayedVacuumIndicator) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.eqv_symm
        (centralPhysicalStationaryMean_displayedVacuum w hw K))) ?_
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean w hw K 0
      (fun state =>
        positiveCentralFaceDisplayedNonvacuumIndicator state +
          positiveCentralFaceDisplayedVacuumIndicator state)) _
    (Q'.eqv_symm
      (centralPhysicalStationaryMean_add_local
        w hw K positiveCentralFaceDisplayedNonvacuumIndicator
        positiveCentralFaceDisplayedVacuumIndicator)) ?_
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean w hw K 0 (fun _ => 1)) _ ?_ ?_
  · unfold centralPhysicalStationaryMean
    apply listQSum_congr_on
    intro state hstate
    exact Q'.mul_eqv_congr_left
      (centralPhysicalRowMarginal w hw K 0 state) _ _
      (positiveCentralFaceDisplayedIndicators_add_eqv_one state)
  · exact centralPhysicalStationaryMean_one w hw K 0

private theorem le_of_add_le_add_right_local
    {left right common : Q'}
    (hbound : left + common ≤ right + common) : left ≤ right := by
  have hshift := Q'.add_le_add_right
    (left + common) (right + common) (-common) hbound
  have hleft : (left + common) + (-common) ≈ left := by
    refine Q'.eqv_trans _ (left + (common + (-common))) _
      (Q'.add_assoc_eqv left common (-common)) ?_
    refine Q'.eqv_trans _ (left + 0) _
      (Q'.add_eqv_congr_left left _ _
        (Q'.add_neg_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' left)
  have hright : (right + common) + (-common) ≈ right := by
    refine Q'.eqv_trans _ (right + (common + (-common))) _
      (Q'.add_assoc_eqv right common (-common)) ?_
    refine Q'.eqv_trans _ (right + 0) _
      (Q'.add_eqv_congr_left right _ _
        (Q'.add_neg_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' right)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

/-- A `5/6` ceiling on the physical vacuum marginal forces at least `1/6`
stationary mass in the displayed non-vacuum complement. -/
theorem oneSixth_le_positiveCentralFaceDisplayedNonvacuumStationaryMass_of_vacuumMass_le_fiveSixths
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (hvacuum :
      centralPhysicalRowMarginal
          w hw K 0 zeroEdgeLabelling ≤
        Q'.mkPos 5 6 (by decide)) :
    Q'.mkPos 1 6 (by decide) ≤
      positiveCentralFaceDisplayedNonvacuumStationaryMass w hw K := by
  let nonvacuum :=
    positiveCentralFaceDisplayedNonvacuumStationaryMass w hw K
  let vacuum :=
    centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling
  have hfirst :
      Q'.mkPos 1 6 (by decide) + vacuum ≤
        Q'.mkPos 1 6 (by decide) + Q'.mkPos 5 6 (by decide) :=
    Q'.add_le_add_left (Q'.mkPos 1 6 (by decide))
      vacuum (Q'.mkPos 5 6 (by decide)) hvacuum
  have hsixths :
      Q'.mkPos 1 6 (by decide) + Q'.mkPos 5 6 (by decide) ≈ 1 := by
    decide
  have hcomplement : nonvacuum + vacuum ≈ 1 :=
    positiveCentralFaceDisplayedNonvacuumStationaryMass_add_vacuumMass_eqv_one
      w hw K
  have hpadded :
      Q'.mkPos 1 6 (by decide) + vacuum ≤
        nonvacuum + vacuum :=
    Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsixths)
        (Q'.ge_of_eqv hcomplement))
  exact le_of_add_le_add_right_local hpadded

/-! ## 4. Necessary aggregate bounds for the ratio route -/

private theorem listQSum_le_termwise
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_le_termwise left right tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

/-- The sharp finite ratio ceiling necessarily bounds the aggregate displayed
non-vacuum mass by the same multiple of the excited spin-cube ray mass. -/
theorem positiveCentralFaceDisplayedNonvacuumStationaryMass_le_finiteCeiling_mul_rayMass
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K) :
    positiveCentralFaceDisplayedNonvacuumStationaryMass
        w (Q'.le_of_lt hw) K ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K := by
  let mean := fun offset =>
    centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
      (positiveCentralFaceAssignedUnitObservable K (offset + 1)).value
  let weight := fun offset =>
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
  let ceiling := positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K
  have hsum : listQSum mean (List.range K) ≤
      listQSum (fun offset => ceiling * weight offset) (List.range K) := by
    apply listQSum_le_termwise
    intro offset hoffsetMem
    have hoffset := List.mem_range.mp hoffsetMem
    have hratio := positiveCentralFaceAssignedStationaryRatioAt_le_finiteCeiling
      hw hoffset
    have hweightNonnegative : (0 : Q') ≤ weight offset := by
      exact Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (weight offset)
      hratio hweightNonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (positiveCentralFaceAssignedStationaryRatioAt_mul_weight_eqv_mean
            hw hoffset)))
      hscaled
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (positiveCentralFaceAssignedStationaryMassSum_eqv_nonvacuum
          w (Q'.le_of_lt hw) hK)))
    (Q'.le_trans' _ _ _ hsum ?_)
  refine Q'.le_of_eqv (Q'.eqv_trans _
    (ceiling * listQSum weight (List.range K)) _
    (listQSum_mul_left ceiling weight (List.range K)) ?_)
  exact Q'.mul_eqv_congr_left ceiling _ _
    (Q'.eqv_symm
      (centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
        w (Q'.le_of_lt hw) K))

/-- Under a `5/6` vacuum calibration, the sharp finite ratio ceiling must pay
at least `1/6` after multiplication by the excited ray mass. -/
theorem oneSixth_le_finiteCeiling_mul_rayMass_of_vacuumMass_le_fiveSixths
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (hvacuum :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling ≤
        Q'.mkPos 5 6 (by decide)) :
    Q'.mkPos 1 6 (by decide) ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K := by
  exact Q'.le_trans' _ _ _
    (oneSixth_le_positiveCentralFaceDisplayedNonvacuumStationaryMass_of_vacuumMass_le_fiveSixths
      w (Q'.le_of_lt hw) K hvacuum)
    (positiveCentralFaceDisplayedNonvacuumStationaryMass_le_finiteCeiling_mul_rayMass
      hw hK)

namespace FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

/-- Any cofinal assigned-ratio producer must satisfy the same aggregate mass
comparison at every admitted cutoff. -/
theorem nonvacuumMass_le_ratioBound_mul_rayMass
    {w : Q'} {hw : (0 : Q') < w}
    (ratio : FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio hw)
    (K : Nat) (hK : ratio.start ≤ K) :
    positiveCentralFaceDisplayedNonvacuumStationaryMass
        w (Q'.le_of_lt hw) K ≤
      ratio.ratioBound *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K := by
  have hpositive : 1 ≤ K :=
    Nat.le_trans ratio.start_positive hK
  let mean := fun offset =>
    centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
      (positiveCentralFaceAssignedUnitObservable K (offset + 1)).value
  let weight := fun offset =>
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
  have hsum : listQSum mean (List.range K) ≤
      listQSum
        (fun offset => ratio.ratioBound * weight offset)
        (List.range K) := by
    apply listQSum_le_termwise
    intro offset hoffsetMem
    exact ratio.assignedMean_le K hK offset
      (List.mem_range.mp hoffsetMem)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (positiveCentralFaceAssignedStationaryMassSum_eqv_nonvacuum
          w (Q'.le_of_lt hw) hpositive)))
    (Q'.le_trans' _ _ _ hsum ?_)
  refine Q'.le_of_eqv (Q'.eqv_trans _
    (ratio.ratioBound * listQSum weight (List.range K)) _
    (listQSum_mul_left ratio.ratioBound weight (List.range K)) ?_)
  exact Q'.mul_eqv_congr_left ratio.ratioBound _ _
    (Q'.eqv_symm
      (centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
        w (Q'.le_of_lt hw) K))

/-- With a `5/6` physical vacuum calibration, any cofinal ratio producer must
keep `ratioBound * rayMass` above `1/6` at every admitted cutoff. -/
theorem oneSixth_le_ratioBound_mul_rayMass_of_vacuumMass_le_fiveSixths
    {w : Q'} {hw : (0 : Q') < w}
    (ratio : FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio hw)
    (K : Nat) (hK : ratio.start ≤ K)
    (hvacuum :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling ≤
        Q'.mkPos 5 6 (by decide)) :
    Q'.mkPos 1 6 (by decide) ≤
      ratio.ratioBound *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K := by
  exact Q'.le_trans' _ _ _
    (oneSixth_le_positiveCentralFaceDisplayedNonvacuumStationaryMass_of_vacuumMass_le_fiveSixths
      w (Q'.le_of_lt hw) K hvacuum)
    (nonvacuumMass_le_ratioBound_mul_rayMass ratio K hK)

end FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.positiveCentralFaceAssignedIndicator_sum_eqv_nonvacuum
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.positiveCentralFaceAssignedStationaryMassSum_eqv_nonvacuum
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.positiveCentralFaceDisplayedNonvacuumStationaryMass_add_vacuumMass_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.oneSixth_le_positiveCentralFaceDisplayedNonvacuumStationaryMass_of_vacuumMass_le_fiveSixths
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.positiveCentralFaceDisplayedNonvacuumStationaryMass_le_finiteCeiling_mul_rayMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.oneSixth_le_finiteCeiling_mul_rayMass_of_vacuumMass_le_fiveSixths
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.nonvacuumMass_le_ratioBound_mul_rayMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.oneSixth_le_ratioBound_mul_rayMass_of_vacuumMass_le_fiveSixths
