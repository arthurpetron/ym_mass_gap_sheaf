/-
# Regroup weighted path occurrences by directed physical edge

Canonical-path congestion is naturally stated per physical edge.  This module
provides the finite constructive reindexing step.  A weighted directed-edge
occurrence carries an edge and a rational load.  Summing all loads attached to
the same edge defines a loaded joint kernel.

For a duplicate-free finite support, the Dirichlet block of that loaded joint
kernel is exactly the sum of the corresponding weighted edge-square costs over
the original occurrence list.  Repeated occurrences are therefore retained
as load rather than discarded.

No BF4 load bound, uniform gap, continuum limit, or Clay conclusion is
asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic weighted occurrence loads -/

/-- A directed edge together with the rational load charged to that
occurrence. -/
abbrev WeightedDirectedEdgeOccurrence (State : Type) :=
  (State × State) × Q'

def weightedDirectedEdgeIndicator {State : Type} [DecidableEq State]
    (occurrence : WeightedDirectedEdgeOccurrence State)
    (source target : State) : Q' :=
  if occurrence.1 = (source, target) then occurrence.2 else 0

/-- Total load of all occurrences of one directed edge. -/
def weightedDirectedEdgeLoad {State : Type} [DecidableEq State]
    (occurrences : List (WeightedDirectedEdgeOccurrence State))
    (source target : State) : Q' :=
  listQSum
    (fun occurrence =>
      weightedDirectedEdgeIndicator occurrence source target)
    occurrences

theorem weightedDirectedEdgeLoad_nonnegative
    {State : Type} [DecidableEq State]
    (occurrences : List (WeightedDirectedEdgeOccurrence State))
    (hload : ∀ occurrence, occurrence ∈ occurrences →
      (0 : Q') ≤ occurrence.2)
    (source target : State) :
    (0 : Q') ≤ weightedDirectedEdgeLoad occurrences source target := by
  unfold weightedDirectedEdgeLoad
  apply listQSum_nonnegative_on
  intro occurrence hoccurrence
  unfold weightedDirectedEdgeIndicator
  by_cases heq : occurrence.1 = (source, target)
  · rw [if_pos heq]
    exact hload occurrence hoccurrence
  · rw [if_neg heq]
    exact Q'.le_refl' 0

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

private theorem listQSum_pos_exists_of_nonnegative_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      (0 : Q') < listQSum value items →
      ∃ item, item ∈ items ∧ (0 : Q') < value item
  | [], _, hsum => by
      exact absurd hsum (Int.not_lt_of_ge (Q'.le_refl' 0))
  | head :: tail, hnonnegative, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have hheadNonpos : value head ≤ 0 :=
          q_nonpos_of_not_pos_local hhead
        have hheadZero : value head ≈ 0 :=
          Q'.eqv_of_le_le hheadNonpos
            (hnonnegative head List.mem_cons_self)
        have hsumEqTail :
            listQSum value (head :: tail) ≈ listQSum value tail := by
          refine Q'.eqv_trans _ (0 + listQSum value tail) _ ?_ ?_
          · exact Q'.add_eqv_congr' hheadZero (Q'.eqv_refl _)
          exact Q'.eqv_of_eq (Q'.zero_add' (listQSum value tail))
        have htailPos : (0 : Q') < listQSum value tail :=
          Q'.pos_of_lt_of_le hsum (Q'.le_of_eqv hsumEqTail)
        rcases listQSum_pos_exists_of_nonnegative_local value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htailPos with ⟨item, hitem, hitemPos⟩
        exact ⟨item, List.mem_cons_of_mem head hitem, hitemPos⟩

/-- A strictly positive grouped edge load is witnessed by a literal
occurrence of that directed edge.  This is the support bridge needed to take
a positive minimum only over edges actually used by a weighted flow. -/
theorem exists_occurrence_of_weightedDirectedEdgeLoad_pos
    {State : Type} [DecidableEq State]
    (occurrences : List (WeightedDirectedEdgeOccurrence State))
    (hload : ∀ occurrence, occurrence ∈ occurrences →
      (0 : Q') ≤ occurrence.2)
    (source target : State)
    (hpositive : (0 : Q') <
      weightedDirectedEdgeLoad occurrences source target) :
    ∃ occurrence, occurrence ∈ occurrences ∧
      occurrence.1 = (source, target) := by
  unfold weightedDirectedEdgeLoad at hpositive
  have hindicator : ∀ occurrence, occurrence ∈ occurrences →
      (0 : Q') ≤
        weightedDirectedEdgeIndicator occurrence source target := by
    intro occurrence hoccurrence
    unfold weightedDirectedEdgeIndicator
    by_cases heq : occurrence.1 = (source, target)
    · rw [if_pos heq]
      exact hload occurrence hoccurrence
    · rw [if_neg heq]
      exact Q'.le_refl' 0
  rcases listQSum_pos_exists_of_nonnegative_local
      (fun occurrence =>
        weightedDirectedEdgeIndicator occurrence source target)
      occurrences hindicator hpositive with
    ⟨occurrence, hoccurrence, htermPositive⟩
  refine ⟨occurrence, hoccurrence, ?_⟩
  by_cases hedge : occurrence.1 = (source, target)
  · exact hedge
  · unfold weightedDirectedEdgeIndicator at htermPositive
    rw [if_neg hedge] at htermPositive
    exact False.elim
      ((Int.not_lt_of_ge (Q'.le_refl' 0)) htermPositive)

/-- Total weighted physical edge-square cost before equal edges are grouped. -/
def finiteWeightedOccurrenceEnergy
    {State : Type}
    (occurrences : List (WeightedDirectedEdgeOccurrence State))
    (coefficient : State → Q') (kernel : State → State → Q') : Q' :=
  listQSum
    (fun occurrence =>
      occurrence.2 *
        (kernel occurrence.1.1 occurrence.1.2 *
          ((coefficient occurrence.1.1 + -coefficient occurrence.1.2) *
            (coefficient occurrence.1.1 + -coefficient occurrence.1.2))))
    occurrences

/-- Dirichlet block after occurrences have been grouped into an edge load. -/
def finiteWeightedOccurrenceLoadedDirichlet
    {State : Type} [DecidableEq State]
    (states : List State)
    (occurrences : List (WeightedDirectedEdgeOccurrence State))
    (coefficient : State → Q') (kernel : State → State → Q') : Q' :=
  finiteJointDirichletBlock states states coefficient
    (fun source target =>
      weightedDirectedEdgeLoad occurrences source target *
        kernel source target)

/-! ## 2. Finite selector and block linearity -/

private theorem listQSum_indicator_mul_eqv_selected
    {State : Type} [DecidableEq State]
    (selected : State) (load : Q') (value : State → Q') :
    ∀ states : List State, states.Nodup → selected ∈ states →
      listQSum
          (fun state =>
            (if selected = state then load else 0) * value state)
          states ≈
        load * value selected
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | first :: rest, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hfirst | hrest
      · subst first
        simp only [listQSum]
        simp only [ite_true]
        have htailZero : listQSum
            (fun state =>
              (if selected = state then load else 0) * value state)
            rest ≈ 0 := by
          refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) rest) _ ?_ ?_
          · apply listQSum_congr_on
            intro state hstate
            have hne : selected ≠ state := by
              intro heq
              exact hparts.1 (heq ▸ hstate)
            rw [if_neg hne]
            exact Q'.zero_mul_eqv _
          · exact listQSum_zero rest
        exact Q'.eqv_trans _ (load * value selected + 0) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : selected ≠ first := by
          intro heq
          subst first
          exact hparts.1 hrest
        simp only [listQSum]
        rw [if_neg hne]
        exact Q'.eqv_trans _ (0 + load * value selected) _
          (Q'.add_eqv_congr' (Q'.zero_mul_eqv _)
            (listQSum_indicator_mul_eqv_selected
              selected load value rest hparts.2 hrest))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem finiteJointDirichletBlock_eqv_cartesian
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient joint ≈
      listQSum
        (fun pair =>
          joint pair.1 pair.2 *
            ((coefficient pair.1 + -coefficient pair.2) *
              (coefficient pair.1 + -coefficient pair.2)))
        (cartesian leftStates rightStates) := by
  unfold finiteJointDirichletBlock cartesian
  let entry : State × State → Q' := fun pair =>
    joint pair.1 pair.2 *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  have hflat := listQSum_flatMap entry
    (fun left => rightStates.map (fun right => (left, right))) leftStates
  have hrows : listQSum
      (fun left =>
        listQSum entry
          (rightStates.map (fun right => (left, right))))
      leftStates ≈
      listQSum
        (fun left => listQSum
          (fun right =>
            joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
        leftStates := by
    apply listQSum_congr
    intro left
    rw [listQSum_map]
    rfl
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hflat hrows)

private theorem finiteJointDirichletBlock_joint_congr
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        first left right ≈ second left right) :
    finiteJointDirichletBlock
        leftStates rightStates coefficient first ≈
      finiteJointDirichletBlock
        leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_right _ _ _
    (hjoint left hleft right hright)

private theorem finiteJointDirichletBlock_add_joint
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => first left right + second left right) ≈
      finiteJointDirichletBlock leftStates rightStates coefficient first +
        finiteJointDirichletBlock leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            first left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)) +
              second left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.add_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right => first left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
          rightStates +
        listQSum
          (fun right => second left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_add _ _ rightStates
  · exact listQSum_add _ _ leftStates

private theorem singletonOccurrenceLoadedDirichlet_eqv
    {State : Type} [DecidableEq State]
    (states : List State) (hnodup : states.Nodup)
    (occurrence : WeightedDirectedEdgeOccurrence State)
    (hedge : occurrence.1.1 ∈ states ∧ occurrence.1.2 ∈ states)
    (coefficient : State → Q') (kernel : State → State → Q') :
    finiteJointDirichletBlock states states coefficient
        (fun source target =>
          weightedDirectedEdgeIndicator occurrence source target *
            kernel source target) ≈
      occurrence.2 *
        (kernel occurrence.1.1 occurrence.1.2 *
          ((coefficient occurrence.1.1 + -coefficient occurrence.1.2) *
            (coefficient occurrence.1.1 + -coefficient occurrence.1.2))) := by
  let pairs := cartesian states states
  let edgeValue : State × State → Q' := fun pair =>
    kernel pair.1 pair.2 *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  have hpair : occurrence.1 ∈ pairs :=
    (mem_cartesian_iff states states occurrence.1).mpr hedge
  have hpairsNodup : pairs.Nodup :=
    cartesian_nodup states states hnodup hnodup
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        (weightedDirectedEdgeIndicator
            occurrence pair.1 pair.2) * edgeValue pair)
      pairs) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun pair =>
          (weightedDirectedEdgeIndicator occurrence pair.1 pair.2 *
              kernel pair.1 pair.2) *
            ((coefficient pair.1 + -coefficient pair.2) *
              (coefficient pair.1 + -coefficient pair.2)))
        pairs) _ ?_ ?_
    · exact finiteJointDirichletBlock_eqv_cartesian
        states states coefficient _
    · apply listQSum_congr
      intro pair
      unfold edgeValue
      exact Q'.mul_assoc_eqv _ _ _
  unfold weightedDirectedEdgeIndicator
  exact listQSum_indicator_mul_eqv_selected
    occurrence.1 occurrence.2 edgeValue
    pairs hpairsNodup hpair

/-! ## 3. Exact regrouping by directed edge -/

/-- A finite weighted occurrence sum is exactly the Dirichlet block whose
joint coefficient is the total load on each directed edge. -/
theorem finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
    {State : Type} [DecidableEq State]
    (states : List State) (hnodup : states.Nodup)
    (coefficient : State → Q') (kernel : State → State → Q') :
    ∀ occurrences : List (WeightedDirectedEdgeOccurrence State),
      (∀ occurrence, occurrence ∈ occurrences →
        occurrence.1.1 ∈ states ∧ occurrence.1.2 ∈ states) →
      finiteWeightedOccurrenceLoadedDirichlet
          states occurrences coefficient kernel ≈
        finiteWeightedOccurrenceEnergy occurrences coefficient kernel
  | [], _ => by
      unfold finiteWeightedOccurrenceLoadedDirichlet
        finiteWeightedOccurrenceEnergy weightedDirectedEdgeLoad
      unfold finiteJointDirichletBlock
      simp only [listQSum]
      refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) states) _ ?_
        (listQSum_zero states)
      apply listQSum_congr
      intro source
      refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) states) _ ?_
        (listQSum_zero states)
      apply listQSum_congr
      intro target
      exact Q'.eqv_trans _
        (0 *
          ((coefficient source + -coefficient target) *
            (coefficient source + -coefficient target))) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.zero_mul_eqv _)
  | occurrence :: rest, hedge => by
      have hoccurrence := hedge occurrence List.mem_cons_self
      have hrest : ∀ item, item ∈ rest →
          item.1.1 ∈ states ∧ item.1.2 ∈ states := by
        intro item hitem
        exact hedge item (List.mem_cons_of_mem occurrence hitem)
      have hpoint : ∀ source, source ∈ states →
          ∀ target, target ∈ states →
          weightedDirectedEdgeLoad (occurrence :: rest) source target *
              kernel source target ≈
            weightedDirectedEdgeIndicator occurrence source target *
                kernel source target +
              weightedDirectedEdgeLoad rest source target *
                kernel source target := by
        intro source _ target _
        unfold weightedDirectedEdgeLoad
        exact Q'.add_mul_eqv _ _ _
      refine Q'.eqv_trans _
        (finiteJointDirichletBlock states states coefficient
          (fun source target =>
            weightedDirectedEdgeIndicator occurrence source target *
                kernel source target +
              weightedDirectedEdgeLoad rest source target *
                kernel source target)) _ ?_ ?_
      · exact finiteJointDirichletBlock_joint_congr
          states states coefficient _ _ hpoint
      refine Q'.eqv_trans _
        (finiteJointDirichletBlock states states coefficient
            (fun source target =>
              weightedDirectedEdgeIndicator occurrence source target *
                kernel source target) +
          finiteJointDirichletBlock states states coefficient
            (fun source target =>
              weightedDirectedEdgeLoad rest source target *
                kernel source target)) _ ?_ ?_
      · exact finiteJointDirichletBlock_add_joint
          states states coefficient _ _
      exact Q'.add_eqv_congr'
        (singletonOccurrenceLoadedDirichlet_eqv
          states hnodup occurrence hoccurrence coefficient kernel)
        (finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
          states hnodup coefficient kernel rest hrest)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad.weightedDirectedEdgeLoad_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad.exists_occurrence_of_weightedDirectedEdgeLoad_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad.finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
