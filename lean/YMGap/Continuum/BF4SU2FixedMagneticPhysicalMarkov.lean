/-
# The physical reversible Markov carrier of the grouped BF4 Choi law

The partition-normalized reflected BF4 kernel is a symmetric joint
probability law, not a row-stochastic matrix.  This module performs the
correct conditional normalization.

For each lower state, `centralPhysicalRowMarginal` is the marginal mass of
its row.  The retained carrier consists exactly of rows with strictly
positive marginal.  Dividing a retained row by its own marginal gives the
literal physical conditional kernel.  Symmetry of the Choi law then gives
detailed balance.  Rows of zero marginal have zero coupling to every
positive row, so filtering them out loses no mass.

The resulting finite operator preserves constants and the mean defined by
the physical row marginal.  Hence the physically relevant non-vacuum
carrier is the marginal-mean-zero subspace, not the uniformly mean-zero
subspace.

Honest scope: this identifies the correct finite physical Perron carrier and
its invariant mean.  It does not prove a quantitative contraction on that
mean-zero carrier or identify its non-vacuum spectral radius with the
Gaussian/Mehler ratio.

## Axiom gate

Finite list recursion and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

namespace YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The joint law and its physical row marginal -/

/-- The marginal of one lower state in the normalized reflected joint law. -/
def centralPhysicalRowMarginal
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling) : Q' :=
  listQSum
    (centralNormalizedPhysicalReflectedKernel
      w hw K half source)
    (centralHalfStates K half)

/-- The literal retained carrier: exactly the lower states whose reflected
joint-law row has positive mass. -/
def centralPositiveHalfStates
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) : List EdgeLabelling :=
  (centralHalfStates K half).filter
    (fun source =>
      decide ((0 : Q') <
        centralPhysicalRowMarginal
          w hw K half source))

theorem mem_centralPositiveHalfStates_iff
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling} :
    source ∈ centralPositiveHalfStates w hw K half ↔
      source ∈ centralHalfStates K half ∧
        (0 : Q') <
          centralPhysicalRowMarginal
            w hw K half source := by
  unfold centralPositiveHalfStates
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem centralPositiveHalfStates_nodup
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    (centralPositiveHalfStates w hw K half).Nodup := by
  unfold centralPositiveHalfStates
  exact List.filter_sublist.nodup
    (centralHalfStates_nodup K half)

theorem centralNormalizedPhysicalReflectedKernel_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling) :
    (0 : Q') ≤
      centralNormalizedPhysicalReflectedKernel
        w hw K half left right := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  apply Q'.mul_nonneg
  · unfold centralPhysicalReflectedKernel
    apply listQSum_nonnegative_on
    intro boundary _
    exact slabParametricKPhysicalTerm_nonnegative
      hw K (centralExtent half)
      (assembleReflectedSlabLabelling
        half left boundary right)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half)))

theorem centralPhysicalRowMarginal_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling) :
    (0 : Q') ≤
      centralPhysicalRowMarginal
        w hw K half source := by
  unfold centralPhysicalRowMarginal
  apply listQSum_nonnegative_on
  intro target _
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    hw K half source target

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem q_nonpositive_of_not_positive
    {q : Q'} (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤
    (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_nonpositive
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnonpositive : q ≤ 0) :
    q ≈ 0 := by
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

/-- Any entry in a row whose marginal is not positive is exactly zero. -/
theorem centralNormalizedPhysicalReflectedKernel_eqv_zero_of_row_not_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (htarget : target ∈ centralHalfStates K half)
    (hrow :
      ¬ (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half source) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half source target ≈ 0 := by
  have hentryNonnegative :=
    centralNormalizedPhysicalReflectedKernel_nonnegative
      hw K half source target
  have hentryLe :
      centralNormalizedPhysicalReflectedKernel
          w hw K half source target ≤
        centralPhysicalRowMarginal
          w hw K half source := by
    unfold centralPhysicalRowMarginal
    exact listQSum_member_le_nonnegative
      (centralNormalizedPhysicalReflectedKernel
        w hw K half source)
      (fun item =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          hw K half source item)
      (centralHalfStates K half) htarget
  exact q_eqv_zero_of_nonnegative_of_nonpositive
    hentryNonnegative
    (Q'.le_trans' _ _ _ hentryLe
      (q_nonpositive_of_not_positive hrow))

/-- Exact symmetry of the partition-normalized physical joint law. -/
theorem centralNormalizedPhysicalReflectedKernel_symm
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half left right ≈
      centralNormalizedPhysicalReflectedKernel
        w hw K half right left := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralPhysicalReflectedKernel_symm
      w hleft hright)

/-- A zero-marginal target has zero joint weight from every physical source. -/
theorem centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half)
    (htarget : target ∈ centralHalfStates K half)
    (hrow :
      ¬ (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half target) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half source target ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralNormalizedPhysicalReflectedKernel_symm
      hsource htarget)
    (centralNormalizedPhysicalReflectedKernel_eqv_zero_of_row_not_pos
      hsource hrow)

/-! ## 2. Conditioning each positive row -/

/-- The physical row-conditional kernel.  It is zero outside the positive
row carrier; on that carrier it is the joint entry divided by its marginal. -/
def centralPhysicalConditionalKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (source target : EdgeLabelling) : Q' :=
  if hrow :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half source then
    Q'.divPos
      (centralNormalizedPhysicalReflectedKernel
        w hw K half source target)
      (centralPhysicalRowMarginal
        w hw K half source)
      hrow
  else 0

theorem centralPhysicalConditionalKernel_eq_divPos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hrow :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half source) :
    centralPhysicalConditionalKernel
        w hw K half source target =
      Q'.divPos
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source target)
        (centralPhysicalRowMarginal
          w hw K half source)
        hrow := by
  unfold centralPhysicalConditionalKernel
  rw [dif_pos hrow]

theorem centralPhysicalConditionalKernel_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤
      centralPhysicalConditionalKernel
        w hw K half source target := by
  unfold centralPhysicalConditionalKernel
  split
  · unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (centralNormalizedPhysicalReflectedKernel_nonnegative
        hw K half source target)
      (Q'.le_of_lt (Q'.recipPos_pos _ (by assumption)))
  · exact Q'.le_refl' 0

private theorem listQSum_filter_eq_of_zero
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          have hhead :=
            hzero head List.mem_cons_self hp
          have htail :=
            listQSum_filter_eq_of_zero value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _
            (listQSum value tail) _ htail
            (Q'.eqv_trans _
              (0 + listQSum value tail) _
              (Q'.eqv_symm
                (Q'.eqv_of_eq
                  (Q'.zero_add' _)))
              (Q'.add_eqv_congr'
                (Q'.eqv_symm hhead)
                (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))

private theorem conditionalKernel_eqv_zero_of_target_not_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half)
    (hsourceRow :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half source)
    (htarget : target ∈ centralHalfStates K half)
    (htargetRow :
      ¬ (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half target) :
    centralPhysicalConditionalKernel
        w hw K half source target ≈ 0 := by
  rw [centralPhysicalConditionalKernel_eq_divPos hsourceRow]
  unfold Q'.divPos
  exact Q'.eqv_trans _
    (0 * Q'.recipPos
      (centralPhysicalRowMarginal
        w hw K half source) hsourceRow) _
    (Q'.mul_eqv_congr_right
      (centralNormalizedPhysicalReflectedKernel
        w hw K half source target) 0
      (Q'.recipPos
        (centralPhysicalRowMarginal
          w hw K half source) hsourceRow)
      (centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
        hsource htarget htargetRow))
    (Q'.zero_mul_eqv _)

/-- Every retained physical row sums to one on the retained carrier. -/
theorem centralPhysicalConditionalKernel_row_normalized
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    listQSum
        (centralPhysicalConditionalKernel
          w hw K half source)
        (centralPositiveHalfStates
          w hw K half) ≈
      1 := by
  have hparts :=
    (mem_centralPositiveHalfStates_iff).1 hsource
  have hfilter :
      listQSum
          (centralPhysicalConditionalKernel
            w hw K half source)
          (centralPositiveHalfStates
            w hw K half) ≈
        listQSum
          (centralPhysicalConditionalKernel
            w hw K half source)
          (centralHalfStates K half) := by
    unfold centralPositiveHalfStates
    apply listQSum_filter_eq_of_zero
    intro target htarget hfalse
    apply conditionalKernel_eqv_zero_of_target_not_pos
      hparts.1 hparts.2 htarget
    simpa only [decide_eq_false_iff_not] using hfalse
  refine Q'.eqv_trans _ _ _ hfilter ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        Q'.divPos
          (centralNormalizedPhysicalReflectedKernel
            w hw K half source target)
          (centralPhysicalRowMarginal
            w hw K half source)
          hparts.2)
      (centralHalfStates K half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.eqv_of_eq
      (centralPhysicalConditionalKernel_eq_divPos
        (target := target) hparts.2)
  · unfold Q'.divPos centralPhysicalRowMarginal
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source)
        (Q'.recipPos
          (listQSum
            (centralNormalizedPhysicalReflectedKernel
              w hw K half source)
            (centralHalfStates K half))
          hparts.2)
        (centralHalfStates K half))
      (Q'.mul_recipPos_eqv _ hparts.2)

private theorem marginal_mul_divPos_eqv
    (marginal joint : Q')
    (hmarginal : (0 : Q') < marginal) :
    marginal *
        Q'.divPos joint marginal hmarginal ≈
      joint := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((marginal * joint) *
      Q'.recipPos marginal hmarginal) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv marginal joint
        (Q'.recipPos marginal hmarginal))) ?_
  refine Q'.eqv_trans _
    ((joint * marginal) *
      Q'.recipPos marginal hmarginal) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv marginal joint)) ?_
  refine Q'.eqv_trans _
    (joint *
      (marginal *
        Q'.recipPos marginal hmarginal)) _
    (Q'.mul_assoc_eqv joint marginal
      (Q'.recipPos marginal hmarginal)) ?_
  exact Q'.eqv_trans _ (joint * 1) _
    (Q'.mul_eqv_congr_left joint _ _
      (Q'.mul_recipPos_eqv marginal hmarginal))
    (Q'.mul_one_eqv joint)

private theorem marginal_mul_conditional_eqv_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalRowMarginal
          w hw K half source *
        centralPhysicalConditionalKernel
          w hw K half source target ≈
      centralNormalizedPhysicalReflectedKernel
        w hw K half source target := by
  have hrow :=
    (mem_centralPositiveHalfStates_iff).1 hsource
  rw [centralPhysicalConditionalKernel_eq_divPos hrow.2]
  exact marginal_mul_divPos_eqv
    (centralPhysicalRowMarginal
      w hw K half source)
    (centralNormalizedPhysicalReflectedKernel
      w hw K half source target)
    hrow.2

/-- Exact detailed balance on the positive physical carrier. -/
theorem centralPhysicalConditionalKernel_detailed_balance
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates
        w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalRowMarginal w hw K half left *
        centralPhysicalConditionalKernel
          w hw K half left right ≈
      centralPhysicalRowMarginal w hw K half right *
        centralPhysicalConditionalKernel
          w hw K half right left := by
  have hleftRaw :=
    (mem_centralPositiveHalfStates_iff).1 hleft
  have hrightRaw :=
    (mem_centralPositiveHalfStates_iff).1 hright
  exact Q'.eqv_trans _ _ _
    (marginal_mul_conditional_eqv_joint hleft)
    (Q'.eqv_trans _ _ _
      (centralNormalizedPhysicalReflectedKernel_symm
        hleftRaw.1 hrightRaw.1)
      (Q'.eqv_symm
        (marginal_mul_conditional_eqv_joint hright)))

/-! ## 3. The stationary marginal is a probability law -/

/-- The complete normalized joint law has total mass one. -/
theorem centralPhysicalRowMarginal_total_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    listQSum
        (centralPhysicalRowMarginal
          w hw K half)
        (centralHalfStates K half) ≈
      1 := by
  let states := centralHalfStates K half
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let hpartition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  let reciprocal :=
    Q'.recipPos partition hpartition
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            centralPhysicalReflectedKernel
                w K half left right *
              reciprocal)
          states)
      states) _ ?_ ?_
  · unfold centralPhysicalRowMarginal
      centralNormalizedPhysicalReflectedKernel
      Q'.divPos states reciprocal partition hpartition
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum
            (centralPhysicalReflectedKernel
              w K half left)
            states *
          reciprocal)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      exact listQSum_mul_right
        (centralPhysicalReflectedKernel
          w K half left)
        reciprocal states
    · refine Q'.eqv_trans _
        (centralPhysicalReflectionQuadratic
            w K half (fun _ => 1) *
          reciprocal) _ ?_ ?_
      · refine Q'.eqv_trans _
          (listQSum
              (fun left =>
                listQSum
                  (centralPhysicalReflectedKernel
                    w K half left)
                  states)
              states *
            reciprocal) _
          (listQSum_mul_right
            (fun left =>
              listQSum
                (centralPhysicalReflectedKernel
                  w K half left)
                states)
            reciprocal states) ?_
        apply Q'.mul_eqv_congr_right
        unfold centralPhysicalReflectionQuadratic states
        apply listQSum_congr
        intro left
        apply listQSum_congr
        intro right
        exact Q'.eqv_symm
          (Q'.eqv_trans _
            (1 *
              centralPhysicalReflectedKernel
                w K half left right) _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.one_mul_eqv 1))
            (Q'.one_mul_eqv _))
      · refine Q'.eqv_trans _
          (centralFullPhysicalReflectionQuadratic
              w K half (fun _ => 1) *
            reciprocal) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (centralPhysicalReflectionQuadratic_eq_full
              w K half (fun _ => 1))
        · change
            centralNormalizedFullPhysicalReflectionQuadratic
                w hw K half (fun _ => 1) ≈
              1
          exact centralNormalizedFullPhysicalReflectionQuadratic_one
            w hw K half

/-- Filtering zero rows preserves the complete stationary mass. -/
theorem centralPositiveRowMarginal_total_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    listQSum
        (centralPhysicalRowMarginal
          w hw K half)
        (centralPositiveHalfStates
          w hw K half) ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalRowMarginal
        w hw K half)
      (centralHalfStates K half)) _ ?_
    (centralPhysicalRowMarginal_total_one
      w hw K half)
  unfold centralPositiveHalfStates
  apply listQSum_filter_eq_of_zero
  intro source _ hfalse
  apply q_eqv_zero_of_nonnegative_of_nonpositive
  · exact centralPhysicalRowMarginal_nonnegative
      hw K half source
  · apply q_nonpositive_of_not_positive
    simpa only [decide_eq_false_iff_not] using hfalse

/-- The retained physical carrier is constructively nonempty. -/
theorem centralPositiveHalfStates_ne_nil
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    centralPositiveHalfStates w hw K half ≠ [] := by
  intro hempty
  have htotal :=
    centralPositiveRowMarginal_total_one
      w hw K half
  rw [hempty] at htotal
  have hne : ¬ ((0 : Q') ≈ (1 : Q')) := by
    decide
  exact hne htotal

theorem centralPositiveHalfStates_length_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    0 <
      (centralPositiveHalfStates
        w hw K half).length := by
  have hne :=
    centralPositiveHalfStates_ne_nil
      w hw K half
  generalize hstates :
      centralPositiveHalfStates
        w hw K half = states at hne ⊢
  cases states with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
      simp only [List.length_cons]
      omega

/-! ## 4. The physical invariant mean and mean-zero carrier -/

/-- Action of the row-conditional kernel on the retained carrier. -/
def centralPhysicalMarkovApply
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      centralPhysicalConditionalKernel
          w hw K half source target *
        observable target)
    (centralPositiveHalfStates w hw K half)

/-- The unnormalized stationary expectation.  Its scale is irrelevant to
the mean-zero equation and avoids a second division. -/
def centralPhysicalStationaryMean
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun state =>
      centralPhysicalRowMarginal
          w hw K half state *
        observable state)
    (centralPositiveHalfStates w hw K half)

/-- The exact physical finite-volume inner product.  Its weight is the
row marginal of the normalized BF4 Choi law, not counting measure. -/
def centralPhysicalWeightedInner
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (left right : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun state =>
      centralPhysicalRowMarginal
          w hw K half state *
        (left state * right state))
    (centralPositiveHalfStates w hw K half)

/-- The actual physical non-vacuum linear carrier. -/
def CentralPhysicalMeanZero
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q') : Prop :=
  centralPhysicalStationaryMean
    w hw K half observable ≈ 0

/-- The physical vacuum projector sends every source to the stationary
row-marginal mean.  Unlike the uniform projector, this is the projector
selected by the actual BF4 joint law. -/
def centralPhysicalVacuumProjectorApply
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q')
    (_source : EdgeLabelling) : Q' :=
  centralPhysicalStationaryMean
    w hw K half observable

/-- Vacuum removal on the correct marginal-weighted carrier. -/
def centralPhysicalCenteredMarkovApply
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  centralPhysicalMarkovApply
      w hw K half observable source +
    -centralPhysicalVacuumProjectorApply
      w hw K half observable source

/-- Constants are fixed by every retained physical row. -/
theorem centralPhysicalMarkovApply_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalMarkovApply
        w hw K half (fun _ => 1) source ≈ 1 := by
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalConditionalKernel
        w hw K half source)
      (centralPositiveHalfStates
        w hw K half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_one_eqv _
  · exact centralPhysicalConditionalKernel_row_normalized
      hsource

/-- The stationary mean of the constant function is one; the retained row
marginal is therefore already normalized as a probability law. -/
theorem centralPhysicalStationaryMean_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    centralPhysicalStationaryMean
        w hw K half (fun _ => 1) ≈
      1 := by
  unfold centralPhysicalStationaryMean
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalRowMarginal
        w hw K half)
      (centralPositiveHalfStates
        w hw K half)) _ ?_
    (centralPositiveRowMarginal_total_one
      w hw K half)
  apply listQSum_congr
  intro state
  exact Q'.mul_one_eqv _

/-- The physical vacuum projector annihilates precisely the
marginal-mean-zero carrier. -/
theorem centralPhysicalVacuumProjector_annihilates_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {observable : EdgeLabelling → Q'}
    (hmean :
      CentralPhysicalMeanZero
        w hw K half observable)
    (source : EdgeLabelling) :
    centralPhysicalVacuumProjectorApply
        w hw K half observable source ≈
      0 := by
  exact hmean

/-- On the physical mean-zero carrier, vacuum removal leaves the genuine
conditional operator unchanged. -/
theorem centralPhysicalCenteredMarkovApply_eq_markov_of_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {observable : EdgeLabelling → Q'}
    (hmean :
      CentralPhysicalMeanZero
        w hw K half observable)
    (source : EdgeLabelling) :
    centralPhysicalCenteredMarkovApply
        w hw K half observable source ≈
      centralPhysicalMarkovApply
        w hw K half observable source := by
  unfold centralPhysicalCenteredMarkovApply
  exact Q'.eqv_trans _
    (centralPhysicalMarkovApply
        w hw K half observable source + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (-0) _
        (Q'.neg_eqv_congr _ _ hmean)
        (Q'.eqv_refl 0)))
    (Q'.eqv_of_eq
      (Q'.add_zero' _))

/-- The centered physical operator removes the constant vacuum exactly. -/
theorem centralPhysicalCenteredMarkovApply_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalCenteredMarkovApply
        w hw K half (fun _ => 1) source ≈
      0 := by
  unfold centralPhysicalCenteredMarkovApply
    centralPhysicalVacuumProjectorApply
  exact Q'.eqv_trans _
    (1 + -1) _
    (Q'.add_eqv_congr'
      (centralPhysicalMarkovApply_one hsource)
      (Q'.neg_eqv_congr _ _
        (centralPhysicalStationaryMean_one
          w hw K half)))
    (Q'.add_neg_self_eqv 1)

private theorem stationarySummand_recode
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (observable : EdgeLabelling → Q')
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates
        w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalRowMarginal w hw K half left *
        (centralPhysicalConditionalKernel
            w hw K half left right *
          observable right) ≈
      centralPhysicalRowMarginal w hw K half right *
        (centralPhysicalConditionalKernel
            w hw K half right left *
          observable right) := by
  refine Q'.eqv_trans _
    ((centralPhysicalRowMarginal w hw K half left *
        centralPhysicalConditionalKernel
          w hw K half left right) *
      observable right) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv _ _ _)
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (centralPhysicalConditionalKernel_detailed_balance
          hleft hright))
      (Q'.mul_assoc_eqv _ _ _)

/-- The row-marginal stationary mean is preserved exactly. -/
theorem centralPhysicalStationaryMean_markovApply
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalStationaryMean w hw K half
        (centralPhysicalMarkovApply
          w hw K half observable) ≈
      centralPhysicalStationaryMean
        w hw K half observable := by
  let states :=
    centralPositiveHalfStates w hw K half
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            centralPhysicalRowMarginal
                w hw K half left *
              (centralPhysicalConditionalKernel
                  w hw K half left right *
                observable right))
          states)
      states) _ ?_ ?_
  · unfold centralPhysicalStationaryMean
      centralPhysicalMarkovApply
    apply listQSum_congr
    intro left
    exact Q'.eqv_symm
      (listQSum_mul_left
        (centralPhysicalRowMarginal
          w hw K half left)
        (fun right =>
          centralPhysicalConditionalKernel
              w hw K half left right *
            observable right)
        states)
  · refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          listQSum
            (fun left =>
              centralPhysicalRowMarginal
                  w hw K half left *
                (centralPhysicalConditionalKernel
                    w hw K half left right *
                  observable right))
            states)
        states) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_swap
          (fun left right =>
            centralPhysicalRowMarginal
                w hw K half left *
              (centralPhysicalConditionalKernel
                  w hw K half left right *
                observable right))
          states states)
    · unfold centralPhysicalStationaryMean
      apply listQSum_congr_on
      intro right hright
      refine Q'.eqv_trans _
        (listQSum
          (fun left =>
            centralPhysicalRowMarginal
                w hw K half right *
              (centralPhysicalConditionalKernel
                  w hw K half right left *
                observable right))
          states) _ ?_ ?_
      · apply listQSum_congr_on
        intro left hleft
        exact stationarySummand_recode
          observable hleft hright
      · refine Q'.eqv_trans _
          (centralPhysicalRowMarginal
              w hw K half right *
            (listQSum
              (centralPhysicalConditionalKernel
                w hw K half right)
              states *
              observable right)) _ ?_ ?_
        · exact Q'.eqv_trans _ _ _
            (listQSum_mul_left
              (centralPhysicalRowMarginal
                w hw K half right)
              (fun left =>
                centralPhysicalConditionalKernel
                    w hw K half right left *
                  observable right)
              states)
            (Q'.mul_eqv_congr_left _ _ _
              (listQSum_mul_right
                (centralPhysicalConditionalKernel
                  w hw K half right)
                (observable right) states))
        · exact Q'.eqv_trans _
            (centralPhysicalRowMarginal
                w hw K half right *
              (1 * observable right)) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (centralPhysicalConditionalKernel_row_normalized
                  hright)))
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.one_mul_eqv _))

/-- Pure commutative four-factor regrouping used to expose the detailed
balance pair in a weighted matrix coefficient. -/
private theorem q_mul_four_cross
    (a b c d : Q') :
    a * (b * (c * d)) ≈
      (a * c) * (b * d) := by
  show
    (a * (b * (c * d))).num *
        (((a * c) * (b * d)).den : Int) =
      ((a * c) * (b * d)).num *
        ((a * (b * (c * d))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- Pure associative four-factor regrouping for the target weighted matrix
coefficient. -/
private theorem q_mul_four_straight
    (a b c d : Q') :
    a * ((b * c) * d) ≈
      (a * b) * (c * d) := by
  show
    (a * ((b * c) * d)).num *
        (((a * b) * (c * d)).den : Int) =
      ((a * b) * (c * d)).num *
        ((a * ((b * c) * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem weightedAdjointSummand_recode
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (leftObservable rightObservable : EdgeLabelling → Q')
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates
        w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates
        w hw K half) :
    centralPhysicalRowMarginal w hw K half left *
        (leftObservable left *
          (centralPhysicalConditionalKernel
              w hw K half left right *
            rightObservable right)) ≈
      centralPhysicalRowMarginal w hw K half right *
        ((centralPhysicalConditionalKernel
              w hw K half right left *
            leftObservable left) *
          rightObservable right) := by
  refine Q'.eqv_trans _
    ((centralPhysicalRowMarginal w hw K half left *
        centralPhysicalConditionalKernel
          w hw K half left right) *
      (leftObservable left * rightObservable right)) _ ?_ ?_
  · exact q_mul_four_cross _ _ _ _
  · refine Q'.eqv_trans _
      ((centralPhysicalRowMarginal w hw K half right *
          centralPhysicalConditionalKernel
            w hw K half right left) *
        (leftObservable left * rightObservable right)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (centralPhysicalConditionalKernel_detailed_balance
          hleft hright)
    · exact Q'.eqv_symm
        (q_mul_four_straight _ _ _ _)

/-- **Physical weighted self-adjointness.**

The exact row-conditional BF4 operator is self-adjoint in the inner product
selected by its own normalized Choi marginal.  No square roots of marginal
weights and no uniform-vacuum surrogate are introduced. -/
theorem centralPhysicalMarkovApply_self_adjoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (leftObservable rightObservable : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw K half
        leftObservable
        (centralPhysicalMarkovApply
          w hw K half rightObservable) ≈
      centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply
          w hw K half leftObservable)
        rightObservable := by
  let states :=
    centralPositiveHalfStates w hw K half
  let leftSummand :=
    fun left right =>
      centralPhysicalRowMarginal w hw K half left *
        (leftObservable left *
          (centralPhysicalConditionalKernel
              w hw K half left right *
            rightObservable right))
  let rightSummand :=
    fun left right =>
      centralPhysicalRowMarginal w hw K half right *
        ((centralPhysicalConditionalKernel
              w hw K half right left *
            leftObservable left) *
          rightObservable right)
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (leftSummand left) states)
      states) _ ?_ ?_
  · unfold centralPhysicalWeightedInner
      centralPhysicalMarkovApply
    apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (centralPhysicalRowMarginal w hw K half left *
        listQSum
          (fun right =>
            leftObservable left *
              (centralPhysicalConditionalKernel
                  w hw K half left right *
                rightObservable right))
          states) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (listQSum_mul_left
            (leftObservable left)
            (fun right =>
              centralPhysicalConditionalKernel
                  w hw K half left right *
                rightObservable right)
            states))
    · exact Q'.eqv_symm
        (listQSum_mul_left
          (centralPhysicalRowMarginal
            w hw K half left)
          (fun right =>
            leftObservable left *
              (centralPhysicalConditionalKernel
                  w hw K half left right *
                rightObservable right))
          states)
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (rightSummand left) states)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro left hleft
      apply listQSum_congr_on
      intro right hright
      exact weightedAdjointSummand_recode
        leftObservable rightObservable hleft hright
    · refine Q'.eqv_trans _
        (listQSum
          (fun right =>
            listQSum
              (fun left => rightSummand left right)
              states)
          states) _ ?_ ?_
      · exact Q'.eqv_symm
          (listQSum_swap rightSummand states states)
      · unfold centralPhysicalWeightedInner
          centralPhysicalMarkovApply
        apply listQSum_congr
        intro right
        refine Q'.eqv_trans _
          (centralPhysicalRowMarginal w hw K half right *
            listQSum
              (fun left =>
                (centralPhysicalConditionalKernel
                    w hw K half right left *
                  leftObservable left) *
                rightObservable right)
              states) _ ?_ ?_
        · exact listQSum_mul_left
            (centralPhysicalRowMarginal
              w hw K half right)
            (fun left =>
              (centralPhysicalConditionalKernel
                  w hw K half right left *
                leftObservable left) *
              rightObservable right)
            states
        · exact Q'.mul_eqv_congr_left _ _ _
            (listQSum_mul_right
              (fun left =>
                centralPhysicalConditionalKernel
                    w hw K half right left *
                  leftObservable left)
              (rightObservable right)
              states)

/-- The physical marginal-mean-zero carrier is invariant under the exact
conditional BF4 operator. -/
theorem centralPhysicalMeanZero_markovApply
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {observable : EdgeLabelling → Q'}
    (hmean :
      CentralPhysicalMeanZero
        w hw K half observable) :
    CentralPhysicalMeanZero w hw K half
      (centralPhysicalMarkovApply
        w hw K half observable) := by
  unfold CentralPhysicalMeanZero at hmean ⊢
  exact Q'.eqv_trans _ _ _
    (centralPhysicalStationaryMean_markovApply
      w hw K half observable)
    hmean

#print axioms centralNormalizedPhysicalReflectedKernel_nonnegative
#print axioms centralNormalizedPhysicalReflectedKernel_symm
#print axioms centralPhysicalConditionalKernel_row_normalized
#print axioms centralPhysicalConditionalKernel_detailed_balance
#print axioms centralPhysicalRowMarginal_total_one
#print axioms centralPositiveRowMarginal_total_one
#print axioms centralPositiveHalfStates_length_pos
#print axioms centralPhysicalMarkovApply_one
#print axioms centralPhysicalStationaryMean_one
#print axioms
  centralPhysicalVacuumProjector_annihilates_meanZero
#print axioms
  centralPhysicalCenteredMarkovApply_eq_markov_of_meanZero
#print axioms centralPhysicalCenteredMarkovApply_one
#print axioms centralPhysicalStationaryMean_markovApply
#print axioms centralPhysicalMarkovApply_self_adjoint
#print axioms centralPhysicalMeanZero_markovApply

end YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
