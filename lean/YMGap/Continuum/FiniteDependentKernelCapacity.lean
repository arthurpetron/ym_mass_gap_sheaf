/-
# Finite dependent stochastic transport with column capacity

A source-dependent recoupling law need not have one common output type: the
available channel carrier can depend on the source configuration.  A
deterministic realization sends each local channel to a common physical
target.  This module pushes every dependent row through that realization and
proves the finite transport principle needed by the slab switch:

* every local row has mass one;
* every realized physical column has enough target capacity;
* therefore total source mass is at most total target mass.

The theorem is exact finite Fubini.  It does not assert that a Yang--Mills
recoupling row satisfies the physical column-capacity inequality.

Constructive contract: exact `Q'`, finite lists, dependent carrier types, no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteDependentKernelCapacity

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Push a source-dependent finite row to one common target type -/

/-- Push one source-dependent finite row through its deterministic physical
target realization. -/
def dependentKernelPushforwardWeight
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target) : Q' :=
  kernelPushforwardWeight
    (choices source) (localWeight source) (realize source) target

theorem dependentKernelPushforwardWeight_nonnegative
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target)
    (hloc : ∀ choice, choice ∈ choices source →
      (0 : Q') ≤ localWeight source choice) :
    (0 : Q') ≤ dependentKernelPushforwardWeight
      Choice choices localWeight realize source target := by
  unfold dependentKernelPushforwardWeight
  exact kernelPushforwardWeight_nonnegative
    (choices source) (localWeight source) (realize source) target hloc

/-- A normalized dependent row remains normalized after realization on a
complete duplicate-free physical target list. -/
theorem dependentKernelPushforwardWeight_row_normalized
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (targets : List Target) (targets_nodup : targets.Nodup)
    (source : Source)
    (hcoverage : ∀ choice, choice ∈ choices source →
      realize source choice ∈ targets)
    (hrow : listQSum (localWeight source) (choices source) ≈ 1) :
    listQSum
        (dependentKernelPushforwardWeight
          Choice choices localWeight realize source)
        targets ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (kernelPushforwardWeight_total
      (choices source) (localWeight source) (realize source)
      targets targets_nodup hcoverage)
    hrow

/-- If source and target weights agree on every realized channel that enters
one target, multiplying that pushed row by either weight gives the same
result. -/
theorem source_mul_dependentKernelPushforwardWeight_eqv_target_mul
    {Source Target : Type} [DecidableEq Target]
    (sourceWeight : Source → Q') (targetWeight : Target → Q')
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target)
    (weight_preserved : ∀ choice,
      target = realize source choice →
        sourceWeight source ≈ targetWeight target) :
    sourceWeight source *
        dependentKernelPushforwardWeight
          Choice choices localWeight realize source target ≈
      targetWeight target *
        dependentKernelPushforwardWeight
          Choice choices localWeight realize source target := by
  unfold dependentKernelPushforwardWeight kernelPushforwardWeight
  refine Q'.eqv_trans _
    (listQSum
      (fun choice => sourceWeight source *
        (localWeight source choice *
          deterministicKernel (realize source) choice target))
      (choices source)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_mul_left
        (sourceWeight source)
        (fun choice => localWeight source choice *
          deterministicKernel (realize source) choice target)
        (choices source))
  refine Q'.eqv_trans _
    (listQSum
      (fun choice => targetWeight target *
        (localWeight source choice *
          deterministicKernel (realize source) choice target))
      (choices source)) _ ?_ ?_
  · apply listQSum_congr
    intro choice
    by_cases htarget : target = realize source choice
    · exact Q'.mul_eqv_congr_right _ _ _
        (weight_preserved choice htarget)
    · rw [deterministicKernel_off_image htarget]
      exact Q'.eqv_trans _ 0 _
        (Q'.eqv_trans _ (sourceWeight source * 0) _
          (Q'.mul_eqv_congr_left (sourceWeight source) _ 0
            (Q'.mul_zero_eqv (localWeight source choice)))
          (Q'.mul_zero_eqv (sourceWeight source)))
        (Q'.eqv_symm (Q'.eqv_trans _ (targetWeight target * 0) _
          (Q'.mul_eqv_congr_left (targetWeight target) _ 0
            (Q'.mul_zero_eqv (localWeight source choice)))
          (Q'.mul_zero_eqv (targetWeight target))))
  · exact listQSum_mul_left
      (targetWeight target)
      (fun choice => localWeight source choice *
        deterministicKernel (realize source) choice target)
      (choices source)

/-- Unweighted column capacity becomes physical weighted capacity whenever
realization preserves the source weight on its support. -/
theorem weightedColumn_le_of_columnCapacity
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source)
    (sourceWeight : Source → Q') (targetWeight : Target → Q')
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (target : Target)
    (targetWeight_nonnegative : (0 : Q') ≤ targetWeight target)
    (weight_preserved : ∀ source, source ∈ sources → ∀ choice,
      target = realize source choice →
        sourceWeight source ≈ targetWeight target)
    (column_capacity :
      listQSum
          (fun source => dependentKernelPushforwardWeight
            Choice choices localWeight realize source target)
          sources ≤ 1) :
    listQSum
        (fun source => sourceWeight source *
          dependentKernelPushforwardWeight
            Choice choices localWeight realize source target)
        sources ≤ targetWeight target := by
  let pushed : Source → Q' := fun source =>
    dependentKernelPushforwardWeight
      Choice choices localWeight realize source target
  have hweighted :
      listQSum (fun source => sourceWeight source * pushed source) sources ≈
        targetWeight target * listQSum pushed sources := by
    refine Q'.eqv_trans _
      (listQSum (fun source => targetWeight target * pushed source) sources) _
      (listQSum_congr_on
        (fun source => sourceWeight source * pushed source)
        (fun source => targetWeight target * pushed source)
        sources (fun source hsource =>
          source_mul_dependentKernelPushforwardWeight_eqv_target_mul
            sourceWeight targetWeight Choice choices localWeight realize
            source target
            (weight_preserved source hsource)))
      (listQSum_mul_left (targetWeight target) pushed sources)
  have hscaled :
      targetWeight target * listQSum pushed sources ≤
        targetWeight target * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      column_capacity targetWeight_nonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hweighted)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv (targetWeight target))))

/-! ## 2. Exact finite row-to-column contraction -/

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

/-- **Dependent stochastic rows plus physical column capacity imply total
mass domination.**

The local channel type may vary with the source.  `column_capacity` is the
only load-bearing physical hypothesis: after every dependent row is realized
on the common target carrier, the source-weighted mass entering a target is
at most that target's available weight. -/
theorem sourceWeight_total_le_of_dependentKernelCapacity
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (targets : List Target) (targetWeight : Target → Q')
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (targets_nodup : targets.Nodup)
    (coverage : ∀ source, source ∈ sources →
      ∀ choice, choice ∈ choices source →
        realize source choice ∈ targets)
    (row_normalized : ∀ source, source ∈ sources →
      listQSum (localWeight source) (choices source) ≈ 1)
    (column_capacity : ∀ target, target ∈ targets →
      listQSum
          (fun source => sourceWeight source *
            dependentKernelPushforwardWeight
              Choice choices localWeight realize source target)
          sources ≤ targetWeight target) :
    listQSum sourceWeight sources ≤ listQSum targetWeight targets := by
  let pushed : Source → Target → Q' :=
    dependentKernelPushforwardWeight
      Choice choices localWeight realize
  have hrow : ∀ source, source ∈ sources →
      listQSum (pushed source) targets ≈ 1 := by
    intro source hsource
    exact dependentKernelPushforwardWeight_row_normalized
      Choice choices localWeight realize targets targets_nodup source
      (coverage source hsource) (row_normalized source hsource)
  have hsourceRows :
      listQSum sourceWeight sources ≈
        listQSum
          (fun source =>
            listQSum
              (fun target => sourceWeight source * pushed source target)
              targets)
          sources := by
    apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_symm (Q'.eqv_trans _
      (sourceWeight source * listQSum (pushed source) targets) _
      (listQSum_mul_left
        (sourceWeight source) (pushed source) targets)
      (Q'.eqv_trans _ (sourceWeight source * 1) _
        (Q'.mul_eqv_congr_left (sourceWeight source) _ _
          (hrow source hsource))
        (Q'.mul_one_eqv (sourceWeight source))))
  have hsourceColumns :
      listQSum sourceWeight sources ≈
        listQSum
          (fun target =>
            listQSum
              (fun source => sourceWeight source * pushed source target)
              sources)
          targets :=
    Q'.eqv_trans _ _ _ hsourceRows
      (Q'.eqv_symm
        (listQSum_swap
          (fun source target => sourceWeight source * pushed source target)
          sources targets))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsourceColumns)
    (listQSum_le_termwise_local
      (fun target =>
        listQSum
          (fun source => sourceWeight source * pushed source target)
          sources)
      targetWeight targets column_capacity)

end YMGap.Continuum.FiniteDependentKernelCapacity

#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.dependentKernelPushforwardWeight
#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.dependentKernelPushforwardWeight_nonnegative
#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.dependentKernelPushforwardWeight_row_normalized
#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.source_mul_dependentKernelPushforwardWeight_eqv_target_mul
#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.weightedColumn_le_of_columnCapacity
#print axioms YMGap.Continuum.FiniteDependentKernelCapacity.sourceWeight_total_le_of_dependentKernelCapacity
