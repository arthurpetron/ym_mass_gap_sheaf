/-
# Sum relative receiver-column bounds without a carrier-cardinality loss

The posterior-column `l1` budget is a finite sum over realized target
columns.  A uniform absolute bound per column would pay for the number of
columns, which grows with the slab.  The volume-safe input is instead
relative to the physical target weight of that column.

This module proves generic pointwise-to-aggregate compilers.  A
source-relative estimate on the unretained coefficient controls the signed
row defect by the total source weight.  A target-relative estimate on each
posterior column controls the posterior `l1` budget by the total target
weight.  Its preferred two-sector theorem accepts one row aggregate and one
combined posterior-sector aggregate directly.  Separate sector aggregates
and pointwise bounds remain sufficient adapters.  Thus later Yang--Mills
specializations can use exact finite mass identities instead of carrier
cardinality without requiring pointwise or sectorwise control when only the
combined posterior total is needed.

No relative estimate is inhabited here.  This is exact finite rational
summation, not stochastic mixing, an asymptotic estimate, a continuum limit,
or a mass-gap theorem.

Constructive contract: exact finite rational inequalities only; no choice,
`Classical`, `native_decide`, proof hole, noncomputable declaration, or new
axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientPosterior
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.FiniteDependentKernelCoefficientTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mul_right_local {A : Type}
    (value : A → Q') (factor : Q') : ∀ items : List A,
    listQSum (fun item => value item * factor) items ≈
      listQSum value items * factor
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv factor)
  | head :: tail => by
      change
        value head * factor +
            listQSum (fun item => value item * factor) tail ≈
          (value head + listQSum value tail) * factor
      refine Q'.eqv_trans _
        (value head * factor + listQSum value tail * factor) _
        (Q'.add_eqv_congr_left (value head * factor) _ _
          (listQSum_mul_right_local value factor tail)) ?_
      exact Q'.eqv_symm
        (Q'.add_mul_eqv (value head) (listQSum value tail) factor)

private theorem abs_mul_nonnegative_left_eqv_local
    (weight value : Q') (hweight : (0 : Q') ≤ weight) :
    Q'.abs (weight * value) ≈ weight * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * weight)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv weight value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * weight) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hweight) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) weight

private theorem abs_nonnegative_outer_factors_eqv_local
    (weight value factor : Q')
    (hweight : (0 : Q') ≤ weight) (hfactor : (0 : Q') ≤ factor) :
    Q'.abs ((weight * value) * factor) ≈
      (weight * factor) * Q'.abs value := by
  have hreorder :
      (weight * value) * factor ≈ (weight * factor) * value := by
    refine Q'.eqv_trans _ (weight * (value * factor)) _
      (Q'.mul_assoc_eqv weight value factor) ?_
    refine Q'.eqv_trans _ (weight * (factor * value)) _
      (Q'.mul_eqv_congr_left weight _ _
        (Q'.mul_comm_eqv value factor)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv weight factor value)
  refine Q'.eqv_trans _ (Q'.abs ((weight * factor) * value)) _
    (Q'.abs_eqv_congr hreorder) ?_
  exact abs_mul_nonnegative_left_eqv_local
    (weight * factor) value
    (Q'.mul_nonneg weight factor hweight hfactor)

namespace FiniteDependentCoefficientTransport

variable {Source Target : Type} [DecidableEq Target]

/-! ## Aggregate coefficient mass through incomplete rows -/

/-- Absolute source coefficient mass retained by the dependent rows. -/
def retainedSourceCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source =>
      (data.sourceWeight source * data.rowMass source) *
        Q'.abs (data.sourceCoefficient source))
    data.sources

/-- Absolute source coefficient mass omitted by the dependent rows. -/
def unretainedSourceCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source =>
      (data.sourceWeight source *
          ((1 : Q') + -data.rowMass source)) *
        Q'.abs (data.sourceCoefficient source))
    data.sources

/-- Full absolute coefficient mass on the source carrier. -/
def sourceCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source =>
      data.sourceWeight source * Q'.abs (data.sourceCoefficient source))
    data.sources

/-- Full absolute coefficient mass on the target carrier. -/
def targetCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun target =>
      data.targetWeight target * Q'.abs (data.targetCoefficient target))
    data.targets

/-- Absolute mass of the transported source coefficient after regrouping by
target column. -/
def transportedSourceCoefficientColumnL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun target => Q'.abs (data.transportedSourceCoefficientColumnMass target))
    data.targets

/-- Finite Fubini sends the absolute transported coefficient mass back to the
retained source rows.  Unlike a pointwise column estimate, this bound needs no
column-capacity hypothesis and remains valid when the target carrier contains
points outside the realization image. -/
theorem transportedSourceCoefficientColumnL1_le_retainedSourceCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice) :
    data.transportedSourceCoefficientColumnL1 ≤
      data.retainedSourceCoefficientL1 := by
  let pushed := fun source target =>
    dependentKernelPushforwardWeight
      data.Choice data.choices data.localWeight data.realize source target
  have hpushed : ∀ source target, (0 : Q') ≤ pushed source target := by
    intro source target
    exact dependentKernelPushforwardWeight_nonnegative
      data.Choice data.choices data.localWeight data.realize source target
      (hlocalWeight source)
  have hcolumns :
      data.transportedSourceCoefficientColumnL1 ≤
        listQSum
          (fun target =>
            listQSum
              (fun source =>
                Q'.abs
                  ((data.sourceWeight source * data.sourceCoefficient source) *
                    pushed source target))
              data.sources)
          data.targets := by
    unfold transportedSourceCoefficientColumnL1
    apply listQSum_le_termwise_local
    intro target _
    unfold transportedSourceCoefficientColumnMass
    simpa only [pushed] using
      abs_listQSum_le_sum_abs_local
        (fun source =>
          (data.sourceWeight source * data.sourceCoefficient source) *
            pushed source target)
        data.sources
  have hfubini :
      listQSum
          (fun target =>
            listQSum
              (fun source =>
                Q'.abs
                  ((data.sourceWeight source * data.sourceCoefficient source) *
                    pushed source target))
              data.sources)
          data.targets ≈
        data.retainedSourceCoefficientL1 := by
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          listQSum
            (fun target =>
              Q'.abs
                ((data.sourceWeight source * data.sourceCoefficient source) *
                  pushed source target))
            data.targets)
        data.sources) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_swap
          (fun target source =>
            Q'.abs
              ((data.sourceWeight source * data.sourceCoefficient source) *
                pushed source target))
          data.targets data.sources)
    · unfold retainedSourceCoefficientL1
      apply listQSum_congr_on
      intro source hsource
      have hpushedTotal :
          listQSum (pushed source) data.targets ≈ data.rowMass source := by
        exact Q'.eqv_trans _ _ _
          (kernelPushforwardWeight_total
            (data.choices source) (data.localWeight source)
            (data.realize source) data.targets data.targets_nodup
            (data.coverage source hsource))
          (data.row_mass source hsource)
      refine Q'.eqv_trans _
        (listQSum
          (fun target =>
            (data.sourceWeight source * pushed source target) *
              Q'.abs (data.sourceCoefficient source))
          data.targets) _ ?_ ?_
      · apply listQSum_congr
        intro target
        exact abs_nonnegative_outer_factors_eqv_local
          (data.sourceWeight source) (data.sourceCoefficient source)
          (pushed source target) (hsourceWeight source hsource)
          (hpushed source target)
      · refine Q'.eqv_trans _
          (listQSum
              (fun target => data.sourceWeight source * pushed source target)
              data.targets *
            Q'.abs (data.sourceCoefficient source)) _
          (listQSum_mul_right_local
            (fun target => data.sourceWeight source * pushed source target)
            (Q'.abs (data.sourceCoefficient source)) data.targets) ?_
        refine Q'.mul_eqv_congr_right _ _
          (Q'.abs (data.sourceCoefficient source)) ?_
        refine Q'.eqv_trans _
          (data.sourceWeight source * listQSum (pushed source) data.targets) _
          (listQSum_mul_left
            (data.sourceWeight source) (pushed source) data.targets) ?_
        exact Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
          hpushedTotal
  exact Q'.le_trans' _ _ _ hcolumns (Q'.le_of_eqv hfubini)

/-- The posterior mismatch is bounded by the retained source coefficient
mass plus the complete target coefficient mass.  This is the aggregate,
coverage-insensitive alternative to uniform pointwise column calibration. -/
theorem posteriorColumnCoefficientL1_le_retainedSource_add_targetCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice)
    (htargetWeight : ∀ target, target ∈ data.targets →
      (0 : Q') ≤ data.targetWeight target) :
    data.posteriorColumnCoefficientL1 ≤
      data.retainedSourceCoefficientL1 + data.targetCoefficientL1 := by
  have htriangle :
      data.posteriorColumnCoefficientL1 ≤
        listQSum
          (fun target =>
            Q'.abs (data.transportedSourceCoefficientColumnMass target) +
              Q'.abs (data.targetWeight target * data.targetCoefficient target))
          data.targets := by
    unfold posteriorColumnCoefficientL1
    apply listQSum_le_termwise_local
    intro target _
    refine Q'.le_trans' _
      (Q'.abs (data.transportedSourceCoefficientColumnMass target) +
        Q'.abs (-(data.targetWeight target * data.targetCoefficient target))) _
      (Q'.abs_add_le'
        (data.transportedSourceCoefficientColumnMass target)
        (-(data.targetWeight target * data.targetCoefficient target))) ?_
    exact Q'.add_le_add
      (Q'.le_refl' _)
      (Q'.le_of_eqv
        (Q'.abs_neg' (data.targetWeight target * data.targetCoefficient target)))
  have hsplit :
      listQSum
          (fun target =>
            Q'.abs (data.transportedSourceCoefficientColumnMass target) +
              Q'.abs (data.targetWeight target * data.targetCoefficient target))
          data.targets ≈
        data.transportedSourceCoefficientColumnL1 + data.targetCoefficientL1 := by
    refine Q'.eqv_trans _
      (listQSum
          (fun target =>
            Q'.abs (data.transportedSourceCoefficientColumnMass target))
          data.targets +
        listQSum
          (fun target =>
            Q'.abs (data.targetWeight target * data.targetCoefficient target))
          data.targets) _
      (listQSum_add _ _ data.targets) ?_
    unfold transportedSourceCoefficientColumnL1 targetCoefficientL1
    exact Q'.add_eqv_congr_left _ _ _
      (listQSum_congr_on
        (fun target =>
          Q'.abs (data.targetWeight target * data.targetCoefficient target))
        (fun target =>
          data.targetWeight target * Q'.abs (data.targetCoefficient target))
        data.targets
        (fun target htarget =>
          abs_mul_nonnegative_left_eqv_local
            (data.targetWeight target) (data.targetCoefficient target)
            (htargetWeight target htarget)))
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add
        (data.transportedSourceCoefficientColumnL1_le_retainedSourceCoefficientL1
          hsourceWeight hlocalWeight)
        (Q'.le_refl' data.targetCoefficientL1)))

/-- If every row has mass at most one, its omitted and retained absolute
source coefficient budgets recombine exactly to the full source budget.  The
row defect plus the complete posterior mismatch is therefore controlled by
the two full carrier coefficient `l1` masses, without pointwise calibration,
column capacity, or a carrier-cardinality factor. -/
theorem rowAbs_add_posteriorColumnL1_le_source_add_targetCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice)
    (htargetWeight : ∀ target, target ∈ data.targets →
      (0 : Q') ≤ data.targetWeight target)
    (hrowMass : ∀ source, source ∈ data.sources →
      data.rowMass source ≤ 1) :
    Q'.abs data.rowCoefficientDefect +
        data.posteriorColumnCoefficientL1 ≤
      data.sourceCoefficientL1 + data.targetCoefficientL1 := by
  have hrow :
      Q'.abs data.rowCoefficientDefect ≤
        data.unretainedSourceCoefficientL1 := by
    refine Q'.le_trans' _
      (listQSum
        (fun source =>
          Q'.abs
            (data.sourceWeight source *
              (data.sourceCoefficient source *
                ((1 : Q') + -data.rowMass source))))
        data.sources) _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr data.rowCoefficientDefect_eqv_unretained))
        (abs_listQSum_le_sum_abs_local _ _)) ?_
    exact Q'.le_of_eqv
      (listQSum_congr_on
        (fun source =>
          Q'.abs
            (data.sourceWeight source *
              (data.sourceCoefficient source *
                ((1 : Q') + -data.rowMass source))))
        (fun source =>
          (data.sourceWeight source *
              ((1 : Q') + -data.rowMass source)) *
            Q'.abs (data.sourceCoefficient source))
        data.sources
        (fun source hsource => by
          refine Q'.eqv_trans _
            (Q'.abs
              ((data.sourceWeight source * data.sourceCoefficient source) *
                ((1 : Q') + -data.rowMass source))) _
            (Q'.abs_eqv_congr
              (Q'.eqv_symm
                (Q'.mul_assoc_eqv
                  (data.sourceWeight source) (data.sourceCoefficient source)
                  ((1 : Q') + -data.rowMass source)))) ?_
          exact abs_nonnegative_outer_factors_eqv_local
            (data.sourceWeight source) (data.sourceCoefficient source)
            ((1 : Q') + -data.rowMass source)
            (hsourceWeight source hsource)
            (Q'.sub_nonneg_of_le (hrowMass source hsource))))
  have hrecombine :
      data.unretainedSourceCoefficientL1 +
          data.retainedSourceCoefficientL1 ≈
        data.sourceCoefficientL1 := by
    unfold unretainedSourceCoefficientL1 retainedSourceCoefficientL1
      sourceCoefficientL1
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          (data.sourceWeight source *
              ((1 : Q') + -data.rowMass source)) *
              Q'.abs (data.sourceCoefficient source) +
            (data.sourceWeight source * data.rowMass source) *
              Q'.abs (data.sourceCoefficient source))
        data.sources) _
      (Q'.eqv_symm (listQSum_add _ _ data.sources)) ?_
    apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      ((data.sourceWeight source *
          ((1 : Q') + -data.rowMass source) +
        data.sourceWeight source * data.rowMass source) *
        Q'.abs (data.sourceCoefficient source)) _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (data.sourceWeight source *
            ((1 : Q') + -data.rowMass source))
          (data.sourceWeight source * data.rowMass source)
          (Q'.abs (data.sourceCoefficient source)))) ?_
    refine Q'.eqv_trans _
      (data.sourceWeight source *
          (((1 : Q') + -data.rowMass source) + data.rowMass source) *
        Q'.abs (data.sourceCoefficient source)) _
      (Q'.mul_eqv_congr_right _ _
        (Q'.abs (data.sourceCoefficient source))
        (Q'.eqv_symm
          (Q'.mul_add_eqv
            (data.sourceWeight source)
            ((1 : Q') + -data.rowMass source)
            (data.rowMass source)))) ?_
    refine Q'.mul_eqv_congr_right _ _
      (Q'.abs (data.sourceCoefficient source)) ?_
    refine Q'.eqv_trans _ (data.sourceWeight source * 1) _
      (Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
        (Q'.eqv_trans _
          (1 + ((-data.rowMass source) + data.rowMass source)) _
          (Q'.add_assoc_eqv
            1 (-data.rowMass source) (data.rowMass source))
          (Q'.eqv_trans _ (1 + 0) _
            (Q'.add_eqv_congr_left 1
              ((-data.rowMass source) + data.rowMass source) 0
              (Q'.neg_add_self_eqv (data.rowMass source)))
            (Q'.eqv_of_eq (Q'.add_zero' 1))))) ?_
    exact Q'.mul_one_eqv (data.sourceWeight source)
  have hposterior :=
    data.posteriorColumnCoefficientL1_le_retainedSource_add_targetCoefficientL1
      hsourceWeight hlocalWeight htargetWeight
  refine Q'.le_trans' _
    (data.unretainedSourceCoefficientL1 +
      (data.retainedSourceCoefficientL1 + data.targetCoefficientL1)) _
    (Q'.add_le_add hrow hposterior) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _
    ((data.unretainedSourceCoefficientL1 +
        data.retainedSourceCoefficientL1) + data.targetCoefficientL1) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv
        data.unretainedSourceCoefficientL1
        data.retainedSourceCoefficientL1 data.targetCoefficientL1)) ?_)
  exact Q'.add_eqv_congr_right _ _ data.targetCoefficientL1 hrecombine

/-- A pointwise bound on the coefficient carried by the unretained part of
each row sums against total source weight, with no source-cardinality factor. -/
theorem rowCoefficientDefect_abs_le_relativeSourceWeight
    (data : FiniteDependentCoefficientTransport Source Target)
    (relative : Q')
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hrelative : ∀ source, source ∈ data.sources →
      Q'.abs
          (data.sourceCoefficient source *
            ((1 : Q') + -data.rowMass source)) ≤ relative) :
    Q'.abs data.rowCoefficientDefect ≤
      relative * listQSum data.sourceWeight data.sources := by
  let residual := fun source =>
    data.sourceCoefficient source * ((1 : Q') + -data.rowMass source)
  have htriangle :
      Q'.abs data.rowCoefficientDefect ≤
        listQSum
          (fun source => Q'.abs (data.sourceWeight source * residual source))
          data.sources := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr data.rowCoefficientDefect_eqv_unretained))
      (abs_listQSum_le_sum_abs_local _ _)
  have htermwise :
      listQSum
          (fun source => Q'.abs (data.sourceWeight source * residual source))
          data.sources ≤
        listQSum
          (fun source => data.sourceWeight source * relative)
          data.sources := by
    apply listQSum_le_termwise_local
    intro source hsource
    refine Q'.le_trans'
      (Q'.abs (data.sourceWeight source * residual source))
      (data.sourceWeight source * Q'.abs (residual source))
      (data.sourceWeight source * relative)
      (Q'.le_of_eqv
        (abs_mul_nonnegative_left_eqv_local
          (data.sourceWeight source) (residual source)
          (hsourceWeight source hsource))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ (data.sourceWeight source)
      (by simpa only [residual] using hrelative source hsource)
      (hsourceWeight source hsource)
  have hfactor :
      listQSum
          (fun source => data.sourceWeight source * relative)
          data.sources ≈
        relative * listQSum data.sourceWeight data.sources := by
    refine Q'.eqv_trans _
      (listQSum
        (fun source => relative * data.sourceWeight source)
        data.sources) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact Q'.mul_comm_eqv (data.sourceWeight source) relative
    · exact listQSum_mul_left relative data.sourceWeight data.sources
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ htermwise (Q'.le_of_eqv hfactor))

/-- Target-weight-relative posterior errors sum against total target mass,
not the number of target columns. -/
theorem posteriorColumnCoefficientL1_le_relativeTargetWeight
    (data : FiniteDependentCoefficientTransport Source Target)
    (relative : Q')
    (hrelative : ∀ target, target ∈ data.targets →
      Q'.abs
          (data.transportedSourceCoefficientColumnMass target -
            data.targetWeight target * data.targetCoefficient target) ≤
        relative * data.targetWeight target) :
    data.posteriorColumnCoefficientL1 ≤
      relative * listQSum data.targetWeight data.targets := by
  unfold posteriorColumnCoefficientL1
  have hsum :
      listQSum
          (fun target =>
            Q'.abs
              (data.transportedSourceCoefficientColumnMass target -
                data.targetWeight target * data.targetCoefficient target))
          data.targets ≤
        listQSum
          (fun target => relative * data.targetWeight target)
          data.targets := by
    apply listQSum_le_termwise_local
    exact hrelative
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (listQSum_mul_left relative data.targetWeight data.targets))

/-- If all carried source coefficients have a common absolute ceiling and a
physical target column has sufficient incoming-mass capacity, then the
absolute signed coefficient arriving in that column is bounded by the same
ceiling times its target weight. -/
theorem transportedSourceCoefficientColumnMass_abs_le_uniformSourceCoefficient
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice)
    (hsourceCoefficient : ∀ source, source ∈ data.sources →
      Q'.abs (data.sourceCoefficient source) ≤ sourceRelative)
    (target : Target)
    (hcolumnCapacity :
      listQSum
          (fun source => data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
          data.sources ≤
        data.targetWeight target) :
    Q'.abs (data.transportedSourceCoefficientColumnMass target) ≤
      sourceRelative * data.targetWeight target := by
  let pushed := fun source =>
    dependentKernelPushforwardWeight
      data.Choice data.choices data.localWeight data.realize source target
  have hpushed : ∀ source, (0 : Q') ≤ pushed source := by
    intro source
    exact dependentKernelPushforwardWeight_nonnegative
      data.Choice data.choices data.localWeight data.realize source target
      (hlocalWeight source)
  have htriangle :
      Q'.abs (data.transportedSourceCoefficientColumnMass target) ≤
        listQSum
          (fun source =>
            Q'.abs
              ((data.sourceWeight source * data.sourceCoefficient source) *
                pushed source))
          data.sources := by
    unfold transportedSourceCoefficientColumnMass
    simpa only [pushed] using
      abs_listQSum_le_sum_abs_local
        (fun source =>
          (data.sourceWeight source * data.sourceCoefficient source) *
            pushed source)
        data.sources
  have htermwise :
      listQSum
          (fun source =>
            Q'.abs
              ((data.sourceWeight source * data.sourceCoefficient source) *
                pushed source))
          data.sources ≤
        listQSum
          (fun source =>
            (data.sourceWeight source * pushed source) * sourceRelative)
          data.sources := by
    apply listQSum_le_termwise_local
    intro source hsource
    refine Q'.le_trans' _
      ((data.sourceWeight source * pushed source) *
        Q'.abs (data.sourceCoefficient source)) _
      (Q'.le_of_eqv
        (abs_nonnegative_outer_factors_eqv_local
          (data.sourceWeight source) (data.sourceCoefficient source)
          (pushed source) (hsourceWeight source hsource)
          (hpushed source))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _
      (data.sourceWeight source * pushed source)
      (hsourceCoefficient source hsource)
      (Q'.mul_nonneg _ _
        (hsourceWeight source hsource) (hpushed source))
  have hfactor :
      listQSum
          (fun source =>
            (data.sourceWeight source * pushed source) * sourceRelative)
          data.sources ≈
        sourceRelative *
          listQSum
            (fun source => data.sourceWeight source * pushed source)
            data.sources := by
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          sourceRelative * (data.sourceWeight source * pushed source))
        data.sources) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact Q'.mul_comm_eqv
        (data.sourceWeight source * pushed source) sourceRelative
    · exact listQSum_mul_left sourceRelative
        (fun source => data.sourceWeight source * pushed source)
        data.sources
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (listQSum
      (fun source => data.sourceWeight source * pushed source)
      data.sources)
    (data.targetWeight target) sourceRelative
    (by simpa only [pushed] using hcolumnCapacity) hsourceRelative
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ htermwise
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hscaled))

/-- Uniform source- and target-coefficient bounds plus physical column
capacity give the required target-weight-relative posterior estimate. -/
theorem posteriorColumnCoefficient_abs_le_uniformCoefficientBounds
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice)
    (hsourceCoefficient : ∀ source, source ∈ data.sources →
      Q'.abs (data.sourceCoefficient source) ≤ sourceRelative)
    (htargetWeight : ∀ target, target ∈ data.targets →
      (0 : Q') ≤ data.targetWeight target)
    (htargetCoefficient : ∀ target, target ∈ data.targets →
      Q'.abs (data.targetCoefficient target) ≤ targetRelative)
    (hcolumnCapacity : ∀ target, target ∈ data.targets →
      listQSum
          (fun source => data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
          data.sources ≤
        data.targetWeight target)
    (target : Target) (htarget : target ∈ data.targets) :
    Q'.abs
        (data.transportedSourceCoefficientColumnMass target -
          data.targetWeight target * data.targetCoefficient target) ≤
      (sourceRelative + targetRelative) * data.targetWeight target := by
  let transported := data.transportedSourceCoefficientColumnMass target
  let targetTerm := data.targetWeight target * data.targetCoefficient target
  have htransported : Q'.abs transported ≤
      sourceRelative * data.targetWeight target := by
    apply data.transportedSourceCoefficientColumnMass_abs_le_uniformSourceCoefficient
      sourceRelative hsourceRelative hsourceWeight hlocalWeight
      hsourceCoefficient target
    exact hcolumnCapacity target htarget
  have htargetTerm : Q'.abs targetTerm ≤
      data.targetWeight target * targetRelative := by
    refine Q'.le_trans' _
      (data.targetWeight target * Q'.abs (data.targetCoefficient target)) _
      (Q'.le_of_eqv
        (abs_mul_nonnegative_left_eqv_local
          (data.targetWeight target) (data.targetCoefficient target)
          (htargetWeight target htarget))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _
      (data.targetWeight target)
      (htargetCoefficient target htarget)
      (htargetWeight target htarget)
  have htriangle : Q'.abs (transported - targetTerm) ≤
      Q'.abs transported + Q'.abs targetTerm := by
    refine Q'.le_trans' _
      (Q'.abs transported + Q'.abs (-targetTerm)) _
      (Q'.abs_add_le' transported (-targetTerm)) ?_
    exact Q'.add_le_add
      (Q'.le_refl' (Q'.abs transported))
      (Q'.le_of_eqv (Q'.abs_neg' targetTerm))
  have hsum := Q'.add_le_add htransported htargetTerm
  have hfactor :
      sourceRelative * data.targetWeight target +
          data.targetWeight target * targetRelative ≈
        (sourceRelative + targetRelative) * data.targetWeight target := by
    refine Q'.eqv_trans _
      (sourceRelative * data.targetWeight target +
        targetRelative * data.targetWeight target) _
      (Q'.add_eqv_congr_left
        (sourceRelative * data.targetWeight target) _ _
        (Q'.mul_comm_eqv
          (data.targetWeight target) targetRelative)) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv sourceRelative targetRelative
        (data.targetWeight target))
  simpa only [transported, targetTerm] using
    Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hfactor))

/-- The uniform coefficient calibration bound sums over all posterior
columns without paying their cardinality. -/
theorem posteriorColumnCoefficientL1_le_uniformCoefficientBounds
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hlocalWeight : ∀ source choice,
      choice ∈ data.choices source →
        (0 : Q') ≤ data.localWeight source choice)
    (hsourceCoefficient : ∀ source, source ∈ data.sources →
      Q'.abs (data.sourceCoefficient source) ≤ sourceRelative)
    (htargetWeight : ∀ target, target ∈ data.targets →
      (0 : Q') ≤ data.targetWeight target)
    (htargetCoefficient : ∀ target, target ∈ data.targets →
      Q'.abs (data.targetCoefficient target) ≤ targetRelative)
    (hcolumnCapacity : ∀ target, target ∈ data.targets →
      listQSum
          (fun source => data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
          data.sources ≤
        data.targetWeight target) :
    data.posteriorColumnCoefficientL1 ≤
      (sourceRelative + targetRelative) *
        listQSum data.targetWeight data.targets := by
  apply data.posteriorColumnCoefficientL1_le_relativeTargetWeight
  intro target htarget
  exact data.posteriorColumnCoefficient_abs_le_uniformCoefficientBounds
    sourceRelative targetRelative hsourceRelative
    hsourceWeight hlocalWeight hsourceCoefficient
    htargetWeight htargetCoefficient hcolumnCapacity target htarget

/-- The row and posterior-column compilers combine without changing either
relative constant. -/
theorem rowAbs_add_posteriorColumnL1_le_relativeWeights
    (data : FiniteDependentCoefficientTransport Source Target)
    (rowRelative columnRelative : Q')
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hrow : ∀ source, source ∈ data.sources →
      Q'.abs
          (data.sourceCoefficient source *
            ((1 : Q') + -data.rowMass source)) ≤ rowRelative)
    (hcolumn : ∀ target, target ∈ data.targets →
      Q'.abs
          (data.transportedSourceCoefficientColumnMass target -
            data.targetWeight target * data.targetCoefficient target) ≤
        columnRelative * data.targetWeight target) :
    Q'.abs data.rowCoefficientDefect + data.posteriorColumnCoefficientL1 ≤
      rowRelative * listQSum data.sourceWeight data.sources +
        columnRelative * listQSum data.targetWeight data.targets :=
  Q'.add_le_add
    (data.rowCoefficientDefect_abs_le_relativeSourceWeight
      rowRelative hsourceWeight hrow)
    (data.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hcolumn)

/-- A row aggregate and one combined posterior-sector aggregate pay their
relative ceilings against a common mass cap.  This is the weakest interface
in this module: it does not require the posterior estimate to split between
the two target sectors. -/
theorem rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_combinedAggregate
    {ConnectedSource ConnectedTarget DisconnectedSource DisconnectedTarget : Type}
    [DecidableEq ConnectedTarget] [DecidableEq DisconnectedTarget]
    (connected :
      FiniteDependentCoefficientTransport ConnectedSource ConnectedTarget)
    (disconnected :
      FiniteDependentCoefficientTransport DisconnectedSource DisconnectedTarget)
    (rowRelative columnRelative massCap : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrowBound :
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hcolumnsBound :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          (listQSum connected.targetWeight connected.targets +
            listQSum disconnected.targetWeight disconnected.targets))
    (hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ massCap)
    (htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤ massCap) :
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        (rowRelative + columnRelative) * massCap := by
  have hrowScaled :
      rowRelative * listQSum connected.sourceWeight connected.sources ≤
        rowRelative * massCap :=
    Q'.mul_le_mul_of_nonneg_left _ _ rowRelative hsourceMass hrowRelative
  have hcolumns :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative * massCap := by
    exact Q'.le_trans' _ _ _ hcolumnsBound
      (Q'.mul_le_mul_of_nonneg_left _ _ columnRelative
        htargetMass hcolumnRelative)
  refine Q'.le_trans' _
    (Q'.abs connected.rowCoefficientDefect +
      (connected.posteriorColumnCoefficientL1 +
        disconnected.posteriorColumnCoefficientL1)) _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        (Q'.abs connected.rowCoefficientDefect)
        connected.posteriorColumnCoefficientL1
        disconnected.posteriorColumnCoefficientL1)) ?_
  refine Q'.le_trans' _
    (rowRelative * massCap + columnRelative * massCap) _
    (Q'.add_le_add
      (Q'.le_trans' _ _ _ hrowBound hrowScaled) hcolumns) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.add_mul_eqv rowRelative columnRelative massCap))

/-- Separate row and posterior-sector aggregates compile to the weaker
combined-posterior interface before paying the common mass cap. -/
theorem rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
    {ConnectedSource ConnectedTarget DisconnectedSource DisconnectedTarget : Type}
    [DecidableEq ConnectedTarget] [DecidableEq DisconnectedTarget]
    (connected :
      FiniteDependentCoefficientTransport ConnectedSource ConnectedTarget)
    (disconnected :
      FiniteDependentCoefficientTransport DisconnectedSource DisconnectedTarget)
    (rowRelative columnRelative massCap : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrowBound :
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hconnectedBound :
      connected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum connected.targetWeight connected.targets)
    (hdisconnectedBound :
      disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum disconnected.targetWeight disconnected.targets)
    (hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ massCap)
    (htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤ massCap) :
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        (rowRelative + columnRelative) * massCap := by
  have hcolumnsBound :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          (listQSum connected.targetWeight connected.targets +
            listQSum disconnected.targetWeight disconnected.targets) := by
    refine Q'.le_trans' _
      (columnRelative * listQSum connected.targetWeight connected.targets +
        columnRelative * listQSum disconnected.targetWeight
          disconnected.targets) _
      (Q'.add_le_add hconnectedBound hdisconnectedBound) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_add_eqv columnRelative
          (listQSum connected.targetWeight connected.targets)
          (listQSum disconnected.targetWeight disconnected.targets)))
  exact
    connected.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_combinedAggregate
      disconnected rowRelative columnRelative massCap
      hrowRelative hcolumnRelative hrowBound hcolumnsBound
      hsourceMass htargetMass

/-- Pointwise source- and target-relative estimates compile to the weaker
aggregate interface, then pay the same common mass cap without a carrier
cardinality factor. -/
theorem rowAbs_add_twoPosteriorColumnL1_le_commonMassCap
    {ConnectedSource ConnectedTarget DisconnectedSource DisconnectedTarget : Type}
    [DecidableEq ConnectedTarget] [DecidableEq DisconnectedTarget]
    (connected :
      FiniteDependentCoefficientTransport ConnectedSource ConnectedTarget)
    (disconnected :
      FiniteDependentCoefficientTransport DisconnectedSource DisconnectedTarget)
    (rowRelative columnRelative massCap : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hsourceWeight : ∀ source, source ∈ connected.sources →
      (0 : Q') ≤ connected.sourceWeight source)
    (hrow : ∀ source, source ∈ connected.sources →
      Q'.abs
          (connected.sourceCoefficient source *
            ((1 : Q') + -connected.rowMass source)) ≤ rowRelative)
    (hconnectedColumn : ∀ target, target ∈ connected.targets →
      Q'.abs
          (connected.transportedSourceCoefficientColumnMass target -
            connected.targetWeight target *
              connected.targetCoefficient target) ≤
        columnRelative * connected.targetWeight target)
    (hdisconnectedColumn : ∀ target, target ∈ disconnected.targets →
      Q'.abs
          (disconnected.transportedSourceCoefficientColumnMass target -
            disconnected.targetWeight target *
              disconnected.targetCoefficient target) ≤
        columnRelative * disconnected.targetWeight target)
    (hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ massCap)
    (htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤ massCap) :
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        (rowRelative + columnRelative) * massCap := by
  have hrowBound :=
    connected.rowCoefficientDefect_abs_le_relativeSourceWeight
      rowRelative hsourceWeight hrow
  have hconnectedBound :=
    connected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hconnectedColumn
  have hdisconnectedBound :=
    disconnected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hdisconnectedColumn
  exact connected.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
    disconnected rowRelative columnRelative massCap
    hrowRelative hcolumnRelative hrowBound hconnectedBound hdisconnectedBound
    hsourceMass htargetMass

end FiniteDependentCoefficientTransport

#print axioms FiniteDependentCoefficientTransport.rowCoefficientDefect_abs_le_relativeSourceWeight
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_le_relativeTargetWeight
#print axioms FiniteDependentCoefficientTransport.retainedSourceCoefficientL1
#print axioms FiniteDependentCoefficientTransport.unretainedSourceCoefficientL1
#print axioms FiniteDependentCoefficientTransport.sourceCoefficientL1
#print axioms FiniteDependentCoefficientTransport.targetCoefficientL1
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientColumnL1
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientColumnL1_le_retainedSourceCoefficientL1
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_le_retainedSource_add_targetCoefficientL1
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_posteriorColumnL1_le_source_add_targetCoefficientL1
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientColumnMass_abs_le_uniformSourceCoefficient
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficient_abs_le_uniformCoefficientBounds
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_le_uniformCoefficientBounds
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_posteriorColumnL1_le_relativeWeights
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_combinedAggregate
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap

end YMGap.Continuum.FiniteDependentKernelCoefficientTransport
