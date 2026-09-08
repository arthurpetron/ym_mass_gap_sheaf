/-
# Exact coefficient transport through a finite dependent kernel

A source-dependent finite row can transport scalar coefficients as well as
mass.  This module separates the signed source-to-target coefficient defect
into three exact pieces:

* coefficient mass omitted by incomplete source rows;
* coefficient variation along the retained source-choice edges;
* the difference between the realized incoming columns and the target mass.

The middle term is reindexed to the literal local choices, while the last
term is reindexed to the common target columns.  Thus later applications can
use successful-row estimates and column-capacity estimates without conflating
them.

No row-retention, coefficient-variation, or column-slack estimate is asserted
here.  Constructive contract: finite lists and exact `Q'` identities only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.FiniteCoefficientZeroExtension
import YMGap.Continuum.FiniteDependentKernelCapacity

namespace YMGap.Continuum.FiniteDependentKernelCoefficientTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_sub_eqv_local (scale left right : Q') :
    scale * (left + -right) ≈
      scale * left + -(scale * right) := by
  ring_qeqv

private theorem add_sub_cancel_middle_local (a middle c : Q') :
    a + -c ≈ (a + -middle) + (middle + -c) := by
  have hright :
      (a + -middle) + (middle + -c) ≈ a + -c := by
    refine Q'.eqv_trans _
      (a + ((-middle) + (middle + -c))) _
      (Q'.add_assoc_eqv a (-middle) (middle + -c)) ?_
    refine Q'.add_eqv_congr_left a _ _ ?_
    refine Q'.eqv_trans _ (((-middle) + middle) + -c) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle (-c))) ?_
    refine Q'.eqv_trans _ (0 + -c) _
      (Q'.add_eqv_congr_right ((-middle) + middle) 0 (-c)
        (Q'.neg_add_self_eqv middle)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-c))
  exact Q'.eqv_symm hright

private theorem three_defect_decomposition_local
    (source transportedSource transportedTarget target : Q') :
    source + -target ≈
      ((source + -transportedSource) +
        (transportedSource + -transportedTarget)) +
          (transportedTarget + -target) := by
  refine Q'.eqv_trans _
    ((source + -transportedSource) +
      (transportedSource + -target)) _
    (add_sub_cancel_middle_local source transportedSource target) ?_
  refine Q'.eqv_trans _
    ((source + -transportedSource) +
      ((transportedSource + -transportedTarget) +
        (transportedTarget + -target))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (source + -transportedSource) _ _
      (add_sub_cancel_middle_local transportedSource transportedTarget target)
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv
        (source + -transportedSource)
        (transportedSource + -transportedTarget)
        (transportedTarget + -target))

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') (items : List A) :
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items) := by
  induction items with
  | nil =>
      change (0 : Q') ≈ -(0 : Q')
      decide
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail)))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_neg_local right items)

private theorem edge_difference_sum_local
    {Choice : Type} (sourceCoefficient : Q')
    (targetCoefficient localWeight : Choice → Q')
    (choices : List Choice) :
    listQSum
        (fun choice =>
          (sourceCoefficient - targetCoefficient choice) *
            localWeight choice)
        choices ≈
      listQSum
          (fun choice => sourceCoefficient * localWeight choice)
          choices -
        listQSum
          (fun choice => targetCoefficient choice * localWeight choice)
          choices := by
  refine Q'.eqv_trans _
    (listQSum
      (fun choice =>
        sourceCoefficient * localWeight choice -
          targetCoefficient choice * localWeight choice)
      choices) _ ?_ ?_
  · apply listQSum_congr
    intro choice
    exact Q'.sub_mul_eqv sourceCoefficient
      (targetCoefficient choice) (localWeight choice)
  · exact listQSum_sub_local _ _ choices

private theorem row_unretained_factor_local
    (weight coefficient rowMass : Q') :
    weight * coefficient - weight * (coefficient * rowMass) ≈
      weight * (coefficient * ((1 : Q') + -rowMass)) := by
  have hinner :
      coefficient * ((1 : Q') + -rowMass) ≈
        coefficient + -(coefficient * rowMass) := by
    refine Q'.eqv_trans _
      (coefficient * 1 + coefficient * (-rowMass)) _
      (Q'.mul_add_eqv coefficient 1 (-rowMass)) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_one_eqv coefficient)
      (Q'.mul_neg_eqv coefficient rowMass)
  have hright :
      weight * (coefficient * ((1 : Q') + -rowMass)) ≈
        weight * coefficient + -(weight * (coefficient * rowMass)) := by
    refine Q'.eqv_trans _
      (weight * (coefficient + -(coefficient * rowMass))) _
      (Q'.mul_eqv_congr_left weight _ _ hinner) ?_
    refine Q'.eqv_trans _
      (weight * coefficient + weight * (-(coefficient * rowMass))) _
      (Q'.mul_add_eqv weight coefficient (-(coefficient * rowMass))) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_neg_eqv weight (coefficient * rowMass))
  exact Q'.eqv_symm hright

/-- All finite data needed for exact signed coefficient transport.  No
positivity or capacity field is required for the identities below. -/
structure FiniteDependentCoefficientTransport
    (Source Target : Type) [DecidableEq Target] : Type 1 where
  sources : List Source
  sourceWeight : Source → Q'
  sourceCoefficient : Source → Q'
  rowMass : Source → Q'
  targets : List Target
  targets_nodup : targets.Nodup
  targetWeight : Target → Q'
  targetCoefficient : Target → Q'
  Choice : Source → Type
  choices : (source : Source) → List (Choice source)
  localWeight : (source : Source) → Choice source → Q'
  realize : (source : Source) → Choice source → Target
  coverage : ∀ source, source ∈ sources →
    ∀ choice, choice ∈ choices source → realize source choice ∈ targets
  row_mass : ∀ source, source ∈ sources →
    listQSum (localWeight source) (choices source) ≈ rowMass source

/-- Linear reindexing of one dependent row through its deterministic target
realization. -/
theorem dependentKernelPushforwardWeight_reindex_mul
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (targets : List Target) (targets_nodup : targets.Nodup)
    (source : Source)
    (coverage : ∀ choice, choice ∈ choices source →
      realize source choice ∈ targets)
    (value : Target → Q') :
    listQSum
        (fun target =>
          dependentKernelPushforwardWeight
              Choice choices localWeight realize source target *
            value target)
        targets ≈
      listQSum
        (fun choice =>
          localWeight source choice * value (realize source choice))
        (choices source) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        finiteCoefficientZeroExtension
            (choices source) (localWeight source) (realize source) target *
          value target)
      targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_eqv_congr_right _ _ (value target)
      (kernelPushforwardWeight_eqv_fiberWeight
        (localWeight source) (realize source) target (choices source))
  · exact finiteCoefficientZeroExtension_reindex_mul
      (choices source) (localWeight source) (realize source)
      targets targets_nodup coverage value

namespace FiniteDependentCoefficientTransport

variable {Source Target : Type} [DecidableEq Target]

def sourceCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source => data.sourceWeight source * data.sourceCoefficient source)
    data.sources

def targetCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun target => data.targetWeight target * data.targetCoefficient target)
    data.targets

def transportedSourceCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source => data.sourceWeight source *
      (data.sourceCoefficient source * data.rowMass source))
    data.sources

def transportedTargetCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source => data.sourceWeight source *
      listQSum
        (fun target =>
          dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target * data.targetCoefficient target)
        data.targets)
    data.sources

def sourceEdgeCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source => data.sourceWeight source *
      listQSum
        (fun choice =>
          data.sourceCoefficient source * data.localWeight source choice)
        (data.choices source))
    data.sources

def targetEdgeCoefficientMass
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun source => data.sourceWeight source *
      listQSum
        (fun choice =>
          data.targetCoefficient (data.realize source choice) *
            data.localWeight source choice)
        (data.choices source))
    data.sources

def rowCoefficientDefect
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  data.sourceCoefficientMass - data.transportedSourceCoefficientMass

def edgeCoefficientDefect
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  data.sourceEdgeCoefficientMass - data.targetEdgeCoefficientMass

def columnCoefficientDefect
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  data.transportedTargetCoefficientMass - data.targetCoefficientMass

theorem transportedSourceCoefficientMass_eqv_edgeMass
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.transportedSourceCoefficientMass ≈
      data.sourceEdgeCoefficientMass := by
  unfold transportedSourceCoefficientMass sourceEdgeCoefficientMass
  apply listQSum_congr_on
  intro source hsource
  refine Q'.mul_eqv_congr_left (data.sourceWeight source) _ _ ?_
  refine Q'.eqv_trans _
    (data.sourceCoefficient source *
      listQSum (data.localWeight source) (data.choices source)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (data.sourceCoefficient source) _ _
      (Q'.eqv_symm (data.row_mass source hsource))
  · exact Q'.eqv_symm
      (listQSum_mul_left (data.sourceCoefficient source)
        (data.localWeight source) (data.choices source))

/-- The row debt is exactly the coefficient-weighted unretained part of each
source row.  This identity does not assert a sign for the coefficient. -/
theorem rowCoefficientDefect_eqv_unretained
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.rowCoefficientDefect ≈
      listQSum
        (fun source =>
          data.sourceWeight source *
            (data.sourceCoefficient source *
              ((1 : Q') + -data.rowMass source)))
        data.sources := by
  unfold rowCoefficientDefect sourceCoefficientMass
    transportedSourceCoefficientMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        data.sourceWeight source * data.sourceCoefficient source -
          data.sourceWeight source *
            (data.sourceCoefficient source * data.rowMass source))
      data.sources) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ data.sources)
  · apply listQSum_congr
    intro source
    exact row_unretained_factor_local
      (data.sourceWeight source) (data.sourceCoefficient source)
      (data.rowMass source)

theorem transportedTargetCoefficientMass_eqv_edgeMass
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.transportedTargetCoefficientMass ≈
      data.targetEdgeCoefficientMass := by
  unfold transportedTargetCoefficientMass targetEdgeCoefficientMass
  apply listQSum_congr_on
  intro source hsource
  refine Q'.mul_eqv_congr_left (data.sourceWeight source) _ _ ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun choice =>
        data.localWeight source choice *
          data.targetCoefficient (data.realize source choice))
      (data.choices source)) _ ?_ ?_
  · exact dependentKernelPushforwardWeight_reindex_mul
      data.Choice data.choices data.localWeight data.realize
      data.targets data.targets_nodup source
      (data.coverage source hsource) data.targetCoefficient
  · apply listQSum_congr
    intro choice
    exact Q'.mul_comm_eqv
      (data.localWeight source choice)
      (data.targetCoefficient (data.realize source choice))

/-- The edge defect is the literal weighted coefficient variation along the
retained source-choice edges. -/
theorem edgeCoefficientDefect_eqv_variation
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.edgeCoefficientDefect ≈
      listQSum
        (fun source => data.sourceWeight source *
          listQSum
            (fun choice =>
              (data.sourceCoefficient source -
                  data.targetCoefficient (data.realize source choice)) *
                data.localWeight source choice)
            (data.choices source))
        data.sources := by
  unfold edgeCoefficientDefect sourceEdgeCoefficientMass
    targetEdgeCoefficientMass
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        data.sourceWeight source *
              listQSum
                (fun choice =>
                  data.sourceCoefficient source *
                    data.localWeight source choice)
                (data.choices source) -
          data.sourceWeight source *
              listQSum
                (fun choice =>
                  data.targetCoefficient (data.realize source choice) *
                    data.localWeight source choice)
                (data.choices source))
      data.sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
        (edge_difference_sum_local
          (data.sourceCoefficient source)
          (fun choice =>
            data.targetCoefficient (data.realize source choice))
          (data.localWeight source) (data.choices source)))
      (mul_sub_eqv_local (data.sourceWeight source)
        (listQSum
          (fun choice =>
            data.sourceCoefficient source * data.localWeight source choice)
          (data.choices source))
        (listQSum
          (fun choice =>
            data.targetCoefficient (data.realize source choice) *
              data.localWeight source choice)
          (data.choices source)))
  · exact listQSum_sub_local _ _ data.sources

/-- The transported target coefficient mass is the same quantity grouped by
the common realized target columns. -/
theorem transportedTargetCoefficientMass_eqv_columns
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.transportedTargetCoefficientMass ≈
      listQSum
        (fun target =>
          listQSum
              (fun source => data.sourceWeight source *
                dependentKernelPushforwardWeight
                  data.Choice data.choices data.localWeight data.realize
                  source target)
              data.sources *
            data.targetCoefficient target)
        data.targets := by
  unfold transportedTargetCoefficientMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (data.sourceWeight source *
                dependentKernelPushforwardWeight
                  data.Choice data.choices data.localWeight data.realize
                  source target) *
              data.targetCoefficient target)
          data.targets)
      data.sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          data.sourceWeight source *
            (dependentKernelPushforwardWeight
                data.Choice data.choices data.localWeight data.realize
                source target * data.targetCoefficient target))
        data.targets) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_mul_left (data.sourceWeight source)
          (fun target =>
            dependentKernelPushforwardWeight
                data.Choice data.choices data.localWeight data.realize
                source target * data.targetCoefficient target)
          data.targets)
    · apply listQSum_congr
      intro target
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (data.sourceWeight source)
          (dependentKernelPushforwardWeight
            data.Choice data.choices data.localWeight data.realize
            source target)
          (data.targetCoefficient target))
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            (data.sourceWeight source *
                dependentKernelPushforwardWeight
                  data.Choice data.choices data.localWeight data.realize
                  source target) *
              data.targetCoefficient target)
          data.sources)
      data.targets) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source target =>
          (data.sourceWeight source *
              dependentKernelPushforwardWeight
                data.Choice data.choices data.localWeight data.realize
                source target) *
            data.targetCoefficient target)
        data.sources data.targets)
  · apply listQSum_congr
    intro target
    refine Q'.eqv_trans _
      (listQSum
        (fun source => data.targetCoefficient target *
          (data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target))
        data.sources) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact Q'.mul_comm_eqv
        (data.sourceWeight source *
          dependentKernelPushforwardWeight
            data.Choice data.choices data.localWeight data.realize
            source target)
        (data.targetCoefficient target)
    · exact Q'.eqv_trans _ _ _
        (listQSum_mul_left (data.targetCoefficient target)
          (fun source => data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
          data.sources)
        (Q'.mul_comm_eqv _ _)

/-- The column debt is the target coefficient paired with the signed incoming
column slack.  A column-capacity inequality controls the sign of the slack but
does not by itself control this product when the coefficient is signed. -/
theorem columnCoefficientDefect_eqv_slack
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.columnCoefficientDefect ≈
      listQSum
        (fun target =>
          (listQSum
                (fun source => data.sourceWeight source *
                  dependentKernelPushforwardWeight
                    data.Choice data.choices data.localWeight data.realize
                    source target)
                data.sources -
              data.targetWeight target) *
            data.targetCoefficient target)
        data.targets := by
  unfold columnCoefficientDefect targetCoefficientMass
  refine Q'.eqv_trans _
    (listQSum
          (fun target =>
            listQSum
                (fun source => data.sourceWeight source *
                  dependentKernelPushforwardWeight
                    data.Choice data.choices data.localWeight data.realize
                    source target)
                data.sources *
              data.targetCoefficient target)
          data.targets -
      listQSum
          (fun target =>
            data.targetWeight target * data.targetCoefficient target)
          data.targets) _ ?_ ?_
  · exact sub_eqv_both_local
      data.transportedTargetCoefficientMass_eqv_columns (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
              (fun source => data.sourceWeight source *
                dependentKernelPushforwardWeight
                  data.Choice data.choices data.localWeight data.realize
                  source target)
              data.sources *
            data.targetCoefficient target -
          data.targetWeight target * data.targetCoefficient target)
      data.targets) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ data.targets)
  · apply listQSum_congr
    intro target
    exact Q'.eqv_symm
      (Q'.sub_mul_eqv
        (listQSum
          (fun source => data.sourceWeight source *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
          data.sources)
        (data.targetWeight target) (data.targetCoefficient target))

/-- Exact row/edge/column decomposition of the signed coefficient cross. -/
theorem coefficientCross_eqv_row_add_edge_add_column
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.sourceCoefficientMass - data.targetCoefficientMass ≈
      data.rowCoefficientDefect + data.edgeCoefficientDefect +
        data.columnCoefficientDefect := by
  have hsource := data.transportedSourceCoefficientMass_eqv_edgeMass
  have htarget := data.transportedTargetCoefficientMass_eqv_edgeMass
  refine Q'.eqv_trans _
    ((data.sourceCoefficientMass - data.transportedSourceCoefficientMass) +
      (data.transportedSourceCoefficientMass -
        data.transportedTargetCoefficientMass) +
      (data.transportedTargetCoefficientMass -
        data.targetCoefficientMass)) _ ?_ ?_
  · exact three_defect_decomposition_local
      data.sourceCoefficientMass data.transportedSourceCoefficientMass
      data.transportedTargetCoefficientMass data.targetCoefficientMass
  · unfold rowCoefficientDefect edgeCoefficientDefect columnCoefficientDefect
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (sub_eqv_both_local hsource htarget))
      (Q'.eqv_refl _)

/-- Triangle bound exposing the three independent analytic debts. -/
theorem coefficientCross_abs_le_row_add_edge_add_column
    (data : FiniteDependentCoefficientTransport Source Target) :
    Q'.abs (data.sourceCoefficientMass - data.targetCoefficientMass) ≤
      (Q'.abs data.rowCoefficientDefect +
        Q'.abs data.edgeCoefficientDefect) +
          Q'.abs data.columnCoefficientDefect := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        data.coefficientCross_eqv_row_add_edge_add_column)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (data.rowCoefficientDefect + data.edgeCoefficientDefect)
      data.columnCoefficientDefect)
    (Q'.add_le_add
      (Q'.abs_add_le' data.rowCoefficientDefect data.edgeCoefficientDefect)
      (Q'.le_refl' (Q'.abs data.columnCoefficientDefect)))

end FiniteDependentCoefficientTransport

#print axioms dependentKernelPushforwardWeight_reindex_mul
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientMass_eqv_edgeMass
#print axioms FiniteDependentCoefficientTransport.rowCoefficientDefect_eqv_unretained
#print axioms FiniteDependentCoefficientTransport.transportedTargetCoefficientMass_eqv_edgeMass
#print axioms FiniteDependentCoefficientTransport.edgeCoefficientDefect_eqv_variation
#print axioms FiniteDependentCoefficientTransport.transportedTargetCoefficientMass_eqv_columns
#print axioms FiniteDependentCoefficientTransport.columnCoefficientDefect_eqv_slack
#print axioms FiniteDependentCoefficientTransport.coefficientCross_eqv_row_add_edge_add_column
#print axioms FiniteDependentCoefficientTransport.coefficientCross_abs_le_row_add_edge_add_column

end YMGap.Continuum.FiniteDependentKernelCoefficientTransport
