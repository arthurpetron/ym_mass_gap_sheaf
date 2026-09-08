/-
# Compress edge and column coefficient debts into one posterior column

The generic dependent coefficient transport previously decomposed a signed
source--target coefficient cross into row, edge, and column debts.  For a
posterior-column argument the intermediate target coefficient is unnecessary:
transport the source coefficient itself through the dependent kernel, regroup
that transported mass by target column, and compare it directly with the
target coefficient mass.

This module proves the exact two-debt identity

```text
source coefficient mass - target coefficient mass
  = row loss + posterior-column mismatch.
```

It also supplies the literal columnwise `l1` majorant.  The result is exact
finite Fubini and does not assume positivity, stochasticity beyond the row
mass already recorded by the transport, or any Yang--Mills estimate.

Constructive contract: finite exact rational algebra only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new
axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientTransport

namespace YMGap.Continuum.FiniteDependentKernelCoefficientTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  induction items with
  | nil =>
      change (0 : Q') ≈ 0 - 0
      decide
  | cons head tail ih =>
      change
        (left head - right head) +
            listQSum (fun item => left item - right item) tail ≈
          (left head + listQSum left tail) -
            (right head + listQSum right tail)
      refine Q'.eqv_trans _
        ((left head - right head) +
          (listQSum left tail - listQSum right tail)) _
        (Q'.add_eqv_congr_left (left head - right head) _ _ ih) ?_
      show
        (left head + -right head) +
            (listQSum left tail + -listQSum right tail) ≈
          (left head + listQSum left tail) +
            -(right head + listQSum right tail)
      refine Q'.eqv_trans _
        ((left head + listQSum left tail) +
          ((-right head) + -listQSum right tail)) _ ?_ ?_
      · exact Q'.add_swap_inner
          (left head) (-right head)
          (listQSum left tail) (-listQSum right tail)
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (Q'.neg_add_eqv
              (right head) (listQSum right tail)))

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

private theorem two_defect_decomposition_local
    (source transported target : Q') :
    source - target ≈
      (source - transported) + (transported - target) := by
  have hright :
      (source - transported) + (transported - target) ≈
        source - target := by
    refine Q'.eqv_trans _
      (source + ((-transported) + (transported + -target))) _
      (Q'.add_assoc_eqv source (-transported)
        (transported + -target)) ?_
    refine Q'.add_eqv_congr_left source _ _ ?_
    refine Q'.eqv_trans _
      (((-transported) + transported) + -target) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (-transported) transported (-target))) ?_
    refine Q'.eqv_trans _ (0 + -target) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.neg_add_self_eqv transported)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-target))
  exact Q'.eqv_symm hright

namespace FiniteDependentCoefficientTransport

variable {Source Target : Type} [DecidableEq Target]

/-- Source coefficient mass delivered into one realized target column. -/
def transportedSourceCoefficientColumnMass
    (data : FiniteDependentCoefficientTransport Source Target)
    (target : Target) : Q' :=
  listQSum
    (fun source =>
      (data.sourceWeight source * data.sourceCoefficient source) *
        dependentKernelPushforwardWeight
          data.Choice data.choices data.localWeight data.realize
          source target)
    data.sources

/-- The transported source coefficient regrouped over target columns is
exactly the row-retained source coefficient mass. -/
theorem transportedSourceCoefficientMass_eqv_posteriorColumns
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.transportedSourceCoefficientMass ≈
      listQSum data.transportedSourceCoefficientColumnMass data.targets := by
  unfold transportedSourceCoefficientMass
    transportedSourceCoefficientColumnMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (data.sourceWeight source * data.sourceCoefficient source) *
              dependentKernelPushforwardWeight
                data.Choice data.choices data.localWeight data.realize
                source target)
          data.targets)
      data.sources) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    let factor := data.sourceWeight source * data.sourceCoefficient source
    let pushed := dependentKernelPushforwardWeight
      data.Choice data.choices data.localWeight data.realize source
    refine Q'.eqv_trans _ (factor * data.rowMass source) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (data.sourceWeight source) (data.sourceCoefficient source)
          (data.rowMass source))
    refine Q'.eqv_trans _
      (factor * listQSum (data.localWeight source) (data.choices source)) _
      (Q'.mul_eqv_congr_left factor _ _
        (Q'.eqv_symm (data.row_mass source hsource))) ?_
    refine Q'.eqv_trans _
      (factor * listQSum pushed data.targets) _
      (Q'.mul_eqv_congr_left factor _ _
        (Q'.eqv_symm
          (kernelPushforwardWeight_total
            (data.choices source) (data.localWeight source)
            (data.realize source) data.targets data.targets_nodup
            (data.coverage source hsource)))) ?_
    exact Q'.eqv_symm
      (listQSum_mul_left factor pushed data.targets)
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source target =>
          (data.sourceWeight source * data.sourceCoefficient source) *
            dependentKernelPushforwardWeight
              data.Choice data.choices data.localWeight data.realize
              source target)
        data.sources data.targets)

/-- The one signed posterior-column debt: transported source coefficient
arriving in each column minus the target coefficient mass assigned there. -/
def posteriorColumnCoefficientDefect
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun target =>
      data.transportedSourceCoefficientColumnMass target -
        data.targetWeight target * data.targetCoefficient target)
    data.targets

/-- Literal target-column `l1` majorant for the posterior coefficient debt. -/
def posteriorColumnCoefficientL1
    (data : FiniteDependentCoefficientTransport Source Target) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (data.transportedSourceCoefficientColumnMass target -
          data.targetWeight target * data.targetCoefficient target))
    data.targets

theorem posteriorColumnCoefficientDefect_eqv_transport_sub_target
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.posteriorColumnCoefficientDefect ≈
      data.transportedSourceCoefficientMass -
        data.targetCoefficientMass := by
  unfold posteriorColumnCoefficientDefect targetCoefficientMass
  refine Q'.eqv_trans _
    (listQSum data.transportedSourceCoefficientColumnMass data.targets -
      listQSum
        (fun target =>
          data.targetWeight target * data.targetCoefficient target)
        data.targets) _
    (listQSum_sub_local _ _ data.targets) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm
      data.transportedSourceCoefficientMass_eqv_posteriorColumns)

/-- Exact row/posterior decomposition.  The former edge and column terms are
not discarded; they are regrouped into the one literal posterior column. -/
theorem coefficientCross_eqv_row_add_posteriorColumn
    (data : FiniteDependentCoefficientTransport Source Target) :
    data.sourceCoefficientMass - data.targetCoefficientMass ≈
      data.rowCoefficientDefect + data.posteriorColumnCoefficientDefect := by
  refine Q'.eqv_trans _
    ((data.sourceCoefficientMass - data.transportedSourceCoefficientMass) +
      (data.transportedSourceCoefficientMass -
        data.targetCoefficientMass)) _
    (two_defect_decomposition_local
      data.sourceCoefficientMass data.transportedSourceCoefficientMass
      data.targetCoefficientMass) ?_
  unfold rowCoefficientDefect
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_symm
      data.posteriorColumnCoefficientDefect_eqv_transport_sub_target)

theorem posteriorColumnCoefficientDefect_abs_le_l1
    (data : FiniteDependentCoefficientTransport Source Target) :
    Q'.abs data.posteriorColumnCoefficientDefect ≤
      data.posteriorColumnCoefficientL1 := by
  unfold posteriorColumnCoefficientDefect posteriorColumnCoefficientL1
  exact abs_listQSum_le_sum_abs_local _ _

/-- Triangle bound exposing only the row loss and the target-column posterior
mismatch. -/
theorem coefficientCross_abs_le_row_add_posteriorColumnL1
    (data : FiniteDependentCoefficientTransport Source Target) :
    Q'.abs (data.sourceCoefficientMass - data.targetCoefficientMass) ≤
      Q'.abs data.rowCoefficientDefect +
        data.posteriorColumnCoefficientL1 := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        data.coefficientCross_eqv_row_add_posteriorColumn)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      data.rowCoefficientDefect data.posteriorColumnCoefficientDefect)
    (Q'.add_le_add
      (Q'.le_refl' (Q'.abs data.rowCoefficientDefect))
      data.posteriorColumnCoefficientDefect_abs_le_l1)

end FiniteDependentCoefficientTransport

#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientColumnMass
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientMass_eqv_posteriorColumns
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientDefect
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientDefect_eqv_transport_sub_target
#print axioms FiniteDependentCoefficientTransport.coefficientCross_eqv_row_add_posteriorColumn
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientDefect_abs_le_l1
#print axioms FiniteDependentCoefficientTransport.coefficientCross_abs_le_row_add_posteriorColumnL1

end YMGap.Continuum.FiniteDependentKernelCoefficientTransport
