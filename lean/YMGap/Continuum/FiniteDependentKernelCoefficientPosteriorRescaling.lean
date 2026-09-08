/-
# Rescale finite dependent posterior coefficients exactly

The posterior-column decomposition is linear in the source and target
coefficient fields.  This module makes that fact literal: replacing both
coefficient fields by normalized fields and then multiplying them by one
common nonnegative rational factor multiplies the signed row defect by that
factor and the posterior-column `l1` budget by that factor.

This is the exact algebra needed to remove physical partition factors from a
posterior-column cost.  It asserts no stochastic contraction, asymptotic
smallness, continuum limit, or mass gap.

Constructive contract: finite exact rational algebra only; no choice,
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

private theorem listQSum_mul_right_local {A : Type}
    (value : A → Q') (factor : Q') : ∀ items : List A,
    listQSum (fun item => value item * factor) items ≈
      listQSum value items * factor
  | [] => by
      change (0 : Q') ≈ 0 * factor
      exact Q'.eqv_symm (Q'.zero_mul_eqv factor)
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

private theorem move_middle_factor_right_local
    (left middle factor right : Q') :
    left * (middle * factor) * right ≈
      (left * middle * right) * factor := by
  refine Q'.eqv_trans _ (left * ((middle * factor) * right)) _
    (Q'.mul_assoc_eqv left (middle * factor) right) ?_
  refine Q'.eqv_trans _ (left * (middle * (factor * right))) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_assoc_eqv middle factor right)) ?_
  refine Q'.eqv_trans _ (left * (middle * (right * factor))) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_eqv_congr_left middle _ _
        (Q'.mul_comm_eqv factor right))) ?_
  refine Q'.eqv_trans _ (left * ((middle * right) * factor)) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv middle right factor))) ?_
  refine Q'.eqv_trans _ ((left * (middle * right)) * factor) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv left (middle * right) factor)) ?_
  exact Q'.mul_eqv_congr_right _ _ factor
    (Q'.eqv_symm (Q'.mul_assoc_eqv left middle right))

private theorem abs_scaled_eqv_factor_mul_abs_local
    (factor base : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (base * factor) ≈ factor * Q'.abs base := by
  refine Q'.eqv_trans _ (Q'.abs base * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right base hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs base) factor

namespace FiniteDependentCoefficientTransport

variable {Source Target : Type} [DecidableEq Target]

/-- Replace only the two coefficient fields of a dependent transport.  The
source/target carriers and the complete dependent kernel are unchanged. -/
def replaceCoefficients
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q') :
    FiniteDependentCoefficientTransport Source Target where
  sources := data.sources
  sourceWeight := data.sourceWeight
  sourceCoefficient := sourceCoefficient
  rowMass := data.rowMass
  targets := data.targets
  targets_nodup := data.targets_nodup
  targetWeight := data.targetWeight
  targetCoefficient := targetCoefficient
  Choice := data.Choice
  choices := data.choices
  localWeight := data.localWeight
  realize := data.realize
  coverage := data.coverage
  row_mass := data.row_mass

theorem sourceCoefficientMass_eqv_replaceCoefficients_mul
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q')
    (factor : Q')
    (hsource : ∀ source,
      data.sourceCoefficient source ≈ sourceCoefficient source * factor) :
    data.sourceCoefficientMass ≈
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).sourceCoefficientMass * factor := by
  unfold sourceCoefficientMass replaceCoefficients
  dsimp only
  refine Q'.eqv_trans _
    (listQSum
      (fun source => (data.sourceWeight source * sourceCoefficient source) *
        factor)
      data.sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      (data.sourceWeight source * (sourceCoefficient source * factor)) _
      (Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
        (hsource source)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (data.sourceWeight source) (sourceCoefficient source) factor)
  · exact listQSum_mul_right_local _ _ _

theorem transportedSourceCoefficientMass_eqv_replaceCoefficients_mul
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q')
    (factor : Q')
    (hsource : ∀ source,
      data.sourceCoefficient source ≈ sourceCoefficient source * factor) :
    data.transportedSourceCoefficientMass ≈
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).transportedSourceCoefficientMass * factor := by
  unfold transportedSourceCoefficientMass replaceCoefficients
  dsimp only
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (data.sourceWeight source *
          (sourceCoefficient source * data.rowMass source)) * factor)
      data.sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      (data.sourceWeight source *
        ((sourceCoefficient source * factor) * data.rowMass source)) _
      (Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
        (Q'.mul_eqv_congr_right _ _ (data.rowMass source)
          (hsource source))) ?_
    refine Q'.eqv_trans _
      ((data.sourceWeight source * (sourceCoefficient source * factor)) *
        data.rowMass source) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (data.sourceWeight source)
          (sourceCoefficient source * factor) (data.rowMass source))) ?_
    refine Q'.eqv_trans _
      (((data.sourceWeight source * sourceCoefficient source) *
        data.rowMass source) * factor) _
      (move_middle_factor_right_local
        (data.sourceWeight source) (sourceCoefficient source) factor
        (data.rowMass source)) ?_
    exact Q'.mul_eqv_congr_right _ _ factor
      (Q'.mul_assoc_eqv (data.sourceWeight source)
        (sourceCoefficient source) (data.rowMass source))
  · exact listQSum_mul_right_local _ _ _

/-- A common coefficient rescaling passes exactly through the signed row
defect. -/
theorem rowCoefficientDefect_eqv_replaceCoefficients_mul
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q')
    (factor : Q')
    (hsource : ∀ source,
      data.sourceCoefficient source ≈ sourceCoefficient source * factor) :
    data.rowCoefficientDefect ≈
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).rowCoefficientDefect * factor := by
  unfold rowCoefficientDefect
  refine Q'.eqv_trans _
    ((data.replaceCoefficients sourceCoefficient targetCoefficient
        ).sourceCoefficientMass * factor -
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).transportedSourceCoefficientMass * factor) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (data.sourceCoefficientMass_eqv_replaceCoefficients_mul
        sourceCoefficient targetCoefficient factor hsource)
      (Q'.neg_eqv_congr _ _
        (data.transportedSourceCoefficientMass_eqv_replaceCoefficients_mul
          sourceCoefficient targetCoefficient factor hsource))
  · exact Q'.eqv_symm
      (Q'.sub_mul_eqv
        (data.replaceCoefficients sourceCoefficient targetCoefficient
          ).sourceCoefficientMass
        (data.replaceCoefficients sourceCoefficient targetCoefficient
          ).transportedSourceCoefficientMass
        factor)

theorem transportedSourceCoefficientColumnMass_eqv_replaceCoefficients_mul
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q')
    (factor : Q')
    (hsource : ∀ source,
      data.sourceCoefficient source ≈ sourceCoefficient source * factor)
    (target : Target) :
    data.transportedSourceCoefficientColumnMass target ≈
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).transportedSourceCoefficientColumnMass target * factor := by
  unfold transportedSourceCoefficientColumnMass replaceCoefficients
  dsimp only
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        ((data.sourceWeight source * sourceCoefficient source) *
          dependentKernelPushforwardWeight
            data.Choice data.choices data.localWeight data.realize
            source target) * factor)
      data.sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      ((data.sourceWeight source * (sourceCoefficient source * factor)) *
        dependentKernelPushforwardWeight
          data.Choice data.choices data.localWeight data.realize
          source target) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (data.sourceWeight source) _ _
          (hsource source))) ?_
    exact move_middle_factor_right_local
      (data.sourceWeight source) (sourceCoefficient source) factor
      (dependentKernelPushforwardWeight
        data.Choice data.choices data.localWeight data.realize source target)
  · exact listQSum_mul_right_local _ _ _

/-- A common nonnegative coefficient rescaling passes exactly through the
literal posterior-column `l1` budget. -/
theorem posteriorColumnCoefficientL1_eqv_factor_mul_replaceCoefficients
    (data : FiniteDependentCoefficientTransport Source Target)
    (sourceCoefficient : Source → Q')
    (targetCoefficient : Target → Q')
    (factor : Q')
    (hfactor : (0 : Q') ≤ factor)
    (hsource : ∀ source,
      data.sourceCoefficient source ≈ sourceCoefficient source * factor)
    (htarget : ∀ target,
      data.targetCoefficient target ≈ targetCoefficient target * factor) :
    data.posteriorColumnCoefficientL1 ≈
      factor *
        (data.replaceCoefficients sourceCoefficient targetCoefficient
          ).posteriorColumnCoefficientL1 := by
  unfold posteriorColumnCoefficientL1 replaceCoefficients
  dsimp only
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        factor * Q'.abs
          ((data.replaceCoefficients sourceCoefficient targetCoefficient
              ).transportedSourceCoefficientColumnMass target -
            data.targetWeight target * targetCoefficient target))
      data.targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    let normalizedColumn :=
      (data.replaceCoefficients sourceCoefficient targetCoefficient
        ).transportedSourceCoefficientColumnMass target
    let normalizedTarget :=
      data.targetWeight target * targetCoefficient target
    have hcolumn :
        data.transportedSourceCoefficientColumnMass target ≈
          normalizedColumn * factor := by
      simpa only [normalizedColumn] using
        data.transportedSourceCoefficientColumnMass_eqv_replaceCoefficients_mul
          sourceCoefficient targetCoefficient factor hsource target
    have htargetTerm :
        data.targetWeight target * data.targetCoefficient target ≈
          normalizedTarget * factor := by
      refine Q'.eqv_trans _
        (data.targetWeight target *
          (targetCoefficient target * factor)) _
        (Q'.mul_eqv_congr_left (data.targetWeight target) _ _
          (htarget target)) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (data.targetWeight target) (targetCoefficient target) factor)
    have hdifference :
        data.transportedSourceCoefficientColumnMass target -
            data.targetWeight target * data.targetCoefficient target ≈
          (normalizedColumn - normalizedTarget) * factor := by
      refine Q'.eqv_trans _
        (normalizedColumn * factor - normalizedTarget * factor) _ ?_ ?_
      · exact Q'.add_eqv_congr' hcolumn
          (Q'.neg_eqv_congr _ _ htargetTerm)
      · exact Q'.eqv_symm
          (Q'.sub_mul_eqv normalizedColumn normalizedTarget factor)
    refine Q'.eqv_trans _
      (Q'.abs ((normalizedColumn - normalizedTarget) * factor)) _
      (Q'.abs_eqv_congr hdifference) ?_
    simpa only [normalizedColumn, normalizedTarget] using
      abs_scaled_eqv_factor_mul_abs_local factor
        (normalizedColumn - normalizedTarget) hfactor
  · exact listQSum_mul_left factor _ data.targets

end FiniteDependentCoefficientTransport

#print axioms FiniteDependentCoefficientTransport.replaceCoefficients
#print axioms FiniteDependentCoefficientTransport.sourceCoefficientMass_eqv_replaceCoefficients_mul
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientMass_eqv_replaceCoefficients_mul
#print axioms FiniteDependentCoefficientTransport.rowCoefficientDefect_eqv_replaceCoefficients_mul
#print axioms FiniteDependentCoefficientTransport.transportedSourceCoefficientColumnMass_eqv_replaceCoefficients_mul
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_eqv_factor_mul_replaceCoefficients

end YMGap.Continuum.FiniteDependentKernelCoefficientTransport
