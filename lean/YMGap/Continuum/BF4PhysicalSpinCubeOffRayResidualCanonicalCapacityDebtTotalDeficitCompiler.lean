/-
# One total-deficit compiler for canonical BF4 correlated capacity debt

The exact finite deficit compiler leaves four independently diagnosable
streams: transported old pairs and the old-new, new-old, and new-new shell
faces.  Requiring four separate summability certificates is unnecessary for
the final proof path.  Their pointwise sum is itself an explicit rational
stream on the same debt observable, and one `AntitoneTailControl` for this
total dominates every regional comparison.

This module constructs that contraction directly.  The four regions remain
visible, so their analytic estimates may still be developed in parallel and
a failure remains localized.  But the serial proof path now consumes one
observable-connected tail certificate, followed only by the already exposed
total-budget and cutoff-zero slack witnesses.

No total-tail witness, budget, or initial slack is supplied.  The fixed
strong-coupling anchor is not the physical AF/grouped-BF4 trajectory, and no
thermodynamic, continuum, or Clay conclusion is asserted.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

private theorem le_add_of_abs_sub_le_local
    {left right bound : Q'}
    (hbound : Q'.abs (left + -right) <= bound) :
    left <= right + bound := by
  have hsub : left + -right <= bound :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (left + -right)) hbound
  have hadd : (left + -right) + right <= bound + right :=
    Q'.add_le_add_right (left + -right) bound right hsub
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv bound right)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-right) right) ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left left (-right + right) 0
      (Q'.neg_add_self_eqv right)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' left)

private theorem right_le_sum
    (left right : Q') (hleft : (0 : Q') <= left) :
    right <= left + right := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg right left hleft)
    (Q'.le_of_eqv (Q'.add_comm_eqv right left))

private theorem base_add_component_le_total
    (base component total : Q')
    (hcomponent : component <= total) :
    base + component <= base + total :=
  Q'.add_le_add_left base component total hcomponent

/-! ## 1. The explicit total stream and its regional diagnostics -/

def anchorCanonicalCapacityDebtTotalDeficit (scale : Nat) : Q' :=
  anchorTransportedCapacityDebtDeficitMaximum scale +
    (anchorOldNewReturnCapacityDebtDeficitMaximum scale +
      (anchorNewOldReturnCapacityDebtDeficitMaximum scale +
        anchorNewNewReturnCapacityDebtDeficitMaximum scale))

theorem anchorCanonicalCapacityDebtTotalDeficit_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorCanonicalCapacityDebtTotalDeficit scale := by
  unfold anchorCanonicalCapacityDebtTotalDeficit
  exact Q'.zero_le_add _ _
    (anchorTransportedCapacityDebtDeficitMaximum_nonnegative scale)
    (Q'.zero_le_add _ _
      (anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative scale)
      (Q'.zero_le_add _ _
        (anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative scale)
        (anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative scale)))

theorem anchorTransportedCapacityDebtDeficitMaximum_le_total
    (scale : Nat) :
    anchorTransportedCapacityDebtDeficitMaximum scale <=
      anchorCanonicalCapacityDebtTotalDeficit scale := by
  unfold anchorCanonicalCapacityDebtTotalDeficit
  exact Q'.add_le_self_of_nonneg _ _
    (Q'.zero_le_add _ _
      (anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative scale)
      (Q'.zero_le_add _ _
        (anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative scale)
        (anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative scale)))

theorem anchorOldNewReturnCapacityDebtDeficitMaximum_le_total
    (scale : Nat) :
    anchorOldNewReturnCapacityDebtDeficitMaximum scale <=
      anchorCanonicalCapacityDebtTotalDeficit scale := by
  unfold anchorCanonicalCapacityDebtTotalDeficit
  have hright : anchorOldNewReturnCapacityDebtDeficitMaximum scale <=
      anchorOldNewReturnCapacityDebtDeficitMaximum scale +
        (anchorNewOldReturnCapacityDebtDeficitMaximum scale +
          anchorNewNewReturnCapacityDebtDeficitMaximum scale) :=
    Q'.add_le_self_of_nonneg _ _
      (Q'.zero_le_add _ _
        (anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative scale)
        (anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative scale))
  exact Q'.le_trans' _ _ _ hright
    (right_le_sum _ _
      (anchorTransportedCapacityDebtDeficitMaximum_nonnegative scale))

theorem anchorNewOldReturnCapacityDebtDeficitMaximum_le_total
    (scale : Nat) :
    anchorNewOldReturnCapacityDebtDeficitMaximum scale <=
      anchorCanonicalCapacityDebtTotalDeficit scale := by
  unfold anchorCanonicalCapacityDebtTotalDeficit
  have hnew : anchorNewOldReturnCapacityDebtDeficitMaximum scale <=
      anchorNewOldReturnCapacityDebtDeficitMaximum scale +
        anchorNewNewReturnCapacityDebtDeficitMaximum scale :=
    Q'.add_le_self_of_nonneg _ _
      (anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative scale)
  have holdNew : anchorNewOldReturnCapacityDebtDeficitMaximum scale <=
      anchorOldNewReturnCapacityDebtDeficitMaximum scale +
        (anchorNewOldReturnCapacityDebtDeficitMaximum scale +
          anchorNewNewReturnCapacityDebtDeficitMaximum scale) :=
    Q'.le_trans' _ _ _ hnew
      (right_le_sum _ _
        (anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative scale))
  exact Q'.le_trans' _ _ _ holdNew
    (right_le_sum _ _
      (anchorTransportedCapacityDebtDeficitMaximum_nonnegative scale))

theorem anchorNewNewReturnCapacityDebtDeficitMaximum_le_total
    (scale : Nat) :
    anchorNewNewReturnCapacityDebtDeficitMaximum scale <=
      anchorCanonicalCapacityDebtTotalDeficit scale := by
  unfold anchorCanonicalCapacityDebtTotalDeficit
  have hnew : anchorNewNewReturnCapacityDebtDeficitMaximum scale <=
      anchorNewOldReturnCapacityDebtDeficitMaximum scale +
        anchorNewNewReturnCapacityDebtDeficitMaximum scale :=
    right_le_sum _ _
      (anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative scale)
  have holdNew : anchorNewNewReturnCapacityDebtDeficitMaximum scale <=
      anchorOldNewReturnCapacityDebtDeficitMaximum scale +
        (anchorNewOldReturnCapacityDebtDeficitMaximum scale +
          anchorNewNewReturnCapacityDebtDeficitMaximum scale) :=
    Q'.le_trans' _ _ _ hnew
      (right_le_sum _ _
        (anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative scale))
  exact Q'.le_trans' _ _ _ holdNew
    (right_le_sum _ _
      (anchorTransportedCapacityDebtDeficitMaximum_nonnegative scale))

/-! ## 2. Four parallel regional tails contract to one total tail -/

/-- The single remaining dynamic analytic input on the canonical path. -/
structure AnchorCanonicalCapacityDebtTotalDeficitTail : Type 1 where
  tailControl : AntitoneTailControl
    anchorCanonicalCapacityDebtTotalDeficit

def anchorCanonicalCapacityDebtTotalDeficitTailOfRegionalTails
    (transport : AnchorCanonicalTransportedCapacityDebtDeficitTail)
    (oldNew : AnchorCanonicalOldNewCapacityDebtDeficitTail)
    (newOld : AnchorCanonicalNewOldCapacityDebtDeficitTail)
    (newNew : AnchorCanonicalNewNewCapacityDebtDeficitTail) :
    AnchorCanonicalCapacityDebtTotalDeficitTail where
  tailControl := by
    unfold anchorCanonicalCapacityDebtTotalDeficit
    exact addAntitoneTailControl transport.tailControl
      (addAntitoneTailControl oldNew.tailControl
        (addAntitoneTailControl newOld.tailControl newNew.tailControl))

/-! ## 3. One total tail constructs the exact correlated envelope -/

def AnchorCanonicalCapacityDebtTotalDeficitTail.toEnvelope
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail) :
    AnchorCanonicalCapacityDebtEnvelope where
  variation := anchorCanonicalCapacityDebtTotalDeficit
  variation_nonnegative :=
    anchorCanonicalCapacityDebtTotalDeficit_nonnegative
  tailControl := data.tailControl
  current_le_next := by
    intro scale pair hpair
    have hregional :
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale pair <=
          anchorRoutedCapacityDebtOnPair
              anchorCanonicalPositiveRoutingSequence
              (scale + 1) (anchorCurrentPairToNext scale pair) +
            anchorTransportedCapacityDebtDeficitMaximum scale := by
      apply le_add_of_abs_sub_le_local
      exact Q'.le_trans' _ _ _
        (Q'.le_max'_left _ _)
        (anchorTransportedCapacityDebtDeficitOnPair_le_maximum
          scale pair hpair)
    exact Q'.le_trans' _ _ _ hregional
      (base_add_component_le_total _ _ _
        (anchorTransportedCapacityDebtDeficitMaximum_le_total scale))
  next_le_current := by
    intro scale pair hpair
    rcases anchorPair_old_or_newShell scale pair hpair with hold | hshell
    · obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hold
      rw [← hmap]
      rw [anchorNextPairToCurrent_currentToNext
        scale currentPair hcurrentPair]
      have hregional :
          anchorRoutedCapacityDebtOnPair
              anchorCanonicalPositiveRoutingSequence
              (scale + 1) (anchorCurrentPairToNext scale currentPair) <=
            anchorRoutedCapacityDebtOnPair
                anchorCanonicalPositiveRoutingSequence scale currentPair +
              anchorTransportedCapacityDebtDeficitMaximum scale := by
        apply le_add_of_abs_sub_le_local
        exact Q'.le_trans' _ _ _
          (Q'.le_max'_right _ _)
          (anchorTransportedCapacityDebtDeficitOnPair_le_maximum
            scale currentPair hcurrentPair)
      exact Q'.le_trans' _ _ _ hregional
        (base_add_component_le_total _ _ _
          (anchorTransportedCapacityDebtDeficitMaximum_le_total scale))
    · rcases anchorNewShellPair_face_cases scale pair hshell with
        hOldNew | hNewOld | hNewNew
      · rw [anchorNextPairToCurrent_eq_oldNewReturn scale pair hOldNew]
        have hregional :
            anchorRoutedCapacityDebtOnPair
                anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
              anchorRoutedCapacityDebtOnPair
                  anchorCanonicalPositiveRoutingSequence scale
                  (anchorOldNewReturnPair scale pair) +
                anchorOldNewReturnCapacityDebtDeficitMaximum scale :=
          le_add_of_abs_sub_le_local
            (anchorOldNewReturnCapacityDebtDeficitOnPair_le_maximum
              scale pair hOldNew)
        exact Q'.le_trans' _ _ _ hregional
          (base_add_component_le_total _ _ _
            (anchorOldNewReturnCapacityDebtDeficitMaximum_le_total scale))
      · rw [anchorNextPairToCurrent_eq_newOldReturn scale pair hNewOld]
        have hregional :
            anchorRoutedCapacityDebtOnPair
                anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
              anchorRoutedCapacityDebtOnPair
                  anchorCanonicalPositiveRoutingSequence scale
                  (anchorNewOldReturnPair scale pair) +
                anchorNewOldReturnCapacityDebtDeficitMaximum scale :=
          le_add_of_abs_sub_le_local
            (anchorNewOldReturnCapacityDebtDeficitOnPair_le_maximum
              scale pair hNewOld)
        exact Q'.le_trans' _ _ _ hregional
          (base_add_component_le_total _ _ _
            (anchorNewOldReturnCapacityDebtDeficitMaximum_le_total scale))
      · rw [anchorNextPairToCurrent_eq_newNewReturn scale pair hNewNew]
        have hregional :
            anchorRoutedCapacityDebtOnPair
                anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
              anchorRoutedCapacityDebtOnPair
                  anchorCanonicalPositiveRoutingSequence scale
                  (anchorNewNewReturnPair scale pair) +
                anchorNewNewReturnCapacityDebtDeficitMaximum scale :=
          le_add_of_abs_sub_le_local
            (anchorNewNewReturnCapacityDebtDeficitOnPair_le_maximum
              scale pair hNewNew)
        exact Q'.le_trans' _ _ _ hregional
          (base_add_component_le_total _ _ _
            (anchorNewNewReturnCapacityDebtDeficitMaximum_le_total scale))

/-! ## 4. Only total budget and cutoff-zero slack follow the one tail -/

def anchorCanonicalCapacityDebtPersistenceOfTotalDeficitTail
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorCanonicalCapacityDebtMaximumVariation
        data.toEnvelope).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence where
  envelope := data.toEnvelope
  budget := budget
  budget_pos := budget_pos
  budget_from_zero := budget_from_zero
  initial_closure := initial_closure

def anchorGeometricCompletedFamilyOfTotalDeficitTail
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorCanonicalCapacityDebtMaximumVariation
        data.toEnvelope).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  (anchorCanonicalCapacityDebtPersistenceOfTotalDeficitTail
    data budget budget_pos budget_from_zero initial_closure).toAnchorGeometricCompletedFamily

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorCanonicalCapacityDebtTotalDeficit
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorCanonicalCapacityDebtTotalDeficit_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorTransportedCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorOldNewReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorNewOldReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorNewNewReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorCanonicalCapacityDebtTotalDeficitTailOfRegionalTails
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.AnchorCanonicalCapacityDebtTotalDeficitTail.toEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorCanonicalCapacityDebtPersistenceOfTotalDeficitTail
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.anchorGeometricCompletedFamilyOfTotalDeficitTail
