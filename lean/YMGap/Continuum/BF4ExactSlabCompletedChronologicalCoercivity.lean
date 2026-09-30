/-
# Chronological area coercivity on every original completed centered state

Reuse the original centered representative and its unchanged explicit Cauchy
modulus, then apply the existing coefficient-parametric Dirichlet closure.
No new completion, representative choice or energy is introduced. The
coefficient is uniform in late heat cutoff, not in nome or spatial extent.
This is original conditional-update L2 dynamics, not OS or physical time.
-/

import YMGap.Continuum.BF4ExactSlabChronologicalCoercivity
import YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity

namespace YMGap.Continuum.BF4ExactSlabCompletedChronologicalCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
open YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity
open YMGap.Continuum.BF4ExactSlabChronologicalCoercivity

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "U" => unit hw0 hw1 extent stage

/-- Every completed state centered in the SAME original full-action form
has the explicit chronological Dirichlet lower coefficient. -/
theorem completed_centered_area_coercivity (x : GNSCompletionSpace F)
    (hx : (F).cinnerCompl x (embedV F U) = RCzero) :
    RCle (RCscale (areaCoercivity hw0 hw1 extent) (normSq x))
      ((P).finalEnergy (schedule extent) x) := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  let Y := centeredCauchy hw0 hw1 extent stage X
  have h := completed_of_termwise_bound hw0 hw1 extent stage
    (areaCoercivity hw0 hw1 extent) Y
    (fun n => dense_centered_area_coercivity hw0 hw1 K extent hK (Y.seq n)
      (centeredCauchy_term_centered hw0 hw1 extent stage X n))
  rw [centeredCauchy_same_class hw0 hw1 extent stage X hx] at h
  exact h

/-- Equivalent completed Poincare upper bound. Its original partition and
replica factor have already cancelled; no volume mass survives in the cost. -/
theorem completed_centered_area_poincare (x : GNSCompletionSpace F)
    (hx : (F).cinnerCompl x (embedV F U) = RCzero) :
    RCle (normSq x) (RCscale (poincareCost hw0 hw1 extent)
      ((P).finalEnergy (schedule extent) x)) := by
  have h := RCscale_mono (Q'.le_of_lt (poincareCost_positive hw0 hw1 extent))
    (completed_centered_area_coercivity hw0 hw1 extent stage x hx)
  rw [RCscale_RCscale] at h
  have he : Q'.eqv (poincareCost hw0 hw1 extent * areaCoercivity hw0 hw1 extent) 1 :=
    Q'.mul_recipPos_eqv _ _
  rw [RCSignedPairBudget.scale_congr he, RCscale_one] at h
  exact h

#print axioms completed_centered_area_coercivity
#print axioms completed_centered_area_poincare

end YMGap.Continuum.BF4ExactSlabCompletedChronologicalCoercivity
