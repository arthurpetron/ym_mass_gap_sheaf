/-
# Original-action completed sweep energy with explicit constant 625

Every physical Ward-star row AND column has at most 25 distinct links.
The constructed sparse-correction estimate consequently bounds the sum
of final residual squared norms by 625 times the actual sweep norm loss.
The eight-layer schedule visits every physical link exactly once.

The constant is geometric, independent of nome, cutoff and extent. This
is an UPPER energy estimate, not the missing positive LOWER coercivity
bound. No uniform gap, OS transfer identification or continuum claim follows.
-/

import YMGap.Continuum.GNSProjectionSweepEnergy
import YMGap.Continuum.BF4ExactSlabEightLayerCone

namespace YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation

def adjacent {extent : Nat} (i j : PhysicalLink extent) : Bool :=
  decide (Near extent i.val j.val)

theorem column_count {extent : Nat} (j : PhysicalLink extent)
    (links : List (PhysicalLink extent)) (hlinks : links.Nodup) :
    (links.filter (fun i => adjacent i j)).length ≤ 25 := by
  have he : links.filter (fun i => adjacent i j) = links.filter (adjacent j) := by
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [adjacent, decide_eq_true_eq]
    exact ⟨near_symm, near_symm⟩
  rw [he]
  exact BF4ExactSlabConditionalSweep.neighbor_count extent j links hlinks

private theorem scale625 (a : RC) :
    RCscale (Q'.ofNat 25 * Q'.ofNat 25) a = RCscale 625 a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (Q'.ofNat 25 * Q'.ofNat 25) 625)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

theorem nonadjacent_commute (i j : PhysicalLink extent) (h : adjacent i j = false)
    (x : GNSCompletionSpace F) : (P).op i ((P).op j x) = (P).op j ((P).op i x) := by
  apply conditionalProjection_commute hw0 hw1 K extent hK i.val j.val i.property j.property
  intro hj
  have hn : Near extent i.val j.val := List.mem_cons_of_mem i.val hj
  have ht : adjacent i j = true := decide_eq_true hn
  rw [h] at ht
  exact Bool.noConfusion ht

/-- No centered-sector or analytic premise: final energy is controlled by
actual loss for any duplicate-free schedule of original physical updates. -/
theorem final_energy_le_625_loss (links : List (PhysicalLink extent))
    (hlinks : links.Nodup) (x : GNSCompletionSpace F) :
    RCle ((P).finalEnergy links ((P).sweep links x))
      (RCscale 625 (RCsub (normSq x) (normSq ((P).sweep links x)))) := by
  have h := (P).finalEnergy_le_norm_loss adjacent
    (nonadjacent_commute hw0 hw1 K extent hK) links links (fun _ hi => hi) x 25
    (fun i _ => BF4ExactSlabConditionalSweep.neighbor_count extent i links hlinks)
    (fun j _ => column_count j links hlinks)
  rw [scale625] at h
  exact h

/-- In particular ALL physical residuals are bounded after the constructed
eight-layer full sweep, without a volume-dependent coefficient. -/
theorem eight_layer_energy_le_625_loss (x : GNSCompletionSpace F) :
    RCle ((P).finalEnergy (schedule extent) ((P).sweep (schedule extent) x))
      (RCscale 625 (RCsub (normSq x) (normSq ((P).sweep (schedule extent) x)))) :=
  final_energy_le_625_loss hw0 hw1 K extent hK (schedule extent) (schedule_nodup extent) x

#print axioms column_count
#print axioms nonadjacent_commute
#print axioms final_energy_le_625_loss
#print axioms eight_layer_energy_le_625_loss

end YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
