/-
# The actual Chebyshev auxiliary state and its reverse-loss cone

The second coupled component at step n+1 has degree n propagation. Its
forward and reverse original-action sweeps therefore agree exactly with
computed, pruned physical-link words. This identifies the finite loss
word consumed by the reverse-energy comparison; it supplies no lower
bound on that loss.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevCone
import YMGap.Continuum.BF4ExactSlabConeSchedule
import YMGap.Continuum.BF4ExactSlabChebyshevRescale

namespace YMGap.Continuum.BF4ExactSlabChebyshevAuxiliaryCone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabChebyshevCone
open YMGap.Continuum.BF4ExactSlabConeSchedule
open YMGap.Continuum.BF4ExactSlabChebyshevRescale
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkEightColor

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

private theorem localized_zero (support : List Z4Link) :
    Localized hw0 hw1 K extent hK support (embedV F (F).zero) := by
  intro i _
  apply eq_of_pairings_equal
  intro z
  rw [(P).adjoint, (F).cinnerCompl_embedZero_left,
    (F).cinnerCompl_embedZero_left]

private theorem affine_zero (c : Q') :
    affine hw0 hw1 K extent hK c (embedV F (F).zero) = embedV F (F).zero := by
  apply eq_of_pairings_equal
  intro z
  rw [affine_selfAdjoint hw0 hw1 K extent hK c,
    (F).cinnerCompl_embedZero_left, (F).cinnerCompl_embedZero_left]

/-- Expose one auxiliary recurrence step without unfolding the full carrier. -/
private theorem coupled_second_step (c : Q') (x : GNSCompletionSpace F) (n : Nat) :
    (coupled hw0 hw1 K extent hK c x (n+1)).2 =
      (F).cAdd (coupled hw0 hw1 K extent hK c x n).1
        (affine hw0 hw1 K extent hK c (coupled hw0 hw1 K extent hK c x n).2) := rfl

/-- The actual auxiliary second component at step n+1 is operationally
localized within n balanced sixteen-star expansions. This is weaker than
literal polynomial support and asserts no norm decrease. -/
theorem coupled_second_succ_localized (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent (16*n) support)
      (coupled hw0 hw1 K extent hK c x (n+1)).2 := by
  induction n with
  | zero =>
      change Localized hw0 hw1 K extent hK support
        ((F).cAdd x (affine hw0 hw1 K extent hK c (embedV F (F).zero)))
      rw [affine_zero hw0 hw1 K extent hK c]
      exact localized_add hw0 hw1 K extent hK support x (embedV F (F).zero)
        hx (localized_zero hw0 hw1 K extent hK support)
  | succ n ih =>
      have ht := coupled_first_localized hw0 hw1 K extent hK c (n+1)
        support x hx
      have ha0 := affine_localized hw0 hw1 K extent hK c
        (grow extent (16*n) support)
        (coupled hw0 hw1 K extent hK c x (n+1)).2 ih
      have ha : Localized hw0 hw1 K extent hK
          (grow extent (16*(n+1)) support)
          (affine hw0 hw1 K extent hK c
            (coupled hw0 hw1 K extent hK c x (n+1)).2) := by
        have hn : 16*(n+1) = 16*n+16 := by omega
        rw [hn, grow_add]
        exact ha0
      rw [coupled_second_step hw0 hw1 K extent hK c x (n+1)]
      exact localized_add hw0 hw1 K extent hK _ _ _ ht ha

/-- The forward full sweep on the actual auxiliary uses precisely its
computed active-link word. -/
theorem auxiliary_forward_eq_coneSchedule (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    (P).sweep (schedule extent) u =
      (P).sweep (coneSchedule extent colors (grow extent (16*n) support)) u := by
  exact forward_eq_coneSchedule hw0 hw1 K extent hK
    (grow extent (16*n) support) _
    (coupled_second_succ_localized hw0 hw1 K extent hK c n support x hx)

/-- The true adjoint word is the reversed color sweep on the actual
forward output, without reversing the original action or changing carrier. -/
theorem auxiliary_reverse_colors (c : Q') (n : Nat)
    (x : GNSCompletionSpace F) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    (P).sweep (schedule extent).reverse ((P).sweep (schedule extent) u) =
      runLayers hw0 hw1 K extent hK colors.reverse
        ((P).sweep (schedule extent) u) := by
  exact schedule_reverse_sweep hw0 hw1 K extent hK _

/-- The reverse sweep on the actual forward auxiliary output has exactly
the explicit pruned word at the enlarged operational support. -/
theorem auxiliary_reverse_eq_coneSchedule (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    let z := (P).sweep (schedule extent) u
    (P).sweep (schedule extent).reverse z =
      (P).sweep
        (coneSchedule extent colors.reverse
          (grow extent 8 (grow extent (16*n) support))) z := by
  have hu := coupled_second_succ_localized hw0 hw1 K extent hK c n support x hx
  have hz := eight_layer_localized hw0 hw1 K extent hK
    (grow extent (16*n) support) _ hu
  exact reverse_eq_coneSchedule hw0 hw1 K extent hK
    (grow extent 8 (grow extent (16*n) support)) _ hz

/-- This is the exact original completed reverse-loss word to be bounded
from below in a future analytic argument. No such lower bound is assumed. -/
theorem auxiliary_reverse_loss_eq_coneSchedule (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    let z := (P).sweep (schedule extent) u
    (P).loss (schedule extent).reverse z =
      (P).loss
        (coneSchedule extent colors.reverse
          (grow extent 8 (grow extent (16*n) support))) z := by
  have hu := coupled_second_succ_localized hw0 hw1 K extent hK c n support x hx
  have hz := eight_layer_localized hw0 hw1 K extent hK
    (grow extent (16*n) support) _ hu
  exact reverse_loss_eq_coneSchedule hw0 hw1 K extent hK
    (grow extent 8 (grow extent (16*n) support)) _ hz

/-- The required reverse-energy input is EXACTLY a lower bound on the
computed pruned loss word at this actual auxiliary vector. The equivalence
constructs neither side; it retains the same state and original norm. -/
theorem auxiliary_reverse_energy_iff_cone_loss (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    let z := (P).sweep (schedule extent) u
    RCle (RCscale c (normSq ((P).balanced (schedule extent) u)))
        (RCscale 2 (normSq z)) ↔
      RCle (RCscale (c + (-(2 : Q'))) (normSq z))
        (RCscale c ((P).loss
          (coneSchedule extent colors.reverse
            (grow extent 8 (grow extent (16*n) support))) z)) := by
  dsimp only
  rw [reverse_energy_iff_loss hw0 hw1 K extent hK,
    auxiliary_reverse_loss_eq_coneSchedule hw0 hw1 K extent hK c n support x hx]

#print axioms coupled_second_succ_localized
#print axioms auxiliary_forward_eq_coneSchedule
#print axioms auxiliary_reverse_colors
#print axioms auxiliary_reverse_eq_coneSchedule
#print axioms auxiliary_reverse_loss_eq_coneSchedule
#print axioms auxiliary_reverse_energy_iff_cone_loss

end YMGap.Continuum.BF4ExactSlabChebyshevAuxiliaryCone
