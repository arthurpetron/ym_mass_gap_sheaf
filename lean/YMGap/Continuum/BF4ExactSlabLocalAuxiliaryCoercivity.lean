/-
# Constructed reverse energy at the actual local Chebyshev auxiliary

The local representative is BUILT through the pruned original conditional
sweeps, not supplied as an analytic assumption. Applying completed local
coercivity at the actual balanced output gives a strictly larger-than-two
reverse coefficient. Its explicit cost depends on nome, seed support size
and recurrence degree, not extent or late heat cutoff.

The conservative cone-volume cost can grow rapidly with degree. This is not
an asymptotic spatial decay estimate, scaling bound or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabLocalCauchyCone
import YMGap.Continuum.BF4ExactSlabCompletedLocalSupportCoercivity
import YMGap.Continuum.BF4ExactSlabConeSize
import YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy

namespace YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabChebyshevCone
open YMGap.Continuum.BF4ExactSlabChebyshevAuxiliaryCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative
open YMGap.Continuum.BF4ExactSlabLocalCauchyCone
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabCompletedLocalSupportCoercivity
open YMGap.Continuum.BF4ExactSlabConeSize
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy

/-- A volume-independent upper budget for the balanced auxiliary cone at
recurrence step n+1. Its deliberately conservative growth remains visible. -/
def coneBudget (size n : Nat) : Nat := 25^(16*(n+1)) * size

/-- A concrete coefficient, with NO extent or cutoff argument. -/
def localCoefficient {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) : Q' :=
  2 + geometricCalibration * supportRatio hw0 hw1 (coneBudget size n)

theorem localCoefficient_gt_two {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) : (2 : Q') < localCoefficient hw0 hw1 size n :=
  calibrated_coefficient_gt_two _ (supportRatio_positive hw0 hw1 (coneBudget size n))

theorem localCoefficient_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) : (0 : Q') ≤ localCoefficient hw0 hw1 size n :=
  Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 2)
    (Q'.le_of_lt (localCoefficient_gt_two hw0 hw1 size n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "B" => Family.balanced (projections hw0 hw1 K extent hK) (schedule extent)
local notation "W" => Family.sweep (projections hw0 hw1 K extent hK) (schedule extent)
local notation "LR" => LocalRep hw0 hw1 K extent hK

/-- Positive Dirichlet control at the ACTUAL balanced auxiliary. The seed's
literal representative is propagated by construction, with its existing moduli. -/
theorem auxiliary_coercivity (c : Q') (n : Nat) (support : List Z4Link)
    (x : GNSCompletionSpace F) (R : LR support x)
    (hl : Localized hw0 hw1 K extent hK support x)
    (hc : Centered hw0 hw1 K extent hK x) :
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    RCle (RCscale (supportRatio hw0 hw1 (coneBudget support.length n)) (normSq (B u)))
      ((P).finalEnergy (schedule extent) (B u)) := by
  let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
  have hu : Localized hw0 hw1 K extent hK (grow extent (16*n) support) u :=
    coupled_second_succ_localized hw0 hw1 K extent hK c n support x hl
  let Ru := auxiliaryRep hw0 hw1 K extent hK c n support R hl
  have Rz0 := balancedRep hw0 hw1 K extent hK (grow extent (16*n) support) Ru hu
  have Rz : LR (grow extent (16*(n+1)) support) (B u) := by
    have he : 16*(n+1) = 16*n+16 := by omega
    rw [he, grow_add]
    exact Rz0
  have huc : Centered hw0 hw1 K extent hK u :=
    (coupled_centered hw0 hw1 K extent hK c x hc (n+1)).2
  have hzc : Centered hw0 hw1 K extent hK (B u) :=
    sweep_centered hw0 hw1 K extent hK (schedule extent).reverse _
      (sweep_centered hw0 hw1 K extent hK (schedule extent) u huc)
  have hrep : (F).cinnerCompl (Quotient.mk (cauchySetoid F) Rz.rep)
      (embedV F (BF4ExactSlabConditionalCovariance.unit hw0 hw1 extent stage)) = RCzero := by
    rw [Rz.pin]
    exact hzc
  have h := completed_local_coercivity hw0 hw1 extent stage
    (grow extent (16*(n+1)) support) (coneBudget support.length n)
    (grow_length_le extent (16*(n+1)) support) Rz.rep Rz.isLocal hrep
  rw [Rz.pin] at h
  exact h

/-- The backwards covariance consumer's strict reverse-energy hypothesis is
now PRODUCED for this actual local seed and degree. No coercivity premise remains. -/
theorem auxiliary_reverse_energy (n : Nat) (support : List Z4Link)
    (x : GNSCompletionSpace F) (R : LR support x)
    (hl : Localized hw0 hw1 K extent hK support x)
    (hc : Centered hw0 hw1 K extent hK x) :
    let c := localCoefficient hw0 hw1 support.length n
    let u := (coupled hw0 hw1 K extent hK c x (n+1)).2
    RCle (RCscale c (normSq (B u))) (RCscale 2 (normSq (W u))) := by
  exact reverse_energy_of_coercivity_at_balanced hw0 hw1 extent stage
    (supportRatio hw0 hw1 (coneBudget support.length n)) _
    (auxiliary_coercivity hw0 hw1 extent stage
      (localCoefficient hw0 hw1 support.length n) n support x R hl hc)

#print axioms coneBudget
#print axioms localCoefficient
#print axioms localCoefficient_gt_two
#print axioms localCoefficient_nonnegative
#print axioms auxiliary_coercivity
#print axioms auxiliary_reverse_energy

end YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity
