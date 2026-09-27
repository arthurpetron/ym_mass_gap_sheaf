/-
# Genuine finite-volume reverse energy for original conditional sweeps

The constructed completed Dirichlet lower bound, applied to the output of
the actual balanced sweep, combines with the geometric 625 sweep-loss upper
bound. It gives a strict reverse-energy coefficient for every centered
completed vector. The coefficient depends on nome and extent; this is not an
OS transfer gap or a scaling-uniform Yang--Mills estimate.
-/

import YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity
import YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
import YMGap.Continuum.BF4ExactSlabSweepChebyshev
import YMGap.Continuum.GNSProjectionSweepEnergyOrder
import YMGap.Continuum.BF4ExactSlabChebyshevRescale
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity
open YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity

local infix:50 " ≈ " => Q'.eqv

/-- Exactly two divided by the geometric row-and-column constant 625. -/
def geometricCalibration : Q' := ⟨2, 624⟩

private theorem geometricCalibration_pos : (0 : Q') < geometricCalibration := by decide

private theorem geometricCalibration_cancel : geometricCalibration * (625 : Q') ≈ 2 := by decide

private theorem scale_eqv {s t : Q'} (h : s ≈ t) (a : RC) :
    RCscale s a = RCscale t a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right _ _ _ h))

private theorem calibration_left (delta : Q') (b : RC) :
    RCadd (RCscale 2 b)
      (RCscale (geometricCalibration * delta) b) =
      RCscale (2 + geometricCalibration * delta) b := by
  refine Quotient.inductionOn b ?_
  intro B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (.mul (.add (.const 2) (.mul (.var 0) (.var 1))) (.var 2))
      (by decide)
      (fun | 0 => geometricCalibration | 1 => delta | _ => B.approx n)))

private theorem calibration_right (a b : RC) :
    RCadd (RCscale 2 b) (RCscale 2 (RCsub a b)) = RCscale 2 a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 1))
        (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))))
      (.mul (.const 2) (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

/-- The exact scalar rearrangement: delta*b <= 625*(a-b) implies
`(2+2*delta/625)*b <= 2*a`. No division of completed norms occurs. -/
private theorem calibrated_reverse_energy (delta : Q') (a b : RC)
    (h : RCle (RCscale delta b) (RCscale 625 (RCsub a b))) :
    RCle (RCscale (2 + geometricCalibration * delta) b) (RCscale 2 a) := by
  have hs := RCscale_mono (Q'.le_of_lt geometricCalibration_pos) h
  rw [RCscale_RCscale, RCscale_RCscale,
    scale_eqv geometricCalibration_cancel] at hs
  have hh := RCadd_le_add (RCle_refl (RCscale 2 b)) hs
  rw [calibration_left, calibration_right] at hh
  exact hh

/-- A strictly larger-than-two coefficient for each fixed nome and extent.
Its positive excess is proportional to the constructed, volume-dependent
coercivity coefficient. -/
def reverseCoefficient {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) : Q' :=
  2 + geometricCalibration * coercivity hw0 hw1 extent

private theorem lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) :
    a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand : (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int) =
      a.num * ((a.den : Int) * (b.den : Int)) +
        b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

/-- Any positive same-carrier Dirichlet coefficient yields a strict
calibrated reverse-energy coefficient. -/
theorem calibrated_coefficient_gt_two (delta : Q') (hdelta : (0 : Q') < delta) :
    (2 : Q') < 2 + geometricCalibration * delta :=
  lt_add_of_pos_right 2 _ (Q'.mul_pos geometricCalibration_pos hdelta)

theorem reverseCoefficient_gt_two {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    (2 : Q') < reverseCoefficient hw0 hw1 extent := by
  unfold reverseCoefficient
  exact calibrated_coefficient_gt_two _ (coercivity_positive hw0 hw1 extent)

theorem reverseCoefficient_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    (0 : Q') ≤ reverseCoefficient hw0 hw1 extent := by
  unfold reverseCoefficient
  exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 2)
    (Q'.add_le_self_of_nonneg 2 _
      (Q'.le_of_lt (Q'.mul_pos geometricCalibration_pos
        (coercivity_positive hw0 hw1 extent))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "W" => Family.sweep (projections hw0 hw1 K extent hK) (schedule extent)
local notation "B" => Family.balanced (projections hw0 hw1 K extent hK) (schedule extent)

/-- Convert a supplied Dirichlet bound at the ACTUAL balanced output into
reverse energy, using only the proved 625 loss of the reversed original
physical schedule. Neither centering nor a spectral assumption is needed
for this algebraic conversion. -/
theorem reverse_energy_of_coercivity_at_balanced (delta : Q')
    (u : GNSCompletionSpace F)
    (hcoerce : RCle (RCscale delta (normSq (B u)))
      ((P).finalEnergy (schedule extent) (B u))) :
    RCle (RCscale (2 + geometricCalibration * delta) (normSq (B u)))
      (RCscale 2 (normSq (W u))) := by
  let y := W u
  let z := B u
  have hnodup : (schedule extent).reverse.Nodup :=
    (List.reverse_perm (schedule extent)).nodup_iff.mpr (schedule_nodup extent)
  have hupper := BF4ExactSlabConditionalSweepEnergy.final_energy_le_625_loss
    hw0 hw1 K extent hK (schedule extent).reverse hnodup y
  change RCle ((P).finalEnergy (schedule extent).reverse z)
    (RCscale 625 (RCsub (normSq y) (normSq z))) at hupper
  rw [(P).finalEnergy_reverse] at hupper
  have hdelta : RCle (RCscale delta (normSq z))
      (RCscale 625 (RCsub (normSq y) (normSq z))) :=
    RCle_trans hcoerce hupper
  exact calibrated_reverse_energy delta (normSq y) (normSq z) hdelta

/-- Actual reverse energy of the original balanced conditional sweep on every
centered vector in the same completed full-action GNS space. -/
theorem finite_volume_reverse_energy (u : GNSCompletionSpace F)
    (hu : Centered hw0 hw1 K extent hK u) :
    RCle (RCscale (reverseCoefficient hw0 hw1 extent) (normSq (B u)))
      (RCscale 2 (normSq (W u))) := by
  let y := W u
  let z := B u
  have hy : Centered hw0 hw1 K extent hK y :=
    sweep_centered hw0 hw1 K extent hK (schedule extent) u hu
  have hz : Centered hw0 hw1 K extent hK z :=
    sweep_centered hw0 hw1 K extent hK (schedule extent).reverse y hy
  have hzUnit : (F).cinnerCompl z
      (embedV F (BF4ExactSlabConditionalCovariance.unit hw0 hw1 extent stage)) = RCzero := by
    change (F).cinnerCompl z
      (embedV F (BF4ExactSlabSweepChebyshev.constant hw0 hw1 K extent hK)) = RCzero at hz
    exact hz
  have hcoerce := completed_centered_coercivity hw0 hw1 extent stage z hzUnit
  exact reverse_energy_of_coercivity_at_balanced hw0 hw1 extent stage
    (coercivity hw0 hw1 extent) u hcoerce

/-- The auxiliary vector generated by the actual Chebyshev recurrence is
centered whenever its initial vector is. Thus the same proved reverse-energy
bound applies at every recurrence order. -/
theorem coupled_auxiliary_reverse_energy (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) (n : Nat) :
    let u := (coupled hw0 hw1 K extent hK
      (reverseCoefficient hw0 hw1 extent) x n).2
    RCle (RCscale (reverseCoefficient hw0 hw1 extent) (normSq (B u)))
      (RCscale 2 (normSq (W u))) := by
  exact finite_volume_reverse_energy hw0 hw1 extent stage _
    (coupled_centered hw0 hw1 K extent hK
      (reverseCoefficient hw0 hw1 extent) x hx n).2

#print axioms geometricCalibration
#print axioms calibrated_coefficient_gt_two
#print axioms reverseCoefficient
#print axioms reverseCoefficient_gt_two
#print axioms reverseCoefficient_nonnegative
#print axioms finite_volume_reverse_energy
#print axioms reverse_energy_of_coercivity_at_balanced
#print axioms coupled_auxiliary_reverse_energy

end YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
