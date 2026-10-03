/-
# Every finite ordinary-log form is dominated by the ORIGINAL domain action

Positive original defect moments make the literal finite logarithm forms
monotone. The existing ordinary-log domain modulus and actual completed
pairing continuity pass this order to the SAME supplied domain output.
Neither transfer inversion nor a uniform preimage norm is used.

Consumer: rational finite-prefix coercivity of the identified original
generator from its checked transfer margin. This is not a physical scaling,
canonical continuum OS realization, or Clay closure.
-/

import YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.CRealSeminormPairingCompletion

namespace YMGap.Continuum.BF4WilsonAllNomeDomainLogForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower mixedMoment mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial (unregularizedLogPartial)
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (vectorSum)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)
open YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm (domainLogModulus domainLogarithm_bound)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (pairing_close)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unregularizedLogPartial hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem term_nonnegative (x : V) (j : Nat) :
    RCnonneg (RCscale (Q'.invSucc j) (B x (DP (j+1) x))) := by
  have h := RCscale_mono (Q'.invSucc_nonneg j)
    (mixedMoment_nonnegative hw0 hw1 x 0 (j+1))
  simpa only [mixedMoment, completedTime_zero, RCscale_RCzero] using h

/-- Increasing the literal cutoff increases its form on the original input. -/
theorem unregularizedLogPartial_form_step (x : V) (n : Nat) :
    RCle (B x (U n x)) (B x (U (n+1) x)) := by
  change RCle (B x (U n x)) (B x (completedAdd hw0 hw1 (U n x)
    (completedSmul hw0 hw1 (Q'.invSucc n) (DP (n+1) x))))
  rw [completedInner_add_right, completedInner_smul_right]
  have h := RCadd_le_add (RCle_refl (B x (U n x))) (term_nonnegative hw0 hw1 x n)
  rwa [add_zero] at h

/-- All finite cutoff comparisons are between the SAME input and form. -/
theorem unregularizedLogPartial_form_mono (x : V) (m n : Nat) (hmn : m ≤ n) :
    RCle (B x (U m x)) (B x (U n x)) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact RCle_refl _
  | succ n ih =>
      by_cases hm : m ≤ n
      · exact RCle_trans (ih hm) (unregularizedLogPartial_form_step hw0 hw1 x n)
      · have heq : m = n+1 := by omega
        subst m
        exact RCle_refl _

private theorem form_le_with_caps (p : DomainPoint hw0 hw1 (width := width))
    (m : Nat) (cap : Q') (hcap : (0 : Q') ≤ cap)
    (hicap : RCle (B p.input.val p.input.val) (rat cap))
    (hocap : RCle (B p.output.val p.output.val) (rat cap)) :
    RCle (B p.input.val (U m p.input.val)) (B p.input.val p.output.val) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  let delta := pairingTolerance cap hcap e
  have hd : (0 : Q') < delta := pairingTolerance_pos cap hcap he
  let n := max m (domainLogModulus hw0 hw1 p delta)
  have hn : domainLogModulus hw0 hw1 p delta ≤ n := Nat.le_max_right _ _
  have hdist := domainLogarithm_bound hw0 hw1 p delta hd n hn
  have hsame : RCle (completedDist hw0 hw1 p.input.val p.input.val) (rat delta) := by
    rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
    exact leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt hd)
  have hreverse : RCle (completedDist hw0 hw1 p.output.val (U n p.input.val))
      (rat delta) := by
    rw [completedDist_symm]
    exact hdist
  have hclose := (pairing_close hw0 hw1 p.input.val p.input.val p.output.val
    (U n p.input.val) cap hcap e he hsame hreverse hocap hicap).2
  exact RCle_trans (unregularizedLogPartial_form_mono hw0 hw1 p.input.val m n
    (Nat.le_max_left _ _)) hclose

private theorem range_norm_cap {x : V}
    (R : YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure.RangeLimit hw0 hw1 x) :
    RCle (B x x) (rat (normCeiling (pairingData hw0 hw1)
      (representative hw0 hw1 R))) := by
  have h := completedInner_diagonal_le_normCeiling (pairingData hw0 hw1)
    (representative hw0 hw1 R)
  change RCle (B (Class (representative hw0 hw1 R))
    (Class (representative hw0 hw1 R))) _ at h
  simpa only [representative_pin] using h

attribute [local irreducible] normCeiling representative

/-- Every finite ordinary-log prefix is bounded by the actual ORIGINAL
domain action, using its computed modulus rather than a new limit premise. -/
theorem domain_logPartial_form_le (p : DomainPoint hw0 hw1 (width := width)) (m : Nat) :
    RCle (B p.input.val (U m p.input.val)) (B p.input.val p.output.val) := by
  let P := pairingData hw0 hw1 (width := width)
  let ci := normCeiling P (representative hw0 hw1 p.input.range)
  let co := normCeiling P (representative hw0 hw1 p.output.range)
  let cap := Q'.max' ci co
  have hci0 : (0 : Q') ≤ ci := normCeiling_nonnegative P _
  have hcap : (0 : Q') ≤ cap := Q'.le_trans' _ _ _ hci0 (Q'.le_max'_left _ _)
  have hicap : RCle (B p.input.val p.input.val) (rat cap) :=
    RCle_trans (range_norm_cap hw0 hw1 p.input.range)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_left ci co))
  have hocap : RCle (B p.output.val p.output.val) (rat cap) :=
    RCle_trans (range_norm_cap hw0 hw1 p.output.range)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right ci co))
  exact form_le_with_caps hw0 hw1 p m cap hcap hicap hocap

#print axioms unregularizedLogPartial_form_step
#print axioms unregularizedLogPartial_form_mono
#print axioms domain_logPartial_form_le

end YMGap.Continuum.BF4WilsonAllNomeDomainLogForm
