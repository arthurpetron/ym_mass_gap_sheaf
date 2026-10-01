/-
# Sharp same-source retention from an original energy bound

Put N=B(x,x), E=B(x,x-Tx), and r=1-c. The ORIGINAL pairing gives

  ||Tx-r*x||² + 2*r*(c*N-E) = ||Tx||²-r²*N.

For c<=1 and E<=c*N both left terms are nonnegative, so smoothing retains
(1-c)² of the source squared norm. No reciprocal or zero decision on N is
used. For 0<=c<1 the actual derivative-core form has ratio c/(1-c)².
The source floor and source-replacement/vacuum laws stay on the SAME carrier.

This sharpens a conditional consumer, not the missing original signed-energy
estimate on a justified changing-coupling/spatial/spacing family. It supplies
neither physical time calibration nor nonzero continuum survival.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorSourceTransfer
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.BF4WilsonAllNomeSectorSharpEnergyTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_smul_left completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (corePoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorSmoothingEnergy (derivative_core_upper)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "E" x => B x (defect hw0 hw1 x)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def retainedFraction (c : Q') : Q' := (1 + (-c)) * (1 + (-c))

theorem retainedFraction_positive {c : Q'} (hc1 : c < (1 : Q')) :
    (0 : Q') < retainedFraction c := HKPos.factorLB_pos hc1

def energyRatio (c : Q') (hc1 : c < (1 : Q')) : Q' :=
  Q'.divPos c (retainedFraction c) (retainedFraction_positive hc1)

theorem energyRatio_nonnegative {c : Q'} (hc0 : (0 : Q') ≤ c)
    (hc1 : c < (1 : Q')) : (0 : Q') ≤ energyRatio c hc1 :=
  Q'.mul_nonneg _ _ hc0 (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem rc_sub_nonnegative {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem rc_le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) :
    RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [rc_zero_add, rc_sub_add_cancel] at h'

private theorem rc_scale_nonnegative {s : Q'} (hs : (0 : Q') ≤ s)
    (a : RC) (ha : RCnonneg a) : RCnonneg (RCscale s a) := by
  change RCle RCzero (RCscale s a)
  rw [← RCscale_RCzero s]
  exact RCscale_mono hs ha

private theorem rc_add_nonnegative {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rwa [rc_zero_add] at h

private theorem retention_scalar (c : Q') (n p m : RC) :
    RCadd
      (RCsub (RCsub m (RCscale (1+(-c)) p))
        (RCscale (1+(-c)) (RCsub p (RCscale (1+(-c)) n))))
      (RCscale (2*(1+(-c))) (RCsub (RCscale c n) (RCsub n p))) =
      RCsub m (RCscale (retainedFraction c) n) := by
  refine Quotient.inductionOn₃ n p m ?_
  intro N P M
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k => by
    let r : PolyExpr := .add (.const 1) (.neg (.var 3))
    exact poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 2) (.neg (.mul r (.var 1))))
          (.neg (.mul r (.add (.var 1) (.neg (.mul r (.var 0)))))))
        (.mul (.mul (.const 2) r)
          (.add (.mul (.var 3) (.var 0)) (.neg (.add (.var 0) (.neg (.var 1)))))))
      (.add (.var 2) (.neg (.mul (.mul r r) (.var 0))))
      (by decide) (fun | 0 => N.approx k | 1 => P.approx k | 2 => M.approx k | _ => c)))

/-- Exact positive-square identity on the ORIGINAL completed pairing. -/
theorem retention_square_identity (x : V) (c : Q') :
    RCadd
      (B (completedSub hw0 hw1 (T 1 x) (completedSmul hw0 hw1 (1+(-c)) x))
        (completedSub hw0 hw1 (T 1 x) (completedSmul hw0 hw1 (1+(-c)) x)))
      (RCscale (2*(1+(-c))) (RCsub (RCscale c (B x x)) (E x))) =
      RCsub (B (T 1 x) (T 1 x)) (RCscale (retainedFraction c) (B x x)) := by
  simp only [completedInner_sub_left, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right]
  rw [completedInner_symm hw0 hw1 (T 1 x) x]
  change RCadd _ (RCscale _ (RCsub (RCscale c (B x x))
    (B x (completedSub hw0 hw1 x (T 1 x))))) = _
  rw [completedInner_sub_right]
  exact retention_scalar c (B x x) (B x (T 1 x)) (B (T 1 x) (T 1 x))

/-- Includes zero norm; no division by a constructive real is performed.
The non-strict c<=1 guard suffices for this retention implication. -/
theorem relative_norm_retention (x : V) (c : Q') (hc1 : c ≤ (1 : Q'))
    (h : RCle (E x) (RCscale c (B x x))) :
    RCle (RCscale (retainedFraction c) (B x x)) (B (T 1 x) (T 1 x)) := by
  have hfactor : (0 : Q') ≤ 2*(1+(-c)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hc1)
  have hsquare := completedInner_nonnegative hw0 hw1
    (completedSub hw0 hw1 (T 1 x) (completedSmul hw0 hw1 (1+(-c)) x))
  have hgap := rc_scale_nonnegative hfactor _ (rc_sub_nonnegative h)
  have hsum := rc_add_nonnegative hsquare hgap
  rw [retention_square_identity] at hsum
  exact rc_le_of_sub_nonnegative hsum

/-- The SAME actual derivative-core form now has ratio c/(1-c)² for 0<=c<1,
instead of requiring the older positive fraction 1-2c. -/
theorem relative_derivative_bound (x : V) (c : Q') (hc0 : (0 : Q') ≤ c)
    (hc1 : c < (1 : Q')) (h : RCle (E x) (RCscale c (B x x))) :
    RCle (B (T 1 x) (derivativeAction hw0 hw1 x))
      (RCscale (energyRatio c hc1) (B (T 1 x) (T 1 x))) := by
  have hratio := RCscale_mono (energyRatio_nonnegative hc0 hc1)
    (relative_norm_retention hw0 hw1 x c (Q'.le_of_lt hc1) h)
  have hcancel : Q'.eqv (energyRatio c hc1 * retainedFraction c) c :=
    Q'.divPos_mul_eqv c (retainedFraction c) (retainedFraction_positive hc1)
  rw [RCscale_RCscale, scale_congr hcancel] at hratio
  exact RCle_trans (derivative_core_upper hw0 hw1 x) (RCle_trans h hratio)

theorem corePoint_relative_bound (X : (D).Cauchy) (c : Q') (hc0 : (0 : Q') ≤ c)
    (hc1 : c < (1 : Q'))
    (h : RCle (E (Class X)) (RCscale c (B (Class X) (Class X)))) :
    RCle (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).output.val)
      (RCscale (energyRatio c hc1)
        (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).input.val)) :=
  relative_derivative_bound hw0 hw1 (Class X) c hc0 hc1 h

/-- A supplied original source floor is retained by the computed square factor. -/
theorem corePoint_norm_floor (X : (D).Cauchy) (floor c : Q') (hc1 : c < (1 : Q'))
    (hfloor : RCle (rat floor) (B (Class X) (Class X)))
    (h : RCle (E (Class X)) (RCscale c (B (Class X) (Class X)))) :
    RCle (rat (retainedFraction c * floor))
      (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).input.val) :=
  RCle_trans (RCscale_mono (Q'.le_of_lt (retainedFraction_positive hc1)) hfloor)
    (relative_norm_retention hw0 hw1 (Class X) c (Q'.le_of_lt hc1) h)

theorem transferredFloor_positive {floor c : Q'} (hf : (0 : Q') < floor)
    (hc1 : c < (1 : Q')) : (0 : Q') < retainedFraction c * floor :=
  Q'.mul_pos (retainedFraction_positive hc1) hf

#print axioms retainedFraction
#print axioms retainedFraction_positive
#print axioms energyRatio
#print axioms energyRatio_nonnegative
#print axioms retention_square_identity
#print axioms relative_norm_retention
#print axioms relative_derivative_bound
#print axioms corePoint_relative_bound
#print axioms corePoint_norm_floor
#print axioms transferredFloor_positive

end YMGap.Continuum.BF4WilsonAllNomeSectorSharpEnergyTransfer
