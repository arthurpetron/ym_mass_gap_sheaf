/-
# Original time smoothing retains norm against its defect cost

The finite dyadic terminal moment controls the original derivative on the
one-step image. Its limit and the exact squared defect identity give a
same-carrier energy upper bound and a quantitative norm-retention inequality.
No source-dependent smallness premise is introduced here.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.RationalScalarTwoSidedError

namespace YMGap.Continuum.BF4WilsonAllNomeSectorSmoothingEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (mesh_double)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
  (moment moment_halfTime weighted_terminal defectPower defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (differenceQuotient quotientRows quotientRows_pin derivativeAction derivativeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_add_sub_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => X.approx n | _ => Y.approx n)))

private theorem rc_add_cancel (a b : RC) : RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0) (by decide)
      (fun | 0 => X.approx n | _ => Y.approx n)))

private theorem rc_two_scale (a : RC) : RCscale 2 a = RCadd a a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
      (.add (.var 0) (.var 0)) (by decide) (fun _ => X.approx n)))

private theorem rc_retention_identity (a b c : RC) :
    RCadd a (RCsub (RCsub a b) (RCsub b c)) =
      RCadd c (RCadd (RCsub a b) (RCsub a b)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro X Y Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 2) (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))) (by decide)
      (fun | 0 => X.approx n | 1 => Y.approx n | _ => Z.approx n)))

private theorem rc_gap_le_defect (a b c : RC)
    (h : RCnonneg (RCsub (RCsub a b) (RCsub b c))) :
    RCle (RCsub b c) (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCsub b c))
  rw [rc_zero_add,rc_add_sub_cancel] at h'
  exact h'

private theorem rc_le_sub_of_add_le {a b c : RC}
    (h : RCle (RCadd a b) c) : RCle a (RCsub c b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  rw [rc_add_cancel] at h'
  exact h'

/-- A full finite dyadic time step retains its terminal moment. The first
term is exactly the quotient derivative paired with the original time image. -/
theorem finite_terminal_energy (depth : Nat) (x : V) :
    RCle (RCadd (B (T 1 x) (Q depth x)) (B (T 1 x) (T 1 x)))
      (B x (T 1 x)) := by
  let m := 2^depth
  have h := weighted_terminal hw0 hw1 depth x m 0 m
  have hmoment1 : moment hw0 hw1 depth x (m+m) 1 =
      B (T 1 x) (defect hw0 hw1 depth (T 1 x)) := by
    rw [moment_halfTime,mesh_double,full_mesh_time]
    rfl
  have hmoment0 : moment hw0 hw1 depth x (m+m) 0 =
      B (T 1 x) (T 1 x) := by
    rw [moment_halfTime,mesh_double,full_mesh_time]
    rfl
  have hmomentR : moment hw0 hw1 depth x m 0 = B x (T 1 x) := by
    unfold moment
    rw [full_mesh_time]
    rfl
  have hscale : RCscale (Q'.ofNat m)
      (B (T 1 x) (defect hw0 hw1 depth (T 1 x))) = B (T 1 x) (Q depth x) := by
    unfold differenceQuotient
    rw [completedInner_smul_right]
  simpa only [Nat.zero_add,hmoment1,hmoment0,hmomentR,hscale] using h

/-- The actual completed derivative satisfies a terminal-energy inequality.
The represented-row limit is taken on the same original carrier. -/
theorem derivative_terminal_energy (x : V) :
    RCle (RCadd (B (T 1 x) (A x)) (B (T 1 x) (T 1 x)))
      (B x (T 1 x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let TX := (timeNonexpansive hw0 hw1 1).mapCauchy X
  let R := constantRows hw0 hw1 TX
  let S := quotientRows hw0 hw1 X
  have hfinite (n : Nat) :
      RCle (B (T 1 (Class X)) (Q n (Class X)))
        (RCsub (B (Class X) (T 1 (Class X)))
          (B (T 1 (Class X)) (T 1 (Class X)))) :=
    rc_le_sub_of_add_le (finite_terminal_energy hw0 hw1 n (Class X))
  have hlimit : RCle (B (T 1 (Class X)) (A (Class X)))
      (RCsub (B (Class X) (T 1 (Class X)))
        (B (T 1 (Class X)) (T 1 (Class X)))) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro epsilon he
    let n := pairingModulus hw0 hw1 R S epsilon
    have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).2
    change RCle (B (limit hw0 hw1 R) (limit hw0 hw1 S))
      (RCadd (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n)) (rat epsilon)) at h
    rw [constantRows_point,quotientRows_pin,limit_constantRows] at h
    exact RCle_trans h (RCadd_le_add (hfinite n) (RCle_refl (rat epsilon)))
  have h := RCadd_le_add hlimit (RCle_refl (B (T 1 (Class X)) (T 1 (Class X))))
  rwa [rc_add_sub_cancel] at h

/-- The original defect cost is precisely the first time-pairing loss. -/
private theorem defect_pair (x : V) :
    B x (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x) =
      RCsub (B x x) (B x (T 1 x)) := by
  unfold BF4WilsonAllNomeTimeDefectMoments.defect
  exact completedInner_sub_right hw0 hw1 x x (T 1 x)

private theorem defect_square (x : V) :
    B (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x)
      (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x) =
    RCsub (RCsub (B x x) (B x (T 1 x)))
      (RCsub (B x (T 1 x)) (B (T 1 x) (T 1 x))) := by
  unfold BF4WilsonAllNomeTimeDefectMoments.defect
  rw [completedInner_sub_left,completedInner_sub_right,completedInner_sub_right,
    completedInner_symm hw0 hw1 (T 1 x) x]

/-- Squared norm retained by one original time step is paid by twice its
one-step defect form. This holds for every completed input. -/
theorem norm_retention (x : V) :
    RCle (B x x)
      (RCadd (B (T 1 x) (T 1 x))
        (RCscale 2 (B x (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x)))) := by
  let a := B x x
  let b := B x (T 1 x)
  let c := B (T 1 x) (T 1 x)
  have hn := completedInner_nonnegative hw0 hw1
    (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x)
  rw [defect_square] at hn
  have h := RCadd_le_add (RCle_refl a) hn
  rw [rc_add_zero,rc_retention_identity] at h
  rw [defect_pair,rc_two_scale]
  exact h

/-- The derivative core form on the smoothed state is at most the original
one-step defect form, without a source-dependent or small-nome premise. -/
theorem derivative_core_upper (x : V) :
    RCle (B (T 1 x) (A x))
      (B x (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x)) := by
  have hterminal := derivative_terminal_energy hw0 hw1 x
  have hgap := rc_le_sub_of_add_le hterminal
  have hn := completedInner_nonnegative hw0 hw1
    (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 x)
  rw [defect_square] at hn
  have horder := rc_gap_le_defect (B x x) (B x (T 1 x))
    (B (T 1 x) (T 1 x)) hn
  rw [defect_pair]
  exact RCle_trans hgap horder

#print axioms finite_terminal_energy
#print axioms derivative_terminal_energy
#print axioms norm_retention
#print axioms derivative_core_upper

end YMGap.Continuum.BF4WilsonAllNomeSectorSmoothingEnergy
