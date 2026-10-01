/-
Finite laws of the actual dyadic root resolvents on the original Wilson
completion.  These are finite-depth identities and estimates; the represented
limit and its graph equation are separate.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicResolventLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
open YMGap.Continuum.BF4WilsonAllNomeRootResolvent
open YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (smul_sub)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "R" => root hw0 hw1
local notation "F" => denominator hw0 hw1
local notation "J" => inverse hw0 hw1
local notation "D" => BF4WilsonAllNomeDyadicDefectDecay.defect hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "half" => HalfPow.half

private theorem reciprocal_scale (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) :
    Q'.eqv (h * Q'.recipPos (lambda*h) (Q'.mul_pos hl hh))
      (Q'.recipPos lambda hl) := by
  apply Q'.mul_left_cancel_of_pos hl
  have ha : Q'.eqv
      (lambda * (h * Q'.recipPos (lambda*h) (Q'.mul_pos hl hh))) 1 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv lambda h _))
      (Q'.mul_recipPos_eqv (lambda*h) (Q'.mul_pos hl hh))
  exact Q'.eqv_trans _ _ _ ha
    (Q'.eqv_symm (Q'.mul_recipPos_eqv lambda hl))

theorem atStep_symmetric (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x y : V) :
    B (atStep hw0 hw1 depth lambda h hl hh x) y =
      B x (atStep hw0 hw1 depth lambda h hl hh y) := by
  unfold atStep BF4WilsonAllNomeShiftedRootResolvent.inverse
  rw [completedInner_smul_left, completedInner_smul_right,
    completedInner_smul_left, completedInner_smul_right]
  rw [resolvent_symmetric]

theorem atStep_add (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x y : V) :
    atStep hw0 hw1 depth lambda h hl hh (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (atStep hw0 hw1 depth lambda h hl hh x)
        (atStep hw0 hw1 depth lambda h hl hh y) := by
  unfold atStep BF4WilsonAllNomeShiftedRootResolvent.inverse
  rw [resolvent_add, completedSmul_add, completedSmul_add]

theorem atStep_smul (depth : Nat) (lambda h c : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) :
    atStep hw0 hw1 depth lambda h hl hh (S c x) =
      S c (atStep hw0 hw1 depth lambda h hl hh x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [atStep_symmetric, completedInner_smul_left, completedInner_smul_left,
    atStep_symmetric]

theorem atStep_sub (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x y : V) :
    atStep hw0 hw1 depth lambda h hl hh (Sub x y) =
      Sub (atStep hw0 hw1 depth lambda h hl hh x)
        (atStep hw0 hw1 depth lambda h hl hh y) := by
  unfold completedSub completedNeg
  rw [atStep_add, atStep_smul]

/-- Sharp bound, uniform in root depth and using only lambda>0. -/
theorem atStep_norm_bound (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) :
    RCle (B (atStep hw0 hw1 depth lambda h hl hh x)
      (atStep hw0 hw1 depth lambda h hl hh x))
      (RCscale (Q'.recipPos lambda hl * Q'.recipPos lambda hl) (B x x)) := by
  unfold atStep
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  have hbound := inverse_norm_bound hw0 hw1 depth (lambda*h) 1
    (Q'.mul_pos hl hh) (by decide) x
  have hscaled := RCscale_mono
    (SumOfSquares.q_mul_self_nonneg h) hbound
  rw [RCscale_RCscale] at hscaled
  have hc := reciprocal_scale lambda h hl hh
  have hs : Q'.eqv
      ((h*h)*(Q'.recipPos (lambda*h) (Q'.mul_pos hl hh) *
        Q'.recipPos (lambda*h) (Q'.mul_pos hl hh)))
      ((h*Q'.recipPos (lambda*h) (Q'.mul_pos hl hh)) *
        (h*Q'.recipPos (lambda*h) (Q'.mul_pos hl hh))) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => h | _ => Q'.recipPos (lambda*h) (Q'.mul_pos hl hh))
  have hp : Q'.eqv
      ((h*h)*(Q'.recipPos (lambda*h) (Q'.mul_pos hl hh) *
        Q'.recipPos (lambda*h) (Q'.mul_pos hl hh)))
      (Q'.recipPos lambda hl * Q'.recipPos lambda hl) :=
    Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
        (Q'.mul_eqv_congr_left _ _ _ hc))
  rw [scale_congr hp] at hscaled
  exact hscaled

theorem dyadic_symmetric (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x y : V) :
    B (dyadic hw0 hw1 depth lambda hl x) y =
      B x (dyadic hw0 hw1 depth lambda hl y) :=
  atStep_symmetric hw0 hw1 depth lambda (half^depth) hl
    (dyadicStep_positive depth) x y

theorem dyadic_add (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x y : V) :
    dyadic hw0 hw1 depth lambda hl (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (dyadic hw0 hw1 depth lambda hl x)
        (dyadic hw0 hw1 depth lambda hl y) :=
  atStep_add hw0 hw1 depth lambda (half^depth) hl
    (dyadicStep_positive depth) x y

theorem dyadic_smul (depth : Nat) (lambda c : Q')
    (hl : (0 : Q') < lambda) (x : V) :
    dyadic hw0 hw1 depth lambda hl (S c x) =
      S c (dyadic hw0 hw1 depth lambda hl x) :=
  atStep_smul hw0 hw1 depth lambda (half^depth) c hl
    (dyadicStep_positive depth) x

theorem dyadic_sub (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x y : V) :
    dyadic hw0 hw1 depth lambda hl (Sub x y) =
      Sub (dyadic hw0 hw1 depth lambda hl x)
        (dyadic hw0 hw1 depth lambda hl y) :=
  atStep_sub hw0 hw1 depth lambda (half^depth) hl
    (dyadicStep_positive depth) x y

theorem dyadic_norm_bound (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x : V) :
    RCle (B (dyadic hw0 hw1 depth lambda hl x)
      (dyadic hw0 hw1 depth lambda hl x))
      (RCscale (Q'.recipPos lambda hl * Q'.recipPos lambda hl) (B x x)) :=
  atStep_norm_bound hw0 hw1 depth lambda (half^depth) hl
    (dyadicStep_positive depth) x

private theorem scaled_denominator_defect (depth : Nat) (m alpha : Q') (y : V) :
    S m (D depth y) = Sub (S m (F depth alpha 1 y)) (S (m*alpha) y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro t
  unfold BF4WilsonAllNomeDyadicDefectDecay.defect denominator
  rw [completedSmul_one]
  simp only [completedInner_smul_left, completedInner_sub_left]
  refine Quotient.inductionOn₂ (B y t) (B (R depth y) t) ?_
  intro Y Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
      (.add
        (.mul (.var 0)
          (.add (.mul (.add (.var 1) (.const 1)) (.var 2))
            (.neg (.var 3))))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (by decide)
      (fun | 0 => m | 1 => alpha | 2 => Y.approx n | _ => Z.approx n)))

private theorem dyadic_mass_cancel (depth : Nat) :
    Q'.eqv (Q'.ofNat (2^depth) * half^depth) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (half_power_normalizes depth)

private theorem dyadic_alpha_cancel (depth : Nat) (lambda : Q') :
    Q'.eqv (Q'.ofNat (2^depth) * (lambda*half^depth)) lambda := by
  have hs : Q'.eqv
      (Q'.ofNat (2^depth) * (lambda*half^depth))
      ((Q'.ofNat (2^depth)*half^depth)*lambda) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide)
      (fun | 0 => Q'.ofNat (2^depth) | 1 => lambda | _ => half^depth)
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (dyadic_mass_cancel depth))
      (Q'.one_mul_eqv lambda))

/-- Exact finite original-carrier generator-quotient equation. -/
theorem dyadic_quotient_equation (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x : V) :
    Q depth (dyadic hw0 hw1 depth lambda hl x) =
      T 1 (Sub x (S lambda (dyadic hw0 hw1 depth lambda hl x))) := by
  let h := half^depth
  let m := Q'.ofNat (2^depth)
  let y := dyadic hw0 hw1 depth lambda hl x
  have hden : F depth (lambda*h) 1 y = S h x :=
    atStep_equation hw0 hw1 depth lambda h hl (dyadicStep_positive depth) x
  have hscaled : S m (D depth y) = Sub x (S lambda y) := by
    calc
      S m (D depth y) =
          Sub (S m (F depth (lambda*h) 1 y)) (S (m*(lambda*h)) y) :=
        scaled_denominator_defect hw0 hw1 depth m (lambda*h) y
      _ = Sub (S m (S h x)) (S (m*(lambda*h)) y) := by rw [hden]
      _ = Sub x (S lambda y) := by
        rw [completedSmul_mul,
          completedSmul_congr hw0 hw1 (dyadic_mass_cancel depth),
          completedSmul_one,
          completedSmul_congr hw0 hw1 (dyadic_alpha_cancel depth lambda)]
  unfold differenceQuotient
  rw [← mesh_original hw0 hw1 1 y,
    ← time_defect hw0 hw1 0 1 depth y,
    mesh_original hw0 hw1 1 (D depth y),
    ← completedTime_smul hw0 hw1 1 m]
  exact congrArg (T 1) hscaled

#print axioms atStep_symmetric
#print axioms atStep_add
#print axioms atStep_smul
#print axioms atStep_sub
#print axioms atStep_norm_bound
#print axioms dyadic_symmetric
#print axioms dyadic_add
#print axioms dyadic_smul
#print axioms dyadic_sub
#print axioms dyadic_norm_bound
#print axioms dyadic_quotient_equation

end YMGap.Continuum.BF4WilsonAllNomeDyadicResolventLaws
