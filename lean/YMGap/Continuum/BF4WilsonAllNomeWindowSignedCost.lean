/-
# Aggregate signed costs on one ORIGINAL temporal orbit

The response loss across a doubled window is at most twice the sum of
its even-lag drops. Thus a joint signed-window estimate can feed the
existing macroscopic-ratio consumers without estimating each drop
separately. This constructs no such analytic estimate or changing family.

The finite original sum retains the SAME depth-stage OWN mean in every
block and each block's DISTINCT Z0,Z1. Its fixed-member convergence uses
the existing original source limits. No unnormalized terminal or source
derivative squares are asserted to telescope; no uniform convergence in
nome, width, square size or growing lag is inferred.
-/

import YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost
import YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio
import YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
import YMGap.Constructive.CRealSum

namespace YMGap.Continuum.BF4WilsonAllNomeWindowSignedCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitResponse dyadicUnitResponse_pin
    dyadicOriginalNorm dyadicOriginalNorm_floor)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
  (originalOwnBlockCost originalOwnBlockVariance originalOwnBlockCost_converges
    originalOwnBlockVariance_converges)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (sub_self_eqv_zero A)

private theorem add_sub_last (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem sub_add_last (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem scale_two (a : RC) : RCscale 2 a = RCadd a a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
      (by decide) (fun _ => A.approx n)))

private theorem scale_add (q : Q') (a b : RC) :
    RCscale q (RCadd a b) = RCadd (RCscale q a) (RCscale q b) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv q (A.approx n) (B.approx n)))

private theorem ratio_of_drop_bound (a b : RC) (kappa : Q')
    (h : RCle (RCsub a b) (RCscale (1-kappa) a)) :
    RCle (RCscale kappa a) b := by
  have ht := RCadd_le_add h (RCle_refl b)
  rw [sub_add_last] at ht
  have hu := RCadd_le_add ht (RCle_refl (RCneg (RCscale (1-kappa) a)))
  change RCle (RCsub a (RCscale (1-kappa) a))
    (RCsub (RCadd (RCscale (1-kappa) a) b) (RCscale (1-kappa) a)) at hu
  have hr : RCsub (RCadd (RCscale (1-kappa) a) b) (RCscale (1-kappa) a) = b := by
    refine Quotient.inductionOn₂ a b ?_
    exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (.var 2))
          (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
        (.var 2) (by decide)
        (fun | 0 => kappa | 1 => A.approx n | _ => B.approx n)))
  have hl : RCsub a (RCscale (1-kappa) a) = RCscale kappa a := by
    refine Quotient.inductionOn a ?_
    exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
        (.mul (.var 0) (.var 1)) (by decide)
        (fun | 0 => kappa | _ => A.approx n)))
  rwa [hl, hr] at hu

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation:max "Resp" x:arg lag:arg => B x (T lag x)
attribute [local irreducible] completedInner completedTime dyadicUnitExcitation dyadicUnitResponse

private theorem first_defect_pin (x : V) (lag : Nat) :
    mixedMoment hw0 hw1 x lag 1 = RCsub (Resp x lag) (Resp x (lag+1)) := by
  have h := mixedMoment_split hw0 hw1 x lag 0
  change Resp x lag = RCadd (Resp x (lag+1)) (mixedMoment hw0 hw1 x lag 1) at h
  have hc := congrArg (fun z => RCsub z (Resp x (lag+1))) h
  change RCsub (Resp x lag) (Resp x (lag+1)) =
    RCsub (RCadd (Resp x (lag+1)) (mixedMoment hw0 hw1 x lag 1)) (Resp x (lag+1)) at hc
  rw [add_sub_first] at hc
  exact hc.symm

/-- Finite SAME-state sum of the actual even-lag signed response drops. -/
def windowSignedCost (x : V) (start : Nat) : Nat → RC
  | 0 => RCzero
  | count+1 => RCadd (windowSignedCost x start count)
      (mixedMoment hw0 hw1 x (2*(start+count)) 1)

private theorem two_step_loss (x : V) (lag : Nat) :
    RCle (RCsub (Resp x lag) (Resp x (lag+2)))
      (RCscale 2 (mixedMoment hw0 hw1 x lag 1)) := by
  have h := RCadd_le_add (RCle_refl (mixedMoment hw0 hw1 x lag 1))
    (mixedMoment_time_decreasing hw0 hw1 x lag 1)
  have ht : RCadd (mixedMoment hw0 hw1 x lag 1) (mixedMoment hw0 hw1 x (lag+1) 1) =
      RCsub (Resp x lag) (Resp x (lag+2)) := by
    rw [first_defect_pin hw0 hw1 x lag, first_defect_pin hw0 hw1 x (lag+1),
      show lag+1+1=lag+2 by omega]
    exact telescope _ _ _
  rw [ht, ← scale_two] at h
  exact h

/-- Unconditional window estimate on EVERY original completed state,
including vacuum and boundary time-kernel components. -/
theorem response_window_cost_bound (x : V) (start count : Nat) :
    RCle (RCsub (Resp x (2*start)) (Resp x (2*(start+count))))
      (RCscale 2 (windowSignedCost hw0 hw1 x start count)) := by
  induction count with
  | zero =>
      rw [Nat.add_zero, sub_self]
      change RCle RCzero (RCscale 2 RCzero)
      rw [RCscale_RCzero]
      exact RCle_refl _
  | succ count ih =>
      have h := RCadd_le_add ih (two_step_loss hw0 hw1 x (2*(start+count)))
      rw [telescope, ← scale_add] at h
      have hi : 2*(start+count)+2=2*(start+(count+1)) := by omega
      rw [hi] at h
      exact h

/-- Exact requested doubled-window instance; no ratio or floor is assumed. -/
theorem response_doubling_window_cost_bound (x : V) (u : Nat) :
    RCle (RCsub (Resp x (2*u)) (Resp x (4*u)))
      (RCscale 2 (windowSignedCost hw0 hw1 x u u)) := by
  have h := response_window_cost_bound hw0 hw1 x u u
  rw [show 2*(u+u)=4*u by omega] at h
  exact h

/-- Conditional analytic implication, not a produced estimate. The joint
signed sum may exploit cancellation unavailable in per-lag ceilings. -/
theorem aggregate_window_macro_ratio (x : V) (u : Nat) (kappa : Q')
    (hbudget : RCle (RCscale 2 (windowSignedCost hw0 hw1 x u u))
      (RCscale (1-kappa) (Resp x (2*u)))) :
    RCle (RCscale kappa (Resp x (2*u))) (Resp x (4*u)) :=
  ratio_of_drop_bound _ _ kappa
    (RCle_trans (response_doubling_window_cost_bound hw0 hw1 x u) hbudget)

section Original

variable (scale width : Nat) (hwidth : side scale < width)
local notation "Unit" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "Norm" => dyadicOriginalNorm hw0 hw1 scale width hwidth
local notation:max "Response" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag
attribute [local irreducible] dyadicOriginalNorm originalOwnBlockCost originalOwnBlockVariance

/-- The literal finite cost sum: each t retains its own two partitions,
while all summands use the existing SAME depth-stage OWN center. -/
def originalWindowCost (stage start count : Nat) : Q' :=
  finSum (fun j => originalOwnBlockCost hw0 hw1 scale width hwidth stage (start+j)) count

/-- Literal existing dyadic unit-response drops, not a new completion. -/
def dyadicWindowCost (start count : Nat) : CReal :=
  csum (fun j => sub (Response (2*(start+j))) (Response (2*(start+j)+1))) count

/-- Exact SAME-state quotient pin for the finite unit-response sum. -/
theorem dyadic_window_pin (start count : Nat) :
    Quotient.mk crealSetoid (dyadicWindowCost hw0 hw1 scale width hwidth start count) =
      windowSignedCost hw0 hw1 Unit start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change RCadd (Quotient.mk crealSetoid (dyadicWindowCost hw0 hw1 scale width hwidth start count))
        (RCsub (Quotient.mk crealSetoid (Response (2*(start+count))))
          (Quotient.mk crealSetoid (Response (2*(start+count)+1)))) = _
      rw [ih, ← dyadicUnitResponse_pin, ← dyadicUnitResponse_pin, ← first_defect_pin]
      rfl

/-- Fixed-member finite sum of the already-constructed original source
limits. This is not uniform convergence across a growing square family. -/
theorem originalWindowCost_converges (start count : Nat) :
    ConvergesTo (fun stage => ofQ' (originalWindowCost hw0 hw1 scale width hwidth stage start count))
      (mul Norm (dyadicWindowCost hw0 hw1 scale width hwidth start count)) := by
  induction count with
  | zero =>
      refine ArctanTrigConvergesProof.convergesTo_of_equiv
        (convergesTo_const (ofQ' 0)) ?_
      exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.eqv_symm (Q'.mul_zero_eqv ((Norm).approx n)))
  | succ count ih =>
      have hsum := TrigAddCReal.convergesTo_add ih
        (originalOwnBlockCost_converges hw0 hw1 scale width hwidth (start+count))
      refine ArctanTrigConvergesProof.convergesTo_of_equiv
        (TrigAddCReal.convergesTo_congr_seq (s := fun stage => add
          (ofQ' (originalWindowCost hw0 hw1 scale width hwidth stage start count))
          (ofQ' (originalOwnBlockCost hw0 hw1 scale width hwidth stage (start+count))))
          (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) hsum) ?_
      exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.eqv_symm (Q'.mul_add_eqv ((Norm).approx n)
          ((dyadicWindowCost hw0 hw1 scale width hwidth start count).approx n)
          ((sub (Response (2*(start+count))) (Response (2*(start+count)+1))).approx n)))

/-- An actual eventual ORIGINAL aggregate estimate reaches the existing
dyadic macro response. No finite stationarity or useful floor is assumed;
only the existing pointwise original norm is canceled at the limit. -/
theorem original_window_budget_macro_ratio (u : Nat) (kappa : Q') (onset : Nat)
    (hbudget : ∀ stage, onset ≤ stage →
      2*originalWindowCost hw0 hw1 scale width hwidth stage u u ≤
        (1-kappa)*originalOwnBlockVariance hw0 hw1 scale width hwidth stage u) :
    leEv (mul (ofQ' kappa) (Response (2*u))) (Response (4*u)) := by
  have hlimit := BF4ExactSlabThermodynamicScalarRows.limit_le_of_eventual
    (convergesTo_mul_general (convergesTo_const (ofQ' 2))
      (originalWindowCost_converges hw0 hw1 scale width hwidth u u))
    (convergesTo_mul_general (convergesTo_const (ofQ' (1-kappa)))
      (originalOwnBlockVariance_converges hw0 hw1 scale width hwidth u))
    onset (fun stage hs epsilon he => by
      refine ⟨0, fun _ _ => ?_⟩
      exact Q'.le_trans' _ _ _ (hbudget stage hs)
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he)))
  have reorder (q : Q') (s : CReal) :
      Equiv (mul (ofQ' q) (mul Norm s)) (mul (mul (ofQ' q) s) Norm) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => q | 1 => (Norm).approx n | _ => s.approx n))
  have hcleared := (leEv_congr
    (reorder 2 (dyadicWindowCost hw0 hw1 scale width hwidth u u))
    (reorder (1-kappa) (Response (2*u)))).mp hlimit
  have hunit := leEv_cancel_mul_right_posEv
    ⟨starRatio w, starRatio_positive hw0 hw1,
      dyadicOriginalNorm_floor hw0 hw1 scale width hwidth⟩ hcleared
  have hrc : RCle (RCscale 2 (windowSignedCost hw0 hw1 Unit u u))
      (RCscale (1-kappa) (Resp Unit (2*u))) := by
    rw [← dyadic_window_pin, dyadicUnitResponse_pin, RCscale_mk, RCscale_mk]
    exact hunit
  have h := aggregate_window_macro_ratio hw0 hw1 Unit u kappa hrc
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin, RCscale_mk] at h
  exact h

end Original

#print axioms windowSignedCost
#print axioms response_window_cost_bound
#print axioms response_doubling_window_cost_bound
#print axioms aggregate_window_macro_ratio
#print axioms originalWindowCost
#print axioms dyadicWindowCost
#print axioms dyadic_window_pin
#print axioms originalWindowCost_converges
#print axioms original_window_budget_macro_ratio

end YMGap.Continuum.BF4WilsonAllNomeWindowSignedCost
