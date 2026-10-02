/-
# A filtered sufficient response bound for the EXISTING dyadic unit state

The positive mixed time/defect moments of the SAME completed operator give
  R(m) >= R(1) - (m-1)*(R(1)-R(2)),   m >= 1.
Only lags one and two enter the sufficient rational-floor consumer.  It
retains the first curvature contribution instead of replacing every later
slope by the lag-zero loss. The original unit state and normalization are
unchanged. No quantitative reserve or filtered budget is produced here,
and no changing-family/scaling or continuum survival claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4DyadicWilsonSquare (side)

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem add_sub_cancel (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem sub_sub (a b c : RC) :
    RCsub (RCsub a b) c = RCsub a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx j))))))

private theorem last_of_split {a b c : RC} (h : a = RCadd b c) :
    RCsub a b = c := by
  rw [h]
  refine Quotient.inductionOn₂ b c ?_
  exact fun B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => B.approx n | _ => C.approx n)))

private theorem first_of_split {a b c : RC} (h : a = RCadd b c) :
    RCsub a c = b := by
  rw [h]
  exact add_sub_cancel b c

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1

private theorem filtered_slope_pin (x : V) :
    RCsub (B x (T 1 x)) (B x (T 2 x)) = M x 1 1 := by
  have h := mixedMoment_split hw0 hw1 x 1 0
  change B x (T 1 x) = RCadd (B x (T 2 x)) (M x 1 1) at h
  exact last_of_split h

private theorem slope_after_one (x : V) : ∀ n : Nat,
    RCle (M x (n+1) 1) (M x 1 1)
  | 0 => RCle_refl _
  | n+1 => RCle_trans (mixedMoment_time_decreasing hw0 hw1 x (n+1) 1)
      (slope_after_one x n)

private theorem response_from_one (x : V) : ∀ n : Nat,
    RCle (RCsub (B x (T 1 x)) (RCscale (Q'.ofNat n) (M x 1 1)))
      (B x (T (n+1) x))
  | 0 => by
      change RCle (RCsub (B x (T 1 x)) (RCscale 0 _)) (B x (T 1 x))
      rw [scale_zero,sub_zero]
      exact RCle_refl _
  | n+1 => by
      have hsplit := mixedMoment_split hw0 hw1 x (n+1) 0
      change B x (T (n+1) x) = RCadd (B x (T (n+2) x)) (M x (n+1) 1) at hsplit
      have hupper : RCle (B x (T (n+1) x))
          (RCadd (B x (T (n+2) x)) (M x 1 1)) := by
        rw [hsplit]
        exact RCadd_le_add (RCle_refl _) (slope_after_one hw0 hw1 x n)
      have h := RCadd_le_add (RCle_trans (response_from_one x n) hupper)
        (RCle_refl (RCneg (M x 1 1)))
      change RCle
        (RCsub (RCsub (B x (T 1 x)) (RCscale (Q'.ofNat n) (M x 1 1))) (M x 1 1))
        (RCsub (RCadd (B x (T (n+2) x)) (M x 1 1)) (M x 1 1)) at h
      rw [sub_sub,← scale_nat_succ,add_sub_cancel] at h
      exact h

variable (scale : Nat) (hwidth : side scale < width)

attribute [local irreducible] dyadicUnitExcitation

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag

/-- The exact positive TD slope, and its exact lag-zero curvature split,
on the original constructed dyadic unit state. -/
theorem dyadicUnit_filtered_slope_pin :
    RCsub (B u (T 1 u)) (B u (T 2 u)) = M u 1 1 ∧
      RCsub (B u (T 1 u)) (B u (T 2 u)) = RCsub (M u 0 1) (M u 0 2) := by
  have hback : RCsub (M u 0 1) (M u 0 2) = M u 1 1 :=
    first_of_split (a := M u 0 1) (b := M u 1 1) (c := M u 0 2)
      (mixedMoment_split hw0 hw1 u 0 1)
  exact ⟨filtered_slope_pin hw0 hw1 u,
    (filtered_slope_pin hw0 hw1 u).trans hback.symm⟩

/-- SAME response at any integer lag >=1, retaining the first curvature
instead of using the larger lag-zero loss for every step. -/
theorem dyadicUnitResponse_filtered_lower (lag : Nat) (hlag : 1 ≤ lag) :
    leEv (sub (R 1)
      (mul (ofQ' (Q'.ofNat (lag-1))) (sub (R 1) (R 2)))) (R lag) := by
  have h := response_from_one hw0 hw1 u (lag-1)
  rw [← filtered_slope_pin hw0 hw1 u] at h
  rw [Nat.sub_add_cancel hlag] at h
  rw [dyadicUnitResponse_pin,dyadicUnitResponse_pin,dyadicUnitResponse_pin] at h
  exact h

private theorem neg_mono {A E : CReal} (h : leEv A E) : leEv (neg E) (neg A) := by
  intro epsilon hepsilon
  obtain ⟨N,hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.neg_le_neg_add (hN n hn)⟩

private theorem floor_minus_budget (A E : CReal) (reserve gamma : Q')
    (hA : leEv (ofQ' reserve) A) (hE : leEv E (ofQ' (reserve-gamma))) :
    leEv (ofQ' gamma) (sub A E) := by
  have h := leEv_add hA (neg_mono hE)
  have hp : Equiv (add (ofQ' reserve) (neg (ofQ' (reserve-gamma)))) (ofQ' gamma) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
      (by decide) (fun | 0 => reserve | _ => gamma))
  exact leEv_trans (leEv_of_equiv hp.symm) h

/-- A rational reserve and a filtered budget give an actual SAME-state
floor. These two quantitative inputs are NOT proved along any schedule. -/
theorem dyadicUnitResponse_filtered_floor (lag : Nat) (hlag : 1 ≤ lag)
    (reserve gamma : Q') (hreserve : leEv (ofQ' reserve) (R 1))
    (hbudget : leEv (mul (ofQ' (Q'.ofNat (lag-1))) (sub (R 1) (R 2)))
      (ofQ' (reserve-gamma))) : leEv (ofQ' gamma) (R lag) :=
  leEv_trans (floor_minus_budget (R 1) _ reserve gamma hreserve hbudget)
    (dyadicUnitResponse_filtered_lower hw0 hw1 scale hwidth lag hlag)

/-- A strictly positive rational floor implies nonzero ORIGINAL response,
not a nonzero changing-family or continuum limit. -/
theorem dyadicUnitResponse_filtered_ne_zero (lag : Nat) (hlag : 1 ≤ lag)
    (reserve gamma : Q') (hgamma : (0 : Q') < gamma)
    (hreserve : leEv (ofQ' reserve) (R 1))
    (hbudget : leEv (mul (ofQ' (Q'.ofNat (lag-1))) (sub (R 1) (R 2)))
      (ofQ' (reserve-gamma))) : ¬ Equiv (R lag) czero := by
  intro hz
  have h := leEv_trans
    (dyadicUnitResponse_filtered_floor hw0 hw1 scale hwidth lag hlag reserve gamma hreserve hbudget)
    (leEv_of_equiv hz)
  have hbad : gamma ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hepsilon
    obtain ⟨N,hN⟩ := h epsilon hepsilon
    exact hN N (Nat.le_refl N)
  have hzero : (0 : Q') < 0 := Q'.pos_of_lt_of_le hgamma hbad
  exact (by decide : ¬ (0 : Q') < 0) hzero

#print axioms dyadicUnit_filtered_slope_pin
#print axioms dyadicUnitResponse_filtered_lower
#print axioms dyadicUnitResponse_filtered_floor
#print axioms dyadicUnitResponse_filtered_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredSurvival
