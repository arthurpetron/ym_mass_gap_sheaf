/-
# A retained macro ratio pays the SAME later filtered cost

Positive mixed moments of the existing original completed time map give
  s*(C(L+s)-C(L+s+1)) <= C(L)-C(L+s),  s>=1.
Keeping the last response in this telescoping budget, a supplied original
macro ratio kappa*C(L)<=C(L+s), kappa>=0, gives the cleared implication
  kappa*s*(C(L+s)-C(L+s+1)) <= (1-kappa)*C(L+s).

This connects two existing alternative analytic targets on the SAME
state, carrier and operator. It constructs neither a useful macro ratio
nor a justified changing family, and asserts no physical or continuum
closure. No real division, normalization lower floor or new frontier
structure is used. The dyadic unit specialization uses literal integer
lags 2*t and 4*t; it does not prescribe a physical-time convention or
reverse a completed limit into a finite original estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
  (mixedMoment_time_budget mixedMoment_time_decreasing)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitResponse dyadicUnitResponse_pin)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun
        | 0 => A.approx n
        | _ => B.approx n)))

private theorem add_sub_last (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun
        | 0 => A.approx n
        | _ => B.approx n)))

private theorem scale_sub (q : Q') (a b : RC) :
    RCscale q (RCsub a b) = RCsub (RCscale q a) (RCscale q b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun
        | 0 => q
        | 1 => A.approx n
        | _ => B.approx n)))

private theorem sub_scaled_self (q : Q') (a : RC) :
    RCsub a (RCscale q a) = RCscale (1-q) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv (A.approx n))
        (Q'.neg_mul_eqv q (A.approx n))))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation:max "C" x:arg lag:arg => B x (T lag x)

attribute [local irreducible] completedInner completedTime dyadicUnitResponse dyadicUnitExcitation

private theorem first_defect_pin (x : V) (lag : Nat) :
    mixedMoment hw0 hw1 x lag 1 = RCsub (C x lag) (C x (lag+1)) := by
  have h := mixedMoment_split hw0 hw1 x lag 0
  change C x lag = RCadd (C x (lag+1)) (mixedMoment hw0 hw1 x lag 1) at h
  have hc := congrArg (fun z => RCsub z (C x (lag+1))) h
  change RCsub (C x lag) (C x (lag+1)) =
    RCsub (RCadd (C x (lag+1)) (mixedMoment hw0 hw1 x lag 1)) (C x (lag+1)) at hc
  rw [add_sub_first] at hc
  exact hc.symm

/-- The last response is retained, rather than discarded from the time
budget. This holds for every state of the original all-nome completion. -/
theorem retained_time_budget (x : V) (L s : Nat) (hs : 1 ≤ s) :
    RCle (RCscale (Q'.ofNat s) (RCsub (C x (L+s)) (C x (L+s+1))))
      (RCsub (C x L) (C x (L+s))) := by
  have hsucc : (s-1)+1=s := by omega
  have hend : L+(s-1)+1=L+s := by omega
  have hb := mixedMoment_time_budget hw0 hw1 x L 0 (s-1)
  rw [hsucc, hend] at hb
  change RCle
    (RCadd (RCscale (Q'.ofNat s) (mixedMoment hw0 hw1 x (L+(s-1)) 1))
      (C x (L+s))) (C x L) at hb
  have hm := mixedMoment_time_decreasing hw0 hw1 x (L+(s-1)) 1
  rw [hend] at hm
  have h := RCle_trans
    (RCadd_le_add (RCscale_mono (Q'.ofNat_nonneg s) hm) (RCle_refl (C x (L+s)))) hb
  rw [first_defect_pin] at h
  have hc := RCadd_le_add h (RCle_refl (RCneg (C x (L+s))))
  change RCle
    (RCsub (RCadd (RCscale (Q'.ofNat s) (RCsub (C x (L+s)) (C x (L+s+1))))
      (C x (L+s))) (C x (L+s))) (RCsub (C x L) (C x (L+s))) at hc
  rwa [add_sub_last] at hc

/-- Conditional implication between the existing macro-ratio and filtered
cost targets. The ratio is NOT produced by positivity or smoothing. -/
theorem macro_to_filtered_budget (x : V) (L s : Nat) (hs : 1 ≤ s)
    (kappa : Q') (hk : (0 : Q') ≤ kappa)
    (hratio : RCle (RCscale kappa (C x L)) (C x (L+s))) :
    RCle (RCscale (kappa*Q'.ofNat s) (RCsub (C x (L+s)) (C x (L+s+1))))
      (RCscale (1-kappa) (C x (L+s))) := by
  have hb := RCscale_mono hk (retained_time_budget hw0 hw1 x L s hs)
  rw [RCscale_RCscale] at hb
  rw [scale_sub kappa (C x L) (C x (L+s))] at hb
  have hr := RCadd_le_add hratio (RCle_refl (RCneg (RCscale kappa (C x (L+s)))))
  change RCle (RCsub (RCscale kappa (C x L)) (RCscale kappa (C x (L+s))))
    (RCsub (C x (L+s)) (RCscale kappa (C x (L+s)))) at hr
  rw [sub_scaled_self] at hr
  exact RCle_trans hb hr

/-- Literal existing unit response. The later drop is at lag 4*t, so it
matches the block-cost limit with block parameter 2*t, not t. -/
theorem dyadicUnit_macro_filtered_budget (scale width : Nat)
    (hwidth : side scale < width) (t : Nat) (ht : 1 ≤ 2*t)
    (kappa : Q') (hk : (0 : Q') ≤ kappa)
    (hratio : leEv (mul (ofQ' kappa)
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*t)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (4*t))) :
    leEv (mul (ofQ' (kappa*Q'.ofNat (2*t)))
      (sub (dyadicUnitResponse hw0 hw1 scale width hwidth (4*t))
        (dyadicUnitResponse hw0 hw1 scale width hwidth (4*t+1))))
      (mul (ofQ' (1-kappa)) (dyadicUnitResponse hw0 hw1 scale width hwidth (4*t))) := by
  let u : Completion hw0 hw1 width :=
    Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
  have hd : 2*t+2*t=4*t := by omega
  have hr : RCle (RCscale kappa (C u (2*t))) (C u (2*t+2*t)) := by
    rw [hd]
    simp only [u, dyadicUnitResponse_pin]
    exact hratio
  have h := macro_to_filtered_budget hw0 hw1 u (2*t) (2*t) ht kappa hk hr
  rw [hd] at h
  simp only [u, dyadicUnitResponse_pin] at h
  exact h

end YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost

#print axioms YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost.retained_time_budget
#print axioms YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost.macro_to_filtered_budget
#print axioms YMGap.Continuum.BF4WilsonAllNomeMacroRatioFilteredCost.dyadicUnit_macro_filtered_budget
