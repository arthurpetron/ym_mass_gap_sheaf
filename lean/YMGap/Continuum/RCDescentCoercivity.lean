/-
# Scalar geometric-descent coercivity

This is the exact scalar consumer of finite telescoping, a positive baseline,
and an explicit geometric error closure. No operator or physical premise is
introduced here.
-/

import YMGap.Continuum.RCGeometricErrorClosure
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.RCDescentCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem sub_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem scale_sub_add_cancel (b : Q') (a c : RC) :
    RCadd (RCscale b (RCsub a c)) (RCscale b c) = RCscale b a := by
  refine Quotient.inductionOn₂ a c ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => b | 1 => A.approx n | _ => C.approx n)))

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem neg_zero : RCneg RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv (-(0:Q')) 0)))

private theorem sub_le_self (a c : RC) (hc : RCnonneg c) :
    RCle (RCsub a c) a := by
  have h := RCadd_le_add (RCle_refl a) (RCSignedPairBudget.neg_mono hc)
  rw [neg_zero, add_zero] at h
  exact h

/-- The baseline only controls the vanishing tail. The final lower
coefficient `b` is independent of the baseline `alpha`. -/
theorem descent_coercivity (V E : Nat → RC) (alpha b q : Q')
    (hAlpha : (0 : Q') < alpha) (hB : (0 : Q') ≤ b)
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hEn : ∀ n, RCnonneg (E n))
    (hdecay : ∀ n, RCle (E n) (RCscale (q ^ n) (E 0)))
    (hfloor : ∀ n, RCle (RCscale alpha (V n)) (E n))
    (hstep : ∀ n, RCle (RCscale b (RCsub (V n) (V (n+1))))
      (RCsub (E n) (E (n+1)))) :
    RCle (RCscale b (V 0)) (E 0) := by
  let r := Q'.divPos 1 alpha hAlpha
  have hr : (0 : Q') ≤ r :=
    Q'.le_of_lt (Q'.divPos_pos 1 alpha hAlpha (by decide))
  have hra : (r * alpha).eqv 1 := Q'.divPos_mul_eqv 1 alpha hAlpha
  have hbr : (0 : Q') ≤ b*r := Q'.mul_nonneg _ _ hB hr
  have hfinite : ∀ n,
      RCle (RCscale b (RCsub (V 0) (V n))) (RCsub (E 0) (E n)) := by
    intro n
    induction n with
    | zero =>
        rw [sub_self, RCscale_RCzero, sub_self]
        exact RCle_refl RCzero
    | succ n ih =>
        have h := RCadd_le_add ih (hstep n)
        rw [← RCscale_RCadd, sub_telescope, sub_telescope] at h
        exact h
  have htail (n : Nat) :
      RCle (RCscale b (V n))
        (RCscale (q ^ n) (RCscale (b*r) (E 0))) := by
    have hf := RCscale_mono hr (hfloor n)
    rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hra (V n),
      RCscale_one] at hf
    have hb1 := RCscale_mono hB hf
    rw [RCscale_RCscale] at hb1
    have hb2 := RCscale_mono hbr (hdecay n)
    rw [RCscale_RCscale] at hb2
    have hcomm : RCscale ((b*r)*(q^n)) (E 0) =
        RCscale (q^n) (RCscale (b*r) (E 0)) := by
      rw [RCscale_RCscale]
      exact RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv _ _) (E 0)
    rw [hcomm] at hb2
    exact RCle_trans hb1 hb2
  apply RCGeometricErrorClosure.le_of_geometric_error q hq0 hq1
    (RCscale b (V 0)) (E 0) (RCscale (b*r) (E 0))
  intro n
  have hsum := RCadd_le_add (hfinite n) (htail n)
  rw [scale_sub_add_cancel] at hsum
  have hrest := RCadd_le_add (sub_le_self (E 0) (E n) (hEn n))
    (RCle_refl (RCscale (q^n) (RCscale (b*r) (E 0))))
  exact RCle_trans hsum hrest

#print axioms descent_coercivity

end YMGap.Continuum.RCDescentCoercivity
