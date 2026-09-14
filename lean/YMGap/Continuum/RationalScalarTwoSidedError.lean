/-
# Signed rational scaling of constructive real error bounds

Two-sided error e is carried through multiplication by ANY rational c
with error |c|e, and through addition with summed errors. The final
closure lemma removes arbitrarily small rational order errors. These
are order facts, not supplied analytic or spectral hypotheses.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence

namespace YMGap.Continuum.RationalScalarTwoSidedError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem scale_error (c e : Q') (he : (0 : Q')≤e) (a b : RC)
    (hab : RCle a (RCadd b (rat e))) (hba : RCle b (RCadd a (rat e))) :
    RCle (RCscale c a) (RCadd (RCscale c b) (rat (Q'.abs c*e))) := by
  revert hab hba
  refine Quotient.inductionOn₂ a b ?_
  intro A B hab hba epsilon hepsilon
  let d := mulModulus (Q'.abs c) epsilon (Q'.abs_nonneg c) hepsilon
  obtain ⟨N,hN⟩ := hab d.1 d.2.1
  obtain ⟨M,hM⟩ := hba d.1 d.2.1
  refine ⟨max N M,fun n hn => ?_⟩
  have h1 := Q'.le_trans' _ _ _ (hN n (Nat.le_trans (Nat.le_max_left _ _) hn))
    (Q'.le_of_eqv (Q'.add_assoc_eqv (B.approx n) e d.1))
  have h2 := Q'.le_trans' _ _ _ (hM n (Nat.le_trans (Nat.le_max_right _ _) hn))
    (Q'.le_of_eqv (Q'.add_assoc_eqv (A.approx n) e d.1))
  have hm := Q'.mul_close_of_two_sided c (A.approx n) (B.approx n) (Q'.abs c) (e+d.1)
    (Q'.abs_nonneg c) (Q'.zero_le_add _ _ he (Q'.le_of_lt d.2.1))
    (ExpNeg.neg_abs_le c) (Q'.le_abs_self c) h1 h2
  have hx : Q'.eqv (c*B.approx n+Q'.abs c*(e+d.1))
      ((c*B.approx n+Q'.abs c*e)+Q'.abs c*d.1) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv _ _ _))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _ hm (Q'.le_trans' _ _ _ (Q'.le_of_eqv hx)
    (Q'.add_le_add_left _ _ _ d.2.2))

theorem add_error_identity (a b : RC) (e f : Q') :
    RCadd (RCadd a (rat e)) (RCadd b (rat f))=RCadd (RCadd a b) (rat (e+f)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_interchange (A.approx n) e (B.approx n) f))

theorem add_error (a b A B : RC) (e f : Q')
    (ha : RCle a (RCadd A (rat e))) (hb : RCle b (RCadd B (rat f))) :
    RCle (RCadd a b) (RCadd (RCadd A B) (rat (e+f))) := by
  have h := RCadd_le_add ha hb
  rw [add_error_identity] at h
  exact h

/-- No rate or witness is extracted from the propositional order relation. -/
theorem le_of_all_errors (a b : RC)
    (h : ∀ e : Q',(0 : Q')<e → RCle a (RCadd b (rat e))) : RCle a b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h epsilon hepsilon
  let d := epsilon*HalfPow.half
  have hd : (0 : Q')<d := Q'.mul_pos hepsilon (Q'.invSucc_pos 1)
  obtain ⟨N,hN⟩ := h d hd d hd
  refine ⟨N,fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (hN n hn)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (half_add_half epsilon))))

end YMGap.Continuum.RationalScalarTwoSidedError

#print axioms YMGap.Continuum.RationalScalarTwoSidedError.scale_error
#print axioms YMGap.Continuum.RationalScalarTwoSidedError.add_error_identity
#print axioms YMGap.Continuum.RationalScalarTwoSidedError.add_error
#print axioms YMGap.Continuum.RationalScalarTwoSidedError.le_of_all_errors
