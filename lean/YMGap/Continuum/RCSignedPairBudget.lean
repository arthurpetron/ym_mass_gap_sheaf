/-
A scalar signed-pair budget.  All form comparisons and mixed-error estimates
are explicit inputs; this file supplies only constructive rational/real order
algebra for their final combination.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RCSignedPairBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The two-sided quarter-error coefficient. -/
def quarter (d : Q') : Q' := HalfPow.half * (HalfPow.half * d)

/-- Exactly the rational ratio d/(2L), written as (d/2)/L so the
constructive reciprocal cancellation has a direct normal form. -/
def coefficient (d L : Q') (hL : (0 : Q') < L) : Q' :=
  Q'.divPos (HalfPow.half * d) L hL

theorem coefficient_nonnegative (d L : Q') (hL : (0 : Q') < L)
    (hd : (0 : Q') ≤ d) : (0 : Q') ≤ coefficient d L hL := by
  unfold coefficient Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg hd)
    (Q'.le_of_lt (Q'.recipPos_pos L hL))

theorem coefficient_mul_L (d L : Q') (hL : (0 : Q') < L) :
    coefficient d L hL * L ≈ HalfPow.half * d :=
  Q'.divPos_mul_eqv _ _ hL

/-- Order reversal on the actual real quotient. -/
theorem neg_mono {a b : RC} (h : RCle a b) : RCle (RCneg b) (RCneg a) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.neg_le_neg_add' (hN n hn)⟩

theorem scale_congr {s t : Q'} (h : s ≈ t) (a : RC) :
    RCscale s a = RCscale t a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right s t (A.approx n) h))

private theorem sub_mono {a a' b b' : RC}
    (ha : RCle a a') (hb : RCle b' b) :
    RCle (RCsub a b) (RCsub a' b') :=
  RCadd_le_add ha (neg_mono hb)

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem neg_add_same (a : RC) :
    RCsub (RCneg a) a = RCneg (RCadd a a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.neg (.var 0)) (.neg (.var 0)))
      (.neg (.add (.var 0) (.var 0))) (by decide)
      (fun _ => A.approx n)))

private theorem scale_double (q : Q') (a : RC) :
    RCadd (RCscale q a) (RCscale q a) = RCscale (q + q) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.add (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => q | _ => A.approx n)))

private theorem quarter_boundary (d L : Q') (hL : (0 : Q') < L) (S : RC) :
    RCsub (RCneg (RCscale (quarter d) S)) (RCscale (quarter d) S) =
      RCneg (RCscale (coefficient d L hL) (RCscale L S)) := by
  rw [neg_add_same, scale_double, RCscale_RCscale]
  have hq : quarter d + quarter d ≈ HalfPow.half * d :=
    ExpNeg.two_halves (HalfPow.half * d)
  rw [scale_congr hq S, scale_congr (Q'.eqv_symm (coefficient_mul_L d L hL)) S]

/-- If two signed corrections each cost at most a quarter of d*S, then
the positive reference contribution can be dropped and the full signed
term loses at most d/(2L) times the original energy E. -/
theorem signed_pair_lower (L d c : Q') (hL : (0 : Q') < L)
    (hd : (0 : Q') ≤ d) (hc : (0 : Q') ≤ c)
    (e0 a b S E t : RC)
    (he0 : RCnonneg e0)
    (ha : RCle (RCneg (RCscale (quarter d) S)) a)
    (hb : RCle b (RCscale (quarter d) S))
    (hE : RCle (RCscale L S) E)
    (ht : t = RCadd (RCscale c e0) (RCsub a b)) :
    RCle (RCneg (RCscale (coefficient d L hL) E)) t := by
  have hcoeff : (0 : Q') ≤ coefficient d L hL := coefficient_nonnegative d L hL hd
  have hscaled : RCle (RCscale (coefficient d L hL) (RCscale L S))
      (RCscale (coefficient d L hL) E) := RCscale_mono hcoeff hE
  have hbase : RCle (RCneg (RCscale (coefficient d L hL) E))
      (RCsub (RCneg (RCscale (quarter d) S)) (RCscale (quarter d) S)) := by
    rw [quarter_boundary d L hL S]
    exact neg_mono hscaled
  have herror := sub_mono ha hb
  have hpositive : RCle RCzero (RCscale c e0) := by
    rw [← RCscale_RCzero c]
    exact RCscale_mono hc he0
  rw [ht]
  exact RCle_trans hbase (RCle_trans herror
    (by simpa only [zero_add] using RCadd_le_add hpositive (RCle_refl (RCsub a b))))

#print axioms quarter
#print axioms coefficient
#print axioms coefficient_nonnegative
#print axioms coefficient_mul_L
#print axioms neg_mono
#print axioms scale_congr
#print axioms signed_pair_lower

end YMGap.Continuum.RCSignedPairBudget
