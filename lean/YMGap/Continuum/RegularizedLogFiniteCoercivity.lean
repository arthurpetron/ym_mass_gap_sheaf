/-
# Finite coercivity of the original regularized entropy polynomials

These are inequalities for the literal partial sums p_N, before any logarithm
identification or limit. An exponential envelope h <= 3*r^k pays the explicit
finite error 3*k/(N+1). Neither h nor p_N(h) is divided out, so zero density
and zero exponent are included. The power estimate also includes r=0.

This scalar producer can be integrated against an actual positive original
action. It supplies no interacting, conditional-entropy, or spectral estimate.
-/

import YMGap.Continuum.RegularizedLogPolynomialProductDefect
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.RegularizedLogFiniteCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.RegularizedLogPolynomialProductDefect (product_defect_bounds)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  tc (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem transport {a b c d : Q'} (ha : a ≈ b) (hc : c ≈ d)
    (h : b ≤ d) : a ≤ c :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hc))

private theorem nat_nonnegative (k : Nat) : (0 : Q') ≤ Q'.ofNat k := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg k

private theorem weighted_term (a b : Q') (ha0 : (0 : Q') ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ 1) (n : Nat) : a*term b n ≤ b*term a n := by
  have hb0 := Q'.le_trans' _ _ _ ha0 hab
  have hcomp : 1-b ≤ 1-a := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hab)
  have hpow := CRealLog.pow_le_pow_base (1-b) (1-a)
    (Q'.sub_nonneg_of_le hb1) hcomp (n+1)
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc n*(a*b)) hpow
    (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n) (Q'.mul_nonneg _ _ ha0 hb0))
  have left : a*term b n ≈ (Q'.invSucc n*(a*b))*(1-b)^(n+1) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 1))) (.var 3))
      (by decide) (fun | 0 => a | 1 => b | 2 => Q'.invSucc n | _ => (1-b)^(n+1))
  have right : b*term a n ≈ (Q'.invSucc n*(a*b))*(1-a)^(n+1) :=
    poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 3))))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 1))) (.var 3))
      (by decide) (fun | 0 => a | 1 => b | 2 => Q'.invSucc n | _ => (1-a)^(n+1))
  exact transport left right hp

/-- Monotonicity with both weights retained; no division by either input. -/
theorem weighted_monotone (a b : Q') (ha0 : (0 : Q') ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ 1) (N : Nat) :
    a*partialSum b N ≤ b*partialSum a N := by
  induction N with
  | zero => exact transport (Q'.mul_zero_eqv a) (Q'.mul_zero_eqv b) (Q'.le_refl' 0)
  | succ N ih =>
      exact transport (Q'.mul_add_eqv _ _ _) (Q'.mul_add_eqv _ _ _)
        (Q'.add_le_add ih (weighted_term a b ha0 hab hb1 N))

private theorem first_term_lower (r : Q') (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (N : Nat) (hN : 1 ≤ N) : r*(1-r) ≤ partialSum r N := by
  have hpin : partialSum r 1 ≈ r*(1-r) := by
    change (0 : Q')+1*(r*((1-r)*1)) ≈ r*(1-r)
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.mul (.const 1) (.mul (.var 0)
        (.mul (.add (.const 1) (.neg (.var 0))) (.const 1)))))
      (.mul (.var 0) (.add (.const 1) (.neg (.var 0)))) (by decide) (fun _ => r)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) (partial_mono r hr0 hr1 hN)

/-- A finite power lower bound. The error is explicit and independent of r. -/
theorem power_lower (r : Q') (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (k N : Nat) (hN : 1 ≤ N) :
    (r^k)*(Q'.ofNat k*(1-r)) ≤ partialSum (r^k) N+Q'.ofNat k*Q'.invSucc N := by
  induction k with
  | zero =>
      have hl : (1 : Q')*(0*(1-r)) ≈ 0 :=
        poly_identity_of_normal_eq
          (.mul (.const 1) (.mul (.const 0) (.add (.const 1) (.neg (.var 0)))))
          (.const 0) (by decide) (fun _ => r)
      have hu : partialSum 1 N+(0 : Q')*Q'.invSucc N ≈ 0 :=
        tc (Q'.add_eqv_congr' (partial_one N) (Q'.zero_mul_eqv _)) (by decide)
      exact transport hl hu (Q'.le_refl' 0)
  | succ k ih =>
      have hp0 := Q'.pow_nonneg r hr0 k
      have hp1 := HKPos.pow_le_one hr0 hr1 k
      have hfirst := first_term_lower r hr0 hr1 N hN
      have hsum := Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left _ _ r ih hr0)
        (Q'.mul_le_mul_of_nonneg_left _ _ (r^k) hfirst hp0)
      have hk := Q'.ofNat_add_eqv k 1
      have hl : (r^(k+1))*(Q'.ofNat (k+1)*(1-r)) ≈
          r*((r^k)*(Q'.ofNat k*(1-r)))+(r^k)*(r*(1-r)) := by
        change (r*(r^k))*(Q'.ofNat (k+1)*(1-r)) ≈ _
        exact tc (mc (Q'.eqv_refl _) (mc hk (Q'.eqv_refl _)))
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 1))
              (.mul (.add (.var 2) (.const 1)) (.var 3)))
            (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
              (.mul (.var 1) (.mul (.var 0) (.var 3))))
            (by decide) (fun | 0 => r | 1 => r^k | 2 => Q'.ofNat k | _ => 1-r))
      have hu : r*(partialSum (r^k) N+Q'.ofNat k*Q'.invSucc N)+(r^k)*partialSum r N ≈
          ((r^k)*partialSum r N+r*partialSum (r^k) N)+r*(Q'.ofNat k*Q'.invSucc N) :=
        poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
          (.add (.add (.var 3) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => r | 1 => partialSum (r^k) N | 2 => Q'.ofNat k*Q'.invSucc N | _ => (r^k)*partialSum r N)
      have hdef := CReal.leAddOfSubLe (product_defect_bounds r (r^k) hr0 hr1 hp0 hp1 N).2
      have herr : r*(Q'.ofNat k*Q'.invSucc N) ≤ Q'.ofNat k*Q'.invSucc N :=
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hr1
          (Q'.mul_nonneg _ _ (nat_nonnegative k) (Q'.invSucc_nonneg N)))
          (Q'.le_of_eqv (Q'.one_mul_eqv _))
      have hend : partialSum (r^(k+1)) N+Q'.invSucc N+Q'.ofNat k*Q'.invSucc N ≈
          partialSum (r^(k+1)) N+Q'.ofNat (k+1)*Q'.invSucc N :=
        tc (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
          (.add (.var 0) (.mul (.add (.var 2) (.const 1)) (.var 1)))
          (by decide) (fun | 0 => partialSum (r^(k+1)) N | 1 => Q'.invSucc N | _ => Q'.ofNat k))
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (mc (Q'.eqv_symm hk) (Q'.eqv_refl _)))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
        (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hu)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hdef herr) (Q'.le_of_eqv hend))))

/-- The rational reciprocal used to retain the envelope constant exactly. -/
def third : Q' := Q'.mkPos 1 3 (by decide)

private theorem triple_third (x : Q') : (3 : Q')*(x*third) ≈ x :=
  tc (poly_identity_of_normal_eq
    (.mul (.const 3) (.mul (.var 0) (.var 1)))
    (.mul (.mul (.const 3) (.var 1)) (.var 0)) (by decide) (fun | 0 => x | _ => third))
    (tc (mc (by decide : (3 : Q')*third ≈ 1) (Q'.eqv_refl x)) (Q'.one_mul_eqv x))

private theorem shrink_power (a b c e : Q') (ha0 : (0 : Q') ≤ a)
    (hab : a ≤ b) (hb0 : (0 : Q') < b) (hb1 : b ≤ 1) (he0 : (0 : Q') ≤ e)
    (N : Nat) (h : b*c ≤ partialSum b N+e) : a*c ≤ partialSum a N+e := by
  have hh := Q'.mul_le_mul_of_nonneg_left _ _ a h ha0
  have hm := weighted_monotone a b ha0 hab hb1 N
  have he := Q'.mul_le_mul_of_nonneg_right _ _ e hab he0
  have hl : b*(a*c) ≈ a*(b*c) :=
    poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => a | 1 => b | _ => c)
  have hf : b*(a*c) ≤ b*(partialSum a N+e) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hh (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.add_le_add hm he) (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _)))))
  exact Q'.le_of_mul_le_mul_left hf hb0

/-- Finite entropy coercivity from the actual rational envelope. Zero h and
zero k are allowed; only r is canceled, through its positive kth power. -/
theorem envelope_coercivity (h : Q') (hh0 : (0 : Q') ≤ h) (hh1 : h ≤ 1)
    (r : Q') (hr0 : (0 : Q') < r) (hr1 : r ≤ 1) (k N : Nat) (hN : 1 ≤ N)
    (henvelope : h ≤ 3*(r^k)) :
    h*(Q'.ofNat k*(1-r)) ≤ partialSum h N+3*h*partialSum third N+
      (3*Q'.ofNat k)*Q'.invSucc N := by
  let a : Q' := h*third
  have ha0 : (0 : Q') ≤ a := Q'.mul_nonneg _ _ hh0 (by decide : (0 : Q') ≤ third)
  have hab : a ≤ r^k := by
    have he := Q'.mul_le_mul_of_nonneg_right _ _ third henvelope (by decide)
    have hp : (3*(r^k))*third ≈ r^k :=
      tc (Q'.mul_assoc_eqv 3 (r^k) third) (triple_third (r^k))
    exact Q'.le_trans' _ _ _ he (Q'.le_of_eqv hp)
  have he0 := Q'.mul_nonneg _ _ (nat_nonnegative k) (Q'.invSucc_nonneg N)
  have hs := shrink_power a (r^k) (Q'.ofNat k*(1-r)) (Q'.ofNat k*Q'.invSucc N)
    ha0 hab (HKPos.pow_pos hr0 k) (HKPos.pow_le_one (Q'.le_of_lt hr0) hr1 k) he0 N
    (power_lower r (Q'.le_of_lt hr0) hr1 k N hN)
  have hs3 := Q'.mul_le_mul_of_nonneg_left _ _ (3 : Q') hs (by decide)
  have hl : h*(Q'.ofNat k*(1-r)) ≈ 3*(a*(Q'.ofNat k*(1-r))) :=
    Q'.eqv_symm (tc (Q'.eqv_symm (Q'.mul_assoc_eqv 3 a _))
      (mc (triple_third h) (Q'.eqv_refl _)))
  have hd := (product_defect_bounds h third hh0 hh1 (by decide) (by decide) N).1
  have ha : partialSum a N ≤ third*partialSum h N+h*partialSum third N :=
    Q'.le_of_sub_nonneg hd
  have ha3 := Q'.mul_le_mul_of_nonneg_left _ _ (3 : Q') ha (by decide)
  have hpin : 3*(third*partialSum h N+h*partialSum third N) ≈
      partialSum h N+3*h*partialSum third N := by
    have ht : (3 : Q')*(third*partialSum h N) ≈ partialSum h N :=
      tc (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (tc (mc (by decide : (3 : Q')*third ≈ 1) (Q'.eqv_refl _)) (Q'.one_mul_eqv _))
    exact tc (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' ht (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  have herr : 3*(Q'.ofNat k*Q'.invSucc N) ≈ (3*Q'.ofNat k)*Q'.invSucc N :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hs3 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (Q'.le_trans' _ _ _ ha3 (Q'.le_of_eqv hpin)))
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) herr)))))

end YMGap.Continuum.RegularizedLogFiniteCoercivity

#print axioms YMGap.Continuum.RegularizedLogFiniteCoercivity.weighted_monotone
#print axioms YMGap.Continuum.RegularizedLogFiniteCoercivity.power_lower
#print axioms YMGap.Continuum.RegularizedLogFiniteCoercivity.third
#print axioms YMGap.Continuum.RegularizedLogFiniteCoercivity.envelope_coercivity
