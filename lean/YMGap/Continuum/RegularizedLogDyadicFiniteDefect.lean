/-
# Uniform finite dyadic reduction for the original regularized polynomials

For every cutoff N and every dyadic exponent k, the finite scale defect is
between zero and 2/(N+1). Combining a dyadic scale with any m in [0,1]
costs at most 3/(N+1), independently of k. The half-step recurrence uses
the actual finite product defect; no logarithm law or division by the input
is assumed. The zero input, zero cutoff and zero exponent are retained.

These are finite scalar identities and inequalities. The computation of a
binary reduction and its limiting logarithm interpretation are consumers,
not hypotheses or conclusions of this module.
-/

import YMGap.Continuum.RegularizedLogPolynomialProductDefect

namespace YMGap.Constructive.Q'.eqv

private theorem trans {a b c : Q'} (h : a.eqv b) (k : b.eqv c) : a.eqv c :=
  Q'.eqv_trans _ _ _ h k

private theorem symm {a b : Q'} (h : a.eqv b) : b.eqv a := Q'.eqv_symm h

end YMGap.Constructive.Q'.eqv

namespace YMGap.Continuum.RegularizedLogDyadicFiniteDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.RegularizedLogPolynomialProductDefect (product_defect_bounds)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  q_add_congr h (Q'.neg_eqv_congr _ _ k)

/-- Congruence for the literal finite partial sums, before any limit or
range-reduction interpretation. -/
theorem partial_congr {a b : Q'} (h : a ≈ b) : ∀ N,
    partialSum a N ≈ partialSum b N
  | 0 => Q'.eqv_refl 0
  | N+1 => q_add_congr (partial_congr h N)
      (mc (Q'.eqv_refl _) (mc h
        (BernsteinSequenceWrap.pow_eqv_congr (sc (Q'.eqv_refl 1) h) (N+1))))

/-- The actual finite scale defect, using the literal rational half power. -/
def dyadicDefect (k N : Nat) : Q' :=
  half^k*Q'.ofNat k*(2*partialSum half N)-partialSum (half^k) N

private theorem half_twice (p : Q') : half*(2*p) ≈ p :=
  (Q'.mul_assoc_eqv half 2 p).symm.trans
    ((mc (by decide : half*2 ≈ 1) (Q'.eqv_refl p)).trans (Q'.one_mul_eqv p))

/-- Exact recurrence: only the already computed finite product defect is
added at each halving. It is valid also at N=0 and k=0. -/
theorem dyadic_recurrence (k N : Nat) :
    dyadicDefect (k+1) N ≈ half*dyadicDefect k N+
      ((half^k)*partialSum half N+half*partialSum (half^k) N-
        partialSum (half*(half^k)) N) := by
  have hk : Q'.ofNat (k+1) ≈ Q'.ofNat k+1 := Q'.ofNat_add_eqv k 1
  have hleft : dyadicDefect (k+1) N ≈
      (half*(half^k)*Q'.ofNat k*(2*partialSum half N)-
        partialSum (half*(half^k)) N)+(half^k)*(half*(2*partialSum half N)) := by
    change (half*(half^k)*Q'.ofNat (k+1)*(2*partialSum half N)-
      partialSum (half*(half^k)) N) ≈ _
    refine (sc (mc (mc (Q'.eqv_refl _) hk) (Q'.eqv_refl _)) (Q'.eqv_refl _)).trans ?_
    exact poly_identity_of_normal_eq
      (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.add (.var 2) (.const 1)))
          (.mul (.const 2) (.var 3))) (.neg (.var 4)))
      (.add (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.const 2) (.var 3))) (.neg (.var 4)))
        (.mul (.var 1) (.mul (.var 0) (.mul (.const 2) (.var 3)))))
      (by decide) (fun | 0 => half | 1 => half^k | 2 => Q'.ofNat k | 3 => partialSum half N | _ => partialSum (half*(half^k)) N)
  have hright : half*dyadicDefect k N+
      ((half^k)*partialSum half N+half*partialSum (half^k) N-
        partialSum (half*(half^k)) N) ≈
      (half*(half^k)*Q'.ofNat k*(2*partialSum half N)-
        partialSum (half*(half^k)) N)+(half^k)*partialSum half N := by
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 2))
          (.mul (.const 2) (.var 3))) (.neg (.var 4))))
        (.add (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4))) (.neg (.var 5))))
      (.add (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.const 2) (.var 3))) (.neg (.var 5))) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => half | 1 => half^k | 2 => Q'.ofNat k | 3 => partialSum half N | 4 => partialSum (half^k) N | _ => partialSum (half*(half^k)) N)
  exact hleft.trans ((q_add_congr (Q'.eqv_refl _)
    (mc (Q'.eqv_refl _) (half_twice (partialSum half N)))).trans hright.symm)

private theorem dyadic_zero (N : Nat) : dyadicDefect 0 N ≈ 0 :=
  (sc (Q'.eqv_refl ((1 : Q')*0*(2*partialSum half N))) (partial_one N)).trans
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 1) (.const 0)) (.mul (.const 2) (.var 0))) (.neg (.const 0)))
      (.const 0) (by decide) (fun _ => partialSum half N))

private theorem two_inv_nonnegative (N : Nat) : (0 : Q') ≤ 2*Q'.invSucc N :=
  Q'.mul_nonneg _ _ (by decide) (Q'.invSucc_nonneg N)

/-- Uniform finite dyadic error, with no cost growing in the exponent. -/
theorem dyadic_defect_bounds (k N : Nat) :
    (0 : Q') ≤ half^k*Q'.ofNat k*(2*partialSum half N)-partialSum (half^k) N ∧
      half^k*Q'.ofNat k*(2*partialSum half N)-partialSum (half^k) N ≤ 2*Q'.invSucc N := by
  change (0 : Q') ≤ dyadicDefect k N ∧ dyadicDefect k N ≤ 2*Q'.invSucc N
  induction k with
  | zero => exact ⟨Q'.ge_of_eqv (dyadic_zero N),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (dyadic_zero N)) (two_inv_nonnegative N)⟩
  | succ k ih =>
      have hp0 := Q'.pow_nonneg half half_nonneg k
      have hp1 := HKPos.pow_le_one half_nonneg (by decide : half ≤ (1 : Q')) k
      have hd := product_defect_bounds half (half^k) half_nonneg (by decide) hp0 hp1 N
      have he := dyadic_recurrence k N
      have hlo := Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ half_nonneg ih.1) hd.1
      have hup := Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left _ _ half ih.2 half_nonneg) hd.2
      have hcap : half*(2*Q'.invSucc N)+Q'.invSucc N ≈ 2*Q'.invSucc N :=
        (q_add_congr (half_twice (Q'.invSucc N)) (Q'.eqv_refl _)).trans
          (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
            (.mul (.const 2) (.var 0)) (by decide) (fun _ => Q'.invSucc N))
      exact ⟨Q'.le_trans' _ _ _ hlo (Q'.ge_of_eqv he),
        Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
          (Q'.le_trans' _ _ _ hup (Q'.le_of_eqv hcap))⟩

private theorem mixed_identity (m : Q') (k N : Nat) :
    ((half^k)*m)*(Q'.ofNat k*(2*partialSum half N))+
      (half^k)*partialSum m N-partialSum ((half^k)*m) N ≈
    m*dyadicDefect k N+
      (m*partialSum (half^k) N+(half^k)*partialSum m N-partialSum ((half^k)*m) N) := by
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.mul (.const 2) (.var 3))))
      (.mul (.var 0) (.var 4))) (.neg (.var 6)))
    (.add (.mul (.var 1) (.add (.mul (.mul (.var 0) (.var 2))
        (.mul (.const 2) (.var 3))) (.neg (.var 5))))
      (.add (.add (.mul (.var 1) (.var 5)) (.mul (.var 0) (.var 4))) (.neg (.var 6))))
    (by decide) (fun | 0 => half^k | 1 => m | 2 => Q'.ofNat k | 3 => partialSum half N | 4 => partialSum m N | 5 => partialSum (half^k) N | _ => partialSum ((half^k)*m) N)

/-- Uniform finite mixed reduction. The mantissa may be anywhere in [0,1],
including zero; no positive lower bound or scale-log identity is required. -/
theorem mixed_defect_bounds (m : Q') (hm0 : (0 : Q') ≤ m) (hm1 : m ≤ 1)
    (k N : Nat) :
    (0 : Q') ≤ ((half^k)*m)*(Q'.ofNat k*(2*partialSum half N))+
      (half^k)*partialSum m N-partialSum ((half^k)*m) N ∧
    ((half^k)*m)*(Q'.ofNat k*(2*partialSum half N))+
      (half^k)*partialSum m N-partialSum ((half^k)*m) N ≤ 3*Q'.invSucc N := by
  have hp0 := Q'.pow_nonneg half half_nonneg k
  have hp1 := HKPos.pow_le_one half_nonneg (by decide : half ≤ (1 : Q')) k
  have hd := product_defect_bounds (half^k) m hp0 hp1 hm0 hm1 N
  have he : (0 : Q') ≤ dyadicDefect k N ∧ dyadicDefect k N ≤ 2*Q'.invSucc N :=
    dyadic_defect_bounds k N
  have hpin := mixed_identity m k N
  have hlo := Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hm0 he.1) hd.1
  have hscaled : m*dyadicDefect k N ≤ 2*Q'.invSucc N :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hm1 he.1)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) he.2)
  have hcap : 2*Q'.invSucc N+Q'.invSucc N ≈ 3*Q'.invSucc N :=
    poly_identity_of_normal_eq (.add (.mul (.const 2) (.var 0)) (.var 0))
      (.mul (.const 3) (.var 0)) (by decide) (fun _ => Q'.invSucc N)
  exact ⟨Q'.le_trans' _ _ _ hlo (Q'.ge_of_eqv hpin),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hscaled hd.2) (Q'.le_of_eqv hcap))⟩

end YMGap.Continuum.RegularizedLogDyadicFiniteDefect

#print axioms YMGap.Continuum.RegularizedLogDyadicFiniteDefect.partial_congr
#print axioms YMGap.Continuum.RegularizedLogDyadicFiniteDefect.dyadicDefect
#print axioms YMGap.Continuum.RegularizedLogDyadicFiniteDefect.dyadic_recurrence
#print axioms YMGap.Continuum.RegularizedLogDyadicFiniteDefect.dyadic_defect_bounds
#print axioms YMGap.Continuum.RegularizedLogDyadicFiniteDefect.mixed_defect_bounds
