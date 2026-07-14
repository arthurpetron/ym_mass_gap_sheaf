/-
# First-pair Casimir eigenvalue on every ordered left channel

The left-associated channel is built by first contracting the first two
legs.  Its coefficient row is therefore an exact eigenvector of the same
discrete pair-exchange operator used to separate right channels.  This file
proves that statement on the complete physical monomial rectangle, including
all boundary coordinates and the lower-support region.
-/

import YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

namespace YMGap.Continuum.SU2OrderedLeftCasimirEigen

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem equal_of_scale_eqv_zero (s x y : Q') (hs : s ≈ 0) :
    s * x ≈ s * y := by
  refine Q'.eqv_trans _ (0 * x) _
    (Q'.mul_eqv_congr_right _ _ x hs) ?_
  refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv x) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ (0 * y) _
    (Q'.mul_eqv_congr_right _ _ y hs) (Q'.zero_mul_eqv y))

private theorem product_scale_zero_left (x : Q') :
    Q'.ofNat 0 * x ≈ 0 := by
  refine Q'.eqv_trans _ ((0 : Q') * x) _
    (Q'.mul_eqv_congr_right _ _ x Q'.ofNat_zero_eqv) ?_
  exact Q'.zero_mul_eqv x

private theorem product_scale_zero_right (x : Q') :
    x * Q'.ofNat 0 ≈ 0 := by
  refine Q'.eqv_trans _ (x * (0 : Q')) _
    (Q'.mul_eqv_congr_left x _ _ Q'.ofNat_zero_eqv) ?_
  exact Q'.mul_zero_eqv x

private theorem neg_zero_eqv : (-(0 : Q')) ≈ 0 := by decide

/-- The outer coefficient left after extracting the first-pair factorial Hahn
row.  The first two source indices enter only through their preserved sum. -/
def fixedLeftOuterCoefficient {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (t l s : Nat) : Q' :=
  transvect q.intermediate c q.r
    (tprod (mono (t - q.k)) (mono l)) s

theorem fixedLeft_monomial_factorization {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (hk : q.k ≤ i + j) :
    triLeft a b c d q.intermediate (mono i) (mono j) (mono l) s ≈
      transvectFactorialCoeff a b q.k i j *
        fixedLeftOuterCoefficient q (i + j) l s := by
  have h := triLeft_monomial_factorization
    a b c d q.intermediate i j l s (by
      rw [fixedLeft_inner_couplingOrder q]
      exact hk)
  simpa only [fixedLeft_inner_couplingOrder q,
    fixedLeft_outer_couplingOrder q, hahnEntry,
    fixedLeftOuterCoefficient,
    show i + j - i = j by omega] using h

private theorem difference_mul_factor (A B O : Q') :
    A * O + -(B * O) ≈ (A + -B) * O := by
  ring_qeqv

private theorem fixedLeft_forward_scaled {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (hi : i ≤ a) (_hj : j ≤ b) (hk : q.k ≤ i + j) :
    (Q'.ofNat (a - i) * Q'.ofNat j) *
        (triLeft a b c d q.intermediate
            (mono (i + 1)) (mono (j - 1)) (mono l) s +
          -triLeft a b c d q.intermediate
            (mono i) (mono j) (mono l) s) ≈
      (Q'.ofNat (a - i) * Q'.ofNat j) *
        ((transvectFactorialCoeff a b q.k (i + 1) (j - 1) +
            -transvectFactorialCoeff a b q.k i j) *
          fixedLeftOuterCoefficient q (i + j) l s) := by
  by_cases hia : i < a
  · by_cases hj0 : 0 < j
    · have hshift := fixedLeft_monomial_factorization q
          (i + 1) (j - 1) l s (by omega)
      have hbase := fixedLeft_monomial_factorization q i j l s hk
      have htotal : i + 1 + (j - 1) = i + j := by omega
      rw [htotal] at hshift
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))
          (difference_mul_factor _ _ _))
    · have hjz : j = 0 := by omega
      rw [hjz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat (a - i)))
  · have haz : a - i = 0 := by omega
    rw [haz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat j))

private theorem fixedLeft_backward_scaled {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (_hi : i ≤ a) (hj : j ≤ b) (hk : q.k ≤ i + j) :
    (Q'.ofNat i * Q'.ofNat (b - j)) *
        (triLeft a b c d q.intermediate
            (mono (i - 1)) (mono (j + 1)) (mono l) s +
          -triLeft a b c d q.intermediate
            (mono i) (mono j) (mono l) s) ≈
      (Q'.ofNat i * Q'.ofNat (b - j)) *
        ((transvectFactorialCoeff a b q.k (i - 1) (j + 1) +
            -transvectFactorialCoeff a b q.k i j) *
          fixedLeftOuterCoefficient q (i + j) l s) := by
  by_cases hi0 : 0 < i
  · by_cases hjb : j < b
    · have hshift := fixedLeft_monomial_factorization q
          (i - 1) (j + 1) l s (by omega)
      have hbase := fixedLeft_monomial_factorization q i j l s hk
      have htotal : i - 1 + (j + 1) = i + j := by omega
      rw [htotal] at hshift
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))
          (difference_mul_factor _ _ _))
    · have hbz : b - j = 0 := by omega
      rw [hbz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat i))
  · have hiz : i = 0 := by omega
    rw [hiz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat (b - j)))

private theorem exchange_factor_ring
    (B D Xp Xm X O : Q') :
    B * ((Xp + -X) * O) + D * ((Xm + -X) * O) ≈
      (B * (Xp + -X) + D * (Xm + -X)) * O := by
  ring_qeqv

private theorem neg_eigen_factor_ring (L H O : Q') :
    (-(L * H)) * O ≈ -(L * (H * O)) := by
  ring_qeqv

/-- Every physical nested left-channel coefficient is an eigenvector of the
first-pair exchange Casimir, uniformly in the third input and output slots. -/
theorem fixedLeftCoefficient_pairExchange_eigen {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (hi : i ≤ a) (hj : j ≤ b) :
    pairExchange a b
        (fun x y => triLeft a b c d q.intermediate
          (mono x) (mono y) (mono l) s) i j ≈
      -(pairEigenvalue a b q.k *
        triLeft a b c d q.intermediate
          (mono i) (mono j) (mono l) s) := by
  by_cases hk : q.k ≤ i + j
  · let O := fixedLeftOuterCoefficient q (i + j) l s
    let H : Nat → Nat → Q' := fun x y =>
      transvectFactorialCoeff a b q.k x y
    have hf := fixedLeft_forward_scaled q i j l s hi hj hk
    have hb := fixedLeft_backward_scaled q i j l s hi hj hk
    have heig := transvectFactorialCoeff_pairExchange_eigen
      a b q.k i j (Nat.le_trans q.k_le (Nat.min_le_left _ _))
        (Nat.le_trans q.k_le (Nat.min_le_right _ _)) hi hj
    have hbase := fixedLeft_monomial_factorization q i j l s hk
    unfold pairExchange
    refine Q'.eqv_trans _
      ((Q'.ofNat (a - i) * Q'.ofNat j) *
          ((H (i + 1) (j - 1) + -H i j) * O) +
        (Q'.ofNat i * Q'.ofNat (b - j)) *
          ((H (i - 1) (j + 1) + -H i j) * O)) _ ?_ ?_
    · exact Q'.add_eqv_congr' (by simpa only [H, O] using hf)
        (by simpa only [H, O] using hb)
    · refine Q'.eqv_trans _ (pairExchange a b H i j * O) _
          (by
            unfold pairExchange
            exact exchange_factor_ring _ _ _ _ _ _) ?_
      refine Q'.eqv_trans _ ((-(pairEigenvalue a b q.k * H i j)) * O) _
        (Q'.mul_eqv_congr_right _ _ O (by simpa only [H] using heig)) ?_
      refine Q'.eqv_trans _ (-(pairEigenvalue a b q.k * (H i j * O))) _
        (neg_eigen_factor_ring _ _ _) ?_
      exact Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (pairEigenvalue a b q.k) _ _
          (Q'.eqv_symm (by simpa only [H, O] using hbase)))
  · have hbase := triLeft_monomial_zero_below_inner_order q i j l s
        (by omega)
    have hforward :
        (Q'.ofNat (a - i) * Q'.ofNat j) *
          (triLeft a b c d q.intermediate
              (mono (i + 1)) (mono (j - 1)) (mono l) s +
            -triLeft a b c d q.intermediate
              (mono i) (mono j) (mono l) s) ≈ 0 := by
      by_cases hia : i < a
      · by_cases hj0 : 0 < j
        · have hshift := triLeft_monomial_zero_below_inner_order q
              (i + 1) (j - 1) l s (by omega)
          refine Q'.eqv_trans _
            ((Q'.ofNat (a - i) * Q'.ofNat j) * ((0 : Q') + -0)) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))) ?_
          ring_qeqv
        · have hjz : j = 0 := by omega
          rw [hjz]
          refine Q'.eqv_trans _ (0 * _) _
            (Q'.mul_eqv_congr_right _ _ _
              (product_scale_zero_right (Q'.ofNat (a - i)))) ?_
          exact Q'.zero_mul_eqv _
      · have haz : a - i = 0 := by omega
        rw [haz]
        refine Q'.eqv_trans _ (0 * _) _
          (Q'.mul_eqv_congr_right _ _ _
            (product_scale_zero_left (Q'.ofNat j))) ?_
        exact Q'.zero_mul_eqv _
    have hbackward :
        (Q'.ofNat i * Q'.ofNat (b - j)) *
          (triLeft a b c d q.intermediate
              (mono (i - 1)) (mono (j + 1)) (mono l) s +
            -triLeft a b c d q.intermediate
              (mono i) (mono j) (mono l) s) ≈ 0 := by
      by_cases hi0 : 0 < i
      · by_cases hjb : j < b
        · have hshift := triLeft_monomial_zero_below_inner_order q
              (i - 1) (j + 1) l s (by omega)
          refine Q'.eqv_trans _
            ((Q'.ofNat i * Q'.ofNat (b - j)) * ((0 : Q') + -0)) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))) ?_
          ring_qeqv
        · have hbz : b - j = 0 := by omega
          rw [hbz]
          refine Q'.eqv_trans _ (0 * _) _
            (Q'.mul_eqv_congr_right _ _ _
              (product_scale_zero_right (Q'.ofNat i))) ?_
          exact Q'.zero_mul_eqv _
      · have hiz : i = 0 := by omega
        rw [hiz]
        refine Q'.eqv_trans _ (0 * _) _
          (Q'.mul_eqv_congr_right _ _ _
            (product_scale_zero_left (Q'.ofNat (b - j)))) ?_
        exact Q'.zero_mul_eqv _
    unfold pairExchange
    refine Q'.eqv_trans _ ((0 : Q') + 0) _
      (Q'.add_eqv_congr' hforward hbackward) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.eqv_of_eq (Q'.zero_add' 0)) ?_
    have hz : pairEigenvalue a b q.k *
        triLeft a b c d q.intermediate
          (mono i) (mono j) (mono l) s ≈ 0 :=
      Q'.eqv_trans _ (pairEigenvalue a b q.k * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hbase) (Q'.mul_zero_eqv _)
    exact Q'.eqv_symm (Q'.eqv_trans _ (-0) _
      (Q'.neg_eqv_congr _ _ hz) neg_zero_eqv)

end YMGap.Continuum.SU2OrderedLeftCasimirEigen

#print axioms YMGap.Continuum.SU2OrderedLeftCasimirEigen.fixedLeft_monomial_factorization
#print axioms YMGap.Continuum.SU2OrderedLeftCasimirEigen.fixedLeftCoefficient_pairExchange_eigen
