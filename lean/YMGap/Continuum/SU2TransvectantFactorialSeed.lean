/-
# Factorial seed for the all-order transvectant coefficient

This module connects the symbolic arbitrary-label transvectant development to
the factorial coefficient used by the finite mixed pentagon.  It proves the
universal factorial identities at contraction orders zero and one: positive
factorials, the zero/one falling factorials, and the zeroth coefficient itself.
These are the base cases for the Pascal induction on arbitrary contraction
order.

No finite cutoff enumeration, classical choice, native decision procedure,
proof hole, or new axiom.
-/

import YMGap.Continuum.SU2TransvectantGeneralCoefficient
import YMGap.Continuum.SU2TransvectantMixedPentagon

namespace YMGap.Continuum.SU2TransvectantFactorialSeed

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2TransvectantMixedPentagon

private theorem mul_congr {a b c d : Q'} (ha : a.eqv c) (hb : b.eqv d) :
    (a * b).eqv (c * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a c b ha)
    (Q'.mul_eqv_congr_left c b d hb)

/-- The factorial carrier is strictly positive for every natural input. -/
theorem tvFact_pos : ∀ n : Nat, 0 < tvFact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (tvFact_pos n)

/-- A positive natural divided by itself, represented through `mkN`, is
semantically one. -/
theorem mkN_self_pred_eqv_one (a : Nat) (ha : 0 < a) :
    (Q'.mkN a (a - 1)).eqv 1 := by
  show (a : Int) * (1 : Int) = (1 : Int) * (((a - 1) + 1 : Nat) : Int)
  have hpred : a - 1 + 1 = a := by omega
  rw [hpred]
  simp

/-- The zeroth falling factorial is one for every label. -/
theorem tvFallQ_zero (n : Nat) : (tvFallQ n 0).eqv 1 := by
  unfold tvFallQ
  rw [if_pos (Nat.zero_le n), Nat.sub_zero]
  exact mkN_self_pred_eqv_one (tvFact n) (tvFact_pos n)

/-- The first falling factorial is the label itself, including the zero edge
case. -/
theorem tvFallQ_one (n : Nat) : (tvFallQ n 1).eqv (Q'.ofNat n) := by
  cases n with
  | zero =>
      unfold tvFallQ
      rw [if_neg (by decide : ¬ 1 ≤ 0)]
      exact Q'.eqv_symm Q'.ofNat_zero_eqv
  | succ n =>
      unfold tvFallQ
      rw [if_pos (by omega : 1 ≤ n + 1)]
      show ((tvFact (n + 1) : Nat) : Int) * (1 : Int) =
        ((n + 1 : Nat) : Int) * (((tvFact (n + 1 - 1) - 1) + 1 : Nat) : Int)
      have hfact : tvFact (n + 1) = (n + 1) * tvFact n := rfl
      have hpred : tvFact n - 1 + 1 = tvFact n := by
        have := tvFact_pos n
        omega
      rw [hfact, show n + 1 - 1 = n by omega, hpred]
      push_cast
      simp

/-- The second falling factorial is `n(n-1)`, uniformly including `n<2`. -/
theorem tvFallQ_two (n : Nat) :
    (tvFallQ n 2).eqv (Q'.ofNat (n * (n - 1))) := by
  cases n with
  | zero =>
      unfold tvFallQ
      rw [if_neg (by decide : ¬ 2 ≤ 0)]
      exact Q'.eqv_symm Q'.ofNat_zero_eqv
  | succ n =>
      cases n with
      | zero =>
          unfold tvFallQ
          rw [if_neg (by decide : ¬ 2 ≤ 1)]
          simpa using Q'.eqv_symm Q'.ofNat_zero_eqv
      | succ k =>
          unfold tvFallQ
          rw [if_pos (by omega : 2 ≤ k + 1 + 1)]
          show ((tvFact (k + 1 + 1) : Nat) : Int) * (1 : Int) =
            (((k + 1 + 1) * (k + 1 + 1 - 1) : Nat) : Int) *
              (((tvFact (k + 1 + 1 - 2) - 1) + 1 : Nat) : Int)
          have hpred : tvFact k - 1 + 1 = tvFact k := by
            have := tvFact_pos k
            omega
          rw [show k + 1 + 1 - 2 = k by omega,
            show k + 1 + 1 - 1 = k + 1 by omega, hpred]
          simp only [tvFact]
          push_cast
          simp only [Int.mul_one]
          ac_rfl

/-- The order-zero binomial coefficient is one. -/
theorem tvBinomQ_zero_zero : (tvBinomQ 0 0).eqv 1 := by
  unfold tvBinomQ
  rw [if_pos (by decide : 0 ≤ 0)]
  decide

/-- Both binomial coefficients at order one are one. -/
theorem tvBinomQ_one_zero : (tvBinomQ 1 0).eqv 1 := by decide

theorem tvBinomQ_one_one : (tvBinomQ 1 1).eqv 1 := by decide

theorem tvBinomQ_two_zero : (tvBinomQ 2 0).eqv 1 := by decide

theorem tvBinomQ_two_one : (tvBinomQ 2 1).eqv 2 := by decide

theorem tvBinomQ_two_two : (tvBinomQ 2 2).eqv 1 := by decide

private theorem positive_chain (a b : Nat) :
    (1 * 1 * Q'.ofNat a * 1 * 1 * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (1 * 1 * Q'.ofNat a * 1 * 1 * Q'.ofNat b).num *
      ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num *
      ((1 * 1 * Q'.ofNat a * 1 * 1 * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl]
  push_cast
  simp

private theorem negative_chain (a b : Nat) :
    (Q'.ofInt (-1) * 1 * 1 * Q'.ofNat a * Q'.ofNat b * 1).eqv
      (-(Q'.ofNat (a * b))) := by
  show (Q'.ofInt (-1) * 1 * 1 * Q'.ofNat a * Q'.ofNat b * 1).num *
      ((-(Q'.ofNat (a * b))).den : Int) =
    (-(Q'.ofNat (a * b))).num *
      ((Q'.ofInt (-1) * 1 * 1 * Q'.ofNat a * Q'.ofNat b * 1).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.neg_den,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    show (Q'.ofInt (-1)).num = -1 from rfl,
    show ((Q'.ofInt (-1)).den : Int) = 1 from rfl,
    show (-(Q'.ofNat (a * b))).num = -((a * b : Nat) : Int) from rfl]
  push_cast
  simp [Int.neg_mul]

private theorem nat_six_chain (a b c d e f : Nat) :
    (Q'.ofNat a * Q'.ofNat b * Q'.ofNat c * Q'.ofNat d *
      Q'.ofNat e * Q'.ofNat f).eqv
      (Q'.ofNat (a * b * c * d * e * f)) := by
  show (Q'.ofNat a * Q'.ofNat b * Q'.ofNat c * Q'.ofNat d *
      Q'.ofNat e * Q'.ofNat f).num *
      ((Q'.ofNat (a * b * c * d * e * f)).den : Int) =
    (Q'.ofNat (a * b * c * d * e * f)).num *
      ((Q'.ofNat a * Q'.ofNat b * Q'.ofNat c * Q'.ofNat d *
        Q'.ofNat e * Q'.ofNat f).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem neg_six_chain (a b c d e : Nat) :
    (Q'.ofInt (-1) * Q'.ofNat a * Q'.ofNat b * Q'.ofNat c *
      Q'.ofNat d * Q'.ofNat e).eqv
      (-(Q'.ofNat (a * b * c * d * e))) := by
  show (Q'.ofInt (-1) * Q'.ofNat a * Q'.ofNat b * Q'.ofNat c *
      Q'.ofNat d * Q'.ofNat e).num *
      ((-(Q'.ofNat (a * b * c * d * e))).den : Int) =
    (-(Q'.ofNat (a * b * c * d * e))).num *
      ((Q'.ofInt (-1) * Q'.ofNat a * Q'.ofNat b * Q'.ofNat c *
        Q'.ofNat d * Q'.ofNat e).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.neg_den,
    show (Q'.ofInt (-1)).num = -1 from rfl,
    show ((Q'.ofInt (-1)).den : Int) = 1 from rfl,
    show (-(Q'.ofNat (a * b * c * d * e))).num =
      -((a * b * c * d * e : Nat) : Int) from rfl]
  push_cast
  simp [Int.neg_mul]

/-- The `r=0` term of the order-one factorial coefficient. -/
theorem transvectFactorialCoeff_one_term_zero (m n i j : Nat) :
    (tvPhase 0 * tvBinomQ 1 0 * tvFallQ i 1 * tvFallQ (m - i) 0 *
      tvFallQ j 0 * tvFallQ (n - j) 1).eqv
      (Q'.ofNat (i * (n - j))) := by
  have hp : (tvPhase 0).eqv 1 := by decide
  have hprod :=
    mul_congr
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr hp tvBinomQ_one_zero) (tvFallQ_one i))
          (tvFallQ_zero (m - i)))
        (tvFallQ_zero j))
      (tvFallQ_one (n - j))
  exact Q'.eqv_trans _ _ _ hprod (positive_chain i (n - j))

/-- The `r=1` term of the order-one factorial coefficient. -/
theorem transvectFactorialCoeff_one_term_one (m n i j : Nat) :
    (tvPhase 1 * tvBinomQ 1 1 * tvFallQ i 0 * tvFallQ (m - i) 1 *
      tvFallQ j 1 * tvFallQ (n - j) 0).eqv
      (-(Q'.ofNat ((m - i) * j))) := by
  have hp : (tvPhase 1).eqv (Q'.ofInt (-1)) := by decide
  have hprod :=
    mul_congr
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr hp tvBinomQ_one_one) (tvFallQ_zero i))
          (tvFallQ_one (m - i)))
        (tvFallQ_one j))
      (tvFallQ_zero (n - j))
  exact Q'.eqv_trans _ _ _ hprod (negative_chain (m - i) j)

/-- The factorial expression at contraction order zero is universally one. -/
theorem transvectFactorialCoeff_zero (m n i j : Nat) :
    (transvectFactorialCoeff m n 0 i j).eqv 1 := by
  unfold transvectFactorialCoeff
  simp only [finSum_succ, finSum_zero, Nat.zero_sub, Nat.zero_mod,
    tvPhase, if_pos]
  have hbin := tvBinomQ_zero_zero
  have hi := tvFallQ_zero i
  have hm := tvFallQ_zero (m - i)
  have hj := tvFallQ_zero j
  have hn := tvFallQ_zero (n - j)
  refine Q'.eqv_trans _
    (0 + (1 * 1 * 1 * 1 * 1 * 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 0 _ _
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr
              (mul_congr (Q'.eqv_refl 1) hbin) hi) hm) hj) hn)
  · decide

/-- The complete order-one factorial coefficient is the signed Cayley
coefficient `i(n-j) - (m-i)j`. -/
theorem transvectFactorialCoeff_one (m n i j : Nat) :
    (transvectFactorialCoeff m n 1 i j).eqv
      (Q'.ofNat (i * (n - j)) + -(Q'.ofNat ((m - i) * j))) := by
  unfold transvectFactorialCoeff
  change ((0 +
      (tvPhase 0 * tvBinomQ 1 0 * tvFallQ i 1 * tvFallQ (m - i) 0 *
        tvFallQ j 0 * tvFallQ (n - j) 1)) +
      (tvPhase 1 * tvBinomQ 1 1 * tvFallQ i 0 * tvFallQ (m - i) 1 *
        tvFallQ j 1 * tvFallQ (n - j) 0)).eqv _
  have hzero :
      (0 + (tvPhase 0 * tvBinomQ 1 0 * tvFallQ i 1 * tvFallQ (m - i) 0 *
        tvFallQ j 0 * tvFallQ (n - j) 1)).eqv
      (Q'.ofNat (i * (n - j))) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
    exact transvectFactorialCoeff_one_term_zero m n i j
  exact Q'.add_eqv_congr' hzero
    (transvectFactorialCoeff_one_term_one m n i j)

/-- The complete order-two factorial coefficient, displaying the Pascal
multiplicity `2` in the signed middle contraction. -/
theorem transvectFactorialCoeff_two (m n i j : Nat) :
    (transvectFactorialCoeff m n 2 i j).eqv
      (Q'.ofNat ((i * (i - 1)) * ((n - j) * (n - j - 1))) +
        -(Q'.ofNat (2 * i * (m - i) * j * (n - j))) +
        Q'.ofNat (((m - i) * (m - i - 1)) * (j * (j - 1)))) := by
  let A := (i * (i - 1)) * ((n - j) * (n - j - 1))
  let B := 2 * i * (m - i) * j * (n - j)
  let C := ((m - i) * (m - i - 1)) * (j * (j - 1))
  let T0 := tvPhase 0 * tvBinomQ 2 0 * tvFallQ i 2 * tvFallQ (m - i) 0 *
    tvFallQ j 0 * tvFallQ (n - j) 2
  let T1 := tvPhase 1 * tvBinomQ 2 1 * tvFallQ i 1 * tvFallQ (m - i) 1 *
    tvFallQ j 1 * tvFallQ (n - j) 1
  let T2 := tvPhase 2 * tvBinomQ 2 2 * tvFallQ i 0 * tvFallQ (m - i) 2 *
    tvFallQ j 2 * tvFallQ (n - j) 0
  have hT0 : T0.eqv (Q'.ofNat A) := by
    have hp : (tvPhase 0).eqv 1 := by decide
    have hprod := mul_congr
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr hp tvBinomQ_two_zero) (tvFallQ_two i))
          (tvFallQ_zero (m - i)))
        (tvFallQ_zero j))
      (tvFallQ_two (n - j))
    refine Q'.eqv_trans _
      (Q'.ofNat 1 * Q'.ofNat 1 * Q'.ofNat (i * (i - 1)) * Q'.ofNat 1 *
        Q'.ofNat 1 * Q'.ofNat ((n - j) * (n - j - 1))) _ hprod ?_
    exact Q'.eqv_trans _ _ _
      (nat_six_chain 1 1 (i * (i - 1)) 1 1 ((n - j) * (n - j - 1)))
      (by simpa [A] using Q'.eqv_refl (Q'.ofNat A))
  have hT1 : T1.eqv (-(Q'.ofNat B)) := by
    have hp : (tvPhase 1).eqv (Q'.ofInt (-1)) := by decide
    have hprod := mul_congr
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr hp tvBinomQ_two_one) (tvFallQ_one i))
          (tvFallQ_one (m - i)))
        (tvFallQ_one j))
      (tvFallQ_one (n - j))
    refine Q'.eqv_trans _
      (Q'.ofInt (-1) * Q'.ofNat 2 * Q'.ofNat i * Q'.ofNat (m - i) *
        Q'.ofNat j * Q'.ofNat (n - j)) _ hprod ?_
    exact Q'.eqv_trans _ _ _
      (neg_six_chain 2 i (m - i) j (n - j))
      (by simpa [B] using Q'.eqv_refl (-(Q'.ofNat B)))
  have hT2 : T2.eqv (Q'.ofNat C) := by
    have hp : (tvPhase 2).eqv 1 := by decide
    have hprod := mul_congr
      (mul_congr
        (mul_congr
          (mul_congr
            (mul_congr hp tvBinomQ_two_two) (tvFallQ_zero i))
          (tvFallQ_two (m - i)))
        (tvFallQ_two j))
      (tvFallQ_zero (n - j))
    refine Q'.eqv_trans _
      (Q'.ofNat 1 * Q'.ofNat 1 * Q'.ofNat 1 *
        Q'.ofNat ((m - i) * (m - i - 1)) * Q'.ofNat (j * (j - 1)) * Q'.ofNat 1)
      _ hprod ?_
    exact Q'.eqv_trans _ _ _
      (nat_six_chain 1 1 1 ((m - i) * (m - i - 1)) (j * (j - 1)) 1)
      (by simpa [C] using Q'.eqv_refl (Q'.ofNat C))
  unfold transvectFactorialCoeff
  change (((0 + T0) + T1) + T2).eqv _
  have h0 : (0 + T0).eqv (Q'.ofNat A) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' T0)) hT0
  have hall : (((0 + T0) + T1) + T2).eqv
      ((Q'.ofNat A + -(Q'.ofNat B)) + Q'.ofNat C) :=
    Q'.add_eqv_congr' (Q'.add_eqv_congr' h0 hT1) hT2
  simpa only [A, B, C] using hall

/-- The actual arbitrary-label zeroth transvectant agrees with the factorial
formula on its unique output shell. -/
theorem transvect_zero_matches_factorial (m n i j : Nat) :
    (YMGap.Continuum.TransvectantCG.transvect m n 0
      (YMGap.Continuum.TransvectantCG.tprod
        (YMGap.Continuum.BinaryForms.mono i)
        (YMGap.Continuum.BinaryForms.mono j)) (i + j)).eqv
      (transvectFactorialCoeff m n 0 i j) := by
  refine Q'.eqv_trans _ 1 _ ?_ (Q'.eqv_symm (transvectFactorialCoeff_zero m n i j))
  simpa using
    (YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_zero_monomial
      m n i j (i + j))

/-- The actual arbitrary-label first transvectant agrees with the factorial
formula on its output shell. -/
theorem transvect_one_matches_factorial (m n i j : Nat) (hij : 0 < i + j) :
    (YMGap.Continuum.TransvectantCG.transvect m n 1
      (YMGap.Continuum.TransvectantCG.tprod
        (YMGap.Continuum.BinaryForms.mono i)
        (YMGap.Continuum.BinaryForms.mono j)) (i + j - 1)).eqv
      (transvectFactorialCoeff m n 1 i j) := by
  let C := Q'.ofNat (i * (n - j)) + -(Q'.ofNat ((m - i) * j))
  refine Q'.eqv_trans _ C _ ?_ (Q'.eqv_symm (transvectFactorialCoeff_one m n i j))
  have hs : i + j - 1 + 1 = i + j := by omega
  simpa only [if_pos hs, C] using
    (YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
      m n i j (i + j - 1))

end YMGap.Continuum.SU2TransvectantFactorialSeed

#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.tvFact_pos
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.tvFallQ_zero
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.tvFallQ_one
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.tvFallQ_two
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.transvectFactorialCoeff_zero
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.transvectFactorialCoeff_one
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.transvectFactorialCoeff_two
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.transvect_zero_matches_factorial
#print axioms YMGap.Continuum.SU2TransvectantFactorialSeed.transvect_one_matches_factorial
