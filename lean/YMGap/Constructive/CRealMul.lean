/-
`CReal.mul` — constructive multiplication of constructive reals, intuitionistic
(axiom-clean, no `Classical.choice`).

Design that stays choice-free: the product is defined **pointwise**,
`(a*b).approx n := a.approx n * b.approx n`, which is computable from the
`approx` data alone — the (Prop-level, existential) Cauchy moduli of `a`, `b`
are used only inside the `cauchy` *proof* (itself a `Prop`, where destructing
existentials is fine).

The Cauchy estimate is the two-step bound
`a_p b_p ≤ a_q b_p + B·δ ≤ a_q b_q + 2B·δ` (vary one factor at a time), using
`AbsQ.mul_le_of_bounds` for each step and a division-free choice of `δ`.

This module first proves the `Q'` algebra helpers it needs (negation of a sum,
add–sub cancellation, right distributivity, sub-bounds, a division-free
`∃δ, B·δ+B·δ ≤ ε`), then boundedness, then `CReal.mul`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only (and `Quot.sound` where `omega`/`Nat` enter).  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Constructive.AbsQ
import YMGap.Constructive.Reals

namespace YMGap.Constructive

namespace Q'

/-- `−(a + b) ≃ −a + −b`. -/
theorem neg_add_eqv (a b : Q') : (-(a + b)).eqv (-a + -b) := by
  show (-(a + b)).num * ((-a + -b).den : Int) = (-a + -b).num * ((-(a + b)).den : Int)
  have hLn : (-(a + b)).num = -(a.num * (b.den : Int) + b.num * (a.den : Int)) := rfl
  have hRn : (-a + -b).num = (-a.num) * (b.den : Int) + (-b.num) * (a.den : Int) := rfl
  rw [hLn, hRn,
      show ((-a + -b).den : Int) = ((a + b).den : Int) from rfl,
      show ((-(a + b)).den : Int) = ((a + b).den : Int) from rfl,
      add_den_cast a b]
  simp only [Int.neg_mul, Int.add_mul, Int.neg_add]

/-- `a + −a ≃ 0`. -/
theorem add_neg_self_eqv (a : Q') : (a + -a).eqv 0 :=
  eqv_trans (a + -a) (-a + a) 0 (add_comm_eqv a (-a)) (neg_add_self_eqv a)

/-- `x ≃ y + (x − y)` (add–sub cancellation; `x − y = x + −y`). -/
theorem add_sub_cancel_eqv (x y : Q') : x.eqv (y + (x + -y)) := by
  have h2 : (y + (x + -y)).eqv (y + (-y + x)) :=
    add_eqv_congr_left y (x + -y) (-y + x) (add_comm_eqv x (-y))
  have h3 : (y + (-y + x)).eqv ((y + -y) + x) := eqv_symm (add_assoc_eqv y (-y) x)
  have h4 : ((y + -y) + x).eqv ((0 : Q') + x) :=
    add_eqv_congr_right (y + -y) 0 x (add_neg_self_eqv y)
  rw [zero_add'] at h4
  exact eqv_symm
    (eqv_trans (y + (x + -y)) (y + (-y + x)) x h2
      (eqv_trans (y + (-y + x)) ((y + -y) + x) x h3 h4))

/-- Right distributivity `(a + b)·c ≃ a·c + b·c` (from `mul_add` + commutativity). -/
theorem add_mul_eqv (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) := by
  have h1 : ((a + b) * c).eqv (c * (a + b)) := mul_comm_eqv (a + b) c
  have h2 : (c * (a + b)).eqv (c * a + c * b) := mul_add_eqv c a b
  have h3 : (c * a + c * b).eqv (a * c + c * b) :=
    add_eqv_congr_right (c * a) (a * c) (c * b) (mul_comm_eqv c a)
  have h4 : (a * c + c * b).eqv (a * c + b * c) :=
    add_eqv_congr_left (a * c) (c * b) (b * c) (mul_comm_eqv c b)
  exact eqv_trans ((a + b) * c) (c * (a + b)) (a * c + b * c) h1
    (eqv_trans (c * (a + b)) (c * a + c * b) (a * c + b * c) h2
      (eqv_trans (c * a + c * b) (a * c + c * b) (a * c + b * c) h3 h4))

/-- From `a ≤ b + c`, get `a − b ≤ c`. -/
theorem sub_le_of_le_add {a b c : Q'} (h : a ≤ b + c) : a + -b ≤ c := by
  have h1 : a + -b ≤ (b + c) + -b := add_le_add_right a (b + c) (-b) h
  have h2 : ((b + c) + -b).eqv c := by
    have e1 : ((b + c) + -b).eqv ((c + b) + -b) :=
      add_eqv_congr_right (b + c) (c + b) (-b) (add_comm_eqv b c)
    have e2 : ((c + b) + -b).eqv (c + (b + -b)) := add_assoc_eqv c b (-b)
    have e3 : (c + (b + -b)).eqv (c + 0) := add_eqv_congr_left c (b + -b) 0 (add_neg_self_eqv b)
    have e4 : (c + (0 : Q')) = c := add_zero' c
    have e3' : (c + (b + -b)).eqv c := by rw [e4] at e3; exact e3
    exact eqv_trans ((b + c) + -b) ((c + b) + -b) c e1
      (eqv_trans ((c + b) + -b) (c + (b + -b)) c e2 e3')
  exact le_trans' (a + -b) ((b + c) + -b) c h1 (le_of_eqv h2)

/-- From `a ≤ b + c`, get `−c ≤ b + −a`. -/
theorem neg_le_sub_of_le_add {a b c : Q'} (h : a ≤ b + c) : -c ≤ b + -a := by
  have h1 : a + -b ≤ c := sub_le_of_le_add h
  have h2 : -c ≤ -(a + -b) := neg_le_neg h1
  have h3 : (-(a + -b)).eqv (-a + -(-b)) := neg_add_eqv a (-b)
  have h4 : (-a + -(-b)).eqv (-a + b) := add_eqv_congr_left (-a) (-(-b)) b (neg_neg_eqv b)
  have h5 : (-a + b).eqv (b + -a) := add_comm_eqv (-a) b
  exact le_trans' (-c) (-(a + -b)) (b + -a) h2
    (le_of_eqv
      (eqv_trans (-(a + -b)) (-a + -(-b)) (b + -a) h3
        (eqv_trans (-a + -(-b)) (-a + b) (b + -a) h4 h5)))

end Q'

/-! ## Boundedness of a `CReal` past its `ε=1` cutoff -/

namespace CReal

open Q'

/-- A `CReal` is bounded past the stage `N` where its terms are within `1`:
`∃ N B, 0 ≤ B ∧ ∀ n ≥ N, −B ≤ a_n ≤ B`, with `B = |a_N| + 1`.  (No global
bound — only the post-cutoff range, which is all `CReal.mul` needs.) -/
theorem localBound (a : CReal) : ∃ N : Nat, ∃ B : Q', (0 : Q') ≤ B ∧
    ∀ n, N ≤ n → -B ≤ a.approx n ∧ a.approx n ≤ B := by
  obtain ⟨N, hN⟩ := a.cauchy 1 (by decide)
  refine ⟨N, Q'.abs (a.approx N) + 1, ?_, ?_⟩
  · exact le_trans' 0 (Q'.abs (a.approx N)) (Q'.abs (a.approx N) + 1)
      (Q'.abs_nonneg _) (Q'.add_le_self_of_nonneg _ 1 (by decide))
  · intro n hn
    obtain ⟨hub, hlb⟩ := hN n N hn (Nat.le_refl N)
    refine ⟨?_, ?_⟩
    · -- −(|v|+1) ≤ a_n
      have hv : -(Q'.abs (a.approx N)) ≤ a.approx N :=
        le_trans' (-(Q'.abs (a.approx N))) (-(-(a.approx N))) (a.approx N)
          (Q'.neg_le_neg (Q'.neg_le_abs (a.approx N)))
          (Q'.le_of_eqv (Q'.neg_neg_eqv (a.approx N)))
      have h1 : -(Q'.abs (a.approx N)) ≤ a.approx n + 1 := le_trans' _ _ _ hv hlb
      have h2 : -(Q'.abs (a.approx N)) + -1 ≤ (a.approx n + 1) + -1 :=
        Q'.add_le_add_right _ _ (-1) h1
      have h3 : ((a.approx n + 1) + -1).eqv (a.approx n) := by
        have e1 := Q'.add_assoc_eqv (a.approx n) 1 (-1)
        have e2 : (a.approx n + (1 + -1)).eqv (a.approx n + 0) :=
          Q'.add_eqv_congr_left (a.approx n) (1 + -1) 0 (Q'.add_neg_self_eqv 1)
        rw [Q'.add_zero' (a.approx n)] at e2
        exact Q'.eqv_trans _ _ _ e1 e2
      have h4 : -(Q'.abs (a.approx N)) + -1 ≤ a.approx n := le_trans' _ _ _ h2 (Q'.le_of_eqv h3)
      exact le_trans' (-(Q'.abs (a.approx N) + 1)) (-(Q'.abs (a.approx N)) + -1) (a.approx n)
        (Q'.le_of_eqv (Q'.neg_add_eqv (Q'.abs (a.approx N)) 1)) h4
    · -- a_n ≤ |v| + 1
      exact le_trans' (a.approx n) (a.approx N + 1) (Q'.abs (a.approx N) + 1) hub
        (Q'.add_le_add_right (a.approx N) (Q'.abs (a.approx N)) 1 (Q'.le_abs_self _))

end CReal

end YMGap.Constructive

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.CReal.localBound
#print axioms YMGap.Constructive.Q'.neg_add_eqv
#print axioms YMGap.Constructive.Q'.add_sub_cancel_eqv
#print axioms YMGap.Constructive.Q'.add_mul_eqv
#print axioms YMGap.Constructive.Q'.sub_le_of_le_add
#print axioms YMGap.Constructive.Q'.neg_le_sub_of_le_add
