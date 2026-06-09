/-
Exponential addition law (L4-add) — `e^{-a}·e^{-b} ≃ e^{-(a+b)}`.

`(mul (expNeg a) (expNeg b)).approx n = P⁻ₙ(a)·P⁻ₙ(b)`, and L3a-add gives
`P⁻ₙ(a)·P⁻ₙ(b) ≃ P⁻ₙ(a+b) + cornerₙ` while L3b-add gives `|cornerₙ| ≤ ε` past
an explicit modulus.  Hence the two `CReal`s have the same limit:

    CReal.Equiv (mul (expNeg a) (expNeg b)) (expNeg (a+b)) .

`CReal.Equiv` is the sound limit-equality (`|A_n − B_n|` eventually `≤ ε`); it
transfers the rational bound `leRat` (`leRat_of_equiv`), which is what the U.6
character-tail geometric majorant consumes:
`e^{−(a+c)} = e^{−a}·e^{−c} ≤ (bound on e^{−a})·(bound on e^{−c})`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Constructive.CornerBoundAdd
import YMGap.Constructive.CRealLe

namespace YMGap.Constructive

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow

namespace CReal

/-- **Sound limit-equality of constructive reals.**  `Equiv A B` says the two
have the same limit: for every `ε > 0`, eventually `|A_n − B_n| ≤ ε`. -/
def Equiv (A B : CReal) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    A.approx n ≤ B.approx n + ε ∧ B.approx n ≤ A.approx n + ε

/-- `Equiv` is symmetric. -/
theorem Equiv.symm {A B : CReal} (h : Equiv A B) : Equiv B A :=
  fun ε hε => by
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => ⟨(hN n hn).2, (hN n hn).1⟩⟩

/-- **`Equiv` transfers `leRat`.**  Same limit ⇒ same rational upper bounds. -/
theorem leRat_of_equiv {A B : CReal} {c : Q'} (h : Equiv A B) (hB : CReal.leRat B c) :
    CReal.leRat A c := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, h1⟩ := h (half * ε) hhε
  obtain ⟨N2, h2⟩ := hB (half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- A_n ≤ B_n + ½ε ≤ (c + ½ε) + ½ε ≃ c + ε
  refine Q'.le_trans' _ _ _ (h1 n hn1).1 ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (half * ε) (h2 n hn2)) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv c (half * ε) (half * ε)) ?_)
  exact Q'.add_eqv_congr_left c (half * ε + half * ε) ε (ExpNeg.two_halves ε)

end CReal

/-! ## The addition law -/

/-- **Exponential addition law.**  `e^{-a}·e^{-b} ≃ e^{-(a+b)}` for `a,b ≥ 0`. -/
theorem expNeg_add_equiv (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    CReal.Equiv (CReal.mul (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb))
      (ExpNeg.expNeg (a + b) (Q'.zero_le_add a b ha hb)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := cornerAbsAdd_le a b ha hb ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- A_n = P⁻ₙ(a)·P⁻ₙ(b), B_n = P⁻ₙ(a+b), and A_n ≃ B_n + cornerₙ
  have hdecomp := prodAdd_eqv_partialSum_add_corner a b n
  have hcle : cornerAdd a b n ≤ cornerAbsAdd a b n := cornerAdd_le_cornerAbs a b ha hb n
  have hnle : -(cornerAdd a b n) ≤ cornerAbsAdd a b n := neg_cornerAdd_le_cornerAbs a b ha hb n
  have hbd : cornerAbsAdd a b n ≤ ε := hN n hn
  refine ⟨?_, ?_⟩
  · -- A_n ≤ B_n + ε
    show partialSum a n * partialSum b n ≤ partialSum (a + b) n + ε
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomp) ?_
    exact Q'.add_le_add_left _ _ ε (Q'.le_trans' _ _ _ hcle hbd)
  · -- B_n ≤ A_n + ε : B_n ≃ A_n + -cornerₙ, and -cornerₙ ≤ ε
    show partialSum (a + b) n ≤ partialSum a n * partialSum b n + ε
    -- B_n ≃ A_n + -cornerₙ
    have hBeqv : (partialSum (a + b) n).eqv
        (partialSum a n * partialSum b n + -(cornerAdd a b n)) := by
      -- A_n + -corner ≃ (B_n + corner) + -corner ≃ B_n
      have e1 : (partialSum a n * partialSum b n + -(cornerAdd a b n)).eqv
          ((partialSum (a + b) n + cornerAdd a b n) + -(cornerAdd a b n)) :=
        Q'.add_eqv_congr_right _ _ (-(cornerAdd a b n)) hdecomp
      have e2 : ((partialSum (a + b) n + cornerAdd a b n) + -(cornerAdd a b n)).eqv
          (partialSum (a + b) n) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (partialSum (a + b) n) (cornerAdd a b n) (-(cornerAdd a b n))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (partialSum (a + b) n) _ 0
            (Q'.add_neg_self_eqv (cornerAdd a b n))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hBeqv) ?_
    exact Q'.add_le_add_left _ _ ε (Q'.le_trans' _ _ _ hnle hbd)

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.leRat_of_equiv
#print axioms YMGap.Constructive.expNeg_add_equiv
