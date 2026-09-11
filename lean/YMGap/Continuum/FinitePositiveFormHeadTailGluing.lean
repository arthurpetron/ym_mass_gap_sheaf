/-
# Constructive head--tail gluing for a positive finite form

Let a positive symmetric bilinear form be split into a head vector `a` and a
tail vector `b`.  If the head and tail diagonal forms obey

    B(a,a) <= q X,       B(b,b) <= tau Y,

then positivity at the deliberately scaled combination

    tau a - q b

absorbs the mixed term without square roots or division:

    2 B(a,b) <= tau X + q Y.

Consequently

    B(a+b,a+b) <= (q+tau)(X+Y).

This is the algebraic gluing step needed to combine a low-spin spectral
estimate with a trace-small high-spin Gram tail.  Both rates are explicit;
there is no claim here that a BF4 tail estimate has already been supplied.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.FinitePositiveFormHeadTailGluing

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-- Cancel a strictly positive rational factor on the left. -/
private theorem le_of_mul_le_mul_left_pos
    {a b c : Q'} (h : c * a ≤ c * b) (hc : (0 : Q') < c) : a ≤ b := by
  have hh :
      (c * a).num * ((c * b).den : Int) ≤
        (c * b).num * ((c * a).den : Int) := h
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  have hcn : 0 < c.num := CReal.num_pos_of_pos hc
  rw [show (c * a).num = c.num * a.num from rfl,
      show (c * b).num = c.num * b.num from rfl,
      Q'.mul_den_cast c b, Q'.mul_den_cast c a] at hh
  have hh2 :
      (c.num * (c.den : Int)) * (a.num * (b.den : Int)) ≤
        (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by
    have e1 :
        (c.num * a.num) * ((c.den : Int) * (b.den : Int)) =
          (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by
      ac_rfl
    have e2 :
        (c.num * b.num) * ((c.den : Int) * (a.den : Int)) =
          (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by
      ac_rfl
    rw [← e1, ← e2]
    exact hh
  have hcc : 0 < c.num * (c.den : Int) :=
    Int.mul_pos hcn (by exact_mod_cast c.den_pos)
  exact Int.le_of_mul_le_mul_left hh2 hcc

/-- A product of two strictly positive rationals is strictly positive. -/
private theorem mul_pos_local
    {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  show (0 : Int) * ((a * b).den : Int) < (a * b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact Int.mul_pos (CReal.num_pos_of_pos ha) (CReal.num_pos_of_pos hb)

/-! ## 1. The scaled-positive-form cross absorption -/

/-- The scaled cross estimate needs only the displayed quadratic-positivity
law; no bundled vector-space interface is required. -/
theorem two_cross_le_tail_head_budget_of_nonnegQuad
    {V : Type} (B : V → V → Q')
    (nonnegQuad : ∀ (s r : Q') (a b : V),
      (0 : Q') ≤
        s * s * B a a + 2 * (s * r) * B a b + r * r * B b b)
    (a b : V) (q tau X Y : Q')
    (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead : B a a ≤ q * X)
    (htail : B b b ≤ tau * Y) :
    2 * B a b ≤ tau * X + q * Y := by
  have hpositive := nonnegQuad tau (-q) a b
  have hcrossScaled :
      (tau * q) * (2 * B a b) ≤
        (tau * tau) * B a a + (q * q) * B b b := by
    apply Q'.le_of_sub_nonneg
    exact OSReconstructionProgress.le_of_le_eqv hpositive (by ring_qeqv)
  have hheadScaled :
      (tau * tau) * B a a ≤
        (tau * tau) * (q * X) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hhead
      (q_mul_self_nonneg tau)
  have htailScaled :
      (q * q) * B b b ≤
        (q * q) * (tau * Y) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htail
      (q_mul_self_nonneg q)
  have hscaledUpper :
      (tau * tau) * B a a + (q * q) * B b b ≤
        (tau * q) * (tau * X + q * Y) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add hheadScaled htailScaled)
      (Q'.le_of_eqv (by ring_qeqv))
  exact le_of_mul_le_mul_left_pos
    (Q'.le_trans' _ _ _ hcrossScaled hscaledUpper)
    (mul_pos_local htau hq)

/-- Positivity of `tau*a - q*b` turns separate head and tail bounds into the
sharp mixed bound `2 B(a,b) <= tau*X + q*Y`.  The proof cancels only the
explicitly positive rational `tau*q`; it introduces no square root. -/
theorem PreInnerForm.two_cross_le_tail_head_budget
    {V : Type} (F : PreInnerForm V)
    (a b : V) (q tau X Y : Q')
    (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead : F.B a a ≤ q * X)
    (htail : F.B b b ≤ tau * Y) :
    2 * F.B a b ≤ tau * X + q * Y := by
  exact two_cross_le_tail_head_budget_of_nonnegQuad
    F.B F.nonnegQuad a b q tau X Y hq htau hhead htail

/-! ## 2. Contraction of the assembled head plus tail -/

/-- Exact diagonal expansion for a sum in a constructive GNS datum. -/
theorem GNSData.add_self_expand
    (D : GNSData) (a b : D.V) :
    D.B (D.add a b) (D.add a b) ≈
      (D.B a a + 2 * D.B a b) + D.B b b := by
  refine Q'.eqv_trans _
    (D.B a (D.add a b) + D.B b (D.add a b)) _
    (D.B_add_left a b (D.add a b)) ?_
  refine Q'.eqv_trans _
    ((D.B a a + D.B a b) + (D.B b a + D.B b b)) _
    (QPoly.q_add_congr
      (D.B_add_right a a b)
      (D.B_add_right b a b)) ?_
  refine Q'.eqv_trans _
    ((D.B a a + D.B a b) + (D.B a b + D.B b b)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (D.B_symm b a))) ?_
  refine Q'.eqv_trans _
    (D.B a a + (D.B a b + (D.B a b + D.B b b))) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (D.B a a + ((D.B a b + D.B a b) + D.B b b)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
  refine Q'.eqv_trans _
    ((D.B a a + (D.B a b + D.B a b)) + D.B b b) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_congr (Q'.eqv_refl _)
      (OSReconstructionProgress.q_two_mul (D.B a b)))
    (Q'.eqv_refl _)

/-- A positive form with head rate `q` and tail rate `tau` contracts their
sum at the additive rate `q+tau`.  This theorem is deliberately stated on
`GNSData`, whose bilinearity identifies the left side with the three-term
head/cross/tail expansion. -/
theorem GNSData.add_self_le_of_head_tail
    (D : GNSData) (a b : D.V) (q tau X Y : Q')
    (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead : D.B a a ≤ q * X)
    (htail : D.B b b ≤ tau * Y) :
    D.B (D.add a b) (D.add a b) ≤
      (q + tau) * (X + Y) := by
  have hcross : 2 * D.B a b ≤ tau * X + q * Y :=
    PreInnerForm.two_cross_le_tail_head_budget D.toPreInnerForm
      a b q tau X Y hq htau hhead htail
  have hthree :
      (D.B a a + 2 * D.B a b) + D.B b b ≤
        (q * X + (tau * X + q * Y)) + tau * Y :=
    Q'.add_le_add (Q'.add_le_add hhead hcross) htail
  have hexpand := GNSData.add_self_expand D a b
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hexpand)
    (Q'.le_trans' _ _ _ hthree
      (Q'.le_of_eqv (by ring_qeqv)))

/-! ## 3. Zero-rate-safe gluing -/

/-- A nonnegative rational squeezed above by zero is semantically zero. -/
private theorem eqv_zero_of_nonnegative_le_zero
    {value : Q'} (hnonnegative : (0 : Q') ≤ value)
    (hle : value ≤ (0 : Q')) : value ≈ 0 := by
  show value.num * ((0 : Q').den : Int) =
    (0 : Q').num * (value.den : Int)
  exact Int.le_antisymm hle hnonnegative

/-- A nonnegative rational that is not semantically zero is positive. -/
private theorem pos_of_nonnegative_not_eqv_zero
    {value : Q'} (hnonnegative : (0 : Q') ≤ value)
    (hne : ¬ value ≈ 0) : (0 : Q') < value := by
  have hnumNonnegative : (0 : Int) ≤ value.num :=
    (Q'.zero_le_iff_num_nonneg value).mp hnonnegative
  have hnumNe : value.num ≠ 0 := by
    intro hnum
    apply hne
    show value.num * (1 : Int) = (0 : Int) * (value.den : Int)
    simp [hnum]
  show (0 : Int) * (value.den : Int) < value.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

/-- The additive-rate gluing theorem remains valid when either rate is zero.
In a zero-rate branch, nonnegativity of the form makes the corresponding
vector radical, so all of its cross terms vanish exactly. -/
theorem GNSData.add_self_le_of_head_tail_nonnegative
    (D : GNSData) (a b : D.V) (q tau X Y : Q')
    (hq : (0 : Q') ≤ q) (htau : (0 : Q') ≤ tau)
    (hX : (0 : Q') ≤ X) (hY : (0 : Q') ≤ Y)
    (hhead : D.B a a ≤ q * X)
    (htail : D.B b b ≤ tau * Y) :
    D.B (D.add a b) (D.add a b) ≤
      (q + tau) * (X + Y) := by
  by_cases hqZero : q ≈ 0
  · have hqXZero : q * X ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right q 0 X hqZero)
        (Q'.zero_mul_eqv X)
    have hheadLeZero : D.B a a ≤ (0 : Q') :=
      OSReconstructionProgress.le_of_le_eqv hhead hqXZero
    have hheadZero : D.B a a ≈ 0 :=
      eqv_zero_of_nonnegative_le_zero (D.self_nonneg a) hheadLeZero
    have hcrossZero : D.B a b ≈ 0 :=
      D.radical_form_zero a b hheadZero
    have htwoCrossZero : 2 * D.B a b ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 2 _ _ hcrossZero)
        (Q'.mul_zero_eqv 2)
    have hleft :
        D.B (D.add a b) (D.add a b) ≈ D.B b b := by
      refine Q'.eqv_trans _ _ _ (GNSData.add_self_expand D a b) ?_
      refine Q'.eqv_trans _
        ((0 : Q') + 0 + D.B b b) _ ?_ ?_
      · exact QPoly.q_add_congr
          (QPoly.q_add_congr hheadZero htwoCrossZero)
          (Q'.eqv_refl _)
      · rw [Q'.zero_add', Q'.zero_add']
        exact Q'.eqv_refl _
    have hYLe : Y ≤ X + Y :=
      Q'.le_trans' _ (Y + X) _
        (Q'.add_le_self_of_nonneg Y X hX)
        (Q'.le_of_eqv (Q'.add_comm_eqv Y X))
    have htailGrow : D.B b b ≤ tau * (X + Y) :=
      Q'.le_trans' _ _ _ htail
        (Q'.mul_le_mul_of_nonneg_left Y (X + Y) tau hYLe htau)
    have hrhs : (q + tau) * (X + Y) ≈ tau * (X + Y) := by
      refine Q'.eqv_trans _
        (q * (X + Y) + tau * (X + Y)) _
        (QPoly.q_add_mul q tau (X + Y)) ?_
      refine Q'.eqv_trans _
        (0 * (X + Y) + tau * (X + Y)) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.mul_eqv_congr_right q 0 (X + Y) hqZero)
          (Q'.eqv_refl _)
      · refine Q'.eqv_trans _
          (0 + tau * (X + Y)) _ ?_ ?_
        · exact QPoly.q_add_congr
            (Q'.zero_mul_eqv (X + Y)) (Q'.eqv_refl _)
        · exact QPoly.q_zero_add_eqv _
    exact OSReconstructionProgress.le_of_eqv_le hleft
      (OSReconstructionProgress.le_of_le_eqv htailGrow
        (Q'.eqv_symm hrhs))
  · by_cases htauZero : tau ≈ 0
    · have htauYZero : tau * Y ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right tau 0 Y htauZero)
          (Q'.zero_mul_eqv Y)
      have htailLeZero : D.B b b ≤ (0 : Q') :=
        OSReconstructionProgress.le_of_le_eqv htail htauYZero
      have htailZero : D.B b b ≈ 0 :=
        eqv_zero_of_nonnegative_le_zero (D.self_nonneg b) htailLeZero
      have hcrossZero : D.B a b ≈ 0 :=
        D.radical_form_zero_right a b htailZero
      have htwoCrossZero : 2 * D.B a b ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 2 _ _ hcrossZero)
          (Q'.mul_zero_eqv 2)
      have hleft :
          D.B (D.add a b) (D.add a b) ≈ D.B a a := by
        refine Q'.eqv_trans _ _ _ (GNSData.add_self_expand D a b) ?_
        refine Q'.eqv_trans _
          ((D.B a a + 0) + 0) _ ?_ ?_
        · exact QPoly.q_add_congr
            (QPoly.q_add_congr (Q'.eqv_refl _) htwoCrossZero)
            htailZero
        · rw [Q'.add_zero', Q'.add_zero']
          exact Q'.eqv_refl _
      have hXLe : X ≤ X + Y := Q'.add_le_self_of_nonneg X Y hY
      have hheadGrow : D.B a a ≤ q * (X + Y) :=
        Q'.le_trans' _ _ _ hhead
          (Q'.mul_le_mul_of_nonneg_left X (X + Y) q hXLe hq)
      have hrhs : (q + tau) * (X + Y) ≈ q * (X + Y) := by
        refine Q'.eqv_trans _
          (q * (X + Y) + tau * (X + Y)) _
          (QPoly.q_add_mul q tau (X + Y)) ?_
        refine Q'.eqv_trans _
          (q * (X + Y) + 0 * (X + Y)) _ ?_ ?_
        · exact QPoly.q_add_congr
            (Q'.eqv_refl _)
            (Q'.mul_eqv_congr_right tau 0 (X + Y) htauZero)
        · refine Q'.eqv_trans _
            (q * (X + Y) + 0) _ ?_ ?_
          · exact QPoly.q_add_congr
              (Q'.eqv_refl _) (Q'.zero_mul_eqv (X + Y))
          · exact QPoly.q_add_zero_eqv _
      exact OSReconstructionProgress.le_of_eqv_le hleft
        (OSReconstructionProgress.le_of_le_eqv hheadGrow
          (Q'.eqv_symm hrhs))
    · exact GNSData.add_self_le_of_head_tail D a b q tau X Y
        (pos_of_nonnegative_not_eqv_zero hq hqZero)
        (pos_of_nonnegative_not_eqv_zero htau htauZero)
        hhead htail

end YMGap.Continuum.FinitePositiveFormHeadTailGluing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.FinitePositiveFormHeadTailGluing.two_cross_le_tail_head_budget_of_nonnegQuad
#print axioms
  YMGap.Continuum.FinitePositiveFormHeadTailGluing.PreInnerForm.two_cross_le_tail_head_budget
#print axioms
  YMGap.Continuum.FinitePositiveFormHeadTailGluing.GNSData.add_self_expand
#print axioms
  YMGap.Continuum.FinitePositiveFormHeadTailGluing.GNSData.add_self_le_of_head_tail
#print axioms
  YMGap.Continuum.FinitePositiveFormHeadTailGluing.GNSData.add_self_le_of_head_tail_nonnegative
