/-
# Nine-term algebra for the first multi-reserve repair

Eight sharp-capacity long codes can each repeat seven of the eight long-arm
activities, omitting a different one.  The short square is the ninth code.
Two of the long codes additionally carry one short-arm activity.  The
resulting exponent vectors have barycentric weights `7/15` for the short
square and `1/15` for each long code, exactly reproducing the source
monomial.  A constructive finite-max argument converts that exponent identity
into an unweighted sum bound.
-/

import YMGap.Continuum.XiExceptionalExternalReserveLimitFence
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.XiExceptionalMultiReserveAlgebra

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalWeightedInjection

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

def qProd : List Q' → Q'
  | [] => 1
  | x :: xs => x * qProd xs

private theorem q_le_of_lt {a b : Q'} (h : a < b) : a ≤ b := by
  exact Int.le_of_lt h

private theorem q_lt_of_not_ge {a b : Q'} (h : ¬ b ≤ a) : a < b := by
  exact Int.not_le.mp h

private theorem q_le_of_not_lt {a b : Q'} (h : ¬ a < b) : b ≤ a := by
  exact Int.not_lt.mp h

private theorem q_mul_lt_mul_of_pos_left {a b c : Q'}
    (hc : (0 : Q') < c) (hab : a < b) : c * a < c * b := by
  show (c * a).num * ((c * b).den : Int) <
    (c * b).num * ((c * a).den : Int)
  rw [show (c * a).num = c.num * a.num from rfl,
    show (c * b).num = c.num * b.num from rfl,
    Q'.mul_den_cast c b, Q'.mul_den_cast c a]
  have hcn : 0 < c.num := Q'.num_pos_of_pos hc
  have habn : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have e1 : (c.num * a.num) * ((c.den : Int) * (b.den : Int)) =
      (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
  have e2 : (c.num * b.num) * ((c.den : Int) * (a.den : Int)) =
      (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
  rw [e1, e2]
  exact Int.mul_lt_mul_of_pos_left habn
    (Int.mul_pos hcn (by exact_mod_cast c.den_pos))

private theorem qProd_nonnegative : ∀ (xs : List Q'),
    (∀ x, x ∈ xs → (0 : Q') ≤ x) → (0 : Q') ≤ qProd xs
  | [], _ => by decide
  | x :: xs, h =>
      Q'.mul_nonneg _ _ (h x List.mem_cons_self)
        (qProd_nonnegative xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem qProd_lt_pow_of_all_lt
    (x : Q') (hx : (0 : Q') < x) : ∀ (xs : List Q'),
    (∀ a, a ∈ xs → (0 : Q') ≤ a) →
    (∀ a, a ∈ xs → a < x) →
    xs ≠ [] → qProd xs < x ^ xs.length
  | [], _, _, hne => False.elim (hne rfl)
  | [a], hnonneg, hlt, _ => by
      rw [show [a].length = 1 by rfl, Q'.pow_succ, Q'.pow_zero]
      show (a * 1).num * ((x * 1).den : Int) <
        (x * 1).num * ((a * 1).den : Int)
      have honeNum : (1 : Q').num = 1 := rfl
      have honeDen : (1 : Q').den = 1 := rfl
      simpa [Q'.mul_num_cast, Q'.mul_den_cast, honeNum, honeDen] using
        hlt a List.mem_cons_self
  | a :: b :: xs, hnonneg, hlt, _ => by
      have htailNonneg : (0 : Q') ≤ qProd (b :: xs) :=
        qProd_nonnegative (b :: xs)
          (fun y hy => hnonneg y (List.mem_cons_of_mem a hy))
      have htailLt : qProd (b :: xs) < x ^ (b :: xs).length :=
        qProd_lt_pow_of_all_lt x hx (b :: xs)
          (fun y hy => hnonneg y (List.mem_cons_of_mem a hy))
          (fun y hy => hlt y (List.mem_cons_of_mem a hy)) (by simp)
      have hfirst : a * qProd (b :: xs) ≤ x * qProd (b :: xs) :=
        Q'.mul_le_mul_of_nonneg_right a x (qProd (b :: xs))
          (q_le_of_lt (hlt a List.mem_cons_self)) htailNonneg
      have hsecond : x * qProd (b :: xs) <
          x * (x ^ (b :: xs).length) :=
        q_mul_lt_mul_of_pos_left hx htailLt
      exact Q'.lt_of_le_of_lt hfirst (by
        simpa [qProd, Q'.pow] using hsecond)

private theorem member_le_qListSum_of_nonnegative
    (x : Q') : ∀ (xs : List Q'), x ∈ xs →
    (∀ y, y ∈ xs → (0 : Q') ≤ y) → x ≤ qListSum id xs
  | [], hmem, _ => by cases hmem
  | y :: ys, hmem, hnonneg => by
      rcases List.mem_cons.mp hmem with hxy | htail
      · subst y
        exact Q'.add_le_self_of_nonneg x (qListSum id ys)
          (qListSum_nonnegative id ys
            (fun z hz => hnonneg z (List.mem_cons_of_mem x hz)))
      · have ih := member_le_qListSum_of_nonnegative x ys htail
          (fun z hz => hnonneg z (List.mem_cons_of_mem y hz))
        have hadd : qListSum id ys ≤ qListSum id ys + y :=
          Q'.add_le_self_of_nonneg (qListSum id ys) y
            (hnonneg y List.mem_cons_self)
        exact Q'.le_trans' _ _ _ ih
          (Q'.le_trans' _ _ _ hadd
            (Q'.le_of_eqv (Q'.add_comm_eqv (qListSum id ys) y)))

/-- If a nonnegative `x` to the number of factors equals their product, one
factor is at least `x`. -/
theorem exists_factor_ge_of_pow_eqv_qProd
    (x : Q') (xs : List Q')
    (hx : (0 : Q') ≤ x)
    (hnonneg : ∀ y, y ∈ xs → (0 : Q') ≤ y)
    (hne : xs ≠ [])
    (hprod : x ^ xs.length ≈ qProd xs) :
    ∃ y, y ∈ xs ∧ x ≤ y := by
  cases hx0 : decide ((0 : Q') < x) with
  | true =>
      have hxpos : (0 : Q') < x := of_decide_eq_true hx0
      by_cases hexists : ∃ y, y ∈ xs ∧ x ≤ y
      · exact hexists
      · have hallLt : ∀ y, y ∈ xs → y < x := by
          intro y hy
          exact q_lt_of_not_ge (fun hxy => hexists ⟨y, hy, hxy⟩)
        have hlt := qProd_lt_pow_of_all_lt x hxpos xs hnonneg hallLt hne
        have hle : x ^ xs.length ≤ qProd xs := Q'.le_of_eqv hprod
        exact False.elim (Int.not_lt_of_ge hle hlt)
  | false =>
      have hnpos : ¬ (0 : Q') < x := of_decide_eq_false hx0
      have hxle0 : x ≤ 0 := q_le_of_not_lt hnpos
      cases xs with
      | nil => exact False.elim (hne rfl)
      | cons y ys =>
          exact ⟨y, List.mem_cons_self,
            Q'.le_trans' _ _ _ hxle0 (hnonneg y List.mem_cons_self)⟩

/-- The witnessed factor belongs to the unweighted sum. -/
theorem le_sum_of_pow_eqv_qProd
    (x : Q') (xs : List Q')
    (hx : (0 : Q') ≤ x)
    (hnonneg : ∀ y, y ∈ xs → (0 : Q') ≤ y)
    (hne : xs ≠ [])
    (hprod : x ^ xs.length ≈ qProd xs) :
    x ≤ qListSum id xs := by
  obtain ⟨y, hy, hxy⟩ := exists_factor_ge_of_pow_eqv_qProd
    x xs hx hnonneg hne hprod
  exact Q'.le_trans' _ _ _ hxy
    (member_le_qListSum_of_nonnegative y xs hy hnonneg)

def shortSquare (a1 a2 : Q') : Q' :=
  (a1 * a2) * (a1 * a2)

def longProduct (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  (((x4 * x5) * (x6 * x7)) * (x8 * x9)) * (x10 * x11)

def omit4 (a1 x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  a1 * (longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x5 * x6) * (x7 * x8)) * (x9 * (x10 * x11))))

def omit5 (a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  a2 * (longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x6) * (x7 * x8)) * (x9 * (x10 * x11))))

def omit6 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x7 * x8)) * (x9 * (x10 * x11)))

def omit7 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x6 * x8)) * (x9 * (x10 * x11)))

def omit8 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x6 * x7)) * (x9 * (x10 * x11)))

def omit9 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x6 * x7)) * (x8 * (x10 * x11)))

def omit10 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x6 * x7)) * (x8 * (x9 * x11)))

def omit11 (x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  longProduct x4 x5 x6 x7 x8 x9 x10 x11 *
    (((x4 * x5) * (x6 * x7)) * (x8 * (x9 * x10)))

def augmentedPayers
    (a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q') : List Q' :=
  [shortSquare a1 a2,
    omit4 a1 x4 x5 x6 x7 x8 x9 x10 x11,
    omit5 a2 x4 x5 x6 x7 x8 x9 x10 x11,
    omit6 x4 x5 x6 x7 x8 x9 x10 x11,
    omit7 x4 x5 x6 x7 x8 x9 x10 x11,
    omit8 x4 x5 x6 x7 x8 x9 x10 x11,
    omit9 x4 x5 x6 x7 x8 x9 x10 x11,
    omit10 x4 x5 x6 x7 x8 x9 x10 x11,
    omit11 x4 x5 x6 x7 x8 x9 x10 x11]

def augmentedFactors
    (a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q') : List Q' :=
  [shortSquare a1 a2, shortSquare a1 a2, shortSquare a1 a2,
    shortSquare a1 a2, shortSquare a1 a2, shortSquare a1 a2,
    shortSquare a1 a2,
    omit4 a1 x4 x5 x6 x7 x8 x9 x10 x11,
    omit5 a2 x4 x5 x6 x7 x8 x9 x10 x11,
    omit6 x4 x5 x6 x7 x8 x9 x10 x11,
    omit7 x4 x5 x6 x7 x8 x9 x10 x11,
    omit8 x4 x5 x6 x7 x8 x9 x10 x11,
    omit9 x4 x5 x6 x7 x8 x9 x10 x11,
    omit10 x4 x5 x6 x7 x8 x9 x10 x11,
    omit11 x4 x5 x6 x7 x8 x9 x10 x11]

def sourceInterior
    (a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q') : Q' :=
  (a1 * a2) * longProduct x4 x5 x6 x7 x8 x9 x10 x11

private theorem pairedSeven_nonnegative
    (a b c d e f g : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hc : (0 : Q') ≤ c) (hd : (0 : Q') ≤ d)
    (he : (0 : Q') ≤ e) (hf : (0 : Q') ≤ f)
    (hg : (0 : Q') ≤ g) :
    (0 : Q') ≤ (((a * b) * (c * d)) * (e * (f * g))) := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha hb)
      (Q'.mul_nonneg _ _ hc hd))
    (Q'.mul_nonneg _ _ he (Q'.mul_nonneg _ _ hf hg))

private theorem pairedEight_nonnegative
    (a b c d e f g h : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hc : (0 : Q') ≤ c) (hd : (0 : Q') ≤ d)
    (he : (0 : Q') ≤ e) (hf : (0 : Q') ≤ f)
    (hg : (0 : Q') ≤ g) (hh : (0 : Q') ≤ h) :
    (0 : Q') ≤ (((a * b) * (c * d)) * (e * f)) * (g * h) := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha hb)
        (Q'.mul_nonneg _ _ hc hd))
      (Q'.mul_nonneg _ _ he hf))
    (Q'.mul_nonneg _ _ hg hh)

theorem augmented_exponent_identity
    (a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q') :
    sourceInterior a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 ^ 15 ≈
      qProd (augmentedFactors a1 a2 x4 x5 x6 x7 x8 x9 x10 x11) := by
  simp only [sourceInterior, shortSquare, longProduct, augmentedFactors,
    omit4, omit5, omit6, omit7, omit8, omit9, omit10, omit11, qProd,
    Q'.pow_succ, Q'.pow_zero]
  ring_qeqv

theorem augmentedPayers_pay
    (a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 : Q')
    (ha1 : (0 : Q') ≤ a1) (ha2 : (0 : Q') ≤ a2)
    (h4 : (0 : Q') ≤ x4) (h5 : (0 : Q') ≤ x5)
    (h6 : (0 : Q') ≤ x6) (h7 : (0 : Q') ≤ x7)
    (h8 : (0 : Q') ≤ x8) (h9 : (0 : Q') ≤ x9)
    (h10 : (0 : Q') ≤ x10) (h11 : (0 : Q') ≤ x11) :
    sourceInterior a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 ≤
      qListSum id
        (augmentedPayers a1 a2 x4 x5 x6 x7 x8 x9 x10 x11) := by
  let source := sourceInterior a1 a2 x4 x5 x6 x7 x8 x9 x10 x11
  let factors := augmentedFactors a1 a2 x4 x5 x6 x7 x8 x9 x10 x11
  have hshort : (0 : Q') ≤ shortSquare a1 a2 := by
    unfold shortSquare
    exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha1 ha2)
      (Q'.mul_nonneg _ _ ha1 ha2)
  have hlong : (0 : Q') ≤
      longProduct x4 x5 x6 x7 x8 x9 x10 x11 := by
    exact pairedEight_nonnegative x4 x5 x6 x7 x8 x9 x10 x11
      h4 h5 h6 h7 h8 h9 h10 h11
  have hOmit4 : (0 : Q') ≤
      omit4 a1 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit4
    exact Q'.mul_nonneg _ _ ha1 (Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x5 x6 x7 x8 x9 x10 x11
        h5 h6 h7 h8 h9 h10 h11))
  have hOmit5 : (0 : Q') ≤
      omit5 a2 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit5
    exact Q'.mul_nonneg _ _ ha2 (Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x6 x7 x8 x9 x10 x11
        h4 h6 h7 h8 h9 h10 h11))
  have hOmit6 : (0 : Q') ≤
      omit6 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit6
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x7 x8 x9 x10 x11
        h4 h5 h7 h8 h9 h10 h11)
  have hOmit7 : (0 : Q') ≤
      omit7 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit7
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x6 x8 x9 x10 x11
        h4 h5 h6 h8 h9 h10 h11)
  have hOmit8 : (0 : Q') ≤
      omit8 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit8
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x6 x7 x9 x10 x11
        h4 h5 h6 h7 h9 h10 h11)
  have hOmit9 : (0 : Q') ≤
      omit9 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit9
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x6 x7 x8 x10 x11
        h4 h5 h6 h7 h8 h10 h11)
  have hOmit10 : (0 : Q') ≤
      omit10 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit10
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x6 x7 x8 x9 x11
        h4 h5 h6 h7 h8 h9 h11)
  have hOmit11 : (0 : Q') ≤
      omit11 x4 x5 x6 x7 x8 x9 x10 x11 := by
    unfold omit11
    exact Q'.mul_nonneg _ _ hlong
      (pairedSeven_nonnegative x4 x5 x6 x7 x8 x9 x10
        h4 h5 h6 h7 h8 h9 h10)
  have hsource : (0 : Q') ≤ source := by
    unfold source sourceInterior
    exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha1 ha2) hlong
  have hfactors : ∀ y, y ∈ factors → (0 : Q') ≤ y := by
    intro y hy
    simp [factors, augmentedFactors] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  have hnonempty : factors ≠ [] := by
    simp [factors, augmentedFactors]
  have hpower : source ^ factors.length ≈ qProd factors := by
    change sourceInterior a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 ^ 15 ≈
      qProd (augmentedFactors a1 a2 x4 x5 x6 x7 x8 x9 x10 x11)
    exact augmented_exponent_identity a1 a2 x4 x5 x6 x7 x8 x9 x10 x11
  obtain ⟨y, hy, hsourceY⟩ := exists_factor_ge_of_pow_eqv_qProd
    source factors hsource hfactors hnonempty hpower
  have hypayer : y ∈
      augmentedPayers a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 := by
    simpa [factors, augmentedFactors, augmentedPayers] using hy
  have hpayersNonneg : ∀ z,
      z ∈ augmentedPayers a1 a2 x4 x5 x6 x7 x8 x9 x10 x11 →
        (0 : Q') ≤ z := by
    intro z hz
    apply hfactors z
    simpa [factors, augmentedFactors, augmentedPayers] using hz
  exact Q'.le_trans' _ _ _ hsourceY
    (member_le_qListSum_of_nonnegative y
      (augmentedPayers a1 a2 x4 x5 x6 x7 x8 x9 x10 x11)
      hypayer hpayersNonneg)

#print axioms exists_factor_ge_of_pow_eqv_qProd
#print axioms le_sum_of_pow_eqv_qProd
#print axioms augmented_exponent_identity
#print axioms augmentedPayers_pay

end YMGap.Continuum.XiExceptionalMultiReserveAlgebra
