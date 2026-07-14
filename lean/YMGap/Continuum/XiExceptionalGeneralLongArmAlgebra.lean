/-
# Uniform algebra for one short pair and an arbitrary long arm

Write the long-pair count as `n = k + 3`.  There are `n` even and `n` odd
long-interior activities.  For every long variable we use one payer which
contains the base long product, the complete opposite-parity product, and
three extra copies of the selected variable.  Thus the `2n` long payers give
every long variable exactly `n + 3` duplicate incidences.  The first `k`
payers on each side also carry the compatible short variable.  Together
with `n + 3 = k + 6` copies of the short square, every variable has exponent

  `3n + 3 = 3k + 12`.

The exponent identity and the resulting unweighted-sum payment are proved
for arbitrary exact rational activity lists; no numerical input is used.
-/

import YMGap.Continuum.XiExceptionalMultiReserveAlgebra

namespace YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalMultiReserveAlgebra

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

def qCube (x : Q') : Q' := (x * x) * x

def repeatFactor : Nat → Q' → List Q'
  | 0, _ => []
  | n + 1, x => x :: repeatFactor n x

/-- Multiply the first `k` entries by a tag. -/
def tagPrefix (tag : Q') : Nat → List Q' → List Q'
  | 0, xs => xs
  | _ + 1, [] => []
  | k + 1, x :: xs => (tag * x) :: tagPrefix tag k xs

/-- One payer per selected long variable. -/
def sidePayers (long opposite : Q') (xs : List Q') : List Q' :=
  xs.map (fun x => long * (opposite * qCube x))

def uniformPayers (k : Nat) (a1 a2 : Q')
    (even odd : List Q') : List Q' :=
  shortSquare a1 a2 ::
    (tagPrefix a1 k (sidePayers (qProd even * qProd odd) (qProd odd) even) ++
      tagPrefix a2 k
        (sidePayers (qProd even * qProd odd) (qProd even) odd))

def uniformFactors (k : Nat) (a1 a2 : Q')
    (even odd : List Q') : List Q' :=
  repeatFactor (k + 6) (shortSquare a1 a2) ++
    (tagPrefix a1 k (sidePayers (qProd even * qProd odd) (qProd odd) even) ++
      tagPrefix a2 k
        (sidePayers (qProd even * qProd odd) (qProd even) odd))

def uniformSource (a1 a2 : Q') (even odd : List Q') : Q' :=
  (a1 * a2) * (qProd even * qProd odd)

private theorem qProd_append_eqv : ∀ xs ys : List Q',
    qProd (xs ++ ys) ≈ qProd xs * qProd ys
  | [], ys => by
      simp only [List.nil_append, qProd]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | x :: xs, ys => by
      simp only [List.cons_append, qProd]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (qProd_append_eqv xs ys)) ?_
      ring_qeqv

private theorem qProd_repeatFactor_eqv (x : Q') : ∀ n,
    qProd (repeatFactor n x) ≈ x ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      simp only [repeatFactor, qProd, Q'.pow_succ]
      exact Q'.mul_eqv_congr_left x _ _ (qProd_repeatFactor_eqv x n)

private theorem tagPrefix_length (tag : Q') : ∀ k xs,
    k ≤ xs.length → (tagPrefix tag k xs).length = xs.length
  | 0, xs, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
      simp only [List.length_cons] at h
      simp only [tagPrefix, List.length_cons]
      rw [tagPrefix_length tag k xs (by omega)]

private theorem qProd_tagPrefix_eqv (tag : Q') : ∀ k xs,
    k ≤ xs.length →
      qProd (tagPrefix tag k xs) ≈ tag ^ k * qProd xs
  | 0, xs, _ => by
      simp only [tagPrefix, Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | _ + 1, [], h => by simp at h
  | k + 1, x :: xs, h => by
      simp only [List.length_cons] at h
      simp only [tagPrefix, qProd, Q'.pow_succ]
      refine Q'.eqv_trans _
        ((tag * x) * (tag ^ k * qProd xs)) _
        (Q'.mul_eqv_congr_left (tag * x) _ _
          (qProd_tagPrefix_eqv tag k xs (by omega))) ?_
      ring_qeqv

private theorem sidePayers_length (long opposite : Q') (xs : List Q') :
    (sidePayers long opposite xs).length = xs.length := by
  simp [sidePayers]

private theorem qProd_sidePayers_eqv (long opposite : Q') : ∀ xs,
    qProd (sidePayers long opposite xs) ≈
      (long * opposite) ^ xs.length * qProd xs ^ 3
  | [] => by
      simp only [sidePayers, List.map_nil, qProd, List.length_nil,
        Q'.pow_zero]
      ring_qeqv
  | x :: xs => by
      simp only [sidePayers, List.map_cons, qProd, List.length_cons,
        Q'.pow_succ, qCube]
      refine Q'.eqv_trans _
        ((long * (opposite * ((x * x) * x))) *
          ((long * opposite) ^ xs.length * qProd xs ^ 3)) _
        (Q'.mul_eqv_congr_left
          (long * (opposite * ((x * x) * x))) _ _
          (qProd_sidePayers_eqv long opposite xs)) ?_
      refine Q'.eqv_trans _
        (((long * opposite) * (long * opposite) ^ xs.length) *
          (((x * x) * x) * qProd xs ^ 3)) _ ?_ ?_
      · ring_qeqv
      simp only [Q'.pow_succ, Q'.pow_zero]
      ring_qeqv

private theorem qProd_taggedSide_eqv
    (tag long opposite : Q') (k : Nat) (xs : List Q')
    (hk : k ≤ xs.length) :
    qProd (tagPrefix tag k (sidePayers long opposite xs)) ≈
      tag ^ k * ((long * opposite) ^ xs.length * qProd xs ^ 3) := by
  refine Q'.eqv_trans _ _ _
    (qProd_tagPrefix_eqv tag k (sidePayers long opposite xs)
      (by rw [sidePayers_length]; exact hk)) ?_
  exact Q'.mul_eqv_congr_left (tag ^ k) _ _
    (qProd_sidePayers_eqv long opposite xs)

private theorem repeatFactor_length (n : Nat) (x : Q') :
    (repeatFactor n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatFactor, ih]

theorem uniformFactors_length (k : Nat) (a1 a2 : Q')
    (even odd : List Q')
    (heven : even.length = k + 3) (hodd : odd.length = k + 3) :
    (uniformFactors k a1 a2 even odd).length = 3 * k + 12 := by
  unfold uniformFactors
  rw [List.length_append, repeatFactor_length,
    List.length_append,
    tagPrefix_length a1 k _ (by rw [sidePayers_length, heven]; omega),
    tagPrefix_length a2 k _ (by rw [sidePayers_length, hodd]; omega),
    sidePayers_length, sidePayers_length, heven, hodd]
  omega

private theorem mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem pow_mul_eqv (a b : Q') : ∀ n : Nat,
    (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => by
      simp only [Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | n + 1 => by
      simp only [Q'.pow_succ]
      refine Q'.eqv_trans _
        ((a * b) * (a ^ n * b ^ n)) _
        (Q'.mul_eqv_congr_left (a * b) _ _ (pow_mul_eqv a b n)) ?_
      ring_qeqv

private theorem pow_add_eqv (x : Q') (a : Nat) : ∀ b,
    x ^ (a + b) ≈ x ^ a * x ^ b
  | 0 => by
      simp only [Nat.add_zero, Q'.pow_zero]
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [Q'.pow_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (pow_add_eqv x a b)) ?_
      ring_qeqv

private theorem short_power_blocks (x : Q') (k : Nat) :
    (x ^ (k + 6) * x ^ (k + 6)) * x ^ k ≈
      x ^ (3 * k + 12) := by
  refine Q'.eqv_trans _ (x ^ ((k + 6) + (k + 6)) * x ^ k) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (x ^ k)
      (Q'.eqv_symm (pow_add_eqv x (k + 6) (k + 6)))
  refine Q'.eqv_trans _ (x ^ ((k + 6) + (k + 6) + k)) _ ?_ ?_
  · exact Q'.eqv_symm (pow_add_eqv x ((k + 6) + (k + 6)) k)
  · rw [show (k + 6) + (k + 6) + k = 3 * k + 12 by omega]
    exact Q'.eqv_refl _

private theorem long_power_blocks (x : Q') (k : Nat) :
    ((x ^ (k + 3) * x ^ (k + 3)) * x ^ (k + 3)) * x ^ 3 ≈
      x ^ (3 * k + 12) := by
  refine Q'.eqv_trans _
    ((x ^ ((k + 3) + (k + 3)) * x ^ (k + 3)) * x ^ 3) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (x ^ 3)
      (Q'.mul_eqv_congr_right _ _ (x ^ (k + 3))
        (Q'.eqv_symm (pow_add_eqv x (k + 3) (k + 3))))
  refine Q'.eqv_trans _
    (x ^ ((k + 3) + (k + 3) + (k + 3)) * x ^ 3) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (x ^ 3)
      (Q'.eqv_symm
        (pow_add_eqv x ((k + 3) + (k + 3)) (k + 3)))
  refine Q'.eqv_trans _
    (x ^ ((k + 3) + (k + 3) + (k + 3) + 3)) _ ?_ ?_
  · exact Q'.eqv_symm
      (pow_add_eqv x ((k + 3) + (k + 3) + (k + 3)) 3)
  · rw [show (k + 3) + (k + 3) + (k + 3) + 3 =
      3 * k + 12 by omega]
    exact Q'.eqv_refl _

private theorem abstract_exponent_identity
    (a1 a2 E O : Q') (k : Nat) :
    (((a1 * a2) * (E * O)) ^ (3 * k + 12)) ≈
      shortSquare a1 a2 ^ (k + 6) *
        ((a1 ^ k * (((E * O) * O) ^ (k + 3) * E ^ 3)) *
          (a2 ^ k * (((E * O) * E) ^ (k + 3) * O ^ 3))) := by
  have hsource : (((a1 * a2) * (E * O)) ^ (3 * k + 12)) ≈
      (a1 ^ (3 * k + 12) * a2 ^ (3 * k + 12)) *
        (E ^ (3 * k + 12) * O ^ (3 * k + 12)) := by
    refine Q'.eqv_trans _
      ((a1 * a2) ^ (3 * k + 12) * (E * O) ^ (3 * k + 12)) _
      (pow_mul_eqv (a1 * a2) (E * O) (3 * k + 12)) ?_
    exact mul_congr
      (pow_mul_eqv a1 a2 (3 * k + 12))
      (pow_mul_eqv E O (3 * k + 12))
  have hshort : shortSquare a1 a2 ^ (k + 6) ≈
      (a1 ^ (k + 6) * a2 ^ (k + 6)) *
        (a1 ^ (k + 6) * a2 ^ (k + 6)) := by
    unfold shortSquare
    refine Q'.eqv_trans _ _ _
      (pow_mul_eqv (a1 * a2) (a1 * a2) (k + 6)) ?_
    exact mul_congr
      (pow_mul_eqv a1 a2 (k + 6))
      (pow_mul_eqv a1 a2 (k + 6))
  have hevenBlock : (((E * O) * O) ^ (k + 3) * E ^ 3) ≈
      ((E ^ (k + 3) * O ^ (k + 3)) * O ^ (k + 3)) * E ^ 3 := by
    exact Q'.mul_eqv_congr_right _ _ (E ^ 3)
      (Q'.eqv_trans _ _ _
        (pow_mul_eqv (E * O) O (k + 3))
        (Q'.mul_eqv_congr_right _ _ (O ^ (k + 3))
          (pow_mul_eqv E O (k + 3))))
  have hoddBlock : (((E * O) * E) ^ (k + 3) * O ^ 3) ≈
      ((E ^ (k + 3) * O ^ (k + 3)) * E ^ (k + 3)) * O ^ 3 := by
    exact Q'.mul_eqv_congr_right _ _ (O ^ 3)
      (Q'.eqv_trans _ _ _
        (pow_mul_eqv (E * O) E (k + 3))
        (Q'.mul_eqv_congr_right _ _ (E ^ (k + 3))
          (pow_mul_eqv E O (k + 3))))
  have hrhs : shortSquare a1 a2 ^ (k + 6) *
        ((a1 ^ k * (((E * O) * O) ^ (k + 3) * E ^ 3)) *
          (a2 ^ k * (((E * O) * E) ^ (k + 3) * O ^ 3))) ≈
      (a1 ^ (3 * k + 12) * a2 ^ (3 * k + 12)) *
        (E ^ (3 * k + 12) * O ^ (3 * k + 12)) := by
    refine Q'.eqv_trans _
      (((a1 ^ (k + 6) * a2 ^ (k + 6)) *
          (a1 ^ (k + 6) * a2 ^ (k + 6))) *
        ((a1 ^ k *
          (((E ^ (k + 3) * O ^ (k + 3)) * O ^ (k + 3)) * E ^ 3)) *
        (a2 ^ k *
          (((E ^ (k + 3) * O ^ (k + 3)) * E ^ (k + 3)) * O ^ 3)))) _ ?_ ?_
    · exact mul_congr hshort
        (mul_congr
          (Q'.mul_eqv_congr_left (a1 ^ k) _ _ hevenBlock)
          (Q'.mul_eqv_congr_left (a2 ^ k) _ _ hoddBlock))
    refine Q'.eqv_trans _
      (((a1 ^ (k + 6) * a1 ^ (k + 6)) * a1 ^ k) *
        ((a2 ^ (k + 6) * a2 ^ (k + 6)) * a2 ^ k) *
        ((((E ^ (k + 3) * E ^ (k + 3)) * E ^ (k + 3)) * E ^ 3) *
          (((O ^ (k + 3) * O ^ (k + 3)) * O ^ (k + 3)) * O ^ 3))) _ ?_ ?_
    · ring_qeqv
    exact mul_congr
      (mul_congr
        (short_power_blocks a1 k) (short_power_blocks a2 k))
      (mul_congr
        (long_power_blocks E k) (long_power_blocks O k))
  exact Q'.eqv_trans _ _ _ hsource (Q'.eqv_symm hrhs)

theorem uniform_exponent_identity
    (k : Nat) (a1 a2 : Q') (even odd : List Q')
    (heven : even.length = k + 3) (hodd : odd.length = k + 3) :
    uniformSource a1 a2 even odd ^
        (uniformFactors k a1 a2 even odd).length ≈
      qProd (uniformFactors k a1 a2 even odd) := by
  rw [uniformFactors_length k a1 a2 even odd heven hodd]
  unfold uniformSource uniformFactors
  refine Q'.eqv_trans _
    (shortSquare a1 a2 ^ (k + 6) *
      ((a1 ^ k * ((((qProd even * qProd odd) * qProd odd) ^ (k + 3)) *
        qProd even ^ 3)) *
      (a2 ^ k * ((((qProd even * qProd odd) * qProd even) ^ (k + 3)) *
        qProd odd ^ 3)))) _
    (abstract_exponent_identity a1 a2 (qProd even) (qProd odd) k) ?_
  let rep := repeatFactor (k + 6) (shortSquare a1 a2)
  let ep := tagPrefix a1 k
    (sidePayers (qProd even * qProd odd) (qProd odd) even)
  let op := tagPrefix a2 k
    (sidePayers (qProd even * qProd odd) (qProd even) odd)
  have hrep : qProd rep ≈ shortSquare a1 a2 ^ (k + 6) := by
    exact qProd_repeatFactor_eqv _ _
  have hep : qProd ep ≈
      a1 ^ k * ((((qProd even * qProd odd) * qProd odd) ^ (k + 3)) *
        qProd even ^ 3) := by
    simpa only [ep, heven] using
      (qProd_taggedSide_eqv a1 (qProd even * qProd odd)
        (qProd odd) k even (by rw [heven]; omega))
  have hop : qProd op ≈
      a2 ^ k * ((((qProd even * qProd odd) * qProd even) ^ (k + 3)) *
        qProd odd ^ 3) := by
    simpa only [op, hodd] using
      (qProd_taggedSide_eqv a2 (qProd even * qProd odd)
        (qProd even) k odd (by rw [hodd]; omega))
  have hcomponents :
      shortSquare a1 a2 ^ (k + 6) *
        ((a1 ^ k * ((((qProd even * qProd odd) * qProd odd) ^ (k + 3)) *
          qProd even ^ 3)) *
        (a2 ^ k * ((((qProd even * qProd odd) * qProd even) ^ (k + 3)) *
          qProd odd ^ 3))) ≈
      qProd rep * (qProd ep * qProd op) :=
    mul_congr (Q'.eqv_symm hrep)
      (mul_congr (Q'.eqv_symm hep) (Q'.eqv_symm hop))
  refine Q'.eqv_trans _ _ _ hcomponents ?_
  have happ : qProd (rep ++ (ep ++ op)) ≈
      qProd rep * (qProd ep * qProd op) :=
    Q'.eqv_trans _ _ _ (qProd_append_eqv rep (ep ++ op))
      (Q'.mul_eqv_congr_left (qProd rep) _ _
        (qProd_append_eqv ep op))
  exact Q'.eqv_symm happ

private theorem qProd_nonnegative_public : ∀ (xs : List Q'),
    (∀ x, x ∈ xs → (0 : Q') ≤ x) → (0 : Q') ≤ qProd xs
  | [], _ => by decide
  | x :: xs, h =>
      Q'.mul_nonneg _ _ (h x List.mem_cons_self)
        (qProd_nonnegative_public xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem mem_repeatFactor_eq {x y : Q'} : ∀ {n : Nat},
    y ∈ repeatFactor n x → y = x
  | 0, h => by cases h
  | _ + 1, h => by
      rcases List.mem_cons.mp h with h | h
      · exact h
      · exact mem_repeatFactor_eq h

private theorem member_le_sum_nonnegative
    (x : Q') : ∀ (xs : List Q'), x ∈ xs →
    (∀ y, y ∈ xs → (0 : Q') ≤ y) → x ≤ qListSum id xs
  | [], h, _ => by cases h
  | y :: ys, h, hn => by
      rcases List.mem_cons.mp h with hxy | ht
      · subst y
        exact Q'.add_le_self_of_nonneg x (qListSum id ys)
          (qListSum_nonnegative id ys
            (fun z hz => hn z (List.mem_cons_of_mem x hz)))
      · have ih := member_le_sum_nonnegative x ys ht
          (fun z hz => hn z (List.mem_cons_of_mem y hz))
        have hadd : qListSum id ys ≤ qListSum id ys + y :=
          Q'.add_le_self_of_nonneg _ _ (hn y List.mem_cons_self)
        exact Q'.le_trans' _ _ _ ih
          (Q'.le_trans' _ _ _ hadd
            (Q'.le_of_eqv (Q'.add_comm_eqv (qListSum id ys) y)))

private theorem sidePayers_nonnegative
    (long opposite : Q') (hlong : (0 : Q') ≤ long)
    (hopposite : (0 : Q') ≤ opposite)
    (xs : List Q') (hxs : ∀ x, x ∈ xs → (0 : Q') ≤ x) :
    ∀ y, y ∈ sidePayers long opposite xs → (0 : Q') ≤ y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact Q'.mul_nonneg _ _ hlong (Q'.mul_nonneg _ _ hopposite
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hxs x hx) (hxs x hx))
      (hxs x hx)))

private theorem tagPrefix_nonnegative
    (tag : Q') (htag : (0 : Q') ≤ tag) : ∀ k xs,
    (∀ x, x ∈ xs → (0 : Q') ≤ x) →
    ∀ y, y ∈ tagPrefix tag k xs → (0 : Q') ≤ y
  | 0, xs, h, y, hy => h y hy
  | _ + 1, [], _, y, hy => by cases hy
  | k + 1, x :: xs, h, y, hy => by
      rcases List.mem_cons.mp hy with rfl | htail
      · exact Q'.mul_nonneg _ _ htag (h x List.mem_cons_self)
      · exact tagPrefix_nonnegative tag htag k xs
          (fun z hz => h z (List.mem_cons_of_mem x hz)) y htail

theorem uniformPayers_pay
    (k : Nat) (a1 a2 : Q') (even odd : List Q')
    (heven : even.length = k + 3) (hodd : odd.length = k + 3)
    (ha1 : (0 : Q') ≤ a1) (ha2 : (0 : Q') ≤ a2)
    (hevenNonneg : ∀ x, x ∈ even → (0 : Q') ≤ x)
    (hoddNonneg : ∀ x, x ∈ odd → (0 : Q') ≤ x) :
    uniformSource a1 a2 even odd ≤
      qListSum id (uniformPayers k a1 a2 even odd) := by
  let factors := uniformFactors k a1 a2 even odd
  have hE : (0 : Q') ≤ qProd even :=
    qProd_nonnegative_public even hevenNonneg
  have hO : (0 : Q') ≤ qProd odd :=
    qProd_nonnegative_public odd hoddNonneg
  have hL : (0 : Q') ≤ qProd even * qProd odd :=
    Q'.mul_nonneg _ _ hE hO
  have hshort : (0 : Q') ≤ shortSquare a1 a2 := by
    unfold shortSquare
    exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha1 ha2)
      (Q'.mul_nonneg _ _ ha1 ha2)
  have hEvenSide : ∀ y,
      y ∈ sidePayers (qProd even * qProd odd) (qProd odd) even →
        (0 : Q') ≤ y :=
    sidePayers_nonnegative _ _ hL hO even hevenNonneg
  have hOddSide : ∀ y,
      y ∈ sidePayers (qProd even * qProd odd) (qProd even) odd →
        (0 : Q') ≤ y :=
    sidePayers_nonnegative _ _ hL hE odd hoddNonneg
  have hTaggedEven := tagPrefix_nonnegative a1 ha1 k _ hEvenSide
  have hTaggedOdd := tagPrefix_nonnegative a2 ha2 k _ hOddSide
  have hfactors : ∀ y, y ∈ factors → (0 : Q') ≤ y := by
    intro y hy
    simp only [factors, uniformFactors, List.mem_append] at hy
    rcases hy with hrepeated | hEven | hOdd
    · rw [mem_repeatFactor_eq hrepeated]
      exact hshort
    · exact hTaggedEven y hEven
    · exact hTaggedOdd y hOdd
  have hne : factors ≠ [] := by
    simp [factors, uniformFactors, repeatFactor]
  have hpower := uniform_exponent_identity k a1 a2 even odd heven hodd
  obtain ⟨y, hy, hsourceY⟩ := exists_factor_ge_of_pow_eqv_qProd
    (uniformSource a1 a2 even odd) factors hfactors hne hpower
  have hypayer : y ∈ uniformPayers k a1 a2 even odd := by
    simp only [factors, uniformFactors, uniformPayers, List.mem_append,
      List.mem_cons] at hy ⊢
    rcases hy with hrepeated | hEven | hOdd
    · left
      exact mem_repeatFactor_eq hrepeated
    · exact Or.inr (Or.inl hEven)
    · exact Or.inr (Or.inr hOdd)
  have hpayersNonneg : ∀ z, z ∈ uniformPayers k a1 a2 even odd →
      (0 : Q') ≤ z := by
    intro z hz
    simp only [uniformPayers, List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | hEven | hOdd
    · exact hshort
    · exact hTaggedEven z hEven
    · exact hTaggedOdd z hOdd
  exact Q'.le_trans' _ _ _ hsourceY
    (member_le_sum_nonnegative y
      (uniformPayers k a1 a2 even odd) hypayer hpayersNonneg)

#print axioms uniformFactors_length
#print axioms uniform_exponent_identity
#print axioms uniformPayers_pay

end YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra
