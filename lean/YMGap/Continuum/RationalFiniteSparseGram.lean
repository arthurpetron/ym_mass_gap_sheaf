/-
# Rational sparse Gram bounds without square roots

Signed pairwise Gram bounds are summed using a symmetric interference
relation and its finite row counts. Repeated labels are permitted: both
counts and sums count occurrences. The leading constant is the row bound,
while the complete family size multiplies only the off-interference error.

These are finite rational inequalities, not an interacting variance or
spectral-gap theorem. The physical consumer must supply the actual pair
bounds and the actual interference geometry.
-/

import YMGap.Continuum.Z4FiniteCylinderQuadraticStability
import YMGap.Continuum.FiniteBistochasticCarrierBalance
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.RationalFiniteSparseGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem square_reflect {a b : Q'} (hb : (0 : Q') ≤ b)
    (h : a*a ≤ b*b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  apply Int.not_lt.mp
  intro hba
  have hba' : b < a := hba
  have ha : (0 : Q') < a := Q'.lt_of_le_of_lt hb hba'
  have h1 : b*b ≤ a*b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hba') hb
  have h2 : a*b < a*a := Q'.mul_lt_mul_of_pos_left ha hba'
  exact (Int.not_lt.mpr h) (Q'.lt_of_le_of_lt h1 h2)

/-- A signed weighted Young bound. No sign assumption on `x` is needed. -/
theorem weighted_young {x r a b : Q'}
    (hr : (0 : Q') ≤ r) (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (h : x*x ≤ (r*r)*(a*b)) : 2*x ≤ r*(a+b) := by
  apply square_reflect (Q'.mul_nonneg _ _ hr (Q'.zero_le_add _ _ ha hb))
  have hstart : (2*x)*(2*x) ≈ 4*(x*x) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => x)
  have hend : 4*((r*r)*(a*b)) + (r*(a + -b))*(r*(a + -b)) ≈
      (r*(a+b))*(r*(a+b)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 4)
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
          (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))))
      (.mul (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 0) (.add (.var 1) (.var 2))))
      (by decide) (fun | 0 => r | 1 => a | _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 4 h (by decide))
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _))
        (Q'.le_of_eqv hend)))

/-- A constant finite sum with the cardinality on the right. -/
theorem listQSum_const {A : Type} (a : Q') (xs : List A) :
    listQSum (fun _ => a) xs ≈ a * Q'.ofNat xs.length := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr (fun _ => Q'.eqv_symm (Q'.mul_one_eqv a)) xs)
    (Q'.eqv_trans _ _ _ (listQSum_mul_left a (fun _ => 1) xs)
      (Q'.mul_eqv_congr_left a _ _ (listQSum_one_eqv_ofNat_length xs)))

private theorem mask_sum {A : Type} (test : A → Bool) (value : A → Q') :
    ∀ xs : List A,
      listQSum (fun i => if test i then value i else 0) xs ≈
        listQSum value (xs.filter test)
  | [] => Q'.eqv_refl 0
  | i :: xs => by
      cases ht : test i with
      | false =>
          simp only [listQSum, ht, Bool.false_eq_true, if_false, List.filter_cons]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0) (mask_sum test value xs))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [listQSum, ht, if_true, List.filter_cons]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _) (mask_sum test value xs)

/-- A decidable indicator sums to the actual filtered-list cardinality. -/
theorem listQSum_indicator {A : Type} (P : A → Prop) [DecidablePred P]
    (xs : List A) :
    listQSum (fun i => if P i then (1 : Q') else 0) xs ≈
      Q'.ofNat (xs.filter (fun i => decide (P i))).length := by
  have hp : listQSum (fun i => if P i then (1 : Q') else 0) xs ≈
      listQSum (fun i => if decide (P i) then (1 : Q') else 0) xs := by
    apply listQSum_congr
    intro i
    by_cases h : P i <;> simp only [h, decide_true, decide_false, if_true,
      Bool.false_eq_true, if_false] <;> exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ (mask_sum (fun i => decide (P i)) (fun _ => 1) xs)
      (listQSum_one_eqv_ofNat_length _))

private theorem add_self_two (a : Q') : a+a ≈ 2*a :=
  poly_identity_of_normal_eq (.add (.var 0) (.var 0))
    (.mul (.const 2) (.var 0)) (by decide) (fun _ => a)

/-- Symmetric row control for signed Gram entries. The weight matrix need
not itself be positive: only its displayed pair and row bounds are used. -/
theorem symmetric_row_bound {A : Type} (xs : List A)
    (w g : A → A → Q') (b : A → Q') (M : Q')
    (hb : ∀ i, i ∈ xs → (0 : Q') ≤ b i)
    (hsym : ∀ i, i ∈ xs → ∀ j, j ∈ xs → w i j ≈ w j i)
    (hrow : ∀ i, i ∈ xs → listQSum (w i) xs ≤ M)
    (hpair : ∀ i, i ∈ xs → ∀ j, j ∈ xs →
      2*g i j ≤ w i j*(b i+b j)) :
    listQSum (fun i => listQSum (g i) xs) xs ≤ M*listQSum b xs := by
  let W := listQSum (fun i => b i*listQSum (w i) xs) xs
  have hleft : listQSum (fun i => listQSum (fun j => w i j*b i) xs) xs ≈ W := by
    apply listQSum_congr
    intro i
    exact Q'.eqv_trans _ _ _
      (listQSum_congr (fun j => Q'.mul_comm_eqv (w i j) (b i)) xs)
      (listQSum_mul_left (b i) (w i) xs)
  have hright : listQSum (fun i => listQSum (fun j => w i j*b j) xs) xs ≈ W := by
    refine Q'.eqv_trans _ _ _ (listQSum_swap (fun j i => w i j*b j) xs xs) ?_
    refine Q'.eqv_trans _ _ _ ?_ hleft
    apply listQSum_congr_on
    intro i hi
    apply listQSum_congr_on
    intro j hj
    exact Q'.mul_eqv_congr_right _ _ _ (hsym j hj i hi)
  have hsplit : listQSum (fun i => listQSum (fun j => w i j*(b i+b j)) xs) xs ≈
      W+W := by
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun i => Q'.eqv_trans _ _ _
        (listQSum_congr (fun j => Q'.mul_add_eqv (w i j) (b i) (b j)) xs)
        (listQSum_add (fun j => w i j*b i) (fun j => w i j*b j) xs)) xs) ?_
    exact Q'.eqv_trans _ _ _
      (listQSum_add (fun i => listQSum (fun j => w i j*b i) xs)
        (fun i => listQSum (fun j => w i j*b j) xs) xs)
      (Q'.add_eqv_congr' hleft hright)
  have hW : W ≤ M*listQSum b xs := by
    refine Q'.le_trans' _ _ _
      (listQSum_mono _ (fun i => b i*M) xs
        (fun i hi => Q'.mul_le_mul_of_nonneg_left _ _ _ (hrow i hi) (hb i hi))) ?_
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (listQSum_mul_right b M xs)
      (Q'.mul_comm_eqv _ _))
  have htwice : listQSum (fun i => listQSum (fun j => 2*g i j) xs) xs ≈
      2*listQSum (fun i => listQSum (g i) xs) xs :=
    Q'.eqv_trans _ _ _ (listQSum_congr (fun i => listQSum_mul_left 2 (g i) xs) xs)
      (listQSum_mul_left 2 (fun i => listQSum (g i) xs) xs)
  apply Q'.le_of_mul_le_mul_left (c := (2 : Q'))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htwice)
      (Q'.le_trans' _ _ _
        (listQSum_mono _ _ xs (fun i hi =>
          listQSum_mono _ _ xs (fun j hj => hpair i hi j hj)))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hW hW)
            (Q'.le_of_eqv (add_self_two _)))))
  · decide

/-- Sparse near pairs and a common off-interference error. The finite row
bound includes the diagonal; no duplicate-free premise is needed. -/
theorem sparse_gram_bound {A : Type} (xs : List A)
    (R : A → A → Prop) [DecidableRel R] (C : Nat) (r : Q')
    (b : A → Q') (g : A → A → Q')
    (hr : (0 : Q') ≤ r) (hb : ∀ i, i ∈ xs → (0 : Q') ≤ b i)
    (hsym : ∀ i, i ∈ xs → ∀ j, j ∈ xs → (R i j ↔ R j i))
    (hrow : ∀ i, i ∈ xs →
      (xs.filter (fun j => decide (R i j))).length ≤ C)
    (hpair : ∀ i, i ∈ xs → ∀ j, j ∈ xs →
      2*g i j ≤ (if R i j then 1 else r)*(b i+b j)) :
    listQSum (fun i => listQSum (g i) xs) xs ≤
      (Q'.ofNat C+r*Q'.ofNat xs.length)*listQSum b xs := by
  let w := fun i j => (if R i j then (1 : Q') else 0)+r
  apply symmetric_row_bound xs w g b _ hb
  · intro i hi j hj
    have h := hsym i hi j hj
    dsimp [w]
    by_cases hij : R i j
    · rw [if_pos hij, if_pos (h.mp hij)]
      exact Q'.eqv_refl _
    · rw [if_neg hij, if_neg (fun hji => hij (h.mpr hji))]
      exact Q'.eqv_refl _
  · intro i hi
    have hpin : listQSum (w i) xs ≈
        Q'.ofNat (xs.filter (fun j => decide (R i j))).length +
          r*Q'.ofNat xs.length :=
      Q'.eqv_trans _ _ _
        (listQSum_add (fun j => if R i j then (1 : Q') else 0) (fun _ => r) xs)
        (Q'.add_eqv_congr' (listQSum_indicator (R i) xs) (listQSum_const r xs))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.add_le_add_right _ _ _ (CReal.ofNat_le_ofNat (hrow i hi)))
  · intro i hi j hj
    have hweight : (if R i j then (1 : Q') else r) ≤ w i j := by
      dsimp [w]
      by_cases hij : R i j
      · simp only [if_pos hij]
        exact Q'.add_le_self_of_nonneg _ _ hr
      · simp only [if_neg hij]
        exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' r))
    exact Q'.le_trans' _ _ _ (hpair i hi j hj)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hweight
        (Q'.zero_le_add _ _ (hb i hi) (hb j hj)))

end YMGap.Continuum.RationalFiniteSparseGram

#print axioms YMGap.Continuum.RationalFiniteSparseGram.weighted_young
#print axioms YMGap.Continuum.RationalFiniteSparseGram.listQSum_const
#print axioms YMGap.Continuum.RationalFiniteSparseGram.listQSum_indicator
#print axioms YMGap.Continuum.RationalFiniteSparseGram.symmetric_row_bound
#print axioms YMGap.Continuum.RationalFiniteSparseGram.sparse_gram_bound
