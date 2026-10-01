/-
# Finite-cutoff coefficients for the quartic SU(2) heat expansion

These are the exact signed five-diagonal coefficients with the original
heat-prefix cutoff retained.  The high-end coefficients are not replaced by
untruncated bulk coefficients.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticExpansion
import YMGap.Continuum.SU2HeatQuarticBulkCoefficient
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2HeatQuarticFiniteRegroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (quarticBulkCoeff)
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The actual finite-prefix heat coefficient, zero beyond the cutoff. -/
def cutCoeff (w : Q') (K j : Nat) : Q' :=
  if j ≤ K then coeffW w j else 0

/-- The exact output coefficient of the squared trace deficit.  Spin zero has
diagonal multiplicity five, while every positive spin has multiplicity six. -/
def quarticCoeff (a : Nat → Q') : Nat → Q'
  | 0 => (5 * a 0 + -(4 * a 1)) + a 2
  | 1 => (6 * a 1 + -(4 * (a 0 + a 2))) + a 3
  | k + 2 => ((6 * a (k+2) + -(4 * (a (k+1) + a (k+3)))) + a k) + a (k+4)

/-- The exact scalar response to each unregrouped character row. -/
def quarticResponse (Gamma : Nat → Q') : Nat → Q'
  | 0 => (5 * Gamma 0 + -(4 * Gamma 1)) + Gamma 2
  | 1 => (6 * Gamma 1 + -(4 * (Gamma 0 + Gamma 2))) + Gamma 3
  | k + 2 => ((6 * Gamma (k+2) +
      -(4 * (Gamma (k+1) + Gamma (k+3)))) + Gamma k) + Gamma (k+4)

/-- No input coefficient remains beyond the original heat cutoff. -/
theorem cutCoeff_zero_of_gt (w : Q') (K j : Nat) (h : K < j) :
    cutCoeff w K j = 0 := by
  unfold cutCoeff
  exact if_neg (Nat.not_le_of_gt h)

/-- Squaring the fundamental trace deficit enlarges finite spin support by
exactly two at most; this includes the short cutoffs K=0 and K=1. -/
theorem quarticCoeff_cut_zero_of_gt (w : Q') (K j : Nat) (h : K+2 < j) :
    (quarticCoeff (cutCoeff w K) j).eqv 0 := by
  match j with
  | 0 => omega
  | 1 => omega
  | k+2 =>
      have h0 : K < k := by omega
      have h1 : K < k+1 := by omega
      have h2 : K < k+2 := by omega
      have h3 : K < k+3 := by omega
      have h4 : K < k+4 := by omega
      simp only [quarticCoeff, cutCoeff_zero_of_gt w K k h0,
        cutCoeff_zero_of_gt w K (k+1) h1,
        cutCoeff_zero_of_gt w K (k+2) h2,
        cutCoeff_zero_of_gt w K (k+3) h3,
        cutCoeff_zero_of_gt w K (k+4) h4]
      decide

/-- Symmetric five-band transfer from an input spin to an output spin.  The
only exceptional matrix entry is the spin-zero diagonal, which is five. -/
def band (i j : Nat) : Q' :=
  if i = j then (if i = 0 then 5 else 6)
  else if i+1 = j ∨ j+1 = i then -4
  else if i+2 = j ∨ j+2 = i then 1
  else 0

theorem band_symm (i j : Nat) : band i j = band j i := by
  by_cases he : i = j
  · subst j
    rfl
  · have he' : j ≠ i := fun h => he h.symm
    by_cases h1 : i+1 = j ∨ j+1 = i
    · have h1' : j+1 = i ∨ i+1 = j := h1.elim Or.inr Or.inl
      simp only [band, if_neg he, if_neg he', if_pos h1, if_pos h1']
    · have h1' : ¬ (j+1 = i ∨ i+1 = j) := by
        intro h
        exact h1 (h.elim Or.inr Or.inl)
      by_cases h2 : i+2 = j ∨ j+2 = i
      · have h2' : j+2 = i ∨ i+2 = j := h2.elim Or.inr Or.inl
        simp only [band, if_neg he, if_neg he', if_neg h1, if_neg h1',
          if_pos h2, if_pos h2']
      · have h2' : ¬ (j+2 = i ∨ i+2 = j) := by
          intro h
          exact h2 (h.elim Or.inr Or.inl)
        simp only [band, if_neg he, if_neg he', if_neg h1, if_neg h1',
          if_neg h2, if_neg h2']

private theorem band_bulk_left_zero (k j : Nat) (hj : j < k) :
    band (k+2) j = 0 := by
  have h0 : k+2 ≠ j := by omega
  have h1 : ¬ (k+2+1 = j ∨ j+1 = k+2) := by omega
  have h2 : ¬ (k+2+2 = j ∨ j+2 = k+2) := by omega
  simp only [band, if_neg h0, if_neg h1, if_neg h2]

private theorem band_bulk_right_zero (k j : Nat) (hj : k+4 < j) :
    band (k+2) j = 0 := by
  have h0 : k+2 ≠ j := by omega
  have h1 : ¬ (k+2+1 = j ∨ j+1 = k+2) := by omega
  have h2 : ¬ (k+2+2 = j ∨ j+2 = k+2) := by omega
  simp only [band, if_neg h0, if_neg h1, if_neg h2]

private theorem band_right_zero (i j : Nat) (h : i+2 < j) : band i j = 0 := by
  have h0 : i ≠ j := by omega
  have h1 : ¬ (i+1 = j ∨ j+1 = i) := by omega
  have h2 : ¬ (i+2 = j ∨ j+2 = i) := by omega
  simp only [band, if_neg h0, if_neg h1, if_neg h2]

private theorem band_left_zero (i j : Nat) (h : j+2 < i) : band i j = 0 := by
  rw [band_symm]
  exact band_right_zero j i h

private theorem band_bulk_0 (k : Nat) : band (k+2) k = 1 := by
  have h0 : k+2 ≠ k := by omega
  have h1 : ¬ (k+2+1 = k ∨ k+1 = k+2) := by omega
  have h2 : k+2+2 = k ∨ k+2 = k+2 := Or.inr rfl
  unfold band
  rw [if_neg h0, if_neg h1, if_pos h2]

private theorem band_bulk_1 (k : Nat) : band (k+2) (k+1) = -4 := by
  have h0 : k+2 ≠ k+1 := by omega
  have h1 : k+2+1 = k+1 ∨ k+1+1 = k+2 := Or.inr (by omega)
  unfold band
  rw [if_neg h0, if_pos h1]

private theorem band_bulk_2 (k : Nat) : band (k+2) (k+2) = 6 := by
  unfold band
  rw [if_pos (rfl : k+2 = k+2), if_neg (by omega : k+2 ≠ 0)]

private theorem band_bulk_3 (k : Nat) : band (k+2) (k+3) = -4 := by
  have h0 : k+2 ≠ k+3 := by omega
  have h1 : k+2+1 = k+3 ∨ k+3+1 = k+2 := Or.inl (by omega)
  unfold band
  rw [if_neg h0, if_pos h1]

private theorem band_bulk_4 (k : Nat) : band (k+2) (k+4) = 1 := by
  have h0 : k+2 ≠ k+4 := by omega
  have h1 : ¬ (k+2+1 = k+4 ∨ k+4+1 = k+2) := by omega
  have h2 : k+2+2 = k+4 ∨ k+4+2 = k+2 := Or.inl (by omega)
  unfold band
  rw [if_neg h0, if_neg h1, if_pos h2]

private theorem finSum_zero_on_local (f : Nat → Q') : ∀ n,
    (∀ j, j < n → f j ≈ 0) → finSum f n ≈ 0
  | 0, _ => Q'.eqv_refl 0
  | n+1, h => by
      change finSum f n + f n ≈ 0
      have hp := finSum_zero_on_local f n (fun j hj => h j (by omega))
      have hl := h n (by omega)
      exact Q'.eqv_trans _ (0+0) _
        (Q'.add_eqv_congr' hp hl)
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem finSum_split_local (f : Nat → Q') (k : Nat) : ∀ d,
    finSum f (k+d) ≈ finSum f k + finSum (fun j => f (k+j)) d
  | 0 => by
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (finSum f k)))
  | d+1 => by
      change finSum f (k+d) + f (k+d) ≈
        finSum f k + (finSum (fun j => f (k+j)) d + f (k+d))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_split_local f k d))
        (Q'.add_assoc_eqv _ _ _)

private theorem finSum_stable_local (f : Nat → Q') (n : Nat)
    (hzero : ∀ j, n ≤ j → f j ≈ 0) (d : Nat) :
    finSum f (n+d) ≈ finSum f n := by
  have htail : finSum (fun j => f (n+j)) d ≈ 0 :=
    finSum_zero_on_local _ d (fun j _ => hzero (n+j) (by omega))
  exact Q'.eqv_trans _ _ _ (finSum_split_local f n d)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ htail)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem five_term_rearrange (a b c d e : Q') :
    (((((0 + 1*a) + (-4)*b) + 6*c) + (-4)*d) + 1*e) ≈
      ((6*c + -(4*(b+d))) + a) + e := by
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.add (.add (.const 0)
      (.mul (.const 1) (.var 0)))
      (.mul (.const (-4)) (.var 1)))
      (.mul (.const 6) (.var 2)))
      (.mul (.const (-4)) (.var 3)))
      (.mul (.const 1) (.var 4)))
    (.add (.add (.add (.mul (.const 6) (.var 2))
      (.neg (.mul (.const 4) (.add (.var 1) (.var 3)))))
      (.var 0)) (.var 4))
    (by decide)
    (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c
      else if i = 3 then d else e)

/-- Every bulk row gives its five exact character-response entries; no
boundary term is dropped, because the sum reaches spin `k+4`. -/
theorem band_bulk_row (Gamma : Nat → Q') (k : Nat) :
    finSum (fun j => band (k+2) j * Gamma j) (k+5) ≈
      quarticResponse Gamma (k+2) := by
  let f : Nat → Q' := fun j => band (k+2) j * Gamma j
  have hpre : finSum f k ≈ 0 :=
    finSum_zero_on_local f k (fun j hj => by
      rw [show f j = band (k+2) j * Gamma j from rfl,
        band_bulk_left_zero k j hj]
      exact Q'.zero_mul_eqv _)
  have hsplit : finSum f (k+5) ≈
      finSum f k + finSum (fun j => f (k+j)) 5 :=
    finSum_split_local f k 5
  have hfive : finSum (fun j => f (k+j)) 5 ≈
      quarticResponse Gamma (k+2) := by
    change (((((0 + f (k+0)) + f (k+1)) + f (k+2)) + f (k+3)) + f (k+4)) ≈
      quarticResponse Gamma (k+2)
    simp only [Nat.add_zero, f, band_bulk_0, band_bulk_1, band_bulk_2,
      band_bulk_3, band_bulk_4, quarticResponse]
    exact five_term_rearrange _ _ _ _ _
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hpre)
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) hfive))

private theorem band_zero_0 : band 0 0 = 5 := by decide
private theorem band_zero_1 : band 0 1 = -4 := by decide
private theorem band_zero_2 : band 0 2 = 1 := by decide
private theorem band_one_0 : band 1 0 = -4 := by decide
private theorem band_one_1 : band 1 1 = 6 := by decide
private theorem band_one_2 : band 1 2 = -4 := by decide
private theorem band_one_3 : band 1 3 = 1 := by decide

private theorem three_term_rearrange (a b c : Q') :
    (((0 + 5*a) + (-4)*b) + 1*c) ≈ ((5*a + -(4*b)) + c) := by
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.const 0) (.mul (.const 5) (.var 0)))
      (.mul (.const (-4)) (.var 1))) (.mul (.const 1) (.var 2)))
    (.add (.add (.mul (.const 5) (.var 0))
      (.neg (.mul (.const 4) (.var 1)))) (.var 2))
    (by decide) (fun i => if i = 0 then a else if i = 1 then b else c)

private theorem four_term_rearrange (a b c d : Q') :
    ((((0 + (-4)*a) + 6*b) + (-4)*c) + 1*d) ≈
      ((6*b + -(4*(a+c))) + d) := by
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.add (.const 0) (.mul (.const (-4)) (.var 0)))
      (.mul (.const 6) (.var 1))) (.mul (.const (-4)) (.var 2)))
      (.mul (.const 1) (.var 3)))
    (.add (.add (.mul (.const 6) (.var 1))
      (.neg (.mul (.const 4) (.add (.var 0) (.var 2))))) (.var 3))
    (by decide)
    (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d)

theorem band_zero_row (Gamma : Nat → Q') :
    finSum (fun j => band 0 j * Gamma j) 3 ≈ quarticResponse Gamma 0 := by
  change (((0 + band 0 0 * Gamma 0) + band 0 1 * Gamma 1) +
    band 0 2 * Gamma 2) ≈ quarticResponse Gamma 0
  rw [band_zero_0, band_zero_1, band_zero_2]
  exact three_term_rearrange _ _ _

theorem band_one_row (Gamma : Nat → Q') :
    finSum (fun j => band 1 j * Gamma j) 4 ≈ quarticResponse Gamma 1 := by
  change ((((0 + band 1 0 * Gamma 0) + band 1 1 * Gamma 1) +
    band 1 2 * Gamma 2) + band 1 3 * Gamma 3) ≈ quarticResponse Gamma 1
  rw [band_one_0, band_one_1, band_one_2, band_one_3]
  exact four_term_rearrange _ _ _ _

/-- A row is evaluated exactly once its two upper neighbors are included. -/
theorem band_row_le (Gamma : Nat → Q') (i N : Nat) (hN : i+3 ≤ N) :
    finSum (fun j => band i j * Gamma j) N ≈ quarticResponse Gamma i := by
  let f : Nat → Q' := fun j => band i j * Gamma j
  have hzero : ∀ j, i+3 ≤ j → f j ≈ 0 := by
    intro j hj
    change band i j * Gamma j ≈ 0
    rw [band_right_zero i j (by omega)]
    exact Q'.zero_mul_eqv _
  have hdecomp : N = (i+3) + (N-(i+3)) := by omega
  rw [hdecomp]
  have hs := finSum_stable_local f (i+3) hzero (N-(i+3))
  have hb : finSum f (i+3) ≈ quarticResponse Gamma i := by
    cases i with
    | zero => exact band_zero_row Gamma
    | succ i =>
        cases i with
        | zero => exact band_one_row Gamma
        | succ k =>
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using band_bulk_row Gamma k
  exact Q'.eqv_trans _ _ _ hs hb

private theorem coeff_eq_response (a : Nat → Q') (j : Nat) :
    quarticCoeff a j = quarticResponse a j := by
  cases j with
  | zero => rfl
  | succ j =>
      cases j with
      | zero => rfl
      | succ k => rfl

private theorem finSum_congr_lt_local (f g : Nat → Q') : ∀ N,
    (∀ i, i < N → f i ≈ g i) → finSum f N ≈ finSum g N
  | 0, _ => Q'.eqv_refl 0
  | N+1, h => by
      change finSum f N + f N ≈ finSum g N + g N
      exact Q'.add_eqv_congr'
        (finSum_congr_lt_local f g N (fun i hi => h i (by omega)))
        (h N (by omega))

private theorem cut_column (w : Q') (K j : Nat) :
    finSum (fun i => cutCoeff w K i * band i j) (K+5) ≈
      quarticCoeff (cutCoeff w K) j := by
  by_cases hj : j ≤ K+2
  · rw [coeff_eq_response]
    have hsym : finSum (fun i => cutCoeff w K i * band i j) (K+5) ≈
        finSum (fun i => band j i * cutCoeff w K i) (K+5) :=
      YMGap.Constructive.RationalTail.finSum_eqv_congr _ _ (fun i => by
        rw [band_symm i j]
        exact Q'.mul_comm_eqv _ _) (K+5)
    exact Q'.eqv_trans _ _ _ hsym
      (band_row_le (cutCoeff w K) j (K+5) (by omega))
  · have hzero : finSum (fun i => cutCoeff w K i * band i j) (K+5) ≈ 0 :=
      finSum_zero_on_local _ (K+5) (fun i _ => by
        by_cases hi : i ≤ K
        · rw [band_right_zero i j (by omega)]
          exact Q'.mul_zero_eqv _
        · rw [cutCoeff_zero_of_gt w K i (by omega)]
          exact Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ _ _ hzero
      (Q'.eqv_symm (quarticCoeff_cut_zero_of_gt w K j (by omega)))

/-- Exact finite scalar transpose of the quartic character response.  The
right sum extends only to `K+2`; every output coefficient beyond it is zero.
There is no cutoff-free substitution at either endpoint. -/
theorem finite_regroup (w : Q') (K : Nat) (Gamma : Nat → Q') :
    finSum (fun i => coeffW w i * quarticResponse Gamma i) (K+1) ≈
      finSum (fun j => quarticCoeff (cutCoeff w K) j * Gamma j) (K+3) := by
  let a : Nat → Q' := cutCoeff w K
  let M : Nat := K+5
  have hinput : finSum (fun i => coeffW w i * quarticResponse Gamma i) (K+1) ≈
      finSum (fun i => a i * quarticResponse Gamma i) M := by
    have hc : finSum (fun i => coeffW w i * quarticResponse Gamma i) (K+1) ≈
        finSum (fun i => a i * quarticResponse Gamma i) (K+1) :=
      finSum_congr_lt_local _ _ (K+1) (fun i hi => by
        change coeffW w i * quarticResponse Gamma i ≈
          cutCoeff w K i * quarticResponse Gamma i
        rw [cutCoeff, if_pos (by omega : i ≤ K)]
        exact Q'.eqv_refl _)
    have hs : finSum (fun i => a i * quarticResponse Gamma i) M ≈
        finSum (fun i => a i * quarticResponse Gamma i) (K+1) := by
      have h := finSum_stable_local
        (fun i => a i * quarticResponse Gamma i) (K+1)
        (fun i hi => by
          change cutCoeff w K i * quarticResponse Gamma i ≈ 0
          rw [cutCoeff_zero_of_gt w K i (by omega)]
          exact Q'.zero_mul_eqv _) 4
      simpa only [M, show (K+1)+4 = K+5 by omega] using h
    exact Q'.eqv_trans _ _ _ hc (Q'.eqv_symm hs)
  have hrows : finSum (fun i => a i * quarticResponse Gamma i) M ≈
      finSum (fun i => finSum
        (fun j => a i * (band i j * Gamma j)) M) M :=
    YMGap.Constructive.RationalTail.finSum_eqv_congr _ _ (fun i => by
      by_cases hi : i ≤ K
      · have hr := band_row_le Gamma i M (by dsimp [M]; omega)
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hr))
          (YMGap.Constructive.RationalTail.const_mul_finSum
            (fun j => band i j * Gamma j) (a i) M)
      · have ha : a i = 0 := cutCoeff_zero_of_gt w K i (by omega)
        rw [ha]
        have hz : finSum (fun j => (0 : Q') * (band i j * Gamma j)) M ≈ 0 :=
          finSum_zero_on_local _ M (fun j _ => Q'.zero_mul_eqv _)
        exact Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _)
          (Q'.eqv_symm hz)) M
  have hswap := YMGap.Constructive.RationalTail.finSum_swap
    (fun i j => a i * (band i j * Gamma j)) M M
  have hcolumns : finSum (fun j => finSum
        (fun i => a i * (band i j * Gamma j)) M) M ≈
      finSum (fun j => quarticCoeff a j * Gamma j) M :=
    YMGap.Constructive.RationalTail.finSum_eqv_congr _ _ (fun j => by
      have ha : finSum (fun i => a i * (band i j * Gamma j)) M ≈
          finSum (fun i => (a i * band i j) * Gamma j) M :=
        YMGap.Constructive.RationalTail.finSum_eqv_congr _ _ (fun i =>
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) M
      have hb : finSum (fun i => (a i * band i j) * Gamma j) M ≈
          finSum (fun i => a i * band i j) M * Gamma j :=
        Q'.eqv_symm (YMGap.Constructive.RationalTail.finSum_mul_const
          (fun i => a i * band i j) (Gamma j) M)
      have hc : finSum (fun i => a i * band i j) M * Gamma j ≈
          quarticCoeff a j * Gamma j := by
        exact Q'.mul_eqv_congr_right _ _ _ (cut_column w K j)
      exact Q'.eqv_trans _ _ _ ha (Q'.eqv_trans _ _ _ hb hc)) M
  have houtput : finSum (fun j => quarticCoeff a j * Gamma j) M ≈
      finSum (fun j => quarticCoeff a j * Gamma j) (K+3) := by
    have hs := finSum_stable_local
      (fun j => quarticCoeff a j * Gamma j) (K+3)
      (fun j hj => by
        change quarticCoeff (cutCoeff w K) j * Gamma j ≈ 0
        have hz := quarticCoeff_cut_zero_of_gt w K j (by omega)
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hz)
          (Q'.zero_mul_eqv _)) 2
    simpa only [M, show (K+3)+2 = K+5 by omega] using hs
  exact Q'.eqv_trans _ _ _ hinput
    (Q'.eqv_trans _ _ _ hrows
      (Q'.eqv_trans _ _ _ hswap
        (Q'.eqv_trans _ _ _ hcolumns houtput)))

/-- On a true interior spin, the cutoff coefficient is exactly the original
untruncated five-term coefficient. -/
theorem quarticCoeff_cut_interior (w : Q') (K k : Nat) (h : k+4 ≤ K) :
    quarticCoeff (cutCoeff w K) (k+2) = quarticBulkCoeff w k := by
  have h0 : k ≤ K := by omega
  have h1 : k+1 ≤ K := by omega
  have h2 : k+2 ≤ K := by omega
  have h3 : k+3 ≤ K := by omega
  simp only [quarticCoeff, quarticBulkCoeff, cutCoeff, if_pos h0,
    if_pos h1, if_pos h2, if_pos h3, if_pos h]

#print axioms cutCoeff
#print axioms quarticCoeff
#print axioms quarticResponse
#print axioms band
#print axioms band_symm
#print axioms band_bulk_left_zero
#print axioms band_bulk_right_zero
#print axioms band_bulk_0
#print axioms band_bulk_1
#print axioms band_bulk_2
#print axioms band_bulk_3
#print axioms band_bulk_4
#print axioms band_bulk_row
#print axioms band_zero_row
#print axioms band_one_row
#print axioms band_row_le
#print axioms finite_regroup
#print axioms cutCoeff_zero_of_gt
#print axioms quarticCoeff_cut_zero_of_gt
#print axioms quarticCoeff_cut_interior

end YMGap.Continuum.SU2HeatQuarticFiniteRegroup
