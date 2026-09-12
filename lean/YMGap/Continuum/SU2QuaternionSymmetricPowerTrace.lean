/-
# Trace of the actual symmetric-power action

The coefficient recursion below reads the actual tensor action on its
explicit symmetric coefficient basis. It is not a character-labelled
replacement representation. Two row counts give a structural recurrence;
no list of all tensor assignments is materialized.

These are rational-complex value identities. They do not on their own
justify congruence under the polynomial Haar functional.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerAction

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerTrace

set_option autoImplicit false

open YMGap.Constructive YMGap.RepTheory
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionTensorPowerAction
open YMGap.Continuum.SU2QuaternionSymmetricPowerAction

local infix:50 " ≃c " => RationalComplexEqv
local infixl:65 " ⊞ " => rationalComplexAdd
local infixl:70 " ⊠ " => rationalComplexMul
local notation "𝟘" => rationalComplexZero
local notation "𝟙" => rationalComplexOne

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> ac_rfl))

private theorem mix_swap (a b c d x y z : RationalComplex) :
    (c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z))) ≃c
      (a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))) ⊞ (b ⊠ ((c ⊠ y) ⊞ (d ⊠ z))) := by
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

/-- Read a sequence of false rows by structural recursion. -/
def falseRowValue (M : FundamentalMatrix) : Nat → (Nat → RationalComplex) → RationalComplex
  | 0, f => f 0
  | m + 1, f => (M false false ⊠ falseRowValue M m f) ⊞
      (M false true ⊠ falseRowValue M m (fun j => f (j + 1)))

/-- Canonical symmetric tensor readout with m false rows and k true rows.
Only coefficients 0 through m+k of f are read. -/
def rowValue (M : FundamentalMatrix) (m : Nat) : Nat → (Nat → RationalComplex) → RationalComplex
  | 0, f => falseRowValue M m f
  | k + 1, f => (M true false ⊠ rowValue M m k f) ⊞
      (M true true ⊠ rowValue M m k (fun j => f (j + 1)))

theorem rowValue_congr (M : FundamentalMatrix) : ∀ m k {f g : Nat → RationalComplex},
    (∀ j, j ≤ m + k → f j ≃c g j) → rowValue M m k f ≃c rowValue M m k g
  | 0, 0, _, _, h => h 0 (by omega)
  | m + 1, 0, f, g, h => rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _)
        (rowValue_congr M m 0 (fun j hj => h j (by omega))))
      (rationalComplexMul_congr (rationalComplexEqv_refl _)
        (rowValue_congr M m 0 (fun j hj => h (j + 1) (by omega))))
  | m, k + 1, f, g, h => rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _)
        (rowValue_congr M m k (fun j hj => h j (by omega))))
      (rationalComplexMul_congr (rationalComplexEqv_refl _)
        (rowValue_congr M m k (fun j hj => h (j + 1) (by omega))))

theorem rowValue_false_succ (M : FundamentalMatrix) (m k : Nat) (f : Nat → RationalComplex) :
    rowValue M (m + 1) k f ≃c
      (M false false ⊠ rowValue M m k f) ⊞
        (M false true ⊠ rowValue M m k (fun j => f (j + 1))) := by
  induction k generalizing f with
  | zero => exact rationalComplexEqv_refl _
  | succ k ih =>
    exact rationalComplexEqv_trans (rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (ih f))
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (ih (fun j => f (j + 1)))))
      (mix_swap _ _ _ _ _ _ _)

private theorem coefficient_mix (a b : RationalComplex) : ∀ n (x y : Tensor n) k,
    coefficient n (tensorAdd n (tensorScale n a x) (tensorScale n b y)) k ≃c
      (a ⊠ coefficient n x k) ⊞ (b ⊠ coefficient n y k)
  | 0, _, _, _ => rationalComplexEqv_refl _
  | n + 1, x, y, 0 => coefficient_mix a b n (x false) (y false) 0
  | n + 1, x, y, k + 1 => coefficient_mix a b n (x true) (y true) k

/-- The two-row recursion is the actual matrix action, not a substituted
scalar recurrence. This holds for every coefficient vector and every 2x2 matrix. -/
theorem coefficient_matrixAction (M : FundamentalMatrix) : ∀ n (f : Nat → RationalComplex) k,
    k ≤ n → coefficient n (matrixAction n M (fromCoefficients n f)) k ≃c
      rowValue M (n - k) k f
  | 0, f, k, hk => by
    have : k = 0 := by omega
    subst k
    exact rationalComplexEqv_refl _
  | n + 1, f, 0, _ =>
    rationalComplexEqv_trans (coefficient_mix _ _ n _ _ 0)
      (rationalComplexAdd_congr
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (coefficient_matrixAction M n f 0 (by omega)))
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (coefficient_matrixAction M n (fun j => f (j + 1)) 0 (by omega))))
  | n + 1, f, k + 1, hk => by
    rw [Nat.add_sub_add_right]
    exact rationalComplexEqv_trans (coefficient_mix _ _ n _ _ k)
      (rationalComplexAdd_congr
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (coefficient_matrixAction M n f k (by omega)))
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (coefficient_matrixAction M n (fun j => f (j + 1)) k (by omega))))

/-- Explicit coefficient basis vector. Only its finite degree window is used. -/
def basis (k j : Nat) : RationalComplex := if j = k then 𝟙 else 𝟘

/-- The literal diagonal matrix coefficient of the actual symmetric sector. -/
def diagonal (M : FundamentalMatrix) (n k : Nat) : RationalComplex :=
  coefficient n (matrixAction n M (fromCoefficients n (basis k))) k

theorem diagonal_eq_rowValue (M : FundamentalMatrix) (n k : Nat) (hk : k ≤ n) :
    diagonal M n k ≃c rowValue M (n - k) k (basis k) :=
  coefficient_matrixAction M n (basis k) k hk

private theorem basis_shift (k : Nat) : (fun j => basis (k + 1) (j + 1)) = basis k := by
  funext j
  simp only [basis, Nat.add_right_cancel_iff]

private theorem zero_mix (a b : RationalComplex) : (a ⊠ 𝟘) ⊞ (b ⊠ 𝟘) ≃c 𝟘 := by
  unfold rationalComplexZero rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem add_mul_zero (a b : RationalComplex) : a ⊞ (b ⊠ 𝟘) ≃c a := by
  unfold rationalComplexZero rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem zero_mul_add (a b : RationalComplex) : (a ⊠ 𝟘) ⊞ b ≃c b := by
  unfold rationalComplexZero rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem rowValue_zero (M : FundamentalMatrix) : ∀ m k,
    rowValue M m k (fun _ => 𝟘) ≃c 𝟘
  | 0, 0 => rationalComplexEqv_refl _
  | m + 1, 0 => rationalComplexEqv_trans (rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (rowValue_zero M m 0))
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (rowValue_zero M m 0))) (zero_mix _ _)
  | m, k + 1 => rationalComplexEqv_trans (rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (rowValue_zero M m k))
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (rowValue_zero M m k))) (zero_mix _ _)

private theorem rowValue_vanish (M : FundamentalMatrix) (m k : Nat) (f : Nat → RationalComplex)
    (h : ∀ j, j ≤ m + k → f j = 𝟘) : rowValue M m k f ≃c 𝟘 :=
  rationalComplexEqv_trans (rowValue_congr M m k (fun j hj => by rw [h j hj]; exact rationalComplexEqv_refl _))
    (rowValue_zero M m k)

private theorem mixed_balance (a b c d x y z : RationalComplex) :
    ((c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z)))) ⊞ ((a ⊠ d) ⊠ y) ≃c
      ((a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z)))) ⊞ ((b ⊠ c) ⊠ y) := by
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

/-- The two-row coefficient identity. Keeping both determinant terms on
opposite sides avoids a division, eigenvalue choice, or diagonalization. -/
theorem rowValue_mixed (M : FundamentalMatrix) (m k j : Nat) :
    rowValue M (m + 1) (k + 1) (basis (j + 1)) ⊞
      ((M false false ⊠ M true true) ⊠ rowValue M m k (basis j)) ≃c
    ((M false false ⊠ rowValue M m (k + 1) (basis (j + 1))) ⊞
      (M true true ⊠ rowValue M (m + 1) k (basis j))) ⊞
      ((M false true ⊠ M true false) ⊠ rowValue M m k (basis j)) := by
  have hfirst := rowValue_false_succ M m k (basis (j + 1))
  rw [basis_shift] at hfirst
  have hsecond := rowValue_false_succ M m k (basis j)
  have hl : rowValue M (m + 1) (k + 1) (basis (j + 1)) ≃c
      (M true false ⊠ ((M false false ⊠ rowValue M m k (basis (j + 1))) ⊞
        (M false true ⊠ rowValue M m k (basis j)))) ⊞
      (M true true ⊠ ((M false false ⊠ rowValue M m k (basis j)) ⊞
        (M false true ⊠ rowValue M m k (fun i => basis j (i + 1))))) := by
    rw [rowValue, basis_shift]
    exact rationalComplexAdd_congr (rationalComplexMul_congr (rationalComplexEqv_refl _) hfirst)
      (rationalComplexMul_congr (rationalComplexEqv_refl _) hsecond)
  refine rationalComplexEqv_trans (rationalComplexAdd_congr hl (rationalComplexEqv_refl _)) ?_
  refine rationalComplexEqv_trans (mixed_balance _ _ _ _ _ _ _) ?_
  apply rationalComplexAdd_congr
  · apply rationalComplexAdd_congr
    · rw [rowValue, basis_shift]
      exact rationalComplexEqv_refl _
    · exact rationalComplexMul_congr (rationalComplexEqv_refl _) (rationalComplexEqv_symm hsecond)
  · exact rationalComplexEqv_refl _

theorem diagonal_zero_succ (M : FundamentalMatrix) (n : Nat) :
    diagonal M (n + 1) 0 ≃c M false false ⊠ diagonal M n 0 := by
  refine rationalComplexEqv_trans (diagonal_eq_rowValue M (n + 1) 0 (by omega)) ?_
  have hz := rowValue_vanish M n 0 (fun j => basis 0 (j + 1)) (by
    intro j _
    simp only [basis, Nat.add_one_ne_zero, ↓reduceIte])
  refine rationalComplexEqv_trans (rationalComplexAdd_congr (rationalComplexEqv_refl _)
    (rationalComplexMul_congr (rationalComplexEqv_refl _) hz)) ?_
  exact rationalComplexEqv_trans (add_mul_zero _ _)
    (rationalComplexMul_congr (rationalComplexEqv_refl _)
      (rationalComplexEqv_symm (diagonal_eq_rowValue M n 0 (by omega))))

theorem diagonal_last_succ (M : FundamentalMatrix) (n : Nat) :
    diagonal M (n + 1) (n + 1) ≃c M true true ⊠ diagonal M n n := by
  refine rationalComplexEqv_trans (diagonal_eq_rowValue M (n + 1) (n + 1) (by omega)) ?_
  rw [Nat.sub_self, rowValue, basis_shift]
  have hz := rowValue_vanish M 0 n (basis (n + 1)) (by
    intro j hj
    have hne : j ≠ n + 1 := by omega
    simp only [basis, hne, ↓reduceIte])
  refine rationalComplexEqv_trans (rationalComplexAdd_congr
    (rationalComplexMul_congr (rationalComplexEqv_refl _) hz) (rationalComplexEqv_refl _)) ?_
  refine rationalComplexEqv_trans (zero_mul_add _ _) ?_
  apply rationalComplexMul_congr (rationalComplexEqv_refl _)
  simpa only [Nat.sub_self] using rationalComplexEqv_symm (diagonal_eq_rowValue M n n (by omega))

theorem diagonal_mixed (M : FundamentalMatrix) (n k : Nat) (hk : k ≤ n) :
    diagonal M (n + 2) (k + 1) ⊞ ((M false false ⊠ M true true) ⊠ diagonal M n k) ≃c
      ((M false false ⊠ diagonal M (n + 1) (k + 1)) ⊞
        (M true true ⊠ diagonal M (n + 1) k)) ⊞
        ((M false true ⊠ M true false) ⊠ diagonal M n k) := by
  have h0 := diagonal_eq_rowValue M n k hk
  have h1 := diagonal_eq_rowValue M (n + 1) (k + 1) (by omega)
  have h2 := diagonal_eq_rowValue M (n + 1) k (by omega)
  have h3 := diagonal_eq_rowValue M (n + 2) (k + 1) (by omega)
  have e1 : n + 1 - (k + 1) = n - k := by omega
  have e2 : n + 1 - k = n - k + 1 := by omega
  have e3 : n + 2 - (k + 1) = n - k + 1 := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  exact rationalComplexEqv_trans (rationalComplexAdd_congr h3
    (rationalComplexMul_congr (rationalComplexEqv_refl _) h0))
    (rationalComplexEqv_trans (rowValue_mixed M (n - k) k k)
      (rationalComplexEqv_symm (rationalComplexAdd_congr
        (rationalComplexAdd_congr (rationalComplexMul_congr (rationalComplexEqv_refl _) h1)
          (rationalComplexMul_congr (rationalComplexEqv_refl _) h2))
        (rationalComplexMul_congr (rationalComplexEqv_refl _) h0))))

/-- Finite diagonal sum; the length remains symbolic in the proofs. -/
def complexSum : Nat → (Nat → RationalComplex) → RationalComplex
  | 0, _ => 𝟘
  | n + 1, f => complexSum n f ⊞ f n

private theorem complexSum_congr : ∀ n {f g : Nat → RationalComplex},
    (∀ j, j < n → f j ≃c g j) → complexSum n f ≃c complexSum n g
  | 0, _, _, _ => rationalComplexEqv_refl _
  | n + 1, _, _, h => rationalComplexAdd_congr
      (complexSum_congr n (fun j hj => h j (by omega))) (h n (by omega))

private theorem complexSum_add : ∀ n (f g : Nat → RationalComplex),
    complexSum n (fun j => f j ⊞ g j) ≃c complexSum n f ⊞ complexSum n g
  | 0, _, _ => by
    unfold complexSum rationalComplexZero rationalComplexAdd RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, f, g => rationalComplexEqv_trans
      (rationalComplexAdd_congr (complexSum_add n f g) (rationalComplexEqv_refl _))
      (rationalComplexAdd_swap_inner _ _ _ _)

private theorem complexSum_scale (a : RationalComplex) : ∀ n (f : Nat → RationalComplex),
    complexSum n (fun j => a ⊠ f j) ≃c a ⊠ complexSum n f
  | 0, _ => by
    unfold complexSum rationalComplexZero rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, f => rationalComplexEqv_trans
      (rationalComplexAdd_congr (complexSum_scale a n f) (rationalComplexEqv_refl _))
      (rationalComplexEqv_symm (rationalComplexMul_add _ _ _))

private theorem complexSum_shift : ∀ n (f : Nat → RationalComplex),
    complexSum (n + 1) f ≃c f 0 ⊞ complexSum n (fun j => f (j + 1))
  | 0, f => by
    change (𝟘 ⊞ f 0) ≃c (f 0 ⊞ 𝟘)
    exact rationalComplexAdd_comm _ _
  | n + 1, f => rationalComplexEqv_trans
      (rationalComplexAdd_congr (complexSum_shift n f) (rationalComplexEqv_refl _))
      (rationalComplexAdd_assoc _ _ _)

/-- Trace on the explicitly reconstructed n+1-coefficient symmetric sector.
This is the sum of the actual action's diagonal entries. -/
def trace (M : FundamentalMatrix) (n : Nat) : RationalComplex :=
  complexSum (n + 1) (diagonal M n)

private theorem sum_mixed (M : FundamentalMatrix) (n : Nat) :
    complexSum (n + 1) (fun k => diagonal M (n + 2) (k + 1)) ⊞
      ((M false false ⊠ M true true) ⊠ trace M n) ≃c
    ((M false false ⊠ complexSum (n + 1) (fun k => diagonal M (n + 1) (k + 1))) ⊞
      (M true true ⊠ complexSum (n + 1) (diagonal M (n + 1)))) ⊞
      ((M false true ⊠ M true false) ⊠ trace M n) := by
  refine rationalComplexEqv_trans (rationalComplexEqv_symm
    (rationalComplexEqv_trans (complexSum_add _ _ _)
      (rationalComplexAdd_congr (rationalComplexEqv_refl _) (complexSum_scale _ _ _)))) ?_
  refine rationalComplexEqv_trans (complexSum_congr (n + 1)
    (fun k hk => diagonal_mixed M n k (by omega))) ?_
  refine rationalComplexEqv_trans (complexSum_add _ _ _) ?_
  apply rationalComplexAdd_congr
  · exact rationalComplexEqv_trans (complexSum_add _ _ _)
      (rationalComplexAdd_congr (complexSum_scale _ _ _) (complexSum_scale _ _ _))
  · exact complexSum_scale _ _ _

private theorem balance_reorder (a d x y i t : RationalComplex) :
    (((a ⊠ x) ⊞ i) ⊞ (d ⊠ y)) ⊞ t ≃c ((a ⊠ x) ⊞ (i ⊞ t)) ⊞ (d ⊠ y) := by
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem balance_contract (a d x y j p t : RationalComplex) :
    ((a ⊠ x) ⊞ (((a ⊠ j) ⊞ (d ⊠ p)) ⊞ t)) ⊞ (d ⊠ y) ≃c
      ((a ⊠ (x ⊞ j)) ⊞ (d ⊠ (p ⊞ y))) ⊞ t := by
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

/-- All-degree trace recurrence for every complex 2x2 matrix, with the
two determinant products retained explicitly. No spectral input is used. -/
theorem trace_recurrence (M : FundamentalMatrix) (n : Nat) :
    trace M (n + 2) ⊞ ((M false false ⊠ M true true) ⊠ trace M n) ≃c
      ((M false false ⊞ M true true) ⊠ trace M (n + 1)) ⊞
        ((M false true ⊠ M true false) ⊠ trace M n) := by
  have hsplit : trace M (n + 2) ≃c
      (diagonal M (n + 2) 0 ⊞ complexSum (n + 1) (fun k => diagonal M (n + 2) (k + 1))) ⊞
        diagonal M (n + 2) (n + 2) :=
    rationalComplexAdd_congr (complexSum_shift (n + 1) _) (rationalComplexEqv_refl _)
  have hboundary := rationalComplexEqv_trans hsplit
    (rationalComplexAdd_congr
      (rationalComplexAdd_congr (diagonal_zero_succ M (n + 1)) (rationalComplexEqv_refl _))
      (diagonal_last_succ M (n + 1)))
  refine rationalComplexEqv_trans (rationalComplexAdd_congr hboundary (rationalComplexEqv_refl _)) ?_
  refine rationalComplexEqv_trans (balance_reorder _ _ _ _ _ _) ?_
  refine rationalComplexEqv_trans (rationalComplexAdd_congr
    (rationalComplexAdd_congr (rationalComplexEqv_refl _) (sum_mixed M n)) (rationalComplexEqv_refl _)) ?_
  refine rationalComplexEqv_trans (balance_contract _ _ _ _ _ _ _) ?_
  refine rationalComplexEqv_trans (rationalComplexAdd_congr
    (rationalComplexAdd_congr
      (rationalComplexMul_congr (rationalComplexEqv_refl _) (rationalComplexEqv_symm (complexSum_shift (n + 1) _)))
      (rationalComplexEqv_refl _)) (rationalComplexEqv_refl _)) ?_
  exact rationalComplexAdd_congr (rationalComplexEqv_symm (rationalComplexAdd_mul _ _ _))
    (rationalComplexEqv_refl _)

theorem trace_zero (M : FundamentalMatrix) : trace M 0 ≃c 𝟙 := by
  change (𝟘 ⊞ 𝟙) ≃c 𝟙
  unfold rationalComplexZero rationalComplexOne rationalComplexAdd RationalComplexEqv
  constructor <;> ring_qeqv

theorem trace_one (M : FundamentalMatrix) : trace M 1 ≃c M false false ⊞ M true true := by
  change (𝟘 ⊞ ((M false false ⊠ 𝟙) ⊞ (M false true ⊠ 𝟘))) ⊞
      ((M true false ⊠ 𝟘) ⊞ (M true true ⊠ 𝟙)) ≃c M false false ⊞ M true true
  unfold rationalComplexZero rationalComplexOne rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem q_add_zero (a : Q') : (a + 0).eqv a := by ring_qeqv

private theorem q_remove (a b : Q') : ((a + b) + -b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv b)) (q_add_zero a))

private theorem q_remove_neg (a b : Q') : ((a + -b) + b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv b)) (q_add_zero a))

private theorem q_cancel_right {a b z : Q'} (h : (a + z).eqv (b + z)) : a.eqv b :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (q_remove a z))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-z) h) (q_remove b z))

private theorem complex_cancel_right {a b z : RationalComplex} (h : (a ⊞ z) ≃c (b ⊞ z)) : a ≃c b :=
  ⟨q_cancel_right h.1, q_cancel_right h.2⟩

private theorem fundamental_diagonal_product (q : RationalQuaternion) :
    (fundamentalMatrixValue q false false ⊠ fundamentalMatrixValue q true true) ≃c
      (q.r * q.r + q.i * q.i, 0) := by
  unfold fundamentalMatrixValue rationalComplexMul RationalComplexEqv
  constructor
  · ring_qeqv
  · refine Q'.eqv_trans _ (-(q.r * q.i) + q.r * q.i) _ ?_ (Q'.neg_add_self_eqv _)
    ring_qeqv

private theorem fundamental_offdiagonal_product (q : RationalQuaternion) :
    (fundamentalMatrixValue q false true ⊠ fundamentalMatrixValue q true false) ≃c
      (-(q.j * q.j + q.k * q.k), 0) := by
  unfold fundamentalMatrixValue rationalComplexMul RationalComplexEqv
  constructor
  · ring_qeqv
  · refine Q'.eqv_trans _ (q.j * q.k + -(q.j * q.k)) _ ?_ (Q'.add_neg_self_eqv _)
    ring_qeqv

/-- The determinant-one relation comes from the actual quaternion norm,
not a separately assumed representation character law. -/
theorem unit_diagonal_product (q : RationalQuaternion.UnitNorm) :
    (fundamentalMatrixValue q.val false false ⊠ fundamentalMatrixValue q.val true true) ≃c
      𝟙 ⊞ (fundamentalMatrixValue q.val false true ⊠ fundamentalMatrixValue q.val true false) := by
  have hp : (q.val.r * q.val.r + q.val.i * q.val.i).eqv
      ((1 : Q') + -(q.val.j * q.val.j + q.val.k * q.val.k)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (q_remove _ _))
      (Q'.add_eqv_congr_right _ _ _ q.unitNorm)
  refine rationalComplexEqv_trans (fundamental_diagonal_product q.val) ?_
  refine rationalComplexEqv_trans (show
    (q.val.r * q.val.r + q.val.i * q.val.i, (0 : Q')) ≃c
      𝟙 ⊞ (-(q.val.j * q.val.j + q.val.k * q.val.k), 0) from ?_) ?_
  · exact ⟨hp, by change (0 : Q').eqv (0 + 0); ring_qeqv⟩
  · exact rationalComplexAdd_congr (rationalComplexEqv_refl _)
      (rationalComplexEqv_symm (fundamental_offdiagonal_product q.val))

private theorem unit_balance (x y b : RationalComplex) :
    (x ⊞ y) ⊞ (b ⊠ y) ≃c x ⊞ ((𝟙 ⊞ b) ⊠ y) := by
  unfold rationalComplexOne rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

theorem trace_unit_recurrence (q : RationalQuaternion.UnitNorm) (n : Nat) :
    trace (fundamentalMatrixValue q.val) (n + 2) ⊞ trace (fundamentalMatrixValue q.val) n ≃c
      (fundamentalMatrixValue q.val false false ⊞ fundamentalMatrixValue q.val true true) ⊠
        trace (fundamentalMatrixValue q.val) (n + 1) := by
  apply complex_cancel_right (z :=
    (fundamentalMatrixValue q.val false true ⊠ fundamentalMatrixValue q.val true false) ⊠
      trace (fundamentalMatrixValue q.val) n)
  refine rationalComplexEqv_trans (unit_balance _ _ _) ?_
  refine rationalComplexEqv_trans (rationalComplexAdd_congr (rationalComplexEqv_refl _)
    (rationalComplexMul_congr (rationalComplexEqv_symm (unit_diagonal_product q)) (rationalComplexEqv_refl _))) ?_
  exact trace_recurrence _ n

private theorem cheb_balance (r : Q') (n : Nat) :
    (YMGap.Continuum.Cheb.U (n + 2) r, 0) ⊞ (YMGap.Continuum.Cheb.U n r, 0) ≃c
      ((2 : Q') * r, 0) ⊠ (YMGap.Continuum.Cheb.U (n + 1) r, 0) := by
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _ _ _ (q_remove_neg _ _) ?_
    ring_qeqv
  · ring_qeqv

/-- At EVERY degree the trace of the concrete symmetric-power action is
the original second-kind Chebyshev character, with zero imaginary part.
The unit-norm quaternion is the same input as in the actual matrix action. -/
theorem trace_eq_cheb (q : RationalQuaternion.UnitNorm) : ∀ n,
    trace (fundamentalMatrixValue q.val) n ≃c (YMGap.Continuum.Cheb.U n q.val.r, 0)
  | 0 => trace_zero _
  | 1 => rationalComplexEqv_trans (trace_one _)
      (YMGap.Continuum.SU2QuaternionFundamentalTraceInversion.fundamentalMatrixTrace_value q.val)
  | n + 2 => by
    apply complex_cancel_right (z := trace (fundamentalMatrixValue q.val) n)
    refine rationalComplexEqv_trans (trace_unit_recurrence q n) ?_
    refine rationalComplexEqv_trans (rationalComplexMul_congr
      (YMGap.Continuum.SU2QuaternionFundamentalTraceInversion.fundamentalMatrixTrace_value q.val)
      (trace_eq_cheb q (n + 1))) ?_
    refine rationalComplexEqv_trans (rationalComplexEqv_symm (cheb_balance q.val.r n)) ?_
    exact rationalComplexAdd_congr (rationalComplexEqv_refl _) (rationalComplexEqv_symm (trace_eq_cheb q n))

/-- Consumer stated directly on the previously constructed coefficient action. -/
theorem symmetricAction_trace_eq_cheb (q : RationalQuaternion.UnitNorm) (n : Nat) :
    complexSum (n + 1) (fun k => symmetricAction n q.val (basis k) k) ≃c
      (YMGap.Continuum.Cheb.U n q.val.r, 0) := trace_eq_cheb q n

end YMGap.Continuum.SU2QuaternionSymmetricPowerTrace

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.rowValue
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.falseRowValue
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.rowValue_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.rowValue_false_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.coefficient_matrixAction
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.basis
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.diagonal
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.diagonal_eq_rowValue
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.rowValue_mixed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.diagonal_zero_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.diagonal_last_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.diagonal_mixed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.complexSum
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace_recurrence
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace_zero
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace_one
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.unit_diagonal_product
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace_unit_recurrence
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.trace_eq_cheb
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerTrace.symmetricAction_trace_eq_cheb
