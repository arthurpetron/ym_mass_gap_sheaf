/-
# The literal symmetric-power trace recurrence with all coefficients retained

This lifts the two-row proof to the ORIGINAL polynomialMatrixCoefficient
and polynomialTrace. Every equality is componentwise RatPolyCoeffEqv;
no value-level trace equality is transported through integration.
-/

import YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial

local infix:50 " ≈c " => ComplexCoeffEqv
local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "𝟘" => complexRatPolyZero
local notation "𝟙" => complexRatPolyOne
private abbrev A := fundamentalMatrixCoefficient
private abbrev D (q : RatPolyQuaternion) (n k : Nat) := polynomialMatrixCoefficient q n k k

theorem row_congr (q : RatPolyQuaternion) : ∀ m k {f g : Nat → ComplexRatPoly},
    (∀ j, j ≤ m + k → f j ≈c g j) → polynomialRow q m k f ≈c polynomialRow q m k g
  | 0, 0, _, _, h => h 0 (by omega)
  | m + 1, 0, _, _, h =>
    ((ComplexCoeffEqv.refl _).mul (row_congr q m 0 (fun j hj => h j (by omega)))).add
      ((ComplexCoeffEqv.refl _).mul (row_congr q m 0 (fun j hj => h (j + 1) (by omega))))
  | m, k + 1, _, _, h =>
    ((ComplexCoeffEqv.refl _).mul (row_congr q m k (fun j hj => h j (by omega)))).add
      ((ComplexCoeffEqv.refl _).mul (row_congr q m k (fun j hj => h (j + 1) (by omega))))

theorem row_false_succ (q : RatPolyQuaternion) (m k : Nat) (f : Nat → ComplexRatPoly) :
    polynomialRow q (m + 1) k f ≈c
      ((A q false false ⊠ polynomialRow q m k f) ⊞
        (A q false true ⊠ polynomialRow q m k (fun j => f (j + 1)))) := by
  induction k generalizing f with
  | zero => exact ComplexCoeffEqv.refl _
  | succ k ih =>
    exact (((ComplexCoeffEqv.refl _).mul (ih f)).add
      ((ComplexCoeffEqv.refl _).mul (ih (fun j => f (j + 1))))).trans (mix_swap _ _ _ _ _ _ _)

private theorem basis_shift (k : Nat) : (fun j => polynomialBasis (k + 1) (j + 1)) = polynomialBasis k := by
  funext j
  simp only [polynomialBasis, Nat.add_right_cancel_iff]

private theorem row_zero (q : RatPolyQuaternion) : ∀ m k, polynomialRow q m k (fun _ => 𝟘) ≈c 𝟘
  | 0, 0 => ComplexCoeffEqv.refl _
  | m + 1, 0 =>
    (((ComplexCoeffEqv.refl _).mul (row_zero q m 0)).add
      ((ComplexCoeffEqv.refl _).mul (row_zero q m 0))).trans
      (((mul_zero _).add (mul_zero _)).trans (zero_add _))
  | m, k + 1 =>
    (((ComplexCoeffEqv.refl _).mul (row_zero q m k)).add
      ((ComplexCoeffEqv.refl _).mul (row_zero q m k))).trans
      (((mul_zero _).add (mul_zero _)).trans (zero_add _))

private theorem row_vanish (q : RatPolyQuaternion) (m k : Nat) (f : Nat → ComplexRatPoly)
    (h : ∀ j, j ≤ m + k → f j = 𝟘) : polynomialRow q m k f ≈c 𝟘 :=
  (row_congr q m k (fun j hj => by rw [h j hj]; exact ComplexCoeffEqv.refl _)).trans (row_zero q m k)

/-- Mixed row identity at coefficient-probe strength, with both determinant
products visible and every spectator polynomial retained. -/
theorem row_mixed (q : RatPolyQuaternion) (m k j : Nat) :
    (polynomialRow q (m + 1) (k + 1) (polynomialBasis (j + 1)) ⊞
      ((A q false false ⊠ A q true true) ⊠ polynomialRow q m k (polynomialBasis j))) ≈c
    (((A q false false ⊠ polynomialRow q m (k + 1) (polynomialBasis (j + 1))) ⊞
      (A q true true ⊠ polynomialRow q (m + 1) k (polynomialBasis j))) ⊞
      ((A q false true ⊠ A q true false) ⊠ polynomialRow q m k (polynomialBasis j))) := by
  have hfirst := row_false_succ q m k (polynomialBasis (j + 1))
  rw [basis_shift] at hfirst
  have hsecond := row_false_succ q m k (polynomialBasis j)
  have hl : polynomialRow q (m + 1) (k + 1) (polynomialBasis (j + 1)) ≈c
      ((A q true false ⊠ ((A q false false ⊠ polynomialRow q m k (polynomialBasis (j + 1))) ⊞
        (A q false true ⊠ polynomialRow q m k (polynomialBasis j)))) ⊞
      (A q true true ⊠ ((A q false false ⊠ polynomialRow q m k (polynomialBasis j)) ⊞
        (A q false true ⊠ polynomialRow q m k (fun i => polynomialBasis j (i + 1)))))) := by
    rw [polynomialRow, basis_shift]
    exact ((ComplexCoeffEqv.refl _).mul hfirst).add ((ComplexCoeffEqv.refl _).mul hsecond)
  refine (hl.add (ComplexCoeffEqv.refl _)).trans ((mixed_balance _ _ _ _ _ _ _).trans ?_)
  apply ComplexCoeffEqv.add
  · apply ComplexCoeffEqv.add
    · rw [polynomialRow, basis_shift]
      exact ComplexCoeffEqv.refl _
    · exact (ComplexCoeffEqv.refl _).mul hsecond.symm
  · exact ComplexCoeffEqv.refl _

theorem diagonal_zero_succ (q : RatPolyQuaternion) (n : Nat) :
    D q (n + 1) 0 ≈c (A q false false ⊠ D q n 0) := by
  have hz := row_vanish q n 0 (fun j => polynomialBasis 0 (j + 1)) (by
    intro j _
    simp only [polynomialBasis, Nat.add_one_ne_zero, ↓reduceIte])
  exact ((ComplexCoeffEqv.refl _).add ((ComplexCoeffEqv.refl _).mul hz)).trans
    (((ComplexCoeffEqv.refl _).add (mul_zero _)).trans (add_zero _))

theorem diagonal_last_succ (q : RatPolyQuaternion) (n : Nat) :
    D q (n + 1) (n + 1) ≈c (A q true true ⊠ D q n n) := by
  simp only [D, polynomialMatrixCoefficient, Nat.sub_self]
  rw [polynomialRow, basis_shift]
  have hz := row_vanish q 0 n (polynomialBasis (n + 1)) (by
    intro j hj
    have hne : j ≠ n + 1 := by omega
    simp only [polynomialBasis, hne, ↓reduceIte])
  exact (((ComplexCoeffEqv.refl _).mul hz).add (ComplexCoeffEqv.refl _)).trans
    (((mul_zero _).add (ComplexCoeffEqv.refl _)).trans (zero_add _))

theorem diagonal_mixed (q : RatPolyQuaternion) (n k : Nat) (hk : k ≤ n) :
    (D q (n + 2) (k + 1) ⊞ ((A q false false ⊠ A q true true) ⊠ D q n k)) ≈c
      (((A q false false ⊠ D q (n + 1) (k + 1)) ⊞ (A q true true ⊠ D q (n + 1) k)) ⊞
        ((A q false true ⊠ A q true false) ⊠ D q n k)) := by
  have e1 : n + 1 - (k + 1) = n - k := by omega
  have e2 : n + 1 - k = n - k + 1 := by omega
  have e3 : n + 2 - (k + 1) = n - k + 1 := by omega
  simp only [D, polynomialMatrixCoefficient, e1, e2, e3]
  exact row_mixed q (n - k) k k

theorem sum_congr : ∀ n {f g : Nat → ComplexRatPoly},
    (∀ j, j < n → f j ≈c g j) → polynomialSum n f ≈c polynomialSum n g
  | 0, _, _, _ => ComplexCoeffEqv.refl _
  | n + 1, _, _, h => (sum_congr n (fun j hj => h j (by omega))).add (h n (by omega))

theorem sum_add : ∀ n (f g : Nat → ComplexRatPoly),
    polynomialSum n (fun j => f j ⊞ g j) ≈c (polynomialSum n f ⊞ polynomialSum n g)
  | 0, _, _ => (zero_add _).symm
  | n + 1, f, g => ((sum_add n f g).add (ComplexCoeffEqv.refl _)).trans (add_swap _ _ _ _)

theorem sum_scale (a : ComplexRatPoly) : ∀ n (f : Nat → ComplexRatPoly),
    polynomialSum n (fun j => a ⊠ f j) ≈c (a ⊠ polynomialSum n f)
  | 0, _ => (mul_zero _).symm
  | n + 1, f => ((sum_scale a n f).add (ComplexCoeffEqv.refl _)).trans (mul_add _ _ _).symm

private theorem sum_shift : ∀ n (f : Nat → ComplexRatPoly),
    polynomialSum (n + 1) f ≈c (f 0 ⊞ polynomialSum n (fun j => f (j + 1)))
  | 0, _ => add_comm _ _
  | n + 1, f => ((sum_shift n f).add (ComplexCoeffEqv.refl _)).trans (add_assoc _ _ _)

private theorem sum_mixed (q : RatPolyQuaternion) (n : Nat) :
    (polynomialSum (n + 1) (fun k => D q (n + 2) (k + 1)) ⊞
      ((A q false false ⊠ A q true true) ⊠ polynomialTrace q n)) ≈c
    (((A q false false ⊠ polynomialSum (n + 1) (fun k => D q (n + 1) (k + 1))) ⊞
      (A q true true ⊠ polynomialSum (n + 1) (D q (n + 1)))) ⊞
      ((A q false true ⊠ A q true false) ⊠ polynomialTrace q n)) := by
  refine ((sum_add _ _ _).trans ((ComplexCoeffEqv.refl _).add (sum_scale _ _ _))).symm.trans ?_
  refine (sum_congr (n + 1) (fun k hk => diagonal_mixed q n k (by omega))).trans ?_
  exact (sum_add _ _ _).trans
    (((sum_add _ _ _).trans ((sum_scale _ _ _).add (sum_scale _ _ _))).add (sum_scale _ _ _))

/-- Trace recurrence on the ORIGINAL raw polynomial matrix, valid against
arbitrary real and imaginary coefficient probes. -/
theorem polynomialTrace_recurrence (q : RatPolyQuaternion) (n : Nat) :
    (polynomialTrace q (n + 2) ⊞ ((A q false false ⊠ A q true true) ⊠ polynomialTrace q n)) ≈c
      (((A q false false ⊞ A q true true) ⊠ polynomialTrace q (n + 1)) ⊞
        ((A q false true ⊠ A q true false) ⊠ polynomialTrace q n)) := by
  have hsplit : polynomialTrace q (n + 2) ≈c
      ((D q (n + 2) 0 ⊞ polynomialSum (n + 1) (fun k => D q (n + 2) (k + 1))) ⊞ D q (n + 2) (n + 2)) :=
    (sum_shift (n + 1) _).add (ComplexCoeffEqv.refl _)
  have hboundary := hsplit.trans
    (((diagonal_zero_succ q (n + 1)).add (ComplexCoeffEqv.refl _)).add (diagonal_last_succ q (n + 1)))
  refine (hboundary.add (ComplexCoeffEqv.refl _)).trans ((balance_reorder _ _ _ _ _ _).trans ?_)
  refine (((ComplexCoeffEqv.refl _).add (sum_mixed q n)).add (ComplexCoeffEqv.refl _)).trans ?_
  refine (balance_contract _ _ _ _ _ _ _).trans ?_
  refine ((((ComplexCoeffEqv.refl _).mul (sum_shift (n + 1) _).symm).add
    (ComplexCoeffEqv.refl _)).add (ComplexCoeffEqv.refl _)).trans ?_
  exact (add_mul _ _ _).symm.add (ComplexCoeffEqv.refl _)

theorem polynomialTrace_zero (q : RatPolyQuaternion) : polynomialTrace q 0 ≈c 𝟙 := zero_add _

theorem polynomialTrace_one (q : RatPolyQuaternion) :
    polynomialTrace q 1 ≈c (A q false false ⊞ A q true true) := by
  change ((𝟘 ⊞ ((A q false false ⊠ 𝟙) ⊞ (A q false true ⊠ 𝟘))) ⊞
      ((A q true false ⊠ 𝟘) ⊞ (A q true true ⊠ 𝟙))) ≈c _
  exact ((zero_add _).trans (((mul_one _).add (mul_zero _)).trans (add_zero _))).add
    (((mul_zero _).add (mul_one _)).trans (zero_add _))

end YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.row_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.row_false_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.row_mixed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.diagonal_zero_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.diagonal_last_succ
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.diagonal_mixed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.sum_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.sum_add
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.sum_scale
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.polynomialTrace_recurrence
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.polynomialTrace_zero
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace.polynomialTrace_one
