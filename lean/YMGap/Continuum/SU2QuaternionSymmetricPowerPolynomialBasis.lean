/-
# Explicit polynomial symmetric basis and its positive rational dual weights

The polynomial tensor action reconstructs from the ORIGINAL two-row
coefficients. Pairing a coefficient basis tensor against an embedded vector
extracts that coefficient times C(n,k), proved by Pascal recursion. Its
positive rational reciprocal is explicit; no orthonormalization, square
root, eigenvector choice, or positivity premise is used.
-/

import YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
import YMGap.RG.PolylogTail
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈c " => ComplexCoeffEqv
local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "𝟘" => complexRatPolyZero
local notation "𝟙" => complexRatPolyOne
private abbrev A := fundamentalMatrixCoefficient

def polyRealScale (s : Q') (z : ComplexRatPoly) : ComplexRatPoly := (polySmul s z.1, polySmul s z.2)

theorem polyRealScale_congr {s t : Q'} (hs : s.eqv t) {x y : ComplexRatPoly} (h : x ≈c y) :
    polyRealScale s x ≈c polyRealScale t y :=
  ⟨(h.1.smul s).trans (RatPolyCoeffEqv.smul_coefficient hs _),
    (h.2.smul s).trans (RatPolyCoeffEqv.smul_coefficient hs _)⟩

theorem polyRealScale_one (z : ComplexRatPoly) : polyRealScale 1 z ≈c z :=
  ⟨RatPolyCoeffEqv.one_smul _, RatPolyCoeffEqv.one_smul _⟩

theorem polyRealScale_zero (z : ComplexRatPoly) : polyRealScale 0 z ≈c 𝟘 :=
  ⟨RatPolyCoeffEqv.zero_smul _, RatPolyCoeffEqv.zero_smul _⟩

theorem polyRealScale_add_same (s t : Q') (z : ComplexRatPoly) :
    (polyRealScale s z ⊞ polyRealScale t z) ≈c polyRealScale (s + t) z :=
  ⟨RatPolyCoeffEqv.add_smul_same _ _ _, RatPolyCoeffEqv.add_smul_same _ _ _⟩

theorem polyRealScale_assoc (s t : Q') (z : ComplexRatPoly) :
    polyRealScale s (polyRealScale t z) ≈c polyRealScale (s * t) z :=
  ⟨RatPolyCoeffEqv.smul_assoc _ _ _, RatPolyCoeffEqv.smul_assoc _ _ _⟩

/-- Literal polynomial version of the symmetric coefficient embedding. -/
def polyEmbed : (n : Nat) → (Nat → ComplexRatPoly) → PolyTensor n
  | 0, f => f 0
  | n + 1, f => fun b => polyEmbed n (fun k => if b then f (k + 1) else f k)

theorem polyEmbed_congr : ∀ (n : Nat) {f g : Nat → ComplexRatPoly},
    (∀ k, k ≤ n → f k ≈c g k) → PolyTensorEqv n (polyEmbed n f) (polyEmbed n g)
  | 0, _, _, h => h 0 (by omega)
  | n + 1, f, g, h => by
    intro b
    cases b
    · exact polyEmbed_congr n (fun k hk => h k (by omega))
    · exact polyEmbed_congr n (fun k hk => h (k + 1) (by omega))

theorem polyEmbed_add : ∀ (n : Nat) (f g : Nat → ComplexRatPoly),
    PolyTensorEqv n (polyEmbed n (fun k => f k ⊞ g k)) (polyTensorAdd n (polyEmbed n f) (polyEmbed n g))
  | 0, f, g => ComplexCoeffEqv.refl (f 0 ⊞ g 0)
  | n + 1, f, g => by
    intro b
    cases b
    · exact polyEmbed_add n f g
    · exact polyEmbed_add n (fun k => f (k + 1)) (fun k => g (k + 1))

theorem polyEmbed_scale (a : ComplexRatPoly) : ∀ (n : Nat) (f : Nat → ComplexRatPoly),
    PolyTensorEqv n (polyEmbed n (fun k => a ⊠ f k)) (polyTensorScale n a (polyEmbed n f))
  | 0, f => ComplexCoeffEqv.refl (a ⊠ f 0)
  | n + 1, f => by
    intro b
    cases b
    · exact polyEmbed_scale a n f
    · exact polyEmbed_scale a n (fun k => f (k + 1))

private theorem polyEmbed_mix (n : Nat) (a b : ComplexRatPoly) (f g : Nat → ComplexRatPoly) :
    PolyTensorEqv n (polyEmbed n (fun k => (a ⊠ f k) ⊞ (b ⊠ g k)))
      (polyTensorAdd n (polyTensorScale n a (polyEmbed n f)) (polyTensorScale n b (polyEmbed n g))) :=
  (polyEmbed_add n _ _).trans ((polyEmbed_scale a n f).add (polyEmbed_scale b n g))

/-- The full acted tensor is reconstructed from the ORIGINAL polynomial
row formula, with coefficient probes retained at every coordinate. -/
theorem polyMatrixAction_embed (q : RatPolyQuaternion) : ∀ (n : Nat) (f : Nat → ComplexRatPoly),
    PolyTensorEqv n (polyMatrixAction n (A q) (polyEmbed n f))
      (polyEmbed n (fun k => polynomialRow q (n - k) k f))
  | 0, f => ComplexCoeffEqv.refl (f 0)
  | n + 1, f => by
    intro b
    refine ((PolyTensorEqv.scale (ComplexCoeffEqv.refl (A q b false)) (polyMatrixAction_embed q n f)).add
      (PolyTensorEqv.scale (ComplexCoeffEqv.refl (A q b true))
        (polyMatrixAction_embed q n (fun j => f (j + 1))))).trans ?_
    refine (polyEmbed_mix n (A q b false) (A q b true) _ _).symm.trans ?_
    apply polyEmbed_congr n
    intro k hk
    cases b
    · have he : n + 1 - k = (n - k) + 1 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, he]
      exact (row_false_succ q (n - k) k f).symm
    · simp only [↓reduceIte, Nat.add_sub_add_right, polynomialRow]
      exact ComplexCoeffEqv.refl _

private theorem basis_shift (k : Nat) : (fun j => polynomialBasis (k + 1) (j + 1)) = polynomialBasis k := by
  funext j
  simp only [polynomialBasis, Nat.add_right_cancel_iff]

private theorem basis_zero_shift : (fun j => polynomialBasis 0 (j + 1)) = (fun _ => 𝟘) := by
  funext j
  simp only [polynomialBasis, Nat.add_one_ne_zero, ↓reduceIte]

private theorem inner_embed_zero : ∀ (n : Nat) (f : Nat → ComplexRatPoly),
    polyTensorInner n (polyEmbed n (fun _ => 𝟘)) (polyEmbed n f) ≈c 𝟘
  | 0, f => zero_mul (f 0)
  | n + 1, f => ((inner_embed_zero n f).add
      (inner_embed_zero n (fun k => f (k + 1)))).trans (zero_add _)

/-- Pairing with the k-th actual basis tensor extracts the coefficient
with its binomial multiplicity. This includes the vanishing out-of-window
cases and holds before evaluation or integration. -/
theorem polyTensorInner_basis : ∀ (n : Nat) (f : Nat → ComplexRatPoly) (k : Nat),
    polyTensorInner n (polyEmbed n (polynomialBasis k)) (polyEmbed n f) ≈c
      polyRealScale (Q'.ofNat (binom n k)) (f k)
  | 0, f, 0 => (one_mul (f 0)).trans (polyRealScale_one (f 0)).symm
  | 0, f, k + 1 => (zero_mul (f 0)).trans (polyRealScale_zero (f (k + 1))).symm
  | n + 1, f, 0 => by
    change (polyTensorInner n (polyEmbed n (polynomialBasis 0)) (polyEmbed n f) ⊞
      polyTensorInner n (polyEmbed n (fun j => polynomialBasis 0 (j + 1)))
        (polyEmbed n (fun j => f (j + 1)))) ≈c _
    rw [basis_zero_shift]
    simpa only [binom_zero_right] using
      ((polyTensorInner_basis n f 0).add (inner_embed_zero n (fun j => f (j + 1)))).trans (add_zero _)
  | n + 1, f, k + 1 => by
    change (polyTensorInner n (polyEmbed n (polynomialBasis (k + 1))) (polyEmbed n f) ⊞
      polyTensorInner n (polyEmbed n (fun j => polynomialBasis (k + 1) (j + 1)))
        (polyEmbed n (fun j => f (j + 1)))) ≈c _
    rw [basis_shift]
    refine ((polyTensorInner_basis n f (k + 1)).add
      (polyTensorInner_basis n (fun j => f (j + 1)) k)).trans ?_
    exact (add_comm _ _).trans ((polyRealScale_add_same _ _ _).trans
      (polyRealScale_congr (Q'.eqv_symm (Q'.ofNat_add_eqv _ _)) (ComplexCoeffEqv.refl _)))

theorem basisWeight_pos : ∀ n k, k ≤ n → 0 < binom n k
  | _, 0, _ => by simp only [binom_zero_right]; omega
  | 0, k + 1, hk => by omega
  | n + 1, k + 1, hk => by
    have h := basisWeight_pos n k (by omega)
    rw [binom_succ_succ]
    omega

/-- Positive, explicit reciprocal of the basis norm on 0..n. The total
fallback outside that window is not used by the trace decomposition. -/
def basisInverseWeight (n k : Nat) : Q' := Q'.invSucc (binom n k - 1)

theorem basisInverseWeight_pos (n k : Nat) : (0 : Q') < basisInverseWeight n k := Q'.invSucc_pos _

theorem basisInverseWeight_cancel (n k : Nat) (hk : k ≤ n) :
    (basisInverseWeight n k * Q'.ofNat (binom n k)).eqv 1 := by
  have h : binom n k - 1 + 1 = binom n k := by have := basisWeight_pos n k hk; omega
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (by simpa only [basisInverseWeight, h] using Q'.ofNat_succ_mul_invSucc (binom n k - 1))

/-- Explicit dual-basis extraction; its denominator has a proved positive
natural witness, so no division by an opaque or possibly zero norm occurs. -/
theorem polyTensorInner_basis_extract (n : Nat) (f : Nat → ComplexRatPoly) (k : Nat) (hk : k ≤ n) :
    polyRealScale (basisInverseWeight n k)
      (polyTensorInner n (polyEmbed n (polynomialBasis k)) (polyEmbed n f)) ≈c f k :=
  (polyRealScale_congr (Q'.eqv_refl _) (polyTensorInner_basis n f k)).trans
    ((polyRealScale_assoc _ _ _).trans
      ((polyRealScale_congr (basisInverseWeight_cancel n k hk) (ComplexCoeffEqv.refl _)).trans
        (polyRealScale_one _)))

end YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale_one
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale_zero
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale_add_same
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyRealScale_assoc
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyEmbed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyEmbed_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyEmbed_add
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyEmbed_scale
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyMatrixAction_embed
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyTensorInner_basis
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.basisWeight_pos
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.basisInverseWeight
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.basisInverseWeight_pos
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.basisInverseWeight_cancel
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis.polyTensorInner_basis_extract
