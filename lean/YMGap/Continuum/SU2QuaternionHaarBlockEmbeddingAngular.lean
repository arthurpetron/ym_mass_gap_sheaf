/-
# Actual angular differentiation under an injective Haar block embedding

Partial derivatives are transported on the literal exponent lists FIRST.
Only the subsequent coordinate multiplication uses common-padding equality.
Source support is essential for off-image zero and Haar reflection; no padded
equivalence is differentiated. These are finite polynomial/Haar identities,
not a transfer bound, completed Gauss domain, or continuum statement.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)

local infix:50 " ≈ " => Q'.eqv

variable {source target : Nat} (E : BlockEmbedding source target)

private theorem lowered_exponent (coordinate destination : Nat) (m : List Nat) :
    exponentAt (lowerExponentAt coordinate m) destination =
      if coordinate = destination then exponentAt m destination - 1
      else exponentAt m destination := by
  induction coordinate generalizing destination m with
  | zero =>
      cases m with
      | nil => cases destination <;> rfl
      | cons exponent rest => cases destination <;> rfl
  | succ coordinate ih =>
      cases m with
      | nil =>
          cases destination with
          | zero =>
              rw [if_neg (show coordinate + 1 ≠ 0 by omega)]
              rfl
          | succ destination =>
              by_cases h : coordinate = destination
              · subst destination
                rw [if_pos rfl]
                rfl
              · rw [if_neg (show coordinate + 1 ≠ destination + 1 by omega)]
                rfl
      | cons exponent rest =>
          cases destination with
          | zero => rfl
          | succ destination =>
              simpa only [lowerExponentAt, exponentAt, Nat.succ.injEq] using
                ih destination rest

private theorem lowered_length (coordinate : Nat) : ∀ m : List Nat,
    (lowerExponentAt coordinate m).length = m.length
  | [] => by cases coordinate <;> rfl
  | _ :: rest => by
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          simp only [lowerExponentAt, List.length_cons]
          exact congrArg Nat.succ (lowered_length coordinate rest)

private theorem mapped_coordinate_exponent {b i : Nat}
    (hb : b < source) (hi : i < 4) (m : List Nat) :
    exponentAt (E.exponents m) (4 * E.block b + i) = exponentAt m (4 * b + i) := by
  have hblock := E.block_lt hb
  rw [E.exponent_pin m (by omega)]
  have hdiv : (4 * E.block b + i) / 4 = E.block b := by omega
  have hmod : (4 * E.block b + i) % 4 = i := by omega
  rw [hdiv, hmod, E.index_block hb]

private theorem exponents_lower {b i : Nat} (hb : b < source) (hi : i < 4)
    (m : List Nat) :
    E.exponents (lowerExponentAt (4 * b + i) m) =
      lowerExponentAt (4 * E.block b + i) (E.exponents m) := by
  apply natList_eq_of_length_getD
  · rw [E.exponents_length, lowered_length, E.exponents_length]
  · intro c hc
    rw [E.exponents_length] at hc
    have hmod : c % 4 < 4 := Nat.mod_lt _ (by decide)
    have hsame : (4 * b + i = 4 * E.index (c / 4) + c % 4) ↔
        (4 * E.block b + i = c) := by
      constructor
      · intro h
        have hidx : E.index (c / 4) = b := by omega
        have hblock : c / 4 = E.block b := (E.index_eq_block hb).mp hidx
        omega
      · intro h
        have hdiv : c / 4 = E.block b := by omega
        have hcomponent : c % 4 = i := by omega
        rw [hdiv, hcomponent, E.index_block hb]
    change exponentAt (E.exponents (lowerExponentAt (4 * b + i) m)) c =
      exponentAt (lowerExponentAt (4 * E.block b + i) (E.exponents m)) c
    rw [E.exponent_pin _ hc, lowered_exponent, lowered_exponent,
      E.exponent_pin m hc]
    simp only [hsame]

/-- Exact actual partial-derivative transport, before any padding relation.
It does not need source support: the differentiated coordinate is in the image. -/
theorem polynomial_ratDerivative_exact {b i : Nat}
    (hb : b < source) (hi : i < 4) (p : RatPoly) :
    E.polynomial (ratDerivative (4 * b + i) p) =
      ratDerivative (4 * E.block b + i) (E.polynomial p) := by
  unfold polynomial ratDerivative
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => p.map f)
  funext term
  simp only [Function.comp_apply]
  rw [E.exponents_lower hb hi, E.mapped_coordinate_exponent hb hi]

theorem polynomial_ratDerivative {b i : Nat}
    (hb : b < source) (hi : i < 4) (p : RatPoly) :
    RatPolyCoeffEqv (E.polynomial (ratDerivative (4 * b + i) p))
      (ratDerivative (4 * E.block b + i) (E.polynomial p)) := by
  rw [E.polynomial_ratDerivative_exact hb hi]
  exact RatPolyCoeffEqv.refl _

/-- Actual angular differentiation commutes with embedding, at common-padded
coefficient strength. No derivative is applied to a padded equality. -/
theorem polynomial_blockAngularDerivative {b i j : Nat}
    (hb : b < source) (hi : i < 4) (hj : j < 4) (p : RatPoly) :
    PaddedPolynomialCoeffEqv target
      (E.polynomial (blockAngularDerivative b i j p))
      (blockAngularDerivative (E.block b) i j (E.polynomial p)) := by
  unfold blockAngularDerivative angularDerivative
  rw [E.polynomial_add, E.polynomial_mul, E.polynomial_smul, E.polynomial_mul]
  exact PaddedPolynomialCoeffEqv.add
    ((PaddedPolynomialCoeffEqv.of_prefix (E.polynomial_var hb hi)).mul
      (PaddedPolynomialCoeffEqv.of_coeff (E.polynomial_ratDerivative hb hj p)))
    (((PaddedPolynomialCoeffEqv.of_prefix (E.polynomial_var hb hj)).mul
      (PaddedPolynomialCoeffEqv.of_coeff (E.polynomial_ratDerivative hb hi p))).smul (-1))

private theorem exponent_zero_of_length : ∀ (m : List Nat) (c : Nat),
    m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: rest, c + 1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length rest c (by simp only [List.length_cons] at h; omega)

/-- Off-image derivatives vanish coefficientwise for a genuinely supported
source. Zero-coefficient terms need not be deleted from the literal list. -/
theorem ratDerivative_offImage_zero {d i : Nat} (hd : d < target)
    (hout : d ∉ E.image) (hi : i < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks source p) :
    RatPolyCoeffEqv (ratDerivative (4 * d + i) (E.polynomial p)) polyZero := by
  intro weight
  revert hp
  induction p with
  | nil => intro _; exact Q'.eqv_refl 0
  | cons term rest ih =>
      intro hp
      have htail : SupportedQuaternionBlocks source rest :=
        fun t ht => hp t (List.mem_cons_of_mem term ht)
      have hexponent : exponentAt (E.exponents term.1) (4 * d + i) = 0 := by
        rw [E.exponent_pin _ (by omega)]
        have hdiv : (4 * d + i) / 4 = d := by omega
        have hmod : (4 * d + i) % 4 = i := by omega
        rw [hdiv, hmod, E.index_not_mem hout]
        exact exponent_zero_of_length _ _ (by
          have hlength := hp term List.mem_cons_self
          omega)
      change (Q'.ofNat (exponentAt (E.exponents term.1) (4 * d + i)) * term.2) *
          weight (lowerExponentAt (4 * d + i) (E.exponents term.1)) +
          ratWeightedSum weight (ratDerivative (4 * d + i) (E.polynomial rest)) ≈ 0
      rw [hexponent]
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv term.2))
            (Q'.zero_mul_eqv _))
          (ih htail)) (QPoly.q_add_zero_eqv 0)

/-- Every angular plane in an unused target block annihilates the embedded
supported source, including diagonal planes and zero-dimensional carriers. -/
theorem blockAngularDerivative_offImage_zero {d i j : Nat} (hd : d < target)
    (hout : d ∉ E.image) (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks source p) :
    RatPolyCoeffEqv (blockAngularDerivative d i j (E.polynomial p)) polyZero := by
  unfold blockAngularDerivative angularDerivative
  have hleft := ((E.ratDerivative_offImage_zero hd hout hj hp).mul_left
    (polyVar (4 * d + i))).trans (RatPolyCoeffEqv.mul_zero_right _)
  have hright := ((E.ratDerivative_offImage_zero hd hout hi hp).mul_left
    (polyVar (4 * d + j))).trans (RatPolyCoeffEqv.mul_zero_right _)
  exact (hleft.add (hright.smul (-1))).trans
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_zero (-1))).trans
      (RatPolyCoeffEqv.add_zero _))

/-- Reflect genuine supported Haar identities through the same embedding.
Both source supports are retained; no unrestricted tail insertion is inferred. -/
theorem polynomial_supportedHaar_reflect {p q : RatPoly}
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (h : SupportedHaarEqv target (E.polynomial p) (E.polynomial q)) :
    SupportedHaarEqv source p q := by
  let d := polyAdd p (polySmul (-1) q)
  have hd : SupportedQuaternionBlocks source d :=
    supported_add hp (polySmul_supported hq (-1))
  have hmap := E.haar (polyMul d d) (supported_polyMul hd hd)
  dsimp only [d] at hmap
  rw [E.polynomial_mul, E.polynomial_add, E.polynomial_smul] at hmap
  exact supportedHaarEqv_of_difference_square_zero hp hq
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hmap)
      (difference_square_zero (E.polynomial_supported p) (E.polynomial_supported q) h))

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_ratDerivative_exact
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_ratDerivative
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_blockAngularDerivative
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.ratDerivative_offImage_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.blockAngularDerivative_offImage_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_supportedHaar_reflect
