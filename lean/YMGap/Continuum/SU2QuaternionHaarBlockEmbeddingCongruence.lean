/-
# Free-polynomial congruence under the original quaternion block embedding

The embedding maps every monomial and leaves its coefficient unchanged.
Pulling a coefficient probe back along this monomial map proves coefficient
congruence, with no support or Haar-positivity premise.

Padded coefficient equality needs BOTH source support guards. With support,
identity reindexing preserves every exponent, including those read at the
sentinel source index for unused target blocks. Its embedding is therefore
literally unchanged, and coefficient congruence transports the padded equality.

The consumer transports one compact original Wilson source identity first
into a finite slab and then into its centered physical charts. These are
free-polynomial coefficient identities, not arbitrary equalities modulo the
quaternion unit-sphere/radial ideal or multiplication of OS-null states.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
  (identityQuaternionBlockInvolution)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

private theorem exponent_zero_of_length :
    ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length m c
        (by simp only [List.length_cons] at h; omega)

/-- Support retains every coordinate, not just those below the padding length. -/
private theorem identity_exponent (source : Nat) (m : List Nat)
    (hm : m.length ≤ 4*source) (c : Nat) :
    exponentAt (reindexQuaternionExponents (identityQuaternionBlockInvolution source) m) c =
      exponentAt m c := by
  by_cases hc : c < 4*source
  · rw [exponentAt_reindexQuaternionExponents _ _ hc]
    change exponentAt m (4*(c/4)+c%4) = exponentAt m c
    exact congrArg (exponentAt m) (by omega)
  · rw [exponent_zero_of_length _ c
      (by rw [reindexQuaternionExponents_length]; omega),
      exponent_zero_of_length m c (by omega)]

variable {source target : Nat} (E : BlockEmbedding source target)

private theorem weighted_polynomial (weight : List Nat → Q') (p : RatPoly) :
    ratWeightedSum weight (E.polynomial p) =
      ratWeightedSum (fun m => weight (E.exponents m)) p := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
      change term.2 * weight (E.exponents term.1) + ratWeightedSum weight (E.polynomial rest) =
        term.2 * weight (E.exponents term.1) + ratWeightedSum (fun m => weight (E.exponents m)) rest
      rw [ih]

/-- Arbitrary coefficient probes pull back along the literal monomial map. -/
theorem polynomial_coeff_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (E.polynomial p) (E.polynomial q) := by
  intro weight
  rw [weighted_polynomial E weight p, weighted_polynomial E weight q]
  exact h (fun m => weight (E.exponents m))

private theorem exponents_identityReindex (m : List Nat) (hm : m.length ≤ 4*source) :
    E.exponents (reindexQuaternionExponents (identityQuaternionBlockInvolution source) m) =
      E.exponents m := by
  apply natList_eq_of_length_getD
  · rw [E.exponents_length, E.exponents_length]
  · intro c hc
    rw [E.exponents_length] at hc
    change exponentAt
      (E.exponents (reindexQuaternionExponents (identityQuaternionBlockInvolution source) m)) c =
      exponentAt (E.exponents m) c
    rw [E.exponent_pin _ hc, E.exponent_pin _ hc]
    exact identity_exponent source m hm _

/-- Original source padding has no effect after embedding when the source is supported. -/
theorem polynomial_identityReindex (p : RatPoly) (hp : SupportedQuaternionBlocks source p) :
    E.polynomial (reindexQuaternionPolynomial (identityQuaternionBlockInvolution source) p) =
      E.polynomial p := by
  unfold polynomial reindexQuaternionPolynomial
  rw [List.map_map]
  apply List.map_congr_left
  intro term ht
  change (E.exponents
    (reindexQuaternionExponents (identityQuaternionBlockInvolution source) term.1), term.2) =
    (E.exponents term.1, term.2)
  rw [exponents_identityReindex E term.1 (hp term ht)]

/-- Both support guards prevent out-of-source exponents entering unused target blocks. -/
theorem polynomial_padded_congr {p q : RatPoly}
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (h : PaddedPolynomialCoeffEqv source p q) :
    PaddedPolynomialCoeffEqv target (E.polynomial p) (E.polynomial q) := by
  apply PaddedPolynomialCoeffEqv.of_coeff
  have he : RatPolyCoeffEqv
      (E.polynomial (reindexQuaternionPolynomial (identityQuaternionBlockInvolution source) p))
      (E.polynomial (reindexQuaternionPolynomial (identityQuaternionBlockInvolution source) q)) :=
    E.polynomial_coeff_congr h
  rw [E.polynomial_identityReindex p hp, E.polynomial_identityReindex q hq] at he
  exact he

#print axioms polynomial_coeff_congr
#print axioms polynomial_identityReindex
#print axioms polynomial_padded_congr

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding
