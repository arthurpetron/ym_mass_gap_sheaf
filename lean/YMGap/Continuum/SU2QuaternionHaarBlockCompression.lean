/-
# Exact compression to the image of a quaternion block embedding

Read the four exponents at each explicitly placed source block, retaining
the original coefficient and term order. For a polynomial local to the
embedding image, embedding this computed restriction back reconstructs its
entire target prefix. Supported target polynomials therefore have exactly
the same normalized quaternion Haar integral on the smaller carrier.

The intended consumer is an original Haar integral whose surviving spatial
boundary blocks have already been identified geometrically. This module
only recodes those same variables; it supplies no interacting marginal,
stationary transfer, positivity estimate, or continuum assertion.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
import YMGap.Continuum.SU2QuaternionBlockLocality

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality

local infix:50 " ≈ " => Q'.eqv

variable {source target : Nat} (E : BlockEmbedding source target)

/-- Read target exponents in the supplied source-block order. -/
def compressExponents (m : List Nat) : List Nat :=
  List.ofFn (fun c : Fin (4 * source) =>
    exponentAt m (4 * E.block (c.val / 4) + c.val % 4))

theorem compressExponents_length (m : List Nat) :
    (E.compressExponents m).length = 4 * source := List.length_ofFn

theorem compress_exponent_pin (m : List Nat) {c : Nat}
    (hc : c < 4 * source) :
    exponentAt (E.compressExponents m) c =
      exponentAt m (4 * E.block (c / 4) + c % 4) := by
  unfold exponentAt
  rw [← List.getElem_eq_getD
    (h := by rw [E.compressExponents_length]; exact hc)]
  exact List.getElem_ofFn
    (h := by rw [List.length_ofFn]; exact hc)

private theorem exponent_zero_of_length :
    ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: m, c + 1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length m c
        (by simp only [List.length_cons] at h; omega)

/-- Locality makes the omitted target blocks literal zero exponents. -/
theorem exponents_compress_pin (m : List Nat)
    (hm : ∀ b, b < target → b ∉ E.image → BlockZero m b)
    {c : Nat} (hc : c < 4 * target) :
    exponentAt (E.exponents (E.compressExponents m)) c =
      exponentAt m c := by
  rw [E.exponent_pin _ hc]
  have hb : c / 4 < target := by omega
  have hr : c % 4 < 4 := by omega
  by_cases hmem : c / 4 ∈ E.image
  · have hi := E.index_lt hmem
    rw [E.compress_exponent_pin m (by omega)]
    have hdiv : (4 * E.index (c / 4) + c % 4) / 4 =
        E.index (c / 4) := by omega
    have hmod : (4 * E.index (c / 4) + c % 4) % 4 =
        c % 4 := by omega
    rw [hdiv, hmod, E.block_index hmem]
    exact congrArg (exponentAt m) (by omega)
  · rw [E.index_not_mem hmem]
    rw [exponent_zero_of_length _ _
      (by rw [E.compressExponents_length]; omega)]
    have hz := hm (c / 4) hb hmem (c % 4) hr
    have hdecomp : 4 * (c / 4) + c % 4 = c := by omega
    rw [hdecomp] at hz
    exact hz.symm

/-- Computed polynomial restriction, preserving signed coefficients and all
terms, including repeated or zero-coefficient terms. -/
def compress (p : RatPoly) : RatPoly :=
  p.map (fun term => (E.compressExponents term.1, term.2))

theorem compress_supported (p : RatPoly) :
    SupportedQuaternionBlocks source (E.compress p) := by
  intro term ht
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp ht
  exact Nat.le_of_eq (E.compressExponents_length original.1)

/-- Embedding the restriction reconstructs every target coordinate. The
prefix identity itself requires locality only; Haar transport below also
requires the original target support bound. -/
theorem polynomial_compress_prefix : ∀ p : RatPoly,
    BlockLocal target (fun b => b ∈ E.image) p →
    QuaternionPrefixPolynomialEqv target (E.polynomial (E.compress p)) p
  | [], _ => .nil
  | term :: rest, hp => by
      change QuaternionPrefixPolynomialEqv target
        ((E.exponents (E.compressExponents term.1), term.2) ::
          E.polynomial (E.compress rest)) (term :: rest)
      apply QuaternionPrefixPolynomialEqv.cons
      · exact ⟨Q'.eqv_refl _, fun c hc =>
          E.exponents_compress_pin term.1
            (hp term List.mem_cons_self) hc⟩
      · exact polynomial_compress_prefix rest
          (fun t ht => hp t (List.mem_cons_of_mem term ht))

/-- Exact normalized product-Haar value on the computed smaller carrier. -/
theorem haar_compress (p : RatPoly)
    (hp : SupportedQuaternionBlocks target p)
    (hloc : BlockLocal target (fun b => b ∈ E.image) p) :
    quaternionHaar target p ≈ quaternionHaar source (E.compress p) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv target
      (E.polynomial_compress_prefix p hloc)
      (E.polynomial_supported _) hp))
    (E.haar _ (E.compress_supported p))

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.compressExponents
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.compressExponents_length
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.compress_exponent_pin
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.exponents_compress_pin
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.compress
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.compress_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_compress_prefix
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.haar_compress
