/-
# Literal compatibility of quaternion block placement and boundary lifting

Suppose a larger block embedding agrees with an existing source placement
on one consecutive source interval. Lifting a supported source polynomial
to that interval and then using the larger embedding gives literally the
same polynomial as the original embedding. Both outputs have the same
complete target padding, and no coefficients or term order change.

The consumer places the original single-slice spatial weight and source
insertions into the head or tail of an ordered pair, and subsequently into
ordered time chains. This is coordinate algebra only.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

private theorem liftBoundary_map : ∀ (offset : Nat) (p : RatPoly),
    liftBoundary offset p =
      p.map (fun term => (List.replicate (4 * offset) 0 ++ term.1, term.2))
  | 0, p => by
      simpa only [liftBoundary, Nat.mul_zero, List.replicate_zero,
        List.nil_append] using (List.map_id p).symm
  | offset + 1, p => by
      rw [liftBoundary, liftBoundary_map]
      simp only [liftHead, List.map_map]
      apply List.map_congr_left
      intro term _
      rw [show 4 * (offset + 1) = 4 * offset + 1 + 1 + 1 + 1 by omega]
      rfl

private theorem exponent_replicate_append (m : List Nat) : ∀ (n c : Nat),
    exponentAt (List.replicate n 0 ++ m) c =
      if c < n then 0 else exponentAt m (c - n)
  | 0, c => by
      simp only [List.replicate_zero, List.nil_append, Nat.not_lt_zero,
        if_false, Nat.sub_zero]
  | n + 1, 0 => by
      simp only [List.replicate_succ, List.cons_append, exponentAt,
        List.getD_cons_zero, Nat.zero_lt_succ, if_true]
  | n + 1, c + 1 => by
      rw [List.replicate_succ, List.cons_append]
      change exponentAt (List.replicate n 0 ++ m) c =
        if c + 1 < n + 1 then 0 else exponentAt m (c + 1 - (n + 1))
      rw [exponent_replicate_append m n c]
      by_cases h : c < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
        exact congrArg (exponentAt m) (by omega)

private theorem exponent_zero_of_length :
    ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: m, c + 1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length m c
        (by simp only [List.length_cons] at h; omega)

variable {source larger target : Nat}
    (E : BlockEmbedding source target) (F : BlockEmbedding larger target)

private theorem exponents_placed (offset : Nat)
    (hroom : offset + source ≤ larger)
    (hblock : ∀ i, i < source → F.block (offset + i) = E.block i)
    (m : List Nat) (hm : m.length ≤ 4 * source) :
    F.exponents (List.replicate (4 * offset) 0 ++ m) = E.exponents m := by
  apply natList_eq_of_length_getD
  · rw [F.exponents_length, E.exponents_length]
  · intro c hc
    rw [F.exponents_length] at hc
    change exponentAt (F.exponents (List.replicate (4 * offset) 0 ++ m)) c =
      exponentAt (E.exponents m) c
    rw [F.exponent_pin _ hc, E.exponent_pin _ hc, exponent_replicate_append]
    have hr : c % 4 < 4 := by omega
    by_cases hmem : c / 4 ∈ E.image
    · have hi := E.index_lt hmem
      have he : F.index (c / 4) = offset + E.index (c / 4) :=
        (F.index_eq_block (by omega)).mpr
          ((E.block_index hmem).symm.trans (hblock _ hi).symm)
      rw [he, if_neg (by omega)]
      exact congrArg (exponentAt m) (by omega)
    · rw [E.index_not_mem hmem,
        exponent_zero_of_length m (4 * source + c % 4) (by omega)]
      by_cases hbefore : 4 * F.index (c / 4) + c % 4 < 4 * offset
      · rw [if_pos hbefore]
      · rw [if_neg hbefore]
        have hstart : offset ≤ F.index (c / 4) := by omega
        by_cases hwithin : F.index (c / 4) < offset + source
        · have hi : F.index (c / 4) - offset < source := by omega
          have he : c / 4 = F.block (offset + (F.index (c / 4) - offset)) :=
            (F.index_eq_block (by omega)).mp (by omega)
          rw [hblock _ hi] at he
          exact False.elim (hmem (he.symm ▸ E.block_mem hi))
        · exact exponent_zero_of_length m _ (by omega)

/-- Placing a supported polynomial in a consecutive source interval and
then embedding is exactly its original placement, including term order. -/
theorem polynomial_liftBoundary (offset : Nat)
    (hroom : offset + source ≤ larger)
    (hblock : ∀ i, i < source → F.block (offset + i) = E.block i)
    (p : RatPoly) (hp : SupportedQuaternionBlocks source p) :
    F.polynomial (liftBoundary offset p) = E.polynomial p := by
  rw [liftBoundary_map]
  unfold polynomial
  rw [List.map_map]
  apply List.map_congr_left
  intro term ht
  change (F.exponents (List.replicate (4 * offset) 0 ++ term.1), term.2) =
    (E.exponents term.1, term.2)
  rw [exponents_placed E F offset hroom hblock term.1 (hp term ht)]

/-- The head placement needs no syntactic lift at all. -/
theorem polynomial_head_placement
    (hroom : source ≤ larger)
    (hblock : ∀ i, i < source → F.block i = E.block i)
    (p : RatPoly) (hp : SupportedQuaternionBlocks source p) :
    F.polynomial p = E.polynomial p :=
  E.polynomial_liftBoundary F 0 (by omega)
    (fun i hi => by simpa only [Nat.zero_add] using hblock i hi) p hp

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_liftBoundary
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_head_placement
