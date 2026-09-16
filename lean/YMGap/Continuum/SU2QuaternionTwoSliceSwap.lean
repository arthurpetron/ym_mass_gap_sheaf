/-
# Exchange two complete quaternion slices

The explicit involution exchanges every block in the two equally sized
slices, including fringe blocks that need not occur in an action factor.
Supported head polynomials become the original boundary lift, and lifted
polynomials become head polynomials. Prefix equivalence records only the
harmless complete padding introduced by reindexing. Zero blocks are allowed.

This is finite coordinate algebra and exact product-Haar invariance, not
an assertion of transfer symmetry or a stationary normalization.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

namespace YMGap.Continuum.SU2QuaternionTwoSliceSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

/-- Exchange the two full slices, without choosing or deleting any block. -/
def swap (blocks : Nat) : QuaternionBlockInvolution (blocks+blocks) where
  map i := if i < blocks then blocks+i else i-blocks
  map_lt := by
    intro i hi
    split <;> omega
  involutive := by
    intro i hi
    by_cases h : i < blocks
    · simp only [if_pos h, if_neg (show ¬ blocks+i < blocks by omega)]
      omega
    · simp only [if_neg h, if_pos (show i-blocks < blocks by omega)]
      omega

theorem swap_lower (blocks i : Nat) (hi : i < blocks) :
    (swap blocks).map i = blocks+i := if_pos hi

theorem swap_upper (blocks i : Nat) (hi : i < blocks) :
    (swap blocks).map (blocks+i) = i := by
  change (if blocks+i < blocks then blocks+(blocks+i) else blocks+i-blocks) = i
  rw [if_neg (by omega)]
  omega

private theorem liftBoundary_map : ∀ (offset : Nat) (p : RatPoly),
    liftBoundary offset p =
      p.map (fun term => (List.replicate (4*offset) 0 ++ term.1, term.2))
  | 0, p => by
      simpa only [liftBoundary, Nat.mul_zero, List.replicate_zero,
        List.nil_append] using (List.map_id p).symm
  | offset+1, p => by
      rw [liftBoundary, liftBoundary_map]
      simp only [liftHead, List.map_map]
      apply List.map_congr_left
      intro term _
      rw [show 4*(offset+1) = 4*offset+1+1+1+1 by omega]
      rfl

private theorem exponent_replicate_append (m : List Nat) : ∀ (n c : Nat),
    exponentAt (List.replicate n 0 ++ m) c =
      if c < n then 0 else exponentAt m (c-n)
  | 0, c => by
      simp only [List.replicate_zero, List.nil_append, Nat.not_lt_zero,
        if_false, Nat.sub_zero]
  | n+1, 0 => by
      simp only [List.replicate_succ, List.cons_append, exponentAt,
        List.getD_cons_zero, Nat.zero_lt_succ, if_true]
  | n+1, c+1 => by
      rw [List.replicate_succ, List.cons_append]
      change exponentAt (List.replicate n 0 ++ m) c =
        if c+1 < n+1 then 0 else exponentAt m (c+1-(n+1))
      rw [exponent_replicate_append m n c]
      by_cases h : c < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
        exact congrArg (exponentAt m) (by omega)

private theorem exponent_zero_of_length :
    ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _::_, 0, h => by simp at h
  | _::m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length m c (by simp only [List.length_cons] at h; omega)

private theorem lower_exponent (blocks : Nat) (m : List Nat) (hm : m.length ≤ 4*blocks)
    (c : Nat) (hc : c < 4*(blocks+blocks)) :
    exponentAt (reindexQuaternionExponents (swap blocks) m) c =
      exponentAt (List.replicate (4*blocks) 0 ++ m) c := by
  rw [exponentAt_reindexQuaternionExponents _ _ hc, exponent_replicate_append]
  by_cases h : c / 4 < blocks
  · rw [swap_lower blocks _ h, if_pos (by omega)]
    exact exponent_zero_of_length m _ (by omega)
  · have hmapped : (swap blocks).map (c / 4) = c / 4-blocks := if_neg h
    rw [hmapped, if_neg (by omega)]
    exact congrArg (exponentAt m) (by omega)

private theorem upper_exponent (blocks : Nat) (m : List Nat) (hm : m.length ≤ 4*blocks)
    (c : Nat) (hc : c < 4*(blocks+blocks)) :
    exponentAt (reindexQuaternionExponents (swap blocks)
      (List.replicate (4*blocks) 0 ++ m)) c = exponentAt m c := by
  rw [exponentAt_reindexQuaternionExponents _ _ hc, exponent_replicate_append]
  by_cases h : c / 4 < blocks
  · rw [swap_lower blocks _ h, if_neg (by omega)]
    exact congrArg (exponentAt m) (by omega)
  · have hmapped : (swap blocks).map (c / 4) = c / 4-blocks := if_neg h
    rw [hmapped, if_pos (by omega)]
    exact (exponent_zero_of_length m c (by omega)).symm

/-- A supported lower-slice polynomial is exactly the upper lift up to padding. -/
theorem lower_prefix (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    QuaternionPrefixPolynomialEqv (blocks+blocks)
      (reindexQuaternionPolynomial (swap blocks) p) (liftBoundary blocks p) := by
  rw [liftBoundary_map]
  induction p with
  | nil => exact .nil
  | cons t ts ih =>
      exact .cons ⟨Q'.eqv_refl _, lower_exponent blocks t.1 (hp t (by simp))⟩
        (ih (fun s hs => hp s (List.mem_cons_of_mem t hs)))

/-- A supported lifted upper-slice polynomial is exactly the lower one up to padding. -/
theorem upper_prefix (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    QuaternionPrefixPolynomialEqv (blocks+blocks)
      (reindexQuaternionPolynomial (swap blocks) (liftBoundary blocks p)) p := by
  rw [liftBoundary_map]
  induction p with
  | nil => exact .nil
  | cons t ts ih =>
      exact .cons ⟨Q'.eqv_refl _, upper_exponent blocks t.1 (hp t (by simp))⟩
        (ih (fun s hs => hp s (List.mem_cons_of_mem t hs)))

/-- Reindexing always returns a polynomial on the complete two-slice carrier. -/
theorem polynomial_supported (blocks : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks (blocks+blocks) (reindexQuaternionPolynomial (swap blocks) p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  exact Nat.le_of_eq (reindexQuaternionExponents_length _ _)

/-- Exact Haar invariance needs the original polynomial's full-carrier support. -/
theorem haar (blocks : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks+blocks) p) :
    Q'.eqv (quaternionHaar (blocks+blocks) (reindexQuaternionPolynomial (swap blocks) p))
      (quaternionHaar (blocks+blocks) p) :=
  quaternionHaar_reindex (swap blocks) p hp

end YMGap.Continuum.SU2QuaternionTwoSliceSwap

#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.swap
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.swap_lower
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.swap_upper
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.lower_prefix
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.upper_prefix
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.polynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionTwoSliceSwap.haar
