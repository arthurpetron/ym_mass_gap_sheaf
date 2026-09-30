/-
# Whole-side replica factors are unchanged by a partial exchange

The original two-copy factor is p(x)*p(y). If all variables of p lie on
one side of a selected-link cut, exchanging that side between the copies
leaves this factor unchanged under every original doubled-Haar insertion.
No factorization of the interacting measure is asserted. This is the exact
cancellation used to charge only crossing faces in the action comparison.
-/

import YMGap.Continuum.SU2QuaternionPartialSliceSwap

namespace YMGap.Continuum.SU2QuaternionReplicaPairSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.QuaternionHaarAngularCarrier

private theorem support_extend {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 (by omega))

/-- Coordinate commutation gives literal equality of the padded polynomials. -/
theorem reindex_commute {n : Nat} (s r : QuaternionBlockInvolution n)
    (hcomm : ∀ b, b < n → s.map (r.map b) = r.map (s.map b)) (p : RatPoly) :
    reindexQuaternionPolynomial s (reindexQuaternionPolynomial r p) =
      reindexQuaternionPolynomial r (reindexQuaternionPolynomial s p) := by
  simp only [reindexQuaternionPolynomial, List.map_map]
  apply List.map_congr_left
  intro term _
  dsimp only [Function.comp_def]
  apply Prod.ext
  · apply natList_eq_of_length_getD
    · simp only [reindexQuaternionExponents_length]
    · intro c hc
      have hc' : c < 4*n := by simpa only [reindexQuaternionExponents_length] using hc
      have hb : c/4 < n := by omega
      have hs := s.map_lt (c/4) hb
      have hr := r.map_lt (c/4) hb
      change exponentAt (reindexQuaternionExponents s (reindexQuaternionExponents r term.1)) c =
        exponentAt (reindexQuaternionExponents r (reindexQuaternionExponents s term.1)) c
      rw [exponentAt_reindexQuaternionExponents s _ hc',
        exponentAt_reindexQuaternionExponents r _ hc',
        exponentAt_reindexQuaternionExponents r _ (by omega),
        exponentAt_reindexQuaternionExponents s _ (by omega)]
      rw [show (4*s.map (c/4)+c%4)/4 = s.map (c/4) by omega,
        show (4*r.map (c/4)+c%4)/4 = r.map (c/4) by omega,
        show (4*s.map (c/4)+c%4)%4 = c%4 by omega,
        show (4*r.map (c/4)+c%4)%4 = c%4 by omega,
        hcomm (c/4) hb]
  · rfl

private theorem swaps_commute (n : Nat) (ids : List Nat) :
    ∀ b, b < n+n → (swap n ids).map ((swap n (List.range n)).map b) =
      (swap n (List.range n)).map ((swap n ids).map b) := by
  intro b hb
  by_cases hl : b < n
  · rw [swap_lower n (List.range n) b hl,
      if_pos (List.mem_range.mpr hl), swap_upper n ids b hl,
      swap_lower n ids b hl]
    by_cases hm : b ∈ ids
    · simp only [if_pos hm]
      rw [swap_upper _ _ _ hl, if_pos (List.mem_range.mpr hl)]
    · simp only [if_neg hm]
      rw [swap_lower _ _ _ hl, if_pos (List.mem_range.mpr hl)]
  · have hi : b-n < n := by omega
    have he : b = n+(b-n) := by omega
    rw [he, swap_upper n (List.range n) (b-n) hi,
      if_pos (List.mem_range.mpr hi), swap_lower n ids (b-n) hi,
      swap_upper n ids (b-n) hi]
    by_cases hm : b-n ∈ ids
    · simp only [if_pos hm]
      rw [swap_lower _ _ _ hi, if_pos (List.mem_range.mpr hi)]
    · simp only [if_neg hm]
      rw [swap_upper _ _ _ hi, if_pos (List.mem_range.mpr hi)]

private theorem fullSwap_lift (n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (List.range n)) p) (liftBoundary n p) :=
  reindex_to_lift n (List.range n) p hp
    (fun j hj hnot => False.elim (hnot (List.mem_range.mpr hj)))

private theorem upper_swap (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) (liftBoundary n p))
      (reindexQuaternionPolynomial (swap n (List.range n))
        (reindexQuaternionPolynomial (swap n ids) p)) := by
  have h := reindex_carrier (swap n ids)
    (lift_supported hp n) (reindex_supported _ p) (fullSwap_lift n p hp).symm
  rw [reindex_commute (swap n ids) (swap n (List.range n)) (swaps_commute n ids)] at h
  exact h

/-- A factor supported entirely on the selected side is exchanged with its
other copy. Its two-copy product is therefore unchanged, not estimated. -/
theorem selected_pair_fixed (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hind : ∀ j, j < n → j ∉ ids → QuaternionBlockIndependent j p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) (polyMul p (liftBoundary n p)))
      (polyMul p (liftBoundary n p)) := by
  let r := swap n (List.range n)
  have hs := reindex_to_lift n ids p hp hind
  have hr := fullSwap_lift n p hp
  have hu := (upper_swap n ids p hp).trans
    (reindex_carrier r (reindex_supported _ p) (reindex_supported _ p) (hs.trans hr.symm))
  have ht : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial r (reindexQuaternionPolynomial r p)) p :=
    carrierOfPrefix (reindex_supported r _) (support_extend hp) (reindex_twice_prefix r p)
  rw [reindexQuaternionPolynomial_mul]
  exact (HaarCarrierEqv.mul hs (hu.trans ht)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_comm _ _))

/-- A factor supported entirely on the unselected side stays fixed in each
copy. Both copies remain in the original doubled carrier. -/
theorem unselected_pair_fixed (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hind : ∀ j, j < n → j ∈ ids → QuaternionBlockIndependent j p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) (polyMul p (liftBoundary n p)))
      (polyMul p (liftBoundary n p)) := by
  have hs := reindex_fixed n ids p hp hind
  have hu := (upper_swap n ids p hp).trans
    ((reindex_carrier (swap n (List.range n)) (reindex_supported _ p)
      (support_extend hp) hs).trans (fullSwap_lift n p hp))
  rw [reindexQuaternionPolynomial_mul]
  exact HaarCarrierEqv.mul hs hu

#print axioms reindex_commute
#print axioms selected_pair_fixed
#print axioms unselected_pair_fixed

end YMGap.Continuum.SU2QuaternionReplicaPairSwap
