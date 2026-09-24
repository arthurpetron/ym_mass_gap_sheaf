/-
# Exchange a selected family between two quaternion slices

The involution below moves exactly the selected lower blocks to the upper
slice and moves their upper partners back.  Unselected blocks stay fixed.
Consequently a polynomial supported on the selected lower blocks becomes its
ordinary upper-slice lift.  This is finite coordinate algebra; it does not
identify a partial product heat map with conditional integration.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionPartialSliceSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection

/-- Exchange the lower and upper copies of precisely the listed blocks.
Membership outside the first slice is never consulted except through the
corresponding lower index. -/
def swap (n : Nat) (ids : List Nat) : QuaternionBlockInvolution (n+n) where
  map block :=
    if block < n then
      if block ∈ ids then n+block else block
    else
      if block-n ∈ ids then block-n else block
  map_lt := by
    intro block hblock
    by_cases hlower : block < n
    · simp only [if_pos hlower]
      split <;> omega
    · simp only [if_neg hlower]
      split <;> omega
  involutive := by
    intro block hblock
    by_cases hlower : block < n
    · by_cases hmem : block ∈ ids
      · simp only [if_pos hlower, if_pos hmem,
          if_neg (show ¬ n+block < n by omega)]
        rw [show n+block-n = block by omega, if_pos hmem]
      · simp only [if_pos hlower, if_neg hmem]
    · have hupp : block-n < n := by omega
      by_cases hmem : block-n ∈ ids
      · simp only [if_neg hlower, if_pos hmem, if_pos hupp]
        omega
      · simp only [if_neg hlower, if_neg hmem]

/-- Action of the partial swap on a lower-slice block. -/
theorem swap_lower (n : Nat) (ids : List Nat) (i : Nat) (hi : i < n) :
    (swap n ids).map i = if i ∈ ids then n+i else i := by
  simp only [swap, hi, if_true]

/-- Action of the partial swap on the matching upper-slice block. -/
theorem swap_upper (n : Nat) (ids : List Nat) (i : Nat) (_hi : i < n) :
    (swap n ids).map (n+i) = if i ∈ ids then i else n+i := by
  simp only [swap, show ¬ n+i < n by omega, if_false,
    show n+i-n = i by omega]

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

private theorem exponent_replicate_append (m : List Nat) : ∀ (k c : Nat),
    exponentAt (List.replicate k 0 ++ m) c =
      if c < k then 0 else exponentAt m (c-k)
  | 0, c => by
      simp only [List.replicate_zero, List.nil_append, Nat.not_lt_zero,
        if_false, Nat.sub_zero]
  | k+1, 0 => by
      simp only [List.replicate_succ, List.cons_append, exponentAt,
        List.getD_cons_zero, Nat.zero_lt_succ, if_true]
  | k+1, c+1 => by
      rw [List.replicate_succ, List.cons_append]
      change exponentAt (List.replicate k 0 ++ m) c =
        if c+1 < k+1 then 0 else exponentAt m (c+1-(k+1))
      rw [exponent_replicate_append m k c]
      by_cases h : c < k
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
        exact congrArg (exponentAt m) (by omega)

private theorem exponent_zero_of_length :
    ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _::_, 0, h => by simp at h
  | _::m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero_of_length m c
        (by simp only [List.length_cons] at h; omega)

private theorem exponent_zero_of_independent {block : Nat} {p : RatPoly}
    (hp : QuaternionBlockIndependent block p) {term : RatTerm}
    (hterm : term ∈ p) (component : Nat) (hcomponent : component < 4) :
    exponentAt term.1 (4*block+component) = 0 := by
  have hclear :=
    SU2QuaternionFiniteProductHaarFubini.exponentAt_clearQuaternionBlock_self
      term.1 block component hcomponent
  rw [hp term hterm] at hclear
  exact hclear

private theorem selected_exponent (n : Nat) (ids : List Nat)
    (m : List Nat) (hm : m.length ≤ 4*n)
    (hind : ∀ j, j < n → j ∉ ids →
      ∀ component, component < 4 → exponentAt m (4*j+component) = 0)
    (c : Nat) (hc : c < 4*(n+n)) :
    exponentAt (reindexQuaternionExponents (swap n ids) m) c =
      exponentAt (List.replicate (4*n) 0 ++ m) c := by
  rw [exponentAt_reindexQuaternionExponents _ _ hc,
    exponent_replicate_append]
  have hcomponent : c % 4 < 4 := Nat.mod_lt _ (by decide)
  have hdecomp : 4*(c/4)+c%4 = c := by
    have h := Nat.div_add_mod c 4
    omega
  by_cases hlower : c / 4 < n
  · have hcoord : c < 4*n := by omega
    rw [swap_lower n ids _ hlower]
    by_cases hmem : c / 4 ∈ ids
    · rw [if_pos hmem, if_pos hcoord]
      exact exponent_zero_of_length m _ (by omega)
    · rw [if_neg hmem, if_pos hcoord]
      exact hind (c/4) hlower hmem (c%4) hcomponent
  · have hupp : c / 4-n < n := by omega
    have hcoord : ¬ c < 4*n := by omega
    have hmap : (swap n ids).map (c/4) =
        (if c/4-n ∈ ids then c/4-n else c/4) := by
      simp only [swap, if_neg hlower]
    have hindex : 4*(c/4-n)+c%4 = c-4*n := by omega
    rw [hmap, if_neg hcoord]
    by_cases hmem : c / 4-n ∈ ids
    · rw [if_pos hmem]
      exact congrArg (exponentAt m) hindex
    · rw [if_neg hmem]
      rw [exponent_zero_of_length m _ (by omega)]
      rw [← hindex, hind (c/4-n) hupp hmem (c%4) hcomponent]

private theorem fixed_exponent (n : Nat) (ids : List Nat)
    (m : List Nat) (hm : m.length ≤ 4*n)
    (hind : ∀ j, j < n → j ∈ ids →
      ∀ component, component < 4 → exponentAt m (4*j+component) = 0)
    (c : Nat) (hc : c < 4*(n+n)) :
    exponentAt (reindexQuaternionExponents (swap n ids) m) c =
      exponentAt m c := by
  rw [exponentAt_reindexQuaternionExponents _ _ hc]
  have hcomponent : c % 4 < 4 := Nat.mod_lt _ (by decide)
  have hdecomp : 4*(c/4)+c%4 = c := by
    have h := Nat.div_add_mod c 4
    omega
  by_cases hlower : c / 4 < n
  · rw [swap_lower n ids _ hlower]
    by_cases hmem : c / 4 ∈ ids
    · rw [if_pos hmem, exponent_zero_of_length m _ (by omega)]
      rw [← hdecomp, hind (c/4) hlower hmem (c%4) hcomponent]
    · rw [if_neg hmem, hdecomp]
  · have hupp : c / 4-n < n := by omega
    have hmap : (swap n ids).map (c/4) =
        (if c/4-n ∈ ids then c/4-n else c/4) := by
      simp only [swap, if_neg hlower]
    rw [hmap]
    by_cases hmem : c / 4-n ∈ ids
    · rw [if_pos hmem, hind (c/4-n) hupp hmem (c%4) hcomponent,
        exponent_zero_of_length m c (by omega)]
    · rw [if_neg hmem, hdecomp]

/-- Prefix form of the selected-slice transport.  A lower polynomial which is
independent of every unselected lower block becomes its ordinary upper lift. -/
theorem reindex_to_lift_prefix (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hindependent : ∀ j, j < n → j ∉ ids → QuaternionBlockIndependent j p) :
    QuaternionPrefixPolynomialEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) p) (liftBoundary n p) := by
  rw [liftBoundary_map]
  induction p with
  | nil => exact .nil
  | cons term rest ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, selected_exponent n ids term.1
          (hp term (by simp)) ?_⟩
        intro j hj hnot component hc
        exact exponent_zero_of_independent (hindependent j hj hnot)
          (by simp) component hc
      · exact ih
          (fun term' hterm => hp term' (List.mem_cons_of_mem term hterm))
          (fun j hj hnot term' hterm =>
            hindependent j hj hnot term' (List.mem_cons_of_mem term hterm))

/-- Carrier form of `reindex_to_lift_prefix`, with both support guards made
explicit before arbitrary insertions are admitted. -/
theorem reindex_to_lift (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hindependent : ∀ j, j < n → j ∉ ids → QuaternionBlockIndependent j p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) p) (liftBoundary n p) :=
  carrierOfPrefix (reindex_supported (swap n ids) p) (lift_supported hp n)
    (reindex_to_lift_prefix n ids p hp hindependent)

/-- A lower-slice polynomial independent of every selected block is fixed by
the partial swap.  The statement is prefix-level because reindexing pads every
monomial to the complete doubled carrier. -/
theorem reindex_fixed_prefix (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hindependent : ∀ j, j < n → j ∈ ids → QuaternionBlockIndependent j p) :
    QuaternionPrefixPolynomialEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) p) p := by
  induction p with
  | nil => exact .nil
  | cons term rest ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, fixed_exponent n ids term.1
          (hp term (by simp)) ?_⟩
        intro j hj hmem component hc
        exact exponent_zero_of_independent (hindependent j hj hmem)
          (by simp) component hc
      · exact ih
          (fun term' hterm => hp term' (List.mem_cons_of_mem term hterm))
          (fun j hj hmem term' hterm =>
            hindependent j hj hmem term' (List.mem_cons_of_mem term hterm))

/-- Carrier form of `reindex_fixed_prefix`. -/
theorem reindex_fixed (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hindependent : ∀ j, j < n → j ∈ ids → QuaternionBlockIndependent j p) :
    HaarCarrierEqv (n+n) (reindexQuaternionPolynomial (swap n ids) p) p :=
  carrierOfPrefix (reindex_supported (swap n ids) p)
    (fun term hterm => Nat.le_trans (hp term hterm)
      (Nat.mul_le_mul_left 4 (by omega)))
    (reindex_fixed_prefix n ids p hp hindependent)

/-- Convenient selected-family form: independence is requested only through
list membership; out-of-range list entries have no effect on the involution. -/
theorem reindex_fixed_of_selected_independent (n : Nat) (ids : List Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hindependent : ∀ i, i ∈ ids → QuaternionBlockIndependent i p) :
    HaarCarrierEqv (n+n) (reindexQuaternionPolynomial (swap n ids) p) p :=
  reindex_fixed n ids p hp
    (fun j _ hmem => hindependent j hmem)

private theorem reindex_familyProject_with {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) : ∀ (ids : List Nat) (p : RatPoly),
    (∀ i, i ∈ ids → i < blocks) →
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial s (familyProject ids p))
      (familyProject (ids.map s.map) (reindexQuaternionPolynomial s p))
  | [], _, _ => .refl _
  | i::ids, p, hids => by
      change RatPolyCoeffEqv
        (reindexQuaternionPolynomial s (familyProject ids (project i p)))
        (familyProject (ids.map s.map)
          (project (s.map i) (reindexQuaternionPolynomial s p)))
      exact (reindex_familyProject_with s ids (project i p)
        (fun j hj => hids j (List.mem_cons_of_mem i hj))).trans
        (familyProject_congr (ids.map s.map)
          (reindex_integrateQuaternionBlock s i
            (hids i List.mem_cons_self) p))

/-- Reindexing commutes with a selected family projection, with the projected
blocks transported to their upper-slice partners. -/
theorem reindex_familyProject (n : Nat) (ids : List Nat) (p : RatPoly)
    (hids : ∀ i, i ∈ ids → i < n) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial (swap n ids) (familyProject ids p))
      (familyProject (ids.map (fun i => n+i))
        (reindexQuaternionPolynomial (swap n ids) p)) := by
  have hmap : ids.map (swap n ids).map = ids.map (fun i => n+i) := by
    apply List.map_congr_left
    intro i hi
    rw [swap_lower n ids i (hids i hi), if_pos hi]
  rw [← hmap]
  exact reindex_familyProject_with (swap n ids) ids p
    (fun i hi => by
      have hin := hids i hi
      omega)

/-- Projecting the selected lower blocks produces a polynomial fixed by the
partial swap, on the doubled Haar carrier. -/
theorem reindex_familyProject_fixed (n : Nat) (ids : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (_hids : ∀ i, i ∈ ids → i < n) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) (familyProject ids p))
      (familyProject ids p) :=
  reindex_fixed n ids (familyProject ids p)
    (familyProject_supported ids hp)
    (fun j _hj hmem => familyProject_independent ids p j hmem)

end YMGap.Continuum.SU2QuaternionPartialSliceSwap

#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.swap
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.swap_lower
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.swap_upper
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_to_lift_prefix
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_to_lift
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_fixed_prefix
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_fixed
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_fixed_of_selected_independent
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_familyProject
#print axioms YMGap.Continuum.SU2QuaternionPartialSliceSwap.reindex_familyProject_fixed
