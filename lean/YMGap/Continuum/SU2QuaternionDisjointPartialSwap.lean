/-
# Composition of disjoint partial slice swaps

Two partial swaps on disjoint lower-slot families compose to the swap on
their concatenation. The polynomial theorem is stated at the existing
prefix/carrier equivalence level because reindexing pads every monomial to
the doubled carrier. This is coordinate algebra, not a covariance bound.
-/

import YMGap.Continuum.SU2QuaternionPartialSwapPairing

namespace YMGap.Continuum.SU2QuaternionDisjointPartialSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.QuaternionHaarAngularCarrier

private theorem swap_comp_lower (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (i : Nat) (hi : i < n) :
    (swap n B).map ((swap n A).map i) = (swap n (A ++ B)).map i := by
  by_cases ha : i ∈ A
  · have hb : i ∉ B := hdisj i ha
    rw [swap_lower n A i hi, if_pos ha, swap_upper n B i hi,
      if_neg hb, swap_lower n (A ++ B) i hi]
    simp [List.mem_append, ha, hb]
  · rw [swap_lower n A i hi, if_neg ha, swap_lower n B i hi,
      swap_lower n (A ++ B) i hi]
    by_cases hb : i ∈ B
    · simp [List.mem_append, ha, hb]
    · simp [List.mem_append, ha, hb]

private theorem swap_comp_upper (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (i : Nat) (hi : i < n) :
    (swap n B).map ((swap n A).map (n+i)) =
      (swap n (A ++ B)).map (n+i) := by
  by_cases ha : i ∈ A
  · have hb : i ∉ B := hdisj i ha
    rw [swap_upper n A i hi, if_pos ha, swap_lower n B i hi,
      if_neg hb, swap_upper n (A ++ B) i hi]
    simp [List.mem_append, ha, hb]
  · rw [swap_upper n A i hi, if_neg ha, swap_upper n B i hi,
      swap_upper n (A ++ B) i hi]
    by_cases hb : i ∈ B
    · simp [List.mem_append, ha, hb]
    · simp [List.mem_append, ha, hb]

/-- Coordinate-level disjoint composition. Out-of-range list entries are
harmless, as in the definition of `swap`; no `Nodup` premise is needed. -/
theorem swap_comp_map (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (block : Nat)
    (hblock : block < n+n) :
    (swap n B).map ((swap n A).map block) =
      (swap n (A ++ B)).map block := by
  by_cases hlower : block < n
  · exact swap_comp_lower n A B hdisj block hlower
  · let i := block-n
    have hi : i < n := by omega
    have he : n+i = block := by omega
    simpa only [he] using swap_comp_upper n A B hdisj i hi

private theorem swap_append_comm_map (n : Nat) (A B : List Nat)
    (block : Nat) (hblock : block < n+n) :
    (swap n (B ++ A)).map block = (swap n (A ++ B)).map block := by
  by_cases hlower : block < n
  · rw [swap_lower n (B ++ A) block hlower,
      swap_lower n (A ++ B) block hlower]
    simp only [List.mem_append, or_comm]
  · let i := block-n
    have hi : i < n := by omega
    have he : n+i = block := by omega
    rw [← he, swap_upper n (B ++ A) i hi,
      swap_upper n (A ++ B) i hi]
    simp only [List.mem_append, or_comm]

/-- Reindexing by two disjoint partial swaps equals reindexing by their
union on every in-carrier coordinate. -/
theorem reindex_comp_prefix (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv (n+n)
      (reindexQuaternionPolynomial (swap n A)
        (reindexQuaternionPolynomial (swap n B) p))
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) := by
  induction p with
  | nil => exact .nil
  | cons term rest ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro coordinate hc
        change exponentAt
          (reindexQuaternionExponents (swap n A)
            (reindexQuaternionExponents (swap n B) term.1)) coordinate =
          exponentAt (reindexQuaternionExponents (swap n (A ++ B)) term.1)
            coordinate
        rw [exponentAt_reindexQuaternionExponents (swap n A) _ hc,
          exponentAt_reindexQuaternionExponents (swap n (A ++ B)) _ hc]
        have hb : coordinate / 4 < n+n := by omega
        have hm := (swap n A).map_lt (coordinate / 4) hb
        rw [exponentAt_reindexQuaternionExponents (swap n B) _ (by omega)]
        have hd :
            (4*(swap n A).map (coordinate/4)+coordinate%4)/4 =
              (swap n A).map (coordinate/4) := by omega
        have hr :
            (4*(swap n A).map (coordinate/4)+coordinate%4)%4 =
              coordinate%4 := by omega
        rw [hd, hr, swap_comp_map n A B hdisj (coordinate/4) hb]
      · exact ih

/-- Carrier-level composition usable under any polynomial insertion on the
same doubled Haar space; it does not silently drop spectators. -/
theorem reindex_comp_carrier (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n A)
        (reindexQuaternionPolynomial (swap n B) p))
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) :=
  carrierOfPrefix
    (reindex_supported (swap n A)
      (reindexQuaternionPolynomial (swap n B) p))
    (reindex_supported (swap n (A ++ B)) p)
    (reindex_comp_prefix n A B hdisj p)

/-- The two concatenation orders define the same partial swap at every
coordinate of the doubled carrier. -/
theorem reindex_append_comm_carrier (n : Nat) (A B : List Nat) (p : RatPoly) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n (B ++ A)) p)
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) := by
  have hprefix : QuaternionPrefixPolynomialEqv (n+n)
      (reindexQuaternionPolynomial (swap n (B ++ A)) p)
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) := by
    induction p with
    | nil => exact .nil
    | cons term rest ih =>
        apply QuaternionPrefixPolynomialEqv.cons
        · refine ⟨Q'.eqv_refl _, ?_⟩
          intro coordinate hc
          change exponentAt
            (reindexQuaternionExponents (swap n (B ++ A)) term.1) coordinate =
            exponentAt
              (reindexQuaternionExponents (swap n (A ++ B)) term.1) coordinate
          rw [exponentAt_reindexQuaternionExponents (swap n (B ++ A)) _ hc,
            exponentAt_reindexQuaternionExponents (swap n (A ++ B)) _ hc,
            swap_append_comm_map n A B (coordinate/4) (by omega)]
        · exact ih
  exact carrierOfPrefix
    (reindex_supported (swap n (B ++ A)) p)
    (reindex_supported (swap n (A ++ B)) p) hprefix

/-- Disjoint partial swaps commute on the existing carrier equivalence,
without any condition on out-of-range entries. -/
theorem reindex_comp_reverse_carrier (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n B)
        (reindexQuaternionPolynomial (swap n A) p))
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) := by
  have hreverse : ∀ i, i ∈ B → i ∉ A := by
    intro i hiB hiA
    exact hdisj i hiA hiB
  exact HaarCarrierEqv.trans
    (reindex_comp_carrier n B A hreverse p)
    (reindex_append_comm_carrier n A B p)

/-- Applying the same partial swap twice fixes every supported polynomial
up to the existing Haar carrier equivalence. -/
theorem reindex_twice_carrier (n : Nat) (A : List Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n+n) p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n A)
        (reindexQuaternionPolynomial (swap n A) p)) p :=
  carrierOfPrefix
    (reindex_supported (swap n A) (reindexQuaternionPolynomial (swap n A) p))
    hp (reindex_twice_prefix (swap n A) p)

/-- Cancelling one of two disjoint swaps leaves the other one. This is the
form needed when a shared-face determinant is antisymmetrized. -/
theorem reindex_comp_cancel (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n A)
        (reindexQuaternionPolynomial (swap n (A ++ B)) p))
      (reindexQuaternionPolynomial (swap n B) p) := by
  let RB := reindexQuaternionPolynomial (swap n B) p
  let RA := reindexQuaternionPolynomial (swap n A)
  have hcomp : HaarCarrierEqv (n+n) (RA RB)
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) :=
    reindex_comp_carrier n A B hdisj p
  have htrans : HaarCarrierEqv (n+n) (RA (RA RB))
      (RA (reindexQuaternionPolynomial (swap n (A ++ B)) p)) :=
    reindex_carrier (swap n A)
      (reindex_supported (swap n A) RB)
      (reindex_supported (swap n (A ++ B)) p) hcomp
  exact HaarCarrierEqv.trans (HaarCarrierEqv.symm htrans)
    (reindex_twice_carrier n A RB (reindex_supported (swap n B) p))

/-- Symmetric cancellation, useful when the right test is independent of the
left selected slots. -/
theorem reindex_comp_cancel_reverse (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n B)
        (reindexQuaternionPolynomial (swap n (A ++ B)) p))
      (reindexQuaternionPolynomial (swap n A) p) := by
  let RA := reindexQuaternionPolynomial (swap n A) p
  let RB := reindexQuaternionPolynomial (swap n B)
  have hcomp : HaarCarrierEqv (n+n) (RB RA)
      (reindexQuaternionPolynomial (swap n (A ++ B)) p) :=
    reindex_comp_reverse_carrier n A B hdisj p
  have htrans : HaarCarrierEqv (n+n) (RB (RB RA))
      (RB (reindexQuaternionPolynomial (swap n (A ++ B)) p)) :=
    reindex_carrier (swap n B)
      (reindex_supported (swap n B) RA)
      (reindex_supported (swap n (A ++ B)) p) hcomp
  exact HaarCarrierEqv.trans (HaarCarrierEqv.symm htrans)
    (reindex_twice_carrier n B RA (reindex_supported (swap n A) p))

#print axioms swap_comp_map
#print axioms reindex_comp_prefix
#print axioms reindex_comp_carrier
#print axioms reindex_append_comm_carrier
#print axioms reindex_comp_reverse_carrier
#print axioms reindex_twice_carrier
#print axioms reindex_comp_cancel
#print axioms reindex_comp_cancel_reverse

end YMGap.Continuum.SU2QuaternionDisjointPartialSwap
