/-
# Literal finite enumeration of degree-bounded quaternion monomials

Enumerate all exponent lists in the carried coordinate prefix, including
shorter lists used by the original polynomial carrier. Each coordinate is
bounded by the ceiling assigned to its quaternion block. This is only a
finite range/completeness interface; it asserts no basis independence or
positive-definiteness beyond existing source theorems.
-/

import YMGap.Continuum.SU2QuaternionBlockDegreeBound

namespace YMGap.Continuum.SU2QuaternionBoundedMonomials

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionBlockDegreeBound

/-- Candidate exponent lists for a finite coordinate interval. At each
coordinate, entries range from zero through the ceiling of its block. The
empty list is included at every recursion depth. -/
def coordinateMonomials : Nat → Nat → (Nat → Nat) → List (List Nat)
  | 0, _, _ => [[]]
  | count + 1, offset, budget =>
      [[]] ++
        (List.range (budget (offset / 4) + 1)).flatMap
          (fun exponent =>
            (coordinateMonomials count (offset + 1) budget).map
              (fun tail => exponent :: tail))

/-- All original list presentations supported in the first `4*blocks`
coordinates, with each exponent bounded by its quaternion-block ceiling. -/
def monomials (blocks : Nat) (budget : Nat → Nat) : List (List Nat) :=
  coordinateMonomials (4 * blocks) 0 budget

private theorem coordinateMonomials_length_le :
    ∀ (count offset : Nat) (budget : Nat → Nat) (m : List Nat),
      m ∈ coordinateMonomials count offset budget → m.length ≤ count
  | 0, offset, budget, m, hm => by
      simp only [coordinateMonomials] at hm
      have hnil : m = [] := List.mem_singleton.mp hm
      subst m
      exact Nat.zero_le _
  | count + 1, offset, budget, m, hm => by
      change m ∈ [[]] ++
        (List.range (budget (offset / 4) + 1)).flatMap
          (fun exponent =>
            (coordinateMonomials count (offset + 1) budget).map
              (fun tail => exponent :: tail)) at hm
      rcases List.mem_append.mp hm with hnil | hcons
      · have h : m = [] := List.mem_singleton.mp hnil
        subst m
        exact Nat.zero_le _
      · obtain ⟨exponent, _, hmap⟩ := List.mem_flatMap.mp hcons
        obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hmap
        exact Nat.succ_le_succ
          (coordinateMonomials_length_le count (offset + 1) budget tail htail)

/-- Completeness for a coordinatewise exponent ceiling on a finite interval. -/
private theorem mem_coordinateMonomials_of_bound :
    ∀ (count offset : Nat) (budget : Nat → Nat) (m : List Nat),
      m.length ≤ count →
      (∀ j, j < m.length → exponentAt m j ≤ budget ((offset + j) / 4)) →
      m ∈ coordinateMonomials count offset budget
  | 0, offset, budget, [], _, _ => by
      simp [coordinateMonomials]
  | 0, offset, budget, _ :: _, hlen, _ => by
      simp at hlen
  | count + 1, offset, budget, [], _, _ => by
      simp [coordinateMonomials]
  | count + 1, offset, budget, exponent :: tail, hlen, hbound => by
      have hlength : tail.length ≤ count := by
        simp only [List.length_cons] at hlen
        omega
      have hhead : exponent ≤ budget (offset / 4) := by
        have h := hbound 0 (by simp)
        simpa [exponentAt] using h
      have htailBound : ∀ j, j < tail.length →
          exponentAt tail j ≤ budget ((offset + 1 + j) / 4) := by
        intro j hj
        have h := hbound (j + 1) (by simp only [List.length_cons]; omega)
        have hoffset : offset + 1 + j = offset + (j + 1) := by omega
        simpa [exponentAt, hoffset] using h
      have htail := mem_coordinateMonomials_of_bound
        count (offset + 1) budget tail hlength htailBound
      have hExponent : exponent ∈ List.range (budget (offset / 4) + 1) :=
        List.mem_range.mpr (Nat.lt_succ_of_le hhead)
      apply List.mem_append.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨exponent, hExponent, ?_⟩
      exact List.mem_map.mpr ⟨tail, htail, rfl⟩

/-- A bounded-degree, supported original monomial occurs literally in the
finite candidate list; no padding equivalence or sphere quotient is used. -/
theorem mem_monomials_of_degree
    (blocks : Nat) (budget : Nat → Nat) (m : List Nat)
    (hsupport : m.length ≤ 4 * blocks)
    (hdegree : ∀ block, block < blocks →
      quaternionBlockDegree m block ≤ budget block) :
    m ∈ monomials blocks budget := by
  apply mem_coordinateMonomials_of_bound (4 * blocks) 0 budget m hsupport
  intro j hj
  have hblock : j / 4 < blocks := by omega
  have hcoord : exponentAt m j ≤ quaternionBlockDegree m (j / 4) := by
    have hmod : j % 4 < 4 := Nat.mod_lt _ (by decide)
    have hindex : j = 4 * (j / 4) + j % 4 := by omega
    have hsum : exponentAt m (4 * (j / 4) + j % 4) ≤
        quaternionBlockDegree m (j / 4) := by
      unfold quaternionBlockDegree
      cases hrem : j % 4 with
      | zero => simp [hrem]; omega
      | succ rem =>
          have hremBound : rem < 3 := by omega
          have hc : rem = 0 ∨ rem = 1 ∨ rem = 2 := by omega
          rcases hc with hzero | hone | htwo
          · simp [hrem, hzero]
            omega
          · simp [hrem, hone]
            omega
          · simp [hrem, htwo]

    simpa only [← hindex] using hsum
  simpa only [Nat.zero_add] using
    Nat.le_trans hcoord (hdegree (j / 4) hblock)

/-- Every enumerated exponent list is supported in the literal original
coordinate prefix. -/
theorem length_le_of_mem_monomials
    (blocks : Nat) (budget : Nat → Nat) (m : List Nat)
    (hm : m ∈ monomials blocks budget) : m.length ≤ 4 * blocks :=
  coordinateMonomials_length_le (4 * blocks) 0 budget m hm

#print axioms coordinateMonomials
#print axioms monomials
#print axioms mem_monomials_of_degree
#print axioms length_le_of_mem_monomials

end YMGap.Continuum.SU2QuaternionBoundedMonomials
