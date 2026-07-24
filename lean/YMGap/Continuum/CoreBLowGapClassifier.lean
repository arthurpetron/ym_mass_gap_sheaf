/-
# Core-B bounded low-gap classifier

This module makes the first kernel-checked connection between the actual
bounded canonical atom ledger and the low-gap arithmetic budget.  It defines
the residual/adverse/gap predicate directly from the bounded monomial atoms,
then classifies the complete odd endpoint-gap-two fiber.

The classifier is not a transcription of a mass list: its soundness and
completeness theorem proves that its five selector patterns are exactly the
bounded non-window/window atoms whose actual exponents are adverse and whose
actual `quotientEndpointDegree` is two.  The stable range used by the budget,
`k ≥ 2`, is retained.

The generic tuple predicate and contribution function are intentionally
public.  A later power- or Bernstein-basis row sum can reuse the same actual
bounded ledger without changing the classifier statement.

Axiom gate (AGENTS.md Rules 1 and 8): constructive proof discipline
throughout.
-/

import YMGap.Continuum.CoreBCanonicalSquareShell
import YMGap.Continuum.CoreBLowGapBudget

namespace YMGap.Continuum.CoreBLowGapClassifier

open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CoreBBoundedMonomialNormalForm
open YMGap.Continuum.CoreBAtomwiseGapBounds
open YMGap.Continuum.CoreBCanonicalSquareShell
open YMGap.Continuum.CoreBLowGapBudget

set_option maxHeartbeats 4000000

/-! ## 1. Actual bounded ledger predicates -/

/-- A bounded odd canonical atom in one of the eleven residual component
pairs, adverse in exponent orientation and carrying the stated actual
square-gap quotient endpoint degree. -/
def oddCanonicalResidualAdverseAtGap
    (gap k t i j p q u v : Nat) : Prop :=
  t < 2 * k + 1 ∧
  i < 4 ∧ j < 3 ∧
  (i ≠ 0 ∨ j ≠ 0) ∧
  p < aLeftCount (t + 1) i ∧
  q < aRightCount (t + 1) i ∧
  u < mLeftCount (t + 1) j ∧
  v < mRightCount (t + 1) j ∧
  (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent <
    (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent ∧
  quotientEndpointDegree (oddContent k)
    (aAtomicMonomial (t + 1)
      (2 * k + 1 - 1 - t) i p q).exponent
    (mAtomicMonomial (t + 1)
      (2 * k + 1 - 1 - t) j u v).exponent = gap

/-- The actual coefficient-times-chain-length contribution of one adverse
bounded atom before the endpoint discount `2^{-gap}` is applied. -/
def adverseAtomContribution
    (a m : WeightMonomial) : Nat :=
  a.coefficientNat * m.coefficientNat * ((m.exponent - a.exponent) / 2)

/-- Actual contribution of one odd canonical bounded selector tuple. -/
def oddCanonicalAtomContribution
    (k t i j p q u v : Nat) : Nat :=
  adverseAtomContribution
    (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q)
    (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v)

/-! ## 2. Centered-shell orientation facts -/

/-- The two centered numerator coordinates of a canonical atom. -/
def canonicalNumeratorCenteredShell
    (n t i p q : Nat) : Nat :=
  centeredIndexSquare (n + 1) (canonicalALeftIndex (t + 1) i p) +
    centeredIndexSquare (n + 3) (canonicalARightIndex (t + 1) i q)

/-- The two centered midpoint coordinates of a canonical atom. -/
def canonicalMidpointCenteredShell
    (n t j u v : Nat) : Nat :=
  centeredIndexSquare (n + 2) (canonicalMLeftIndex (t + 1) j u) +
    centeredIndexSquare (n + 2) (canonicalMRightIndex (t + 1) j v)

private theorem sum_two_twice
    {a b za zb ca cb : Nat}
    (ha : 2 * a = za + ca) (hb : 2 * b = zb + cb) :
    2 * (a + b) = za + zb + (ca + cb) := by
  omega

private theorem canonical_twice_numerator_exponent
    (n t i p q : Nat) (ht : t < n)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i) :
    2 * (aAtomicMonomial (t + 1) (n - 1 - t) i p q).exponent =
      canonicalNumeratorCenteredShell n t i p q +
        ((n + 1) * (n + 1 + 4) + (n + 3) * (n + 3 + 4)) := by
  rw [canonical_a_atom_exponent_all n t i p q ht]
  exact sum_two_twice
    (twice_antidiagonalExponent_eq_centeredSquare_add
      (n + 1) (canonicalALeftIndex (t + 1) i p)
      (canonicalALeftIndex_le n t i p ht hp))
    (twice_antidiagonalExponent_eq_centeredSquare_add
      (n + 3) (canonicalARightIndex (t + 1) i q)
      (canonicalARightIndex_le n t i q ht hq))

private theorem canonical_twice_midpoint_exponent
    (n t j u v : Nat) (ht : t < n)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    2 * (mAtomicMonomial (t + 1) (n - 1 - t) j u v).exponent =
      canonicalMidpointCenteredShell n t j u v +
        ((n + 2) * (n + 2 + 4) + (n + 2) * (n + 2 + 4)) := by
  rw [canonical_m_atom_exponent_all n t j u v ht]
  exact sum_two_twice
    (twice_antidiagonalExponent_eq_centeredSquare_add
      (n + 2) (canonicalMLeftIndex (t + 1) j u)
      (canonicalMLeftIndex_le n t j u ht hu))
    (twice_antidiagonalExponent_eq_centeredSquare_add
      (n + 2) (canonicalMRightIndex (t + 1) j v)
      (canonicalMRightIndex_le n t j v ht hv))

private theorem canonical_shell_constant_orientation (n : Nat) :
    (n + 1) * (n + 1 + 4) + (n + 3) * (n + 3 + 4) =
      (n + 2) * (n + 2 + 4) + (n + 2) * (n + 2 + 4) + 2 := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- Adverse exponent orientation is exactly a strict centered-shell
orientation after accounting for the numerator's two-unit constant excess. -/
theorem canonical_adverse_centered_shell
    (n t i j p q u v : Nat) (ht : t < n)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hadverse :
      (aAtomicMonomial (t + 1) (n - 1 - t) i p q).exponent <
        (mAtomicMonomial (t + 1) (n - 1 - t) j u v).exponent) :
    canonicalNumeratorCenteredShell n t i p q + 2 <
      canonicalMidpointCenteredShell n t j u v := by
  have ha := canonical_twice_numerator_exponent n t i p q ht hp hq
  have hm := canonical_twice_midpoint_exponent n t j u v ht hu hv
  have hc := canonical_shell_constant_orientation n
  omega

private theorem canonical_adverse_of_centered_shell
    (n t i j p q u v : Nat) (ht : t < n)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hcenter :
      canonicalNumeratorCenteredShell n t i p q + 2 <
        canonicalMidpointCenteredShell n t j u v) :
    (aAtomicMonomial (t + 1) (n - 1 - t) i p q).exponent <
      (mAtomicMonomial (t + 1) (n - 1 - t) j u v).exponent := by
  have ha := canonical_twice_numerator_exponent n t i p q ht hp hq
  have hm := canonical_twice_midpoint_exponent n t j u v ht hu hv
  have hc := canonical_shell_constant_orientation n
  omega

/-- A centered shell of ten is exactly endpoint degree two on the odd
canonical diagonal. -/
theorem canonical_odd_quotientEndpointDegree_of_shell_ten
    (k t i j p q u v : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hshell :
      canonicalNumeratorCenteredShell (2 * k + 1) t i p q +
        canonicalMidpointCenteredShell (2 * k + 1) t j u v = 10) :
    quotientEndpointDegree (oddContent k)
      (aAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) i p q).exponent
      (mAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) j u v).exponent = 2 := by
  have ha := canonical_twice_numerator_exponent
    (2 * k + 1) t i p q ht hp hq
  have hm := canonical_twice_midpoint_exponent
    (2 * k + 1) t j u v ht hu hv
  have hconst := canonicalShellConstant_odd k
  have hsum :
      2 * ((aAtomicMonomial (t + 1)
          (2 * k + 1 - 1 - t) i p q).exponent +
        (mAtomicMonomial (t + 1)
          (2 * k + 1 - 1 - t) j u v).exponent) =
        canonicalNumeratorCenteredShell (2 * k + 1) t i p q +
          canonicalMidpointCenteredShell (2 * k + 1) t j u v +
          canonicalShellConstant (2 * k + 1) := by
    unfold canonicalShellConstant
    omega
  unfold quotientEndpointDegree
  omega

/-! ## 3. Small centered-square classification -/

private theorem centeredIndexSquare_even_zero_or_four_le (K p : Nat) :
    centeredIndexSquare (2 * K) p = 0 ∨
      4 ≤ centeredIndexSquare (2 * K) p := by
  by_cases hp : p = K
  · left
    subst p
    simp [centeredIndexSquare]
  · right
    by_cases hleft : p < K
    · have hd : 2 ≤ 2 * K - 2 * p := by omega
      have hsq := Nat.mul_le_mul hd hd
      unfold centeredIndexSquare
      omega
    · have hd : 2 ≤ 2 * p - 2 * K := by omega
      have hsq := Nat.mul_le_mul hd hd
      unfold centeredIndexSquare
      omega

private theorem centeredIndexSquare_even_eq_zero_iff (K p : Nat) :
    centeredIndexSquare (2 * K) p = 0 ↔ p = K := by
  constructor
  · intro h
    unfold centeredIndexSquare at h
    simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero] at h
    omega
  · intro h
    subst p
    simp [centeredIndexSquare]

private theorem centeredIndexSquare_odd_ge_nine_of_not_center
    (K p : Nat) (hp : p ≠ K) (hp' : p ≠ K + 1) :
    9 ≤ centeredIndexSquare (2 * K + 1) p := by
  by_cases hleft : p < K
  · have hd : 3 ≤ 2 * K + 1 - 2 * p := by omega
    have hsq := Nat.mul_le_mul hd hd
    unfold centeredIndexSquare
    omega
  · have hd : 3 ≤ 2 * p - (2 * K + 1) := by omega
    have hsq := Nat.mul_le_mul hd hd
    unfold centeredIndexSquare
    omega

private theorem centeredIndexSquare_odd_one_or_nine_le (K p : Nat) :
    centeredIndexSquare (2 * K + 1) p = 1 ∨
      9 ≤ centeredIndexSquare (2 * K + 1) p := by
  by_cases hp : p = K
  · left
    subst p
    simp [centeredIndexSquare]
  · by_cases hp' : p = K + 1
    · left
      subst p
      unfold centeredIndexSquare
      rw [show 2 * K + 1 - 2 * (K + 1) = 0 by omega]
      rw [show 2 * (K + 1) - (2 * K + 1) = 1 by omega]
    · exact Or.inr
        (centeredIndexSquare_odd_ge_nine_of_not_center K p hp hp')

private theorem centeredIndexSquare_odd_eq_one_iff (K p : Nat) :
    centeredIndexSquare (2 * K + 1) p = 1 ↔
      p = K ∨ p = K + 1 := by
  constructor
  · intro h
    by_cases hp : p = K
    · exact Or.inl hp
    · by_cases hp' : p = K + 1
      · exact Or.inr hp'
      · have h9 :=
          centeredIndexSquare_odd_ge_nine_of_not_center K p hp hp'
        omega
  · intro h
    rcases h with h | h
    · subst p
      unfold centeredIndexSquare
      rw [show 2 * K + 1 - 2 * K = 1 by omega]
      rw [show 2 * K - (2 * K + 1) = 0 by omega]
    · subst p
      unfold centeredIndexSquare
      rw [show 2 * K + 1 - 2 * (K + 1) = 0 by omega]
      rw [show 2 * (K + 1) - (2 * K + 1) = 1 by omega]

private theorem self_mul_le_nine {x : Nat} (h : x * x ≤ 9) : x ≤ 3 := by
  by_cases hx : x ≤ 3
  · exact hx
  · have h4 : 4 ≤ x := by omega
    have h16 := Nat.mul_le_mul h4 h4
    omega

private theorem centeredIndexSquare_odd_eq_nine_iff
    (K p : Nat) (hK : 1 ≤ K) :
    centeredIndexSquare (2 * K + 1) p = 9 ↔
      p = K - 1 ∨ p = K + 2 := by
  constructor
  · intro h
    by_cases hleft : p ≤ K
    · have hprod :
          (2 * K + 1 - 2 * p) * (2 * K + 1 - 2 * p) ≤ 9 := by
        unfold centeredIndexSquare at h
        omega
      have hsmall := self_mul_le_nine hprod
      have hpK : p ≠ K := by
        intro hp
        subst p
        have hcenter :=
          (centeredIndexSquare_odd_eq_one_iff K K).2 (Or.inl rfl)
        omega
      exact Or.inl (by omega)
    · have hprod :
          (2 * p - (2 * K + 1)) * (2 * p - (2 * K + 1)) ≤ 9 := by
        unfold centeredIndexSquare at h
        omega
      have hsmall := self_mul_le_nine hprod
      have hpK : p ≠ K + 1 := by
        intro hp
        subst p
        have hcenter :=
          (centeredIndexSquare_odd_eq_one_iff K (K + 1)).2 (Or.inr rfl)
        omega
      exact Or.inr (by omega)
  · intro h
    rcases h with h | h
    · subst p
      unfold centeredIndexSquare
      rw [show 2 * K + 1 - 2 * (K - 1) = 3 by omega]
      rw [show 2 * (K - 1) - (2 * K + 1) = 0 by omega]
    · subst p
      unfold centeredIndexSquare
      rw [show 2 * K + 1 - 2 * (K + 2) = 0 by omega]
      rw [show 2 * (K + 2) - (2 * K + 1) = 3 by omega]

private def oddMidpointTenIndexPattern (k left right : Nat) : Prop :=
  (((left = k ∨ left = k + 3) ∧
      (right = k + 1 ∨ right = k + 2)) ∨
    ((left = k + 1 ∨ left = k + 2) ∧
      (right = k ∨ right = k + 3)))

private theorem odd_numerator_centered_shell_eq_zero
    (k t i p q : Nat)
    (hleft : canonicalALeftIndex (t + 1) i p = k + 1)
    (hright : canonicalARightIndex (t + 1) i q = k + 2) :
    canonicalNumeratorCenteredShell (2 * k + 1) t i p q = 0 := by
  unfold canonicalNumeratorCenteredShell
  rw [hleft, hright]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
  rw [(centeredIndexSquare_even_eq_zero_iff (k + 1) (k + 1)).2 rfl]
  rw [(centeredIndexSquare_even_eq_zero_iff (k + 2) (k + 2)).2 rfl]

private theorem odd_midpoint_centered_shell_eq_ten
    (k t j u v : Nat) (hk : 2 ≤ k)
    (hindices :
      oddMidpointTenIndexPattern k
        (canonicalMLeftIndex (t + 1) j u)
        (canonicalMRightIndex (t + 1) j v)) :
    canonicalMidpointCenteredShell (2 * k + 1) t j u v = 10 := by
  unfold canonicalMidpointCenteredShell
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
  unfold oddMidpointTenIndexPattern at hindices
  rcases hindices with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rcases hl with hl | hl <;> rcases hr with hr | hr
    all_goals rw [hl, hr]
    all_goals
      rw [(centeredIndexSquare_odd_eq_nine_iff
        (k + 1) _ (by omega)).2 (by omega)]
    all_goals
      rw [(centeredIndexSquare_odd_eq_one_iff (k + 1) _).2 (by omega)]
  · rcases hl with hl | hl <;> rcases hr with hr | hr
    all_goals rw [hl, hr]
    all_goals
      rw [(centeredIndexSquare_odd_eq_one_iff (k + 1) _).2 (by omega)]
    all_goals
      rw [(centeredIndexSquare_odd_eq_nine_iff
        (k + 1) _ (by omega)).2 (by omega)]

private theorem odd_gap_two_of_centered_split
    (k t i j p q u v : Nat)
    (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hnum :
      canonicalNumeratorCenteredShell (2 * k + 1) t i p q = 0)
    (hmid :
      canonicalMidpointCenteredShell (2 * k + 1) t j u v = 10) :
    (aAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) i p q).exponent <
      (mAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) j u v).exponent ∧
    quotientEndpointDegree (oddContent k)
      (aAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) i p q).exponent
      (mAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) j u v).exponent = 2 := by
  have hadverse := canonical_adverse_of_centered_shell
    (2 * k + 1) t i j p q u v ht hp hq hu hv (by omega)
  have hgap := canonical_odd_quotientEndpointDegree_of_shell_ten
    k t i j p q u v ht hp hq hu hv (by omega)
  exact ⟨hadverse, hgap⟩

/-! ## 4. The complete odd gap-two classifier -/

/-- The five selector patterns in the stable odd gap-two fiber.  Selectors
belonging to singleton boundary factors are recorded at their actual bounded
value zero. -/
def oddGapTwoSelectorPattern
    (k t i j p q u v : Nat) : Prop :=
  (t = k ∧ i = 1 ∧ j = 0 ∧ p = k + 1 ∧ q = 0 ∧
    ((u = k ∧ v = k + 1) ∨ (u = k + 1 ∧ v = k))) ∨
  (t = k ∧ i = 1 ∧ j = 1 ∧ p = k + 1 ∧ q = 0 ∧
    u = k ∧ v = 0) ∨
  (t = k + 1 ∧ i = 0 ∧ j = 1 ∧ p = k + 1 ∧ q = k + 2 ∧
    (u = k + 1 ∨ u = k + 2) ∧ v = 0)

/-- Kernel-computable classifier for the complete odd endpoint-gap-two
fiber. -/
def oddGapTwoClassifier
    (k t i j p q u v : Nat) : Bool :=
  @decide (oddGapTwoSelectorPattern k t i j p q u v) (by
    unfold oddGapTwoSelectorPattern
    infer_instance)

/-- Every one of the five stable selector patterns is an actual bounded
residual adverse atom of endpoint gap two. -/
theorem oddGapTwoSelectorPattern_sound
    (k t i j p q u v : Nat) (hk : 2 ≤ k)
    (h : oddGapTwoSelectorPattern k t i j p q u v) :
    oddCanonicalResidualAdverseAtGap 2 k t i j p q u v := by
  rcases h with h | h | h
  · rcases h with ⟨htp, hip, hjp, hpp, hqp, h⟩
    subst t
    subst i
    subst j
    subst p
    subst q
    rcases h with ⟨hup, hvp⟩ | ⟨hup, hvp⟩
    · subst u
      subst v
      have ht : k < 2 * k + 1 := by omega
      have hp : k + 1 < aLeftCount (k + 1) 1 := by
        simp [aLeftCount]
      have hq : 0 < aRightCount (k + 1) 1 := by
        simp [aRightCount]
      have hu : k < mLeftCount (k + 1) 0 := by
        simp [mLeftCount]
        omega
      have hv : k + 1 < mRightCount (k + 1) 0 := by
        simp [mRightCount]
      have hnum := odd_numerator_centered_shell_eq_zero
        k k 1 (k + 1) 0 (by simp [canonicalALeftIndex])
          (by simp [canonicalARightIndex])
      have hmid := odd_midpoint_centered_shell_eq_ten
        k k 0 k (k + 1) hk (by
          unfold oddMidpointTenIndexPattern canonicalMLeftIndex
            canonicalMRightIndex
          exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
      have hcore := odd_gap_two_of_centered_split
        k k 1 0 (k + 1) 0 k (k + 1)
          ht hp hq hu hv hnum hmid
      exact ⟨ht, by decide, by decide, Or.inl (by decide),
        hp, hq, hu, hv, hcore.1, hcore.2⟩
    · have ht : k < 2 * k + 1 := by omega
      subst u
      subst v
      have hp : k + 1 < aLeftCount (k + 1) 1 := by
        simp [aLeftCount]
      have hq : 0 < aRightCount (k + 1) 1 := by
        simp [aRightCount]
      have hu : k + 1 < mLeftCount (k + 1) 0 := by
        simp [mLeftCount]
      have hv : k < mRightCount (k + 1) 0 := by
        simp [mRightCount]
        omega
      have hnum := odd_numerator_centered_shell_eq_zero
        k k 1 (k + 1) 0 (by simp [canonicalALeftIndex])
          (by simp [canonicalARightIndex])
      have hmid := odd_midpoint_centered_shell_eq_ten
        k k 0 (k + 1) k hk (by
          unfold oddMidpointTenIndexPattern canonicalMLeftIndex
            canonicalMRightIndex
          exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)
      have hcore := odd_gap_two_of_centered_split
        k k 1 0 (k + 1) 0 (k + 1) k
          ht hp hq hu hv hnum hmid
      exact ⟨ht, by decide, by decide, Or.inl (by decide),
        hp, hq, hu, hv, hcore.1, hcore.2⟩
  · rcases h with ⟨htp, hip, hjp, hpp, hqp, hup, hvp⟩
    subst t
    subst i
    subst j
    subst p
    subst q
    subst u
    subst v
    have ht : k < 2 * k + 1 := by omega
    have hp : k + 1 < aLeftCount (k + 1) 1 := by
      simp [aLeftCount]
    have hq : 0 < aRightCount (k + 1) 1 := by
      simp [aRightCount]
    have hu : k < mLeftCount (k + 1) 1 := by
      simp [mLeftCount]
      omega
    have hv : 0 < mRightCount (k + 1) 1 := by
      simp [mRightCount]
    have hnum := odd_numerator_centered_shell_eq_zero
      k k 1 (k + 1) 0 (by simp [canonicalALeftIndex])
        (by simp [canonicalARightIndex])
    have hmid := odd_midpoint_centered_shell_eq_ten
      k k 1 k 0 hk (by
        change oddMidpointTenIndexPattern k k (k + 2)
        unfold oddMidpointTenIndexPattern
        exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)
    have hcore := odd_gap_two_of_centered_split
      k k 1 1 (k + 1) 0 k 0 ht hp hq hu hv hnum hmid
    exact ⟨ht, by decide, by decide, Or.inl (by decide),
      hp, hq, hu, hv, hcore.1, hcore.2⟩
  · rcases h with ⟨htp, hip, hjp, hpp, hqp, h, hvp⟩
    subst t
    subst i
    subst j
    subst p
    subst q
    subst v
    rcases h with hup | hup
    · subst u
      have ht : k + 1 < 2 * k + 1 := by omega
      have hp : k + 1 < aLeftCount (k + 2) 0 := by
        simp [aLeftCount]
      have hq : k + 2 < aRightCount (k + 2) 0 := by
        simp [aRightCount]
      have hu : k + 1 < mLeftCount (k + 2) 1 := by
        simp [mLeftCount]
      have hv : 0 < mRightCount (k + 2) 1 := by
        simp [mRightCount]
      have hnum := odd_numerator_centered_shell_eq_zero
        k (k + 1) 0 (k + 1) (k + 2)
          (by simp [canonicalALeftIndex])
          (by simp [canonicalARightIndex])
      have hmid := odd_midpoint_centered_shell_eq_ten
        k (k + 1) 1 (k + 1) 0 hk (by
          change oddMidpointTenIndexPattern k (k + 1) (k + 3)
          unfold oddMidpointTenIndexPattern
          exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
      have hcore := odd_gap_two_of_centered_split
        k (k + 1) 0 1 (k + 1) (k + 2) (k + 1) 0
          ht hp hq hu hv hnum hmid
      exact ⟨ht, by decide, by decide, Or.inr (by decide),
        hp, hq, hu, hv, hcore.1, hcore.2⟩
    · subst u
      have ht : k + 1 < 2 * k + 1 := by omega
      have hp : k + 1 < aLeftCount (k + 2) 0 := by
        simp [aLeftCount]
      have hq : k + 2 < aRightCount (k + 2) 0 := by
        simp [aRightCount]
      have hu : k + 2 < mLeftCount (k + 2) 1 := by
        simp [mLeftCount]
      have hv : 0 < mRightCount (k + 2) 1 := by
        simp [mRightCount]
      have hnum := odd_numerator_centered_shell_eq_zero
        k (k + 1) 0 (k + 1) (k + 2)
          (by simp [canonicalALeftIndex])
          (by simp [canonicalARightIndex])
      have hmid := odd_midpoint_centered_shell_eq_ten
        k (k + 1) 1 (k + 2) 0 hk (by
          change oddMidpointTenIndexPattern k (k + 2) (k + 3)
          unfold oddMidpointTenIndexPattern
          exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩)
      have hcore := odd_gap_two_of_centered_split
        k (k + 1) 0 1 (k + 1) (k + 2) (k + 2) 0
          ht hp hq hu hv hnum hmid
      exact ⟨ht, by decide, by decide, Or.inr (by decide),
        hp, hq, hu, hv, hcore.1, hcore.2⟩

/-- Completeness of the five-pattern odd gap-two selector classifier against
the actual bounded canonical residual ledger. -/
theorem oddGapTwoSelectorPattern_complete
    (k t i j p q u v : Nat) (hk : 2 ≤ k)
    (h : oddCanonicalResidualAdverseAtGap 2 k t i j p q u v) :
    oddGapTwoSelectorPattern k t i j p q u v := by
  rcases h with
    ⟨ht, hi, hj, hresidual, hp, hq, hu, hv, hadverse, hgap⟩
  have hbalance :
      2 * oddContent k + 2 ≤
        (aAtomicMonomial (t + 1)
            (2 * k + 1 - 1 - t) i p q).exponent +
          (mAtomicMonomial (t + 1)
            (2 * k + 1 - 1 - t) j u v).exponent := by
    unfold quotientEndpointDegree at hgap
    omega
  have hshell := canonical_odd_four_square_shell_quotient
    k t i j p q u v ht hp hq hu hv hbalance
  rw [hgap] at hshell
  have htotal :
      canonicalNumeratorCenteredShell (2 * k + 1) t i p q +
        canonicalMidpointCenteredShell (2 * k + 1) t j u v = 10 := by
    unfold canonicalCenteredShell at hshell
    unfold canonicalNumeratorCenteredShell canonicalMidpointCenteredShell
    omega
  have horient := canonical_adverse_centered_shell
    (2 * k + 1) t i j p q u v ht hp hq hu hv hadverse
  have hnumle :
      canonicalNumeratorCenteredShell (2 * k + 1) t i p q ≤ 3 := by
    omega
  have hnumle' :
      centeredIndexSquare (2 * (k + 1))
          (canonicalALeftIndex (t + 1) i p) +
        centeredIndexSquare (2 * (k + 2))
          (canonicalARightIndex (t + 1) i q) ≤ 3 := by
    unfold canonicalNumeratorCenteredShell at hnumle
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at hnumle
    rw [show 2 * k + 1 + 3 = 2 * (k + 2) by omega] at hnumle
    exact hnumle
  have haLeftZero :
      centeredIndexSquare (2 * (k + 1))
        (canonicalALeftIndex (t + 1) i p) = 0 := by
    rcases centeredIndexSquare_even_zero_or_four_le
      (k + 1) (canonicalALeftIndex (t + 1) i p) with hzero | hfour
    · exact hzero
    · omega
  have haRightZero :
      centeredIndexSquare (2 * (k + 2))
        (canonicalARightIndex (t + 1) i q) = 0 := by
    rcases centeredIndexSquare_even_zero_or_four_le
      (k + 2) (canonicalARightIndex (t + 1) i q) with hzero | hfour
    · exact hzero
    · omega
  have haLeft :
      canonicalALeftIndex (t + 1) i p = k + 1 :=
    (centeredIndexSquare_even_eq_zero_iff
      (k + 1) (canonicalALeftIndex (t + 1) i p)).1 haLeftZero
  have haRight :
      canonicalARightIndex (t + 1) i q = k + 2 :=
    (centeredIndexSquare_even_eq_zero_iff
      (k + 2) (canonicalARightIndex (t + 1) i q)).1 haRightZero
  have hmid :
      canonicalMidpointCenteredShell (2 * k + 1) t j u v = 10 := by
    have hnum := odd_numerator_centered_shell_eq_zero
      k t i p q haLeft haRight
    omega
  have hmid' :
      centeredIndexSquare (2 * (k + 1) + 1)
          (canonicalMLeftIndex (t + 1) j u) +
        centeredIndexSquare (2 * (k + 1) + 1)
          (canonicalMRightIndex (t + 1) j v) = 10 := by
    unfold canonicalMidpointCenteredShell at hmid
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega] at hmid
    exact hmid
  have hleftClass := centeredIndexSquare_odd_one_or_nine_le
    (k + 1) (canonicalMLeftIndex (t + 1) j u)
  have hrightClass := centeredIndexSquare_odd_one_or_nine_le
    (k + 1) (canonicalMRightIndex (t + 1) j v)
  have hsquares :
      (centeredIndexSquare (2 * (k + 1) + 1)
            (canonicalMLeftIndex (t + 1) j u) = 9 ∧
        centeredIndexSquare (2 * (k + 1) + 1)
            (canonicalMRightIndex (t + 1) j v) = 1) ∨
      (centeredIndexSquare (2 * (k + 1) + 1)
            (canonicalMLeftIndex (t + 1) j u) = 1 ∧
        centeredIndexSquare (2 * (k + 1) + 1)
            (canonicalMRightIndex (t + 1) j v) = 9) := by
    rcases hleftClass with hleft | hleft
    · rcases hrightClass with hright | hright
      · omega
      · exact Or.inr ⟨hleft, by omega⟩
    · rcases hrightClass with hright | hright
      · exact Or.inl ⟨by omega, hright⟩
      · omega
  have hmidIndices :
      oddMidpointTenIndexPattern k
        (canonicalMLeftIndex (t + 1) j u)
        (canonicalMRightIndex (t + 1) j v) := by
    unfold oddMidpointTenIndexPattern
    rcases hsquares with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · left
      exact ⟨
        (centeredIndexSquare_odd_eq_nine_iff
          (k + 1) _ (by omega)).1 hleft,
        (centeredIndexSquare_odd_eq_one_iff (k + 1) _).1 hright⟩
    · right
      exact ⟨
        (centeredIndexSquare_odd_eq_one_iff (k + 1) _).1 hleft,
        (centeredIndexSquare_odd_eq_nine_iff
          (k + 1) _ (by omega)).1 hright⟩
  unfold oddGapTwoSelectorPattern
  unfold oddMidpointTenIndexPattern at hmidIndices
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hiCases with hi0 | hi1 | hi2 | hi3
  · subst i
    rcases hjCases with hj0 | hj1 | hj2
    · subst j
      have hfalse : False := by
        rcases hresidual with hi0 | hj0
        · exact hi0 rfl
        · exact hj0 rfl
      exact False.elim hfalse
    · subst j
      simp only [canonicalALeftIndex, canonicalARightIndex,
        canonicalMLeftIndex, canonicalMRightIndex,
        aLeftCount, aRightCount, mLeftCount, mRightCount] at haLeft haRight hmidIndices hp hq hu hv
      rcases hmidIndices with ⟨hml, hmr⟩ | ⟨hml, hmr⟩
      · have hfalse : False := by
          rcases hmr with hmr | hmr <;> omega
        exact False.elim hfalse
      · rcases hmr with hmr | hmr
        · have hfalse : False := by omega
          exact False.elim hfalse
        · have ht' : t = k + 1 := by omega
          have hv' : v = 0 := by omega
          exact Or.inr (Or.inr
            ⟨ht', rfl, rfl, haLeft, haRight, hml, hv'⟩)
    · subst j
      simp only [canonicalALeftIndex, canonicalARightIndex,
        canonicalMLeftIndex, canonicalMRightIndex,
        aLeftCount, aRightCount, mLeftCount, mRightCount] at haLeft haRight hmidIndices hp hq hu hv
      rcases hmidIndices with ⟨hml, hmr⟩ | ⟨hml, hmr⟩
      all_goals rcases hml with hml | hml
      all_goals rcases hmr with hmr | hmr
      all_goals
        have hfalse : False := by omega
        exact False.elim hfalse
  · subst i
    rcases hjCases with hj0 | hj1 | hj2
    · subst j
      simp only [canonicalALeftIndex, canonicalARightIndex,
        canonicalMLeftIndex, canonicalMRightIndex,
        aLeftCount, aRightCount, mLeftCount, mRightCount] at haLeft haRight hmidIndices hp hq hu hv
      rcases hmidIndices with ⟨hml, hmr⟩ | ⟨hml, hmr⟩
      · rcases hml with hml | hml
        · rcases hmr with hmr | hmr
          · have ht' : t = k := by omega
            have hq' : q = 0 := by omega
            exact Or.inl
              ⟨ht', rfl, rfl, haLeft, hq',
                Or.inl ⟨hml, hmr⟩⟩
          · have hfalse : False := by omega
            exact False.elim hfalse
        · have hfalse : False := by omega
          exact False.elim hfalse
      · rcases hml with hml | hml
        · rcases hmr with hmr | hmr
          · have ht' : t = k := by omega
            have hq' : q = 0 := by omega
            exact Or.inl
              ⟨ht', rfl, rfl, haLeft, hq',
                Or.inr ⟨hml, hmr⟩⟩
          · have hfalse : False := by omega
            exact False.elim hfalse
        · have hfalse : False := by omega
          exact False.elim hfalse
    · subst j
      simp only [canonicalALeftIndex, canonicalARightIndex,
        canonicalMLeftIndex, canonicalMRightIndex,
        aLeftCount, aRightCount, mLeftCount, mRightCount] at haLeft haRight hmidIndices hp hq hu hv
      rcases hmidIndices with ⟨hml, hmr⟩ | ⟨hml, hmr⟩
      · rcases hml with hml | hml
        · rcases hmr with hmr | hmr
          · have hfalse : False := by omega
            exact False.elim hfalse
          · have ht' : t = k := by omega
            have hq' : q = 0 := by omega
            have hv' : v = 0 := by omega
            exact Or.inr (Or.inl
              ⟨ht', rfl, rfl, haLeft, hq', hml, hv'⟩)
        · have hfalse : False := by omega
          exact False.elim hfalse
      · have hfalse : False := by
          rcases hmr with hmr | hmr <;> omega
        exact False.elim hfalse
    · subst j
      simp only [canonicalALeftIndex, canonicalARightIndex,
        canonicalMLeftIndex, canonicalMRightIndex,
        aLeftCount, aRightCount, mLeftCount, mRightCount] at haLeft haRight hmidIndices hp hq hu hv
      rcases hmidIndices with ⟨hml, hmr⟩ | ⟨hml, hmr⟩
      all_goals rcases hml with hml | hml
      all_goals rcases hmr with hmr | hmr
      all_goals
        have hfalse : False := by omega
        exact False.elim hfalse
  · subst i
    simp only [canonicalALeftIndex, canonicalARightIndex,
      aRightCount] at haLeft haRight hq
    have hfalse : False := by omega
    exact False.elim hfalse
  · subst i
    simp only [canonicalALeftIndex, canonicalARightIndex] at haLeft haRight
    have hfalse : False := by omega
    exact False.elim hfalse

/-- Exact stable odd gap-two fiber: the five explicit patterns are equivalent
to the bounded canonical residual/adverse/gap predicate. -/
theorem oddGapTwoSelectorPattern_iff
    (k t i j p q u v : Nat) (hk : 2 ≤ k) :
    oddGapTwoSelectorPattern k t i j p q u v ↔
      oddCanonicalResidualAdverseAtGap 2 k t i j p q u v :=
  ⟨oddGapTwoSelectorPattern_sound k t i j p q u v hk,
    oddGapTwoSelectorPattern_complete k t i j p q u v hk⟩

/-- Boolean form of the exact stable odd gap-two fiber classifier. -/
theorem oddGapTwoClassifier_eq_true_iff
    (k t i j p q u v : Nat) (hk : 2 ≤ k) :
    oddGapTwoClassifier k t i j p q u v = true ↔
      oddCanonicalResidualAdverseAtGap 2 k t i j p q u v := by
  simpa only [oddGapTwoClassifier, decide_eq_true_eq] using
    oddGapTwoSelectorPattern_iff k t i j p q u v hk

#print axioms canonical_adverse_centered_shell
#print axioms canonical_odd_quotientEndpointDegree_of_shell_ten
#print axioms oddGapTwoSelectorPattern_sound
#print axioms oddGapTwoSelectorPattern_complete
#print axioms oddGapTwoSelectorPattern_iff
#print axioms oddGapTwoClassifier_eq_true_iff

end YMGap.Continuum.CoreBLowGapClassifier
