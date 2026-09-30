/-
# Finite polynomial degree bounds for quaternion blocks

This module records a finite, coefficient-level degree ceiling on the
original rational polynomial carrier. It is preserved by conditional Haar
projection away from other blocks and by finite schedules of such
projections. No analytic or uniform mixing estimate is assumed.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

namespace YMGap.Continuum.SU2QuaternionBlockDegreeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (clearQuaternionBlock exponentAt_clearQuaternionBlock_of_ne)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (exponentAt_monoMul)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

/-- The maximum total degree in one quaternion block among a finite list of
polynomial terms. -/
def degreeBound (block : Nat) : RatPoly → Nat
  | [] => 0
  | t :: p => max (quaternionBlockDegree t.1 block) (degreeBound block p)

/-- Every term of `p` has degree at most `d` in the selected block. -/
def DegreeLE (block d : Nat) (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → quaternionBlockDegree t.1 block ≤ d

private theorem degree_monoMul (block : Nat) (left right : List Nat) :
    quaternionBlockDegree (monoMul left right) block =
      quaternionBlockDegree left block + quaternionBlockDegree right block := by
  unfold quaternionBlockDegree
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul]
  omega

theorem bound_spec (block : Nat) (p : RatPoly) :
    DegreeLE block (degreeBound block p) p := by
  induction p with
  | nil => simp [DegreeLE]
  | cons t p ih =>
      intro u hu
      rcases List.mem_cons.mp hu with h | h
      · subst u
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_refl _)
      · exact Nat.le_trans (ih u h) (Nat.le_max_right _ _)

theorem degreeBound_le_iff (block d : Nat) (p : RatPoly) :
    degreeBound block p ≤ d ↔ DegreeLE block d p := by
  constructor
  · intro h
    exact fun t ht => Nat.le_trans (bound_spec block p t ht) h
  · intro h
    induction p with
    | nil => simp [degreeBound]
    | cons t p ih =>
        change max (quaternionBlockDegree t.1 block) (degreeBound block p) ≤ d
        apply Nat.max_le.mpr
        constructor
        · exact h t List.mem_cons_self
        · exact ih (fun u hu => h u (List.mem_cons_of_mem t hu))

theorem DegreeLE.mono {block d e : Nat} {p : RatPoly}
    (hp : DegreeLE block d p) (hde : d ≤ e) : DegreeLE block e p :=
  fun t ht => Nat.le_trans (hp t ht) hde

theorem DegreeLE.add {block d : Nat} {p q : RatPoly}
    (hp : DegreeLE block d p) (hq : DegreeLE block d q) :
    DegreeLE block d (polyAdd p q) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hp t h
  · exact hq t h

theorem DegreeLE.smul {block d : Nat} {p : RatPoly}
    (hp : DegreeLE block d p) (c : Q') : DegreeLE block d (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem DegreeLE.mul {block d e : Nat} {p q : RatPoly}
    (hp : DegreeLE block d p) (hq : DegreeLE block e q) :
    DegreeLE block (d + e) (polyMul p q) := by
  intro u hu
  obtain ⟨s, hs, hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  rw [degree_monoMul]
  exact Nat.add_le_add (hp s hs) (hq t ht)

theorem DegreeLE.one (block : Nat) (d : Nat) :
    DegreeLE block d polyOne := by
  intro t ht
  have ht' : t = ([], 1) := by simpa [polyOne] using ht
  subst t
  simp [quaternionBlockDegree, exponentAt]

theorem DegreeLE.of_independent {block : Nat} {p : RatPoly}
    (hp : QuaternionBlockIndependent block p) : DegreeLE block 0 p := by
  intro t ht
  have hz := independent_has_degree_zero hp t ht
  rw [hz]
  exact Nat.le_refl 0

/-- Integrating any block preserves a ceiling in each distinct block; the
selected block itself becomes degree zero. -/
theorem project_degree (block selected d : Nat) (p : RatPoly)
    (hp : DegreeLE block d p) : DegreeLE block d (project selected p) := by
  by_cases h : block = selected
  · subst selected
    exact (DegreeLE.of_independent (project_independent block p)).mono
      (Nat.zero_le d)
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    change quaternionBlockDegree (clearQuaternionBlock selected s.1) block ≤ d
    unfold quaternionBlockDegree
    have hzero := exponentAt_clearQuaternionBlock_of_ne s.1 h (by decide : 0 < 4)
    simp only [Nat.add_zero] at hzero
    rw [hzero,
      exponentAt_clearQuaternionBlock_of_ne s.1 h (by decide : 1 < 4),
      exponentAt_clearQuaternionBlock_of_ne s.1 h (by decide : 2 < 4),
      exponentAt_clearQuaternionBlock_of_ne s.1 h (by decide : 3 < 4)]
    exact hp s hs

/-- A finite sequence of conditional integrations cannot increase a degree
ceiling in any block. -/
theorem familyProject_degree (ids : List Nat) (block d : Nat) (p : RatPoly)
    (hp : DegreeLE block d p) : DegreeLE block d (familyProject ids p) := by
  induction ids generalizing p with
  | nil => exact hp
  | cons i ids ih =>
      change DegreeLE block d (familyProject ids (project i p))
      exact ih (project i p) (project_degree block i d p hp)

/-- A family schedule containing a block removes all degree in that block. -/
theorem familyProject_selected_degree_zero (ids : List Nat) (block : Nat)
    (p : RatPoly) (hb : block ∈ ids) :
    DegreeLE block 0 (familyProject ids p) :=
  DegreeLE.of_independent (familyProject_independent ids p block hb)

theorem degreeBound_zero (block : Nat) : degreeBound block polyZero = 0 := rfl

theorem degreeBound_le_of_DegreeLE {block d : Nat} {p : RatPoly}
    (hp : DegreeLE block d p) : degreeBound block p ≤ d :=
  (degreeBound_le_iff block d p).2 hp

#print axioms bound_spec
#print axioms degreeBound
#print axioms DegreeLE
#print axioms degreeBound_le_iff
#print axioms DegreeLE.mono
#print axioms DegreeLE.add
#print axioms DegreeLE.smul
#print axioms DegreeLE.mul
#print axioms DegreeLE.one
#print axioms DegreeLE.of_independent
#print axioms degreeBound_zero
#print axioms degreeBound_le_of_DegreeLE
#print axioms project_degree
#print axioms familyProject_degree
#print axioms familyProject_selected_degree_zero

end YMGap.Continuum.SU2QuaternionBlockDegreeBound
