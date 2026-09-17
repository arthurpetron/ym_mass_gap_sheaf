/-
# Coefficientwise algebra of the ORIGINAL conditional Haar projections

Conditional integration respects polynomial coefficient equality and pulls
independent factors through without integrating any spectator. The concrete
projections preserve independence and commute with a weighted selected-block
projection whenever the weight is independent of the spectator block.

These are exact identities on the full raw polynomial carrier. The intended
consumer is the original selected-pair heat map, not an assumed contraction
structure or a diagonal replacement of the polynomial space.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (natList_eq_of_length_getD)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarBlockProjection

local infix:50 " ≈ " => Q'.eqv

private theorem project_probe (block : Nat) (weight : List Nat → Q') : ∀ f : RatPoly,
    ratWeightedSum weight (project block f) ≈
      ratWeightedSum (fun m => quaternionBlockMoment block m *
        weight (clearQuaternionBlock block m)) f
  | [] => Q'.eqv_refl _
  | _t::rest => Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (project_probe block weight rest)

/-- Conditional projection respects every coefficient probe, not only Haar values. -/
theorem project_congr (block : Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (project block f) (project block g) := by
  intro weight
  exact Q'.eqv_trans _ _ _ (project_probe block weight f)
    (Q'.eqv_trans _ _ _ (h _) (Q'.eqv_symm (project_probe block weight g)))

private theorem project_single_mul_termwise (block : Nat) (s : RatTerm)
    (hs : clearQuaternionBlock block s.1 = s.1) : ∀ f : RatPoly,
    RatPolyTermwiseEqv (project block (polyMul [s] f))
      (polyMul [s] (project block f))
  | [] => True.intro
  | t::rest => by
      refine ⟨clearQuaternionBlock_monoMul_of_left_fixed block s.1 t.1 hs, ?_,
        project_single_mul_termwise block s hs rest⟩
      change (s.2*t.2) * quaternionBlockMoment block (monoMul s.1 t.1) ≈
        s.2 * (t.2 * quaternionBlockMoment block t.1)
      rw [quaternionBlockMoment_monoMul_of_left_fixed block s.1 t.1 hs]
      exact Q'.mul_assoc_eqv _ _ _

/-- An independent polynomial factor pulls through with all coefficients retained. -/
theorem project_mul_of_independent (block : Nat) : ∀ (r f : RatPoly),
    QuaternionBlockIndependent block r →
      RatPolyCoeffEqv (project block (polyMul r f)) (polyMul r (project block f))
  | [], _, _ => RatPolyCoeffEqv.refl _
  | s::rest, f, hr => by
      rw [polyMul_cons_left_exact s rest f,
        polyMul_cons_left_exact s rest (project block f), project_add]
      have hs : RatPolyCoeffEqv (project block (polyMul [s] f))
          (polyMul [s] (project block f)) :=
        fun weight => ratWeightedSum_termwise_eqv weight
          (project_single_mul_termwise block s (hr s List.mem_cons_self) f)
      exact hs.add (project_mul_of_independent block rest f
        (fun t ht => hr t (List.mem_cons_of_mem s ht)))

/-- Symmetric form for a fixed independent right factor. -/
theorem project_mul_right_of_independent (block : Nat) (f r : RatPoly)
    (hr : QuaternionBlockIndependent block r) :
    RatPolyCoeffEqv (project block (polyMul f r)) (polyMul (project block f) r) :=
  (project_congr block (RatPolyCoeffEqv.mul_comm f r)).trans
    ((project_mul_of_independent block r f hr).trans (RatPolyCoeffEqv.mul_comm _ _))

/-- Mask commutation preserves independence of every other slot. The statement
also holds when the selected and spectator slots coincide. -/
theorem project_preserves_independent (selected : Nat) {block : Nat} {f : RatPoly}
    (hf : QuaternionBlockIndependent block f) :
    QuaternionBlockIndependent block (project selected f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change clearQuaternionBlock block (clearQuaternionBlock selected s.1) =
    clearQuaternionBlock selected s.1
  rw [clearQuaternionBlock_comm, hf s hs]

theorem fluctuation_preserves_independent (selected : Nat) {block : Nat} {f : RatPoly}
    (hf : QuaternionBlockIndependent block f) :
    QuaternionBlockIndependent block (fluctuation selected f) :=
  quaternionBlockIndependent_polyAdd hf
    (quaternionBlockIndependent_polyNeg (project_preserves_independent selected hf))

/-- The mask and exact-degree predicates describe the same zero-dependence condition. -/
theorem independent_has_degree_zero {block : Nat} {f : RatPoly}
    (hf : QuaternionBlockIndependent block f) : HasQuaternionBlockDegree block 0 f := by
  intro t ht
  have hz (component : Nat) (hc : component < 4) :
      exponentAt t.1 (4*block+component) = 0 := by
    have h := exponentAt_clearQuaternionBlock_self t.1 block component hc
    rw [hf t ht] at h
    exact h
  change exponentAt t.1 (4*block+0) + exponentAt t.1 (4*block+1) +
    exponentAt t.1 (4*block+2) + exponentAt t.1 (4*block+3) = 0
  rw [hz 0 (by decide), hz 1 (by decide), hz 2 (by decide), hz 3 (by decide)]

theorem degree_zero_independent {block : Nat} {f : RatPoly}
    (hf : HasQuaternionBlockDegree block 0 f) : QuaternionBlockIndependent block f := by
  intro t ht
  have hd := hf t ht
  unfold quaternionBlockDegree at hd
  have hz (component : Nat) (hc : component < 4) :
      exponentAt t.1 (4*block+component) = 0 := by
    have he : component = 0 ∨ component = 1 ∨ component = 2 ∨ component = 3 := by omega
    rcases he with rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega
  apply natList_eq_of_length_getD (clearQuaternionBlock_length block t.1)
  intro coordinate _
  change exponentAt (clearQuaternionBlock block t.1) coordinate = exponentAt t.1 coordinate
  rw [exponentAt_clearQuaternionBlock]
  by_cases hc : coordinateInQuaternionBlock block coordinate
  · rw [if_pos hc]
    unfold coordinateInQuaternionBlock at hc
    have he : 4*block + (coordinate-4*block) = coordinate := by omega
    have hzero := hz (coordinate-4*block) (by omega)
    rw [he] at hzero
    exact hzero.symm
  · rw [if_neg hc]

theorem independent_iff_degree_zero (block : Nat) (f : RatPoly) :
    QuaternionBlockIndependent block f ↔ HasQuaternionBlockDegree block 0 f :=
  ⟨independent_has_degree_zero, degree_zero_independent⟩

/-- Direct input to the full-carrier heat-vacuum marginal theorem. -/
theorem project_has_degree_zero (block : Nat) (f : RatPoly) :
    HasQuaternionBlockDegree block 0 (project block f) :=
  independent_has_degree_zero (project_independent block f)

/-- Spectator projection commutes with the actual weighted selected-block map.
No positivity or contraction input is used; independence of W is explicit. -/
theorem project_weighted_projection_comm (selected spectator : Nat) (W f : RatPoly)
    (hW : QuaternionBlockIndependent spectator W) :
    RatPolyCoeffEqv (project spectator (project selected (polyMul W f)))
      (project selected (polyMul W (project spectator f))) :=
  (project_comm spectator selected (polyMul W f)).trans
    (project_congr selected (project_mul_of_independent spectator W f hW))

end YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_congr
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_mul_of_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_mul_right_of_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_preserves_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.fluctuation_preserves_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.independent_has_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.degree_zero_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.independent_iff_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_has_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra.project_weighted_projection_comm
