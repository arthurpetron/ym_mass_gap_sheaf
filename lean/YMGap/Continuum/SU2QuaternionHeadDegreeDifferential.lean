/-
# Degree-preserving representatives of the original head derivatives

The raw derivative retains zero-coefficient terms. Removing precisely the
terms with zero differentiation exponent gives a computable representative
with the expected homogeneous degree. Coefficient-probe equality proves
that the derivative and Laplacian are unchanged. These representatives permit
degree induction in the high-spin Haar annihilation argument; no convergence
or cutoff stabilization is assumed here.
-/

import YMGap.Continuum.SU2QuaternionPartialSphereGaussian

namespace YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- Delete only terms whose differentiation exponent is zero. -/
def activeDerivative (i : Nat) (p : RatPoly) : RatPoly :=
  ratDerivative i (p.filter fun t => 0 < exponentAt t.1 i)

theorem activeDerivative_coeff (i : Nat) : ∀ p : RatPoly,
    RatPolyCoeffEqv (activeDerivative i p) (ratDerivative i p)
  | [] => RatPolyCoeffEqv.refl _
  | t :: rest => by
    by_cases ht : 0 < exponentAt t.1 i
    · simp only [activeDerivative, List.filter_cons, ht, decide_true,
        ↓reduceIte, ratDerivative, List.map_cons]
      intro weight
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (activeDerivative_coeff i rest weight)
    · have hz : exponentAt t.1 i = 0 := by omega
      intro weight
      simp only [activeDerivative, List.filter_cons, ht, decide_false, Bool.false_eq,
        ratDerivative, List.map_cons, ratWeightedSum]
      exact Q'.eqv_trans _ _ _ (activeDerivative_coeff i rest weight)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
              (by rw [hz]; exact Q'.zero_mul_eqv _)) (Q'.zero_mul_eqv _)))
          (Q'.eqv_of_eq (Q'.zero_add' _))))

theorem headDegree_lower {i : Nat} (hi : i < 4) (m : List Nat)
    (hm : 0 < exponentAt m i) :
    quaternionBlockDegree (lowerExponentAt i m) 0 + 1 = quaternionBlockDegree m 0 := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl
  all_goals try (rcases m with _ | ⟨a, m⟩)
  all_goals try (rcases m with _ | ⟨b, m⟩)
  all_goals try (rcases m with _ | ⟨c, m⟩)
  all_goals try (rcases m with _ | ⟨d, tail⟩)
  all_goals simp [quaternionBlockDegree, lowerExponentAt, exponentAt] at hm ⊢ <;> omega

theorem headExponent_le_degree {i : Nat} (hi : i < 4) (m : List Nat) :
    exponentAt m i ≤ quaternionBlockDegree m 0 := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl
  all_goals change _ ≤ exponentAt m 0 + exponentAt m 1 + exponentAt m 2 + exponentAt m 3
  all_goals omega

/-- Homogeneity is syntactic again, including the degree-zero case. -/
theorem activeDerivative_degree {i d : Nat} {p : RatPoly}
    (hi : i < 4) (hp : HasQuaternionBlockDegree 0 d p) :
    HasQuaternionBlockDegree 0 (d - 1) (activeDerivative i p) := by
  intro term ht
  unfold activeDerivative ratDerivative at ht
  obtain ⟨t, hfiltered, rfl⟩ := List.mem_map.mp ht
  have hf := List.mem_filter.mp hfiltered
  have hpos : 0 < exponentAt t.1 i := of_decide_eq_true hf.2
  have hd := hp t hf.1
  have hl := headDegree_lower hi t.1 hpos
  change quaternionBlockDegree (lowerExponentAt i t.1) 0 = d - 1
  omega

theorem activeDerivative_zero {i : Nat} (hi : i < 4) : ∀ p : RatPoly,
    HasQuaternionBlockDegree 0 0 p → activeDerivative i p = []
  | [], _ => rfl
  | t :: rest, hp => by
    have hd := hp t List.mem_cons_self
    have he := headExponent_le_degree hi t.1
    have hz : ¬ (0 < exponentAt t.1 i) := by omega
    have hr := activeDerivative_zero hi rest (fun s hs => hp s (List.mem_cons_of_mem t hs))
    simpa only [activeDerivative, List.filter_cons, hz, decide_false, Bool.false_eq, ↓reduceIte] using hr

def activeLaplacian (p : RatPoly) : RatPoly :=
  polyFour (activeDerivative 0 (activeDerivative 0 p))
    (activeDerivative 1 (activeDerivative 1 p))
    (activeDerivative 2 (activeDerivative 2 p))
    (activeDerivative 3 (activeDerivative 3 p))

theorem activeLaplacian_coeff (p : RatPoly) :
    RatPolyCoeffEqv (activeLaplacian p) (headLaplacian p) := by
  have h (i : Nat) := (activeDerivative_coeff i (activeDerivative i p)).trans
    ((activeDerivative_coeff i p).derivative i)
  exact (h 0).add ((h 1).add ((h 2).add (h 3)))

theorem activeLaplacian_degree {d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 d p) :
    HasQuaternionBlockDegree 0 (d - 2) (activeLaplacian p) := by
  have h (i : Nat) (hi : i < 4) := activeDerivative_degree hi (activeDerivative_degree hi hp)
  have hd : d - 1 - 1 = d - 2 := by omega
  simpa only [hd] using (h 0 (by decide)).add
    ((h 1 (by decide)).add ((h 2 (by decide)).add (h 3 (by decide))))

theorem activeLaplacian_zero {p : RatPoly} (hp : HasQuaternionBlockDegree 0 0 p) :
    activeLaplacian p = [] := by
  have h (i : Nat) (hi : i < 4) := activeDerivative_zero hi p hp
  rw [activeLaplacian, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  rfl

end YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeDerivative
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeDerivative_coeff
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.headDegree_lower
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.headExponent_le_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeDerivative_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeDerivative_zero
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeLaplacian
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeLaplacian_coeff
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeLaplacian_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadDegreeDifferential.activeLaplacian_zero
