/-
# Exact finite subset expansion in the original polynomial algebra

Selections are computed by choosing or omitting each entry of the input
list. Products of (1+r_i) expand into the actual signed products of selected
remainders, before any Haar evaluation. Insertions and Haar integration
preserve the equality. This is a finite expansion, not a connected-cluster
reorganization or a summability hypothesis.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.FinitePolynomialSubsetExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

def selections {A : Type} : List A → List (List A)
  | [] => [[]]
  | a :: xs => selections xs ++ (selections xs).map (fun ys => a :: ys)

/-- Every selected entry is an actual input entry. No equality oracle is used. -/
theorem selected_mem {A : Type} : ∀ {xs ys : List A}, ys ∈ selections xs → ∀ a, a ∈ ys → a ∈ xs
  | [], ys, h, a, ha => by
      have he : ys = [] := List.mem_singleton.mp h
      rw [he] at ha
      exact False.elim (List.not_mem_nil ha)
  | x :: xs, ys, h, a, ha => by
      rcases List.mem_append.mp h with h | h
      · exact List.mem_cons_of_mem x (selected_mem h a ha)
      · obtain ⟨zs, hz, he⟩ := List.mem_map.mp h
        rw [← he] at ha
        rcases List.mem_cons.mp ha with heq | hin
        · exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons_of_mem x (selected_mem hz a hin)

theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs++ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | a :: xs, ys => by
      change polyAdd (f a) (finitePolySum f (xs++ys)) = _
      rw [sum_append f xs ys]
      exact (List.append_assoc _ _ _).symm

theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a :: xs => by change polyAdd _ _ = polyAdd _ _; rw [sum_map f g xs]

theorem sum_mul_left {A : Type} (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul p (finitePolySum f xs)) (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: xs => (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (sum_mul_left p f xs))

theorem product_expansion {A : Type} (f r : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) : ∀ xs : List A,
    RatPolyCoeffEqv (polynomialProduct f xs)
      (finitePolySum (polynomialProduct r) (selections xs))
  | [] => (RatPolyCoeffEqv.add_zero polyOne).symm
  | a :: xs => by
      rw [selections, sum_append, sum_map]
      have hp := (h a).mul (product_expansion f r h xs)
      rw [polyMul_add_left_exact] at hp
      exact hp.trans ((RatPolyCoeffEqv.one_mul _).add (sum_mul_left (r a) (polynomialProduct r) (selections xs)))

theorem insertion_expansion {A : Type} (f r : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) (p : RatPoly) (xs : List A) :
    RatPolyCoeffEqv (polyMul p (polynomialProduct f xs))
      (finitePolySum (fun ys => polyMul p (polynomialProduct r ys)) (selections xs)) :=
  ((RatPolyCoeffEqv.refl p).mul (product_expansion f r h xs)).trans (sum_mul_left p _ _)

/-- Exact original Haar integral, with the insertion and cutoff unchanged. -/
theorem haar_expansion {A : Type} (blocks : Nat) (f r : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) (p : RatPoly) (xs : List A) :
    Q'.eqv (quaternionHaar blocks (polyMul p (polynomialProduct f xs)))
      (listQSum (fun ys => quaternionHaar blocks (polyMul p (polynomialProduct r ys))) (selections xs)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (insertion_expansion f r h p xs)) (quaternionHaar_finitePolySum _ _ _)

end YMGap.Continuum.FinitePolynomialSubsetExpansion

#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.selections
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.selected_mem
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.sum_append
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.sum_map
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.sum_mul_left
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.product_expansion
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.insertion_expansion
#print axioms YMGap.Continuum.FinitePolynomialSubsetExpansion.haar_expansion
