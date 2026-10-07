/-
# Torus RP (d3h): crossing-kernel product and iterated Haar substitution

* `cross_witness`: every split crossing word has a Θ-witness `Y = B₁PB₂*`.
* `rpk_cross_prod`: the `tkProd` over a list of split crossing words (each with `SupQ a Y`) is an RPK. This
  supplies the `RPK a (C Wc)` hypothesis of `rp_conj_assembly` once `C Wc` is identified with this product.
* `haar_chain`: iterating `haar_step` over a list of Haar-invariant substitutions (the per-link crossing splits).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (open: the concrete per-link split instances on the torus integrand
and the identification `C Wc ≈PE tkProd …`).
-/

import YMGap.Continuum.SU2TorusRPCrossSplit

namespace YMGap.Continuum.SU2TorusRPCrossProd

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open PolyQuaternion (mul conj)
open YMGap.Continuum.SU2TorusRPWord (dot)
open YMGap.Continuum.SU2TorusRPKernel (shQ shQ_mul shQ_conj SupQ tkProd rpk_tkProd)
open YMGap.Continuum.SU2TorusRPCore (RPK)
open YMGap.Continuum.SU2TorusRPCrossSplit (cross_split_word)

local infix:50 " ≅ " => RatPolyCoeffEqv

/-- Split crossing word scalar for link data `(B₁, P, B₂)`. -/
def crossWord (a : Nat) (B1 P B2 : PolyQuaternion) : RatPoly :=
  (mul (mul (mul (conj (shQ a B1)) B1) P) (mul (conj (mul (conj (shQ a B2)) B2)) (conj (shQ a P)))).scalar

theorem cross_witness (a : Nat) (B1 P B2 : PolyQuaternion) :
    crossWord a B1 P B2 ≅ dot (shQ a (mul (mul B1 P) (conj B2))) (mul (mul B1 P) (conj B2)) := by
  have h := cross_split_word B1 P B2 (shQ a B1) (shQ a P) (shQ a B2)
  rw [shQ_mul, shQ_mul, shQ_conj]; exact h

/-- Positive-half support of the crossing data triple. -/
def CrossOK (a : Nat) (t : PolyQuaternion × PolyQuaternion × PolyQuaternion) : Prop :=
  SupQ a (mul (mul t.1 t.2.1) (conj t.2.2))

theorem rpk_cross_prod {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat)
    (ts : List (PolyQuaternion × PolyQuaternion × PolyQuaternion)) (h : ∀ t ∈ ts, CrossOK a t) :
    RPK a (tkProd β K (ts.map fun t => crossWord a t.1 t.2.1 t.2.2)) := by
  refine rpk_tkProd hβ K _ fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact ⟨_, h t ht, cross_witness a t.1 t.2.1 t.2.2⟩

/-- Iterated `haar_step`: each substitution is Haar-invariant on the current polynomial. -/
theorem haar_chain (n : Nat) :
    ∀ (Ss : List (RatPoly → RatPoly)) (P : RatPoly),
      (∀ S ∈ Ss, ∀ Q : RatPoly, (quaternionHaar n (S Q)).eqv (quaternionHaar n Q)) →
      (quaternionHaar n (Ss.foldr (fun S Q => S Q) P)).eqv (quaternionHaar n P)
  | [], _, _ => Q'.eqv_refl _
  | S :: Ss, P, h =>
    Q'.eqv_trans _ _ _ (h S (List.mem_cons_self ..) _)
      (haar_chain n Ss P fun T hT => h T (List.mem_cons_of_mem _ hT))

end YMGap.Continuum.SU2TorusRPCrossProd

#print axioms YMGap.Continuum.SU2TorusRPCrossProd.cross_witness
#print axioms YMGap.Continuum.SU2TorusRPCrossProd.rpk_cross_prod
#print axioms YMGap.Continuum.SU2TorusRPCrossProd.haar_chain
