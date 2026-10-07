/-
# Torus RP assembly (b8): supported composition, and the composition-free chaining rule

* `RingSubOn n S`: the `RingSub` laws, required only for supported inputs (`Sup n`).
* `ringSubOn_comp`: if `S` is `RingSubOn` and `PECongrOn`, `R` is `RingSubOn` and keeps polynomials supported, then
  `S ∘ R` is `RingSubOn`. With `reindex_peCongrOn` and `conj_peCongr`, this composes reindex and conj flips over
  any inner substitution.
* `haar_step`: if `∫ S P ≈ ∫ P` (Haar invariance of `S`) and `S P ≈PE P'` (e.g. from `RingSub`), then `∫ P ≈ ∫ P'`.
  Chaining `haar_step` once per substitution changes the integrand one substitution at a time, so the assembly
  does NOT need the head shear to be `PECongr`. This is how (d) avoids the head-shear congruence.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (geometry (c), assembly (d)).
-/

import YMGap.Continuum.SU2TorusRPReindexCongr

namespace YMGap.Continuum.SU2TorusRPCompOn

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_haar)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul sup_one)
open YMGap.Continuum.SU2TorusRPSubst (RingSub)
open YMGap.Continuum.SU2TorusRPReindexCongr (PECongrOn)

structure RingSubOn (n : Nat) (S : RatPoly → RatPoly) : Prop where
  mul : ∀ p q, Sup n p → Sup n q → PE n (S (polyMul p q)) (polyMul (S p) (S q))
  add : ∀ p q, Sup n p → Sup n q → PE n (S (polyAdd p q)) (polyAdd (S p) (S q))
  smul : ∀ c p, Sup n p → PE n (S (polySmul c p)) (polySmul c (S p))
  neg : ∀ p, Sup n p → PE n (S (polyNeg p)) (polyNeg (S p))
  one : PE n (S polyOne) polyOne

variable {n : Nat}

theorem RingSub.on {S : RatPoly → RatPoly} (h : RingSub n S) : RingSubOn n S :=
  ⟨fun p q _ _ => h.mul p q, fun p q _ _ => h.add p q, fun c p _ => h.smul c p, fun p _ => h.neg p, h.one⟩

theorem sup_add {p q : RatPoly} (hp : Sup n p) (hq : Sup n q) : Sup n (polyAdd p q) := fun s hs => by
  rcases List.mem_append.mp hs with h | h
  · exact hp s h
  · exact hq s h

theorem sup_smul (c : Q') {p : RatPoly} (hp : Sup n p) : Sup n (polySmul c p) := fun s hs => by
  simp only [polySmul, List.mem_map] at hs
  obtain ⟨x, hx, rfl⟩ := hs; exact hp x hx

theorem sup_neg {p : RatPoly} (hp : Sup n p) : Sup n (polyNeg p) := fun s hs => by
  simp only [polyNeg, List.mem_map] at hs
  obtain ⟨x, hx, rfl⟩ := hs; exact hp x hx

theorem ringSubOn_comp {S R : RatPoly → RatPoly} (hS : RingSubOn n S) (hSc : PECongrOn n S)
    (hR : RingSubOn n R) (hRs : ∀ p, Sup n p → Sup n (R p)) : RingSubOn n (fun p => S (R p)) where
  mul p q hp hq := pe_trans n (hSc (hRs _ (sup_mul hp hq)) (sup_mul (hRs p hp) (hRs q hq)) (hR.mul p q hp hq))
    (hS.mul _ _ (hRs p hp) (hRs q hq))
  add p q hp hq := pe_trans n (hSc (hRs _ (sup_add hp hq)) (sup_add (hRs p hp) (hRs q hq)) (hR.add p q hp hq))
    (hS.add _ _ (hRs p hp) (hRs q hq))
  smul c p hp := pe_trans n (hSc (hRs _ (sup_smul c hp)) (sup_smul c (hRs p hp)) (hR.smul c p hp))
    (hS.smul _ _ (hRs p hp))
  neg p hp := pe_trans n (hSc (hRs _ (sup_neg hp)) (sup_neg (hRs p hp)) (hR.neg p hp)) (hS.neg _ (hRs p hp))
  one := pe_trans n (hSc (hRs _ (sup_one n)) (sup_one n) hR.one) hS.one

theorem haar_step (S : RatPoly → RatPoly) {P P' : RatPoly} (hinv : (quaternionHaar n (S P)).eqv (quaternionHaar n P))
    (h : PE n (S P) P') : (quaternionHaar n P).eqv (quaternionHaar n P') :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm hinv) (pe_haar n h)

end YMGap.Continuum.SU2TorusRPCompOn

#print axioms YMGap.Continuum.SU2TorusRPCompOn.ringSubOn_comp
#print axioms YMGap.Continuum.SU2TorusRPCompOn.haar_step
