/-
# Torus RP bridge, item 4 (part): quaternion-product crossing kernels and the generalized Wilson RP

* `pe_of_coeff`: coefficient equivalence `≅` implies Haar-PE. This transports the word identities of
  `SU2TorusRPWord` into the RPK calculus.
* `shQ a`: Θ on quaternions, i.e. `shiftPoly a` on each component. `shQ_mul`, `shQ_conj` (literal) say Θ commutes
  with Hamilton products.
* `rpk_qdot`: `RPK a (dot (shQ a Y) Y)` for every Λ₊ quaternion `Y`, i.e. `Σ_c Θ(Y_c)·Y_c`.
* `rpk_cut1`: the actual split crossing word at cut 1, `Re(V·L'·U*·L*)` with `L = A*B`, `L' = A'*B'` and
  `(A, V, A') = Θ(B, U, B')`, after `T_K` (`wilsonPoly … (wilsonA β) K`) is an RPK.
* `wilson_rp_qfull`: `wilson_rp_full` generalised to any list of crossing scalars, each `≅ dot (shQ a Y) Y`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** The assembly of the torus integrand into the form `W₊·ΘW₊·Π crossing`
(discharging `hW`) is NOT done here; see the obstruction in `docs/J04-TORUS-RP-SCOPE-2026-10-07.md`. Valid for every β ≥ 0.
-/

import YMGap.Continuum.SU2TorusRPWord
import YMGap.Continuum.SU2TorusRPWilson

namespace YMGap.Continuum.SU2TorusRPKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm pe_refl pe_symm pe_trans pe_append pe_comm pe_const pe_mulL)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)
open YMGap.Continuum.SU2TorusRPCore
open YMGap.Continuum.SU2TorusRPWord (dot cross_word_cut1)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2WilsonActivity (wilsonA wilsonA_nonneg)

local infix:50 " ≅ " => RatPolyCoeffEqv

theorem phi_eq (n : Nat) (m : List Nat) : ∀ X : RatPoly,
    phi n X m = ratWeightedSum (fun mono => quaternionHaarMono n (monoMul m mono)) X
  | [] => rfl
  | (mono, c) :: X => by
    show c * quaternionHaarMono n (monoMul m mono) + phi n X m = _
    rw [phi_eq n m X]; rfl

theorem pe_of_coeff (n : Nat) {X Y : RatPoly} (h : X ≅ Y) : PE n X Y := fun m => by
  rw [phi_eq, phi_eq]; exact h _

theorem rpk_of_coeff {a : Nat} {x y : RatPoly} (h : x ≅ y) (hy : RPK a y) : RPK a x :=
  rpk_congr (pe_of_coeff _ h) hy

/-! ## Θ on quaternions -/

def shQ (a : Nat) (q : PolyQuaternion) : PolyQuaternion :=
  ⟨shiftPoly a q.scalar, shiftPoly a q.iPart, shiftPoly a q.jPart, shiftPoly a q.kPart⟩

theorem sh_add (a : Nat) (p q : RatPoly) : shiftPoly a (polyAdd p q) = polyAdd (shiftPoly a p) (shiftPoly a q) := by
  simp [shiftPoly, polyAdd]

theorem sh_neg (a : Nat) (p : RatPoly) : shiftPoly a (polyNeg p) = polyNeg (shiftPoly a p) := by
  simp [shiftPoly, polyNeg]

theorem shQ_mul (a : Nat) (q r : PolyQuaternion) :
    shQ a (PolyQuaternion.mul q r) = PolyQuaternion.mul (shQ a q) (shQ a r) := by
  simp only [shQ, PolyQuaternion.mul, sh_add, sh_neg, sh_mul]

theorem shQ_conj (a : Nat) (q : PolyQuaternion) : shQ a (PolyQuaternion.conj q) = PolyQuaternion.conj (shQ a q) := by
  simp only [shQ, PolyQuaternion.conj, sh_neg]

/-- A quaternion on the positive half. -/
def SupQ (a : Nat) (q : PolyQuaternion) : Prop := Sup a q.scalar ∧ Sup a q.iPart ∧ Sup a q.jPart ∧ Sup a q.kPart

theorem pe_term1 (a : Nat) (Z : RatPoly) : PE (a + a) (polyMul (shiftPoly a Z) Z) (term a (1, Z)) :=
  pe_trans _ (pe_comm _ _ _) (pe_symm _ (pe_const _ 1 (Q'.eqv_refl 1) _))

/-- **Quaternion-product crossing kernel** `Σ_c Θ(Y_c)·Y_c` is an RPK. -/
theorem rpk_qdot {a : Nat} (Y : PolyQuaternion) (hY : SupQ a Y) : RPK a (dot (shQ a Y) Y) := by
  refine ⟨[(1, Y.scalar), (1, Y.iPart), (1, Y.jPart), (1, Y.kPart)], fun x hx => ?_, ?_⟩
  · have h1 : (0 : Q') ≤ 1 := by decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨h1, hY.1⟩
    · exact ⟨h1, hY.2.1⟩
    · exact ⟨h1, hY.2.2.1⟩
    · exact ⟨h1, hY.2.2.2⟩
  · show PE _ (polyAdd _ (polyAdd _ (polyAdd _ _))) (term a _ ++ (term a _ ++ (term a _ ++ (term a _ ++ []))))
    rw [List.append_nil]
    exact pe_append _ (pe_term1 a _) (pe_append _ (pe_term1 a _) (pe_append _ (pe_term1 a _) (pe_term1 a _)))

/-! ## `T_K` respects `≅` -/

theorem chiPow_congr {x y : RatPoly} (h : x ≅ y) : ∀ k, chiPow x k ≅ chiPow y k
  | 0 => RatPolyCoeffEqv.refl _
  | k + 1 => RatPolyCoeffEqv.mul (RatPolyCoeffEqv.smul 2 h) (chiPow_congr h k)

theorem wilsonPoly_congr {x y : RatPoly} (h : x ≅ y) (c : Nat → Q') : ∀ K, wilsonPoly x c K ≅ wilsonPoly y c K
  | 0 => RatPolyCoeffEqv.smul _ (chiPow_congr h 0)
  | K + 1 => RatPolyCoeffEqv.add (wilsonPoly_congr h c K) (RatPolyCoeffEqv.smul _ (chiPow_congr h _))

/-- `T_K` of any crossing scalar `x ≅ Σ_c Θ(Y_c)·Y_c` is an RPK. -/
theorem rpk_TK {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (x : RatPoly) (Y : PolyQuaternion)
    (hY : SupQ a Y) (hx : x ≅ dot (shQ a Y) Y) : RPK a (wilsonPoly x (wilsonA β) K) :=
  rpk_of_coeff (wilsonPoly_congr hx _ K)
    (YMGap.Continuum.SU2TorusRPWilson.rpk_wilsonPoly (rpk_qdot Y hY) _ (wilsonA_nonneg hβ) K)

/-- **Cut-1 crossing plaquette (actual split word) under `T_K` is an RPK.** -/
theorem rpk_cut1 {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (U B B' : PolyQuaternion)
    (hY : SupQ a (PolyQuaternion.mul (PolyQuaternion.mul B U) (PolyQuaternion.conj B'))) :
    RPK a (wilsonPoly
      (PolyQuaternion.mul (PolyQuaternion.mul (shQ a U) (PolyQuaternion.mul (PolyQuaternion.conj (shQ a B')) B'))
        (PolyQuaternion.mul (PolyQuaternion.conj U)
          (PolyQuaternion.conj (PolyQuaternion.mul (PolyQuaternion.conj (shQ a B)) B)))).scalar
      (wilsonA β) K) := by
  refine rpk_TK hβ K _ _ hY ?_
  have h := cross_word_cut1 (shQ a U) U (shQ a B) (shQ a B') B B'
  rwa [shQ_mul, shQ_mul, shQ_conj]

/-- Product of `T_K`s over crossing scalars, each with a Θ-witness. -/
def tkProd (β : Q') (K : Nat) : List RatPoly → RatPoly
  | [] => polyOne
  | x :: xs => polyMul (wilsonPoly x (wilsonA β) K) (tkProd β K xs)

theorem rpk_tkProd {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) :
    ∀ xs : List RatPoly, (∀ x ∈ xs, ∃ Y, SupQ a Y ∧ x ≅ dot (shQ a Y) Y) → RPK a (tkProd β K xs)
  | [], _ => rpk_one a
  | x :: xs, h => by
    obtain ⟨Y, hY, hx⟩ := h x (List.mem_cons_self ..)
    exact rpk_mul (rpk_TK hβ K x Y hY hx) (rpk_tkProd hβ K xs fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- **Generalized half-split Wilson RP** (crossing kernels = quaternion products). `hW` is still a hypothesis. -/
theorem wilson_rp_qfull {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (xs : List RatPoly)
    (hxs : ∀ x ∈ xs, ∃ Y, SupQ a Y ∧ x ≅ dot (shQ a Y) Y)
    (F Wp W : RatPoly) (hF : Sup a F) (hWp : Sup a Wp)
    (hW : PE (a + a) W (polyMul (polyMul Wp (shiftPoly a Wp)) (tkProd β K xs))) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul (shiftPoly a F) F) W) :=
  rp_full F Wp _ W hF hWp (rpk_tkProd hβ K xs hxs) hW

end YMGap.Continuum.SU2TorusRPKernel

#print axioms YMGap.Continuum.SU2TorusRPKernel.rpk_cut1
#print axioms YMGap.Continuum.SU2TorusRPKernel.wilson_rp_qfull
