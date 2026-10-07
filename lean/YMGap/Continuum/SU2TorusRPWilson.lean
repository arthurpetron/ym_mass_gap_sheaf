/-
# Torus RP, commit 2: crossing plaquettes for the truncated Wilson weight `T_K` (every β ≥ 0)

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** `wilson_rp_full` takes the factorization `hW` as a hypothesis. The torus
bridge that discharges it has not landed.

The crossing scalar `σ_b = Σ_{c<4} u_c v_c = Re(U V*)` pairs block `b` (U, positive half) with block `a+b`
(V = Θ U). In the split formulation the crossing scalar is `Σ_c Y_c · shift Y_c` with `Y` a quaternion product,
an RPK term of the same kind.
`σ_b` is a reflection-positive kernel. Since `T_K = Σ_k a_k χ_1^k` with `a_k = wilsonA β k ≥ 0` and
`χ_1 = 2σ`, every crossing `T_K` and every finite product of them is an RPK (power-sum argument, no `D^s`).

* `sh_var`: `Θ x_j = x_{4a+j}`.
* `rpk_cross`: `RPK a σ_b` for `b < a`.
* `rpk_wilsonPoly`: `RPK a x → (∀ k, 0 ≤ c k) → RPK a (wilsonPoly x c K)`.
* `wilson_cross_rp`: `0 ≤ ∫ F · ΘF · T_K(σ_b)`.
* `wilson_rp_full`: `0 ≤ ∫ ΘF · F · W` when `W ≡ W₊ · ΘW₊ · Π_{b∈bs} T_K(σ_b)`.
* Validity is any `β ≥ 0`: RP itself is not a strong-coupling statement.
-/

import YMGap.Continuum.SU2TorusRPCore
import YMGap.Continuum.SU2WilsonPolymerIdentity

namespace YMGap.Continuum.SU2TorusRPWilson

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)
open YMGap.Continuum.SU2TorusRPCore
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2WilsonActivity (wilsonA wilsonA_nonneg)

theorem smul_eq (c : Q') (X : RatPoly) : polySmul c X = polyMul (polyConst c) X := by
  simp [polyMul, polyConst, polySmul, monoMul]

theorem sh_var (a j : Nat) : shiftPoly a (polyVar j) = polyVar (4 * a + j) := by
  simp [shiftPoly, polyVar, varMono, ← List.append_assoc]

theorem rpk_chiPow {a : Nat} {x : RatPoly} (hx : RPK a x) : ∀ k, RPK a (chiPow x k)
  | 0 => rpk_one a
  | k + 1 => by
    show RPK a (polyMul (characterPolynomial x 1) (chiPow x k))
    refine rpk_mul ?_ (rpk_chiPow hx k)
    show RPK a (polySmul 2 x)
    rw [smul_eq]; exact rpk_smul 2 (by decide) hx

theorem rpk_wilsonPoly {a : Nat} {x : RatPoly} (hx : RPK a x) (c : Nat → Q') (hc : ∀ k, (0 : Q') ≤ c k) :
    ∀ K, RPK a (wilsonPoly x c K)
  | 0 => by
    show RPK a (polySmul (c 0) (chiPow x 0)); rw [smul_eq]; exact rpk_smul _ (hc 0) (rpk_chiPow hx 0)
  | K + 1 => by
    show RPK a (polyAdd (wilsonPoly x c K) (polySmul (c (K + 1)) (chiPow x (K + 1))))
    rw [smul_eq]
    exact rpk_append (rpk_wilsonPoly hx c hc K) (rpk_smul _ (hc _) (rpk_chiPow hx _))

/-- Crossing scalar `σ_b = Σ_{c<4} x_{4b+c} · x_{4a+4b+c}`, which is `Re(U_b V_b*)`. -/
def cross (a b : Nat) : RatPoly := kern a ((List.range 4).map fun c => ((1 : Q'), polyVar (4 * b + c)))

/-- Each summand of `σ_b` is `x_{4b+c} · x_{4a+4b+c}`. -/
theorem cross_term (a b c : Nat) :
    term a ((1 : Q'), polyVar (4 * b + c)) =
      polyMul (polyConst 1) (polyMul (polyVar (4 * b + c)) (polyVar (4 * a + (4 * b + c)))) := by
  simp only [term, sh_var]

theorem rpk_cross {a b : Nat} (hb : b < a) : RPK a (cross a b) := by
  refine ⟨_, fun x hx => ?_, pe_refl _ _⟩
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨show (0 : Q') ≤ 1 by decide, fun s hs => ?_⟩
  simp [polyVar, varMono] at hs; subst hs; simp; omega

/-- Truncated Wilson weight on a crossing plaquette: `T_K = Σ_{k≤K} wilsonA β k · χ_1(σ_b)^k`. -/
def crossTK (a b : Nat) (β : Q') (K : Nat) : RatPoly := wilsonPoly (cross a b) (wilsonA β) K

theorem rpk_crossTK {a b : Nat} (hb : b < a) {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) :
    RPK a (crossTK a b β K) :=
  rpk_wilsonPoly (rpk_cross hb) _ (wilsonA_nonneg hβ) K

/-- Product of the crossing weights over the crossing blocks `bs`. -/
def crossProd (a : Nat) (β : Q') (K : Nat) : List Nat → RatPoly
  | [] => polyOne
  | b :: bs => polyMul (crossTK a b β K) (crossProd a β K bs)

theorem rpk_crossProd {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) :
    ∀ bs : List Nat, (∀ b ∈ bs, b < a) → RPK a (crossProd a β K bs)
  | [], _ => rpk_one a
  | b :: bs, h => rpk_mul (rpk_crossTK (h b (List.mem_cons_self ..)) hβ K)
      (rpk_crossProd hβ K bs fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- **Single crossing plaquette RP for `T_K`.** -/
theorem wilson_cross_rp {a b : Nat} (hb : b < a) {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat)
    (F : RatPoly) (hF : Sup a F) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul F (shiftPoly a F)) (crossTK a b β K)) :=
  rpk_pos (rpk_crossTK hb hβ K) F hF

/-- **Half-split RP for the `T_K` measure.** The weight `W` factors as a positive-half weight `W₊`, its
reflection, and the crossing plaquettes `bs`. -/
theorem wilson_rp_full {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (bs : List Nat) (hbs : ∀ b ∈ bs, b < a)
    (F Wp W : RatPoly) (hF : Sup a F) (hWp : Sup a Wp)
    (hW : PE (a + a) W (polyMul (polyMul Wp (shiftPoly a Wp)) (crossProd a β K bs))) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul (shiftPoly a F) F) W) :=
  rp_full F Wp _ W hF hWp (rpk_crossProd hβ K bs hbs) hW

end YMGap.Continuum.SU2TorusRPWilson

#print axioms YMGap.Continuum.SU2TorusRPWilson.wilson_cross_rp
#print axioms YMGap.Continuum.SU2TorusRPWilson.wilson_rp_full
