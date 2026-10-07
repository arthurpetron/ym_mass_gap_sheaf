/-
# Finite-volume SU(2) Wilson Gibbs measure on the Z⁴ torus: first honest layer

Scope: `audits/SCOPE-SU2-TORUS-WILSON-GIBBS-2026-10-06.md`.  ADDITIVE.

An honest finite-volume lattice Gibbs measure is
`⟨F⟩ = Z⁻¹ ∫ F(U) Π_p W(U_p) Π_ℓ dHaar(U_ℓ)`, `Z = ∫ Π_p W(U_p) Π_ℓ dHaar`,
with `W(g) = exp(−β(1 − ½ tr g))` (Wilson) or a positive class weight.

What is in this file:

* `ConfigHaar G N` (**OPEN hypothesis**): the product Haar integral over torus
  configurations as an abstract functional: linear, congruent, positive,
  normalised, invariant under gauge transforms and translations.  On the
  rational quaternion carrier (countable, non-compact) no such integral is
  constructed; it is a field-bundle, not a proof.
* `LinkHaar G` + `SU2Schur` (**OPEN hypothesis**): a single-link Haar
  functional with left/right invariance, and Schur orthogonality of the spin
  characters `h(χ_s χ_t) = δ_{st}`.
* `boltzmann`, `partition`: the unnormalised weight `Π_p W(U_p)` and
  `Z = I(Π_p W(U_p))` as functionals of the hypothesis (REDUCTION).
* `partition_ge` / `partition_pos` (proved from the fields): `W ≥ δ > 0`
  pointwise gives `Z ≥ δ^{6N⁴} > 0`.
* `boltzmann_gauge_invariant` (proved): for a class-function weight,
  `Π_p W(U_p)` is gauge invariant (from `TorusGaugeInvariance`), and
  `numerator_gauge_invariant`: `∫ (F∘g)·B ≈ ∫ F·B`.
* `su2SpinClass` (proved): on `RationalQuaternion.UnitNorm.group`, the spin
  characters `χ_s(x) = U_s(Re x)` are setoid-respecting class functions,
  via `Re(g h ḡ) = |g|² Re h`.
* `charWeight c J`, `su2CharWeightClass` (proved): a finite character sum
  `Σ_{s≤J} c_s χ_s` is a class weight.  The Wilson coefficients
  `c_s(β) = (s+1) I_{s+1}(β)/I_1(β)` and the truncation error are NOT formalised
  (explicit data; OPEN).

**U(1) test.**  Everything proved here is group-generic except the SU(2)
character layer; the U(1) analogue (characters `e^{inθ}`, coefficients
`I_n(β)/I_0(β)`, dimension 1, abelian fusion) satisfies the same abstract
statements.  No gap statement is made.  Choice-free; axioms ⊆ {propext, Quot.sound}.
-/

import YMGap.Continuum.TorusGaugeInvariance
import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.SU2TorusWilsonGibbs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq PolyExpr)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.TorusWilsonAction
open YMGap.Continuum.TorusGaugeInvariance
open YMGap.RepTheory

/-! ## 1. Open Haar hypotheses -/

/-- **DEPRECATED (vacuous for `G = SU2`).** Product Haar integral on ALL functions of
configurations.  For the rational unit quaternions no invariant mean on all
functions exists (free rank-2 subgroup, non-amenability), so theorems assuming it are
vacuous there.  Kept for compatibility; use `SU2TorusPolyGibbs` (polynomial domain). -/
structure ConfigHaar (G : ConstructiveGroup.{0}) (N : Nat) where
  I : (GaugeConfig G → Q') → Q'
  add : ∀ F H, (I (fun U => F U + H U)).eqv (I F + I H)
  smul : ∀ (c : Q') F, (I (fun U => c * F U)).eqv (c * I F)
  congr : ∀ F H, (∀ U, (F U).eqv (H U)) → (I F).eqv (I H)
  pos : ∀ F, (∀ U, (0 : Q') ≤ F U) → (0 : Q') ≤ I F
  norm : (I (fun _ => 1)).eqv 1
  gauge_inv : ∀ (g : Z4Vertex → G.Carrier) F,
    (I (fun U => F (gaugeTransform G N g U))).eqv (I F)
  shift_inv : ∀ (t : Z4Vertex) F, (I (fun U => F (shiftConfig G N t U))).eqv (I F)

/-- **DEPRECATED (vacuous for `G = SU2`).** Single-link Haar functional on ALL
functions: `LinkHaar SU2` is empty (non-amenability of the rational unit
quaternions, free subgroup from `(3+4i)/5`, `(3+4j)/5`).  Kept for compatibility;
use `SU2PolyLinkHaar.PolyLinkHaar` and `SU2TorusPolyGibbs`. -/
structure LinkHaar (G : ConstructiveGroup.{0}) where
  h : (G.Carrier → Q') → Q'
  add : ∀ F H, (h (fun x => F x + H x)).eqv (h F + h H)
  smul : ∀ (c : Q') F, (h (fun x => c * F x)).eqv (c * h F)
  pos : ∀ F, (∀ x, (0 : Q') ≤ F x) → (0 : Q') ≤ h F
  norm : (h (fun _ => 1)).eqv 1
  left_inv : ∀ g F, (h (fun x => F (G.mul g x))).eqv (h F)
  right_inv : ∀ g F, (h (fun x => F (G.mul x g))).eqv (h F)

/-! ## 2. SU(2) carrier: spin characters are class functions -/

abbrev SU2 : ConstructiveGroup.{0} := RationalQuaternion.UnitNorm.group

/-- Quaternion of polynomial expressions (mirrors `RationalQuaternion.mul/conj`). -/
structure QE where
  r : PolyExpr
  i : PolyExpr
  j : PolyExpr
  k : PolyExpr

def qmulE (x y : QE) : QE :=
  ⟨.add (.add (.mul x.r y.r) (.neg (.mul x.i y.i))) (.add (.neg (.mul x.j y.j)) (.neg (.mul x.k y.k))),
   .add (.add (.mul x.r y.i) (.mul x.i y.r)) (.add (.mul x.j y.k) (.neg (.mul x.k y.j))),
   .add (.add (.mul x.r y.j) (.neg (.mul x.i y.k))) (.add (.mul x.j y.r) (.mul x.k y.i)),
   .add (.add (.mul x.r y.k) (.mul x.i y.j)) (.add (.neg (.mul x.j y.i)) (.mul x.k y.r))⟩

def qconjE (x : QE) : QE := ⟨x.r, .neg x.i, .neg x.j, .neg x.k⟩

def gE : QE := ⟨.var 0, .var 1, .var 2, .var 3⟩
def hE : QE := ⟨.var 4, .var 5, .var 6, .var 7⟩

/-- `Re((g h) ḡ) = |g|² · Re h` (polynomial identity). -/
theorem re_conj (g h : RationalQuaternion) :
    (RationalQuaternion.mul (RationalQuaternion.mul g h) (RationalQuaternion.conj g)).r.eqv
      (RationalQuaternion.normSq g * h.r) :=
  poly_identity_of_normal_eq (qmulE (qmulE gE hE) (qconjE gE)).r
    (.mul (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) (.var 4))
    (by decide)
    (fun | 0 => g.r | 1 => g.i | 2 => g.j | 3 => g.k
         | 4 => h.r | 5 => h.i | 6 => h.j | _ => h.k)

private theorem qmul' {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha) (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Chebyshev-`U` respects `Q'` equivalence (same proof as `SU2Realized.U_congr`). -/
theorem chebU_congr' {a b : Q'} (h : a.eqv b) : ∀ n,
    (YMGap.Continuum.Cheb.U n a).eqv (YMGap.Continuum.Cheb.U n b) ∧
    (YMGap.Continuum.Cheb.U (n + 1) a).eqv (YMGap.Continuum.Cheb.U (n + 1) b)
  | 0 => ⟨Q'.eqv_refl _, qmul' (Q'.eqv_refl _) h⟩
  | n + 1 => by
      have ih := chebU_congr' h n
      refine ⟨ih.2, ?_⟩
      rw [YMGap.Continuum.Cheb.U_succ_succ, YMGap.Continuum.Cheb.U_succ_succ]
      exact Q'.add_eqv_congr' (qmul' (qmul' (Q'.eqv_refl _) h) ih.2)
        (Q'.neg_eqv_congr _ _ ih.1)

theorem chebU_congr {a b : Q'} (hab : a.eqv b) (s : Nat) :
    (YMGap.Continuum.Cheb.U s a).eqv (YMGap.Continuum.Cheb.U s b) :=
  (chebU_congr' hab s).1

/-- Spin character `χ_s(x) = U_s(Re x)` on the unit-quaternion carrier (equal to
`SU2Realized.spinCharacterUnit s x` by `SU2Realized.chebU_eq_U`; not imported, to
keep this module off the J04 import tree). -/
def chi (s : Nat) (x : SU2.Carrier) : Q' := YMGap.Continuum.Cheb.U s x.val.r

theorem chi_congr (s : Nat) (x y : SU2.Carrier) (hxy : SU2.setoid.r x y) :
    (chi s x).eqv (chi s y) :=
  chebU_congr hxy.1 s

theorem chi_conj (s : Nat) (g h : SU2.Carrier) :
    (chi s (SU2.mul (SU2.mul g h) (SU2.inv g))).eqv (chi s h) := by
  apply chebU_congr
  have e := re_conj g.val h.val
  exact Q'.eqv_trans _ _ _ e (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ g.unitNorm) (Q'.one_mul_eqv _))

/-- **Spin characters are class functions** on the SU(2) carrier. -/
def su2SpinClass (s : Nat) : ClassFunction SU2 :=
  ⟨chi s, chi_congr s, chi_conj s⟩

/-! ## 3. Character-expanded plaquette weights -/

/-- `Σ_{s ≤ J} c_s χ_s(x)` (explicit coefficient data). -/
def charWeight {G : ConstructiveGroup.{0}} (χ : Nat → ClassFunction G) (c : Nat → Q') :
    Nat → G.Carrier → Q'
  | 0, x => c 0 * (χ 0).f x
  | J + 1, x => charWeight χ c J x + c (J + 1) * (χ (J + 1)).f x

theorem charWeight_congr {G : ConstructiveGroup.{0}} (χ : Nat → ClassFunction G)
    (c : Nat → Q') : ∀ (J : Nat) (x y : G.Carrier), G.setoid.r x y →
      (charWeight χ c J x).eqv (charWeight χ c J y)
  | 0, x, y, h => Q'.mul_eqv_congr_left _ _ _ ((χ 0).congr x y h)
  | J + 1, x, y, h => Q'.add_eqv_congr' (charWeight_congr χ c J x y h)
      (Q'.mul_eqv_congr_left _ _ _ ((χ (J + 1)).congr x y h))

theorem charWeight_conj {G : ConstructiveGroup.{0}} (χ : Nat → ClassFunction G)
    (c : Nat → Q') : ∀ (J : Nat) (g h : G.Carrier),
      (charWeight χ c J (G.mul (G.mul g h) (G.inv g))).eqv (charWeight χ c J h)
  | 0, g, h => Q'.mul_eqv_congr_left _ _ _ ((χ 0).conj g h)
  | J + 1, g, h => Q'.add_eqv_congr' (charWeight_conj χ c J g h)
      (Q'.mul_eqv_congr_left _ _ _ ((χ (J + 1)).conj g h))

/-- A finite character sum is a class weight (any group). -/
def charWeightClass {G : ConstructiveGroup.{0}} (χ : Nat → ClassFunction G)
    (c : Nat → Q') (J : Nat) : ClassFunction G :=
  ⟨charWeight χ c J, charWeight_congr χ c J, charWeight_conj χ c J⟩

/-- The SU(2) character-expanded plaquette weight (coefficients explicit data). -/
def su2CharWeightClass (c : Nat → Q') (J : Nat) : ClassFunction SU2 :=
  charWeightClass su2SpinClass c J

/-- **OPEN data.** Schur orthogonality of SU(2) spin characters under a link
Haar functional. -/
structure SU2Schur (H : LinkHaar SU2) : Prop where
  orth : ∀ s t, (H.h (fun x => chi s x * chi t x)).eqv (if s = t then 1 else 0)

/-! ## 4. Boltzmann weight and partition function -/

def qprod : List Q' → Q'
  | [] => 1
  | a :: l => a * qprod l

/-- `Π_p W(U_p)` over the torus plaquettes. -/
def boltzmann {G : ConstructiveGroup.{0}} (N : Nat) (W : ClassFunction G)
    (U : GaugeConfig G) : Q' :=
  qprod ((torusPlaquettes N).map fun p => W.f (holonomy G N U p))

/-- `Z = ∫ Π_p W(U_p) Π_ℓ dHaar` (a functional of the OPEN Haar hypothesis). -/
def partition {G : ConstructiveGroup.{0}} {N : Nat} (I : ConfigHaar G N)
    (W : ClassFunction G) : Q' :=
  I.I (boltzmann N W)

/-- Unnormalised expectation numerator `∫ F · Π_p W(U_p)`. -/
def numerator {G : ConstructiveGroup.{0}} {N : Nat} (I : ConfigHaar G N)
    (W : ClassFunction G) (F : GaugeConfig G → Q') : Q' :=
  I.I (fun U => F U * boltzmann N W U)

theorem qprod_map_congr {α : Type} (f₁ f₂ : α → Q') :
    ∀ (l : List α), (∀ x, x ∈ l → (f₁ x).eqv (f₂ x)) →
      (qprod (l.map f₁)).eqv (qprod (l.map f₂))
  | [], _ => Q'.eqv_refl _
  | x :: l, h => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (h x List.mem_cons_self))
      (Q'.mul_eqv_congr_left _ _ _
        (qprod_map_congr f₁ f₂ l (fun y hy => h y (List.mem_cons_of_mem _ hy))))

/-- **Gauge invariance of the Boltzmann weight** (class-function weight). -/
theorem boltzmann_gauge_invariant {G : ConstructiveGroup.{0}} (N : Nat)
    (W : ClassFunction G) (g : Z4Vertex → G.Carrier) (U : GaugeConfig G) :
    (boltzmann N W (gaugeTransform G N g U)).eqv (boltzmann N W U) :=
  qprod_map_congr _ _ _ (fun p _ =>
    Q'.eqv_trans _ _ _ (W.congr _ _ (holonomy_gauge G N g U p)) (W.conj _ _))

/-- Gauge-transformed observables have the same unnormalised expectation. -/
theorem numerator_gauge_invariant {G : ConstructiveGroup.{0}} {N : Nat}
    (I : ConfigHaar G N) (W : ClassFunction G) (F : GaugeConfig G → Q')
    (g : Z4Vertex → G.Carrier) :
    (numerator I W (fun U => F (gaugeTransform G N g U))).eqv (numerator I W F) := by
  unfold numerator
  have h1 := I.congr (fun U => F (gaugeTransform G N g U) * boltzmann N W U)
    (fun U => F (gaugeTransform G N g U) * boltzmann N W (gaugeTransform G N g U))
    (fun U => Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boltzmann_gauge_invariant N W g U)))
  exact Q'.eqv_trans _ _ _ h1 (I.gauge_inv g (fun U => F U * boltzmann N W U))

theorem qprod_ge (δ : Q') (hδ : (0 : Q') ≤ δ) :
    ∀ (l : List Q'), (∀ a, a ∈ l → δ ≤ a) → δ ^ l.length ≤ qprod l
  | [], _ => by show (1 : Q') ≤ (1 : Q'); decide
  | a :: l, h => by
      show δ * δ ^ l.length ≤ a * qprod l
      have ha := h a List.mem_cons_self
      have ih := qprod_ge δ hδ l (fun b hb => h b (List.mem_cons_of_mem _ hb))
      exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ δ ih hδ)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ ha
          (Q'.le_trans' _ _ _ (Q'.pow_nonneg δ hδ l.length) ih))

/-- `F ≥ c` pointwise gives `I F ≥ c` (from linearity, positivity, normalisation). -/
theorem ConfigHaar.ge_const {G : ConstructiveGroup.{0}} {N : Nat} (I : ConfigHaar G N)
    (F : GaugeConfig G → Q') (c : Q') (hF : ∀ U, c ≤ F U) : c ≤ I.I F := by
  have hpos := I.pos (fun U => F U + -c) (fun U => by
    have := Q'.add_le_add_right _ _ (-c) (hF U)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq (.const 0)
      (.add (.var 0) (.neg (.var 0))) (by decide) (fun _ => c))) this)
  have hadd := I.add F (fun _ => -c)
  have hc : (I.I (fun _ => -c)).eqv (-c) := by
    have e1 := I.congr (fun _ => -c) (fun _ => -c * 1) (fun _ =>
      poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.neg (.var 0)) (.const 1))
        (by decide) (fun _ => c))
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ (I.smul (-c) (fun _ => 1))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ I.norm)
        (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.const 1)) (.neg (.var 0))
          (by decide) (fun _ => c))))
  have h2 : (0 : Q') ≤ I.I F + -c := Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr_left _ _ _ hc)))
  have h3 := Q'.add_le_add_right _ _ c h2
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq (.var 0)
      (.add (.const 0) (.var 0)) (by decide) (fun _ => c)))
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => I.I F | _ => c))))

/-- **Lower bound on Z.** If `W ≥ δ ≥ 0` pointwise, `Z ≥ δ^{6N⁴}`. -/
theorem partition_ge {G : ConstructiveGroup.{0}} {N : Nat} (I : ConfigHaar G N)
    (W : ClassFunction G) (δ : Q') (hδ : (0 : Q') ≤ δ) (hW : ∀ x, δ ≤ W.f x) :
    δ ^ (6 * (N * N * N * N)) ≤ partition I W := by
  apply I.ge_const
  intro U
  have h := qprod_ge δ hδ ((torusPlaquettes N).map fun p => W.f (holonomy G N U p))
    (fun a ha => by obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha; exact hW _)
  rwa [List.length_map, torusPlaquettes_length] at h

theorem pos_of_pos_le {a b : Q'} (ha : (0 : Q') < a) (h : a ≤ b) : (0 : Q') < b := by
  have ha' : (0 : Int) * (a.den : Int) < a.num * (1 : Int) := ha
  rw [Int.zero_mul, Int.mul_one] at ha'
  have hb : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h
  have hbd : (0 : Int) < (b.den : Int) := Int.ofNat_lt.mpr (Q'.den_pos b)
  have had : (0 : Int) < (a.den : Int) := Int.ofNat_lt.mpr (Q'.den_pos a)
  have h1 : (0 : Int) < b.num * (a.den : Int) := Int.lt_of_lt_of_le (Int.mul_pos ha' hbd) hb
  have h2 : (0 : Int) < b.num := Int.pos_of_mul_pos_left h1 had
  show (0 : Int) * (b.den : Int) < b.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]; exact h2

theorem pow_pos' (δ : Q') (hδ : (0 : Q') < δ) : ∀ n : Nat, (0 : Q') < δ ^ n
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | n + 1 => Q'.mul_pos hδ (pow_pos' δ hδ n)

/-- **Z > 0** from a uniform positive lower bound on the plaquette weight. -/
theorem partition_pos {G : ConstructiveGroup.{0}} {N : Nat} (I : ConfigHaar G N)
    (W : ClassFunction G) (δ : Q') (hδ : (0 : Q') < δ) (hW : ∀ x, δ ≤ W.f x) :
    (0 : Q') < partition I W :=
  pos_of_pos_le (pow_pos' δ hδ _) (partition_ge I W δ (Q'.le_of_lt hδ) hW)

end YMGap.Continuum.SU2TorusWilsonGibbs
