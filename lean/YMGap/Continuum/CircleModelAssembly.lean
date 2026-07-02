/-
# Assembling a `CircleModel` from the direction-pair encoding

This module discharges the **load-bearing algebraic core** of the arctan↔trig
inversion interface `ArctanTanInversion.CircleModel`: the exponential addition
law `rep_add` (`e^{i(a+b)} = e^{ia}·e^{ib}` transported to Gaussian-integer
directions) and the positive-radius extraction `sin_zero_of_rep_im_zero`.

## The encoding (the "load-bearing correction" to the framing)

We take the angle to BE its unit direction `(sinValue, cosValue) : CReal × CReal`
and define angle addition AS the complex product:

    add p q = ( p.1·q.2 + p.2·q.1 ,   -- sin(a+b) = s₁c₂ + c₁s₂
                p.2·q.2 − p.1·q.1 )   -- cos(a+b) = c₁c₂ − s₁s₂

and represent a Gaussian integer `z` by the direction `p` with a positive radius
`r`:

    rep p z := ∃ r, IsPositive r ∧ ofInt z.re ≃ r·p.2 ∧ ofInt z.im ≃ r·p.1 .

With this encoding the complex-product identity is **definitional**, so the
exponential addition law `rep_add` needs NO trig addition law: it collapses to
pure `CReal` ring algebra, discharged here in small lemma steps (`prodLemma`,
`mul4_reorder`, `cmul_sub`, `realHom`/`imagHom`).  The radius work is concentrated
into the two base links `repBaseP`/`repBaseM`, which is where the genuine
transcendental content already had to live.

## What is genuinely proved here (axiom-clean)

* `mul4_reorder`, `cmul_sub`, `ofQ'_ofInt_mul`, `realHom`, `imagHom`,
  `prodLemma` — the `CReal`-ring-algebra toolkit.
* `repDir_add` — the exponential addition law on direction pairs, **fully
  proved** from the toolkit (this is the load-bearing brick).
* `sinZeroDir` — the positive-radius extraction, from the `sinZero`
  cancellation datum.
* `toModel` — the assembled `CircleModel` (as a function of the honest residual
  bundle `CircleData`).
* `sinPi_eqv_zero` — `sin π ≃ 0` for the assembled model, i.e.
  `CircleModel.sinMachinAngle_eqv_zero` instantiated.

## The honest residual (`CircleData`)

Everything NOT closed here is bundled as the Type-level datum `CircleData`, whose
fields are EXACTLY the residuals flagged in the task framing:

  * `mulPos`  — product of positive `CReal`s is positive (elementary; the repo's
     one-slack order makes it non-`rfl`, currently absent);
  * `sinZero` — the positive-cancellation lemma
     `IsPositive r → r·s ≃ 0 → s ≃ 0` (elementary; absent);
  * `baseP`, `repBaseP` — the `arctan(1/5)` base link `rep · ⟨5,1⟩`;
  * `baseM`, `repBaseM` — the `−arctan(1/239)` base link `rep · ⟨239,−1⟩`.

The base links carry the sole transcendental content (`ArctanTrigConverges` for
`1/5` and its `1/239` clone) plus the elementary normalization (positivity of the
cosines + a `CReal` reciprocal / `√`-closed-form radius).  This module does NOT
fake them; it isolates them and closes everything algebraic around them.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (the latter via reused `omega`/`Nat`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
All witness data is `Type`-level (`CircleData` is a structure of data; the
`rep`-predicate's radius `∃` is inside the `Prop`-valued interface field `rep`,
as fixed by `ArctanTanInversion.CircleModel`).
-/

import YMGap.Continuum.ArctanTanInversion
import YMGap.Constructive.CRealExp
import YMGap.Constructive.TrigSignedAddFull
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.CircleModelAssembly

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ArctanTanInversion

/-! ## 0. Tiny `Q'` num/den helpers (all `rfl`, for the `ofInt` homomorphism) -/

private theorem addNumCast (a b : Q') :
    (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl

private theorem mulNumCast (a b : Q') : (a * b).num = a.num * b.num := rfl

private theorem negNum (q : Q') : (-q).num = -(q.num) := rfl

private theorem ofIntNum (n : Int) : (Q'.ofInt n).num = n := rfl

private theorem ofIntDen (n : Int) : ((Q'.ofInt n).den : Int) = 1 := rfl

/-! ## 1. Pointwise `ofInt` ring-homomorphism steps (via `omega`) -/

/-- `ofInt(a·b) ≃ ofInt a · ofInt b` at the `Q'` level. -/
private theorem ofInt_mul_pt (a b : Int) :
    (Q'.ofInt (a * b)).eqv (Q'.ofInt a * Q'.ofInt b) := by
  unfold Q'.eqv
  simp only [Q'.mul_den_cast, mulNumCast, ofIntNum, ofIntDen]
  omega

/-- `ofInt(a·b) ≃ ofInt a · ofInt b` at the `CReal` level. -/
theorem ofQ'_ofInt_mul (a b : Int) :
    Equiv (ofQ' (Q'.ofInt (a * b))) (mul (ofQ' (Q'.ofInt a)) (ofQ' (Q'.ofInt b))) :=
  TrigAdd.equiv_of_approx_eqv (fun _ => ofInt_mul_pt a b)

/-! ## 2. Pure `CReal` ring-algebra bricks -/

/-- **Four-factor product reshuffle**: `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem mul4_reorder (a b c d : CReal) :
    Equiv (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
  have s1 : Equiv (mul (mul a b) (mul c d)) (mul a (mul b (mul c d))) :=
    CRealAlg.cmul_assoc a b (mul c d)
  have s2 : Equiv (mul b (mul c d)) (mul c (mul b d)) := by
    have t1 : Equiv (mul b (mul c d)) (mul (mul b c) d) := (CRealAlg.cmul_assoc b c d).symm
    have t2 : Equiv (mul (mul b c) d) (mul (mul c b) d) :=
      CReal.mul_congr_left (CRealAlg.cmul_comm b c)
    have t3 : Equiv (mul (mul c b) d) (mul c (mul b d)) := CRealAlg.cmul_assoc c b d
    exact (t1.trans t2).trans t3
  have s3 : Equiv (mul a (mul b (mul c d))) (mul a (mul c (mul b d))) :=
    TrigSignedAdd.mul_congr_right s2
  have s4 : Equiv (mul a (mul c (mul b d))) (mul (mul a c) (mul b d)) :=
    (CRealAlg.cmul_assoc a c (mul b d)).symm
  exact (s1.trans s3).trans s4

/-- **Left-distributivity over subtraction**: `A·(B − C) ≃ A·B − A·C`. -/
theorem cmul_sub (A B C : CReal) :
    Equiv (mul A (sub B C)) (sub (mul A B) (mul A C)) := by
  have h1 : Equiv (mul A (sub B C)) (add (mul A B) (mul A (neg C))) :=
    TrigSignedAddFull.cmul_add A B (neg C)
  have h2 : Equiv (add (mul A B) (mul A (neg C))) (add (mul A B) (neg (mul A C))) :=
    CReal.add_congr_right (TrigSignedAdd.mul_neg A C)
  exact h1.trans h2

/-- **One product term of the complex product.**  If `ofInt a ≃ s·c` and
`ofInt b ≃ t·d`, then `ofInt(a·b) ≃ (s·t)·(c·d)`. -/
theorem prodLemma (a b : Int) (s c t d : CReal)
    (hac : Equiv (ofQ' (Q'.ofInt a)) (mul s c))
    (hbd : Equiv (ofQ' (Q'.ofInt b)) (mul t d)) :
    Equiv (ofQ' (Q'.ofInt (a * b))) (mul (mul s t) (mul c d)) := by
  have e0 : Equiv (ofQ' (Q'.ofInt (a * b)))
      (mul (ofQ' (Q'.ofInt a)) (ofQ' (Q'.ofInt b))) := ofQ'_ofInt_mul a b
  have e1 : Equiv (mul (ofQ' (Q'.ofInt a)) (ofQ' (Q'.ofInt b)))
      (mul (mul s c) (mul t d)) :=
    (CReal.mul_congr_left hac).trans (TrigSignedAdd.mul_congr_right hbd)
  have e2 : Equiv (mul (mul s c) (mul t d)) (mul (mul s t) (mul c d)) :=
    mul4_reorder s c t d
  exact (e0.trans e1).trans e2

/-! ## 3. The two Gaussian-integer component homomorphisms -/

/-- **Real component**: `ofInt((z·w).re) ≃ ofInt(z.re·w.re) − ofInt(z.im·w.im)`. -/
theorem realHom (z w : GaussInt) :
    Equiv (ofQ' (Q'.ofInt (gMul z w).re))
      (sub (ofQ' (Q'.ofInt (z.re * w.re))) (ofQ' (Q'.ofInt (z.im * w.im)))) := by
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  change (Q'.ofInt (z.re * w.re - z.im * w.im)).eqv
    (Q'.ofInt (z.re * w.re) + -(Q'.ofInt (z.im * w.im)))
  unfold Q'.eqv
  simp only [Q'.add_den_cast, Q'.neg_den, addNumCast, negNum, ofIntNum, ofIntDen]
  omega

/-- **Imaginary component**: `ofInt((z·w).im) ≃ ofInt(z.im·w.re) + ofInt(z.re·w.im)`. -/
theorem imagHom (z w : GaussInt) :
    Equiv (ofQ' (Q'.ofInt (gMul z w).im))
      (add (ofQ' (Q'.ofInt (z.im * w.re))) (ofQ' (Q'.ofInt (z.re * w.im)))) := by
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  change (Q'.ofInt (z.re * w.im + z.im * w.re)).eqv
    (Q'.ofInt (z.im * w.re) + Q'.ofInt (z.re * w.im))
  unfold Q'.eqv
  simp only [Q'.add_den_cast, addNumCast, ofIntNum, ofIntDen]
  omega

/-! ## 4. The direction-pair encoding -/

/-- Angle addition = the complex product on `(sin, cos)` pairs. -/
def dadd (p q : CReal × CReal) : CReal × CReal :=
  ( add (mul p.1 q.2) (mul p.2 q.1),
    sub (mul p.2 q.2) (mul p.1 q.1) )

/-- The direction-pair representation predicate:
`z` points along `p = (sin, cos)` with positive radius `r`. -/
def repDir (p : CReal × CReal) (z : GaussInt) : Prop :=
  ∃ r : CReal, CReal.IsPositive r
    ∧ Equiv (ofQ' (Q'.ofInt z.re)) (mul r p.2)
    ∧ Equiv (ofQ' (Q'.ofInt z.im)) (mul r p.1)

/-! ## 5. The honest residual bundle -/

/-- The Type-level bundle of the residuals this assembly is conditional on:
the two elementary positivity facts and the two transcendental base links. -/
structure CircleData : Type where
  /-- Product of positive `CReal`s is positive (elementary; absent from repo). -/
  mulPos : ∀ {r₁ r₂ : CReal},
    CReal.IsPositive r₁ → CReal.IsPositive r₂ → CReal.IsPositive (mul r₁ r₂)
  /-- Positive cancellation `r·s ≃ 0 → s ≃ 0` for `IsPositive r`
  (elementary; absent from repo). -/
  sinZero : ∀ {r s : CReal},
    CReal.IsPositive r → Equiv (mul r s) czero → Equiv s czero
  /-- The `arctan(1/5)` unit direction. -/
  baseP : CReal × CReal
  /-- The base link `rep (arctan 1/5) ⟨5,1⟩`. -/
  repBaseP : repDir baseP gi5
  /-- The `−arctan(1/239)` unit direction. -/
  baseM : CReal × CReal
  /-- The base link `rep (−arctan 1/239) ⟨239,−1⟩`. -/
  repBaseM : repDir baseM gi239m

/-! ## 6. The exponential addition law (load-bearing brick) -/

/-- **`rep_add` for the direction-pair encoding.**  Pure `CReal` ring algebra:
the radius is `r₁·r₂` and the two scalar identities collapse via `realHom`
/`imagHom`, `prodLemma`, `cmul_sub`/`cmul_add`. -/
theorem repDir_add (D : CircleData) {a b : CReal × CReal} {x y : GaussInt}
    (ha : repDir a x) (hb : repDir b y) :
    repDir (dadd a b) (gMul x y) := by
  obtain ⟨r₁, hp1, har, hai⟩ := ha
  obtain ⟨r₂, hp2, hbr, hbi⟩ := hb
  refine ⟨mul r₁ r₂, D.mulPos hp1 hp2, ?_, ?_⟩
  · -- real component: ≃ mul (r₁·r₂) (cos component)
    have t1 : Equiv (ofQ' (Q'.ofInt (x.re * y.re)))
        (mul (mul r₁ r₂) (mul a.2 b.2)) := prodLemma x.re y.re r₁ a.2 r₂ b.2 har hbr
    have t2 : Equiv (ofQ' (Q'.ofInt (x.im * y.im)))
        (mul (mul r₁ r₂) (mul a.1 b.1)) := prodLemma x.im y.im r₁ a.1 r₂ b.1 hai hbi
    refine (realHom x y).trans ?_
    refine ((sub_congr_left t1).trans (sub_congr_right t2)).trans ?_
    exact (cmul_sub (mul r₁ r₂) (mul a.2 b.2) (mul a.1 b.1)).symm
  · -- imaginary component: ≃ mul (r₁·r₂) (sin component)
    have u1 : Equiv (ofQ' (Q'.ofInt (x.im * y.re)))
        (mul (mul r₁ r₂) (mul a.1 b.2)) := prodLemma x.im y.re r₁ a.1 r₂ b.2 hai hbr
    have u2 : Equiv (ofQ' (Q'.ofInt (x.re * y.im)))
        (mul (mul r₁ r₂) (mul a.2 b.1)) := prodLemma x.re y.im r₁ a.2 r₂ b.1 har hbi
    refine (imagHom x y).trans ?_
    refine ((add_congr_left u1).trans (add_congr_right u2)).trans ?_
    exact (TrigSignedAddFull.cmul_add (mul r₁ r₂) (mul a.1 b.2) (mul a.2 b.1)).symm

/-! ## 7. The positive-radius extraction -/

/-- **`sin_zero_of_rep_im_zero` for the direction-pair encoding.**  A direction
with zero imaginary part has zero sine, via the `sinZero` cancellation datum. -/
theorem sinZeroDir (D : CircleData) {θ : CReal × CReal} {z : GaussInt}
    (hrep : repDir θ z) (hzim : z.im = 0) : Equiv θ.1 czero := by
  obtain ⟨r, hpos, _, himag⟩ := hrep
  have h0 : Equiv (mul r θ.1) czero := by
    have hs := himag.symm
    rw [hzim] at hs
    exact hs
  exact D.sinZero hpos h0

/-! ## 8. The assembled model and `sin π ≃ 0` -/

/-- **The assembled `CircleModel`**, as a function of the honest residual bundle
`CircleData`.  `rep_add` and `sin_zero_of_rep_im_zero` are the proved bricks
above; the base links and the two positivity data are the `CircleData` fields. -/
def toModel (D : CircleData) : CircleModel where
  Angle := CReal × CReal
  add := dadd
  sinOf := fun p => p.1
  rep := repDir
  rep_add := fun ha hb => repDir_add D ha hb
  baseP := D.baseP
  repBaseP := D.repBaseP
  baseM := D.baseM
  repBaseM := D.repBaseM
  sin_zero_of_rep_im_zero := fun hrep hzim => sinZeroDir D hrep hzim

/-- **`sin π ≃ 0` for the assembled model.**  The full Machin telescoping
(`CircleModel.sinMachinAngle_eqv_zero`) applied to `toModel D`, conditional only
on the `CircleData` residuals. -/
theorem sinPi_eqv_zero (D : CircleData) :
    CReal.Equiv ((toModel D).sinOf (toModel D).piAngle) CReal.czero :=
  ArctanTanInversion.CircleModel.sinMachinAngle_eqv_zero (toModel D)

end YMGap.Continuum.CircleModelAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CircleModelAssembly.ofQ'_ofInt_mul
#print axioms YMGap.Continuum.CircleModelAssembly.mul4_reorder
#print axioms YMGap.Continuum.CircleModelAssembly.cmul_sub
#print axioms YMGap.Continuum.CircleModelAssembly.prodLemma
#print axioms YMGap.Continuum.CircleModelAssembly.realHom
#print axioms YMGap.Continuum.CircleModelAssembly.imagHom
#print axioms YMGap.Continuum.CircleModelAssembly.repDir_add
#print axioms YMGap.Continuum.CircleModelAssembly.sinZeroDir
#print axioms YMGap.Continuum.CircleModelAssembly.toModel
#print axioms YMGap.Continuum.CircleModelAssembly.sinPi_eqv_zero
