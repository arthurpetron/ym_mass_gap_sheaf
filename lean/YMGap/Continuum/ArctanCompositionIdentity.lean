/-
# `ArctanCompositionIdentity`: the "Route A" structural dedup of the arctan↔trig atom

This module implements the sharp *structural* reduction of the arctan↔trig
value-identity `ValueIdentityResidual` (the pair `sval ≃ sinC(arctan 1/5)`,
`cval ≃ cosC(arctan 1/5)`) to the **single tangent LINK**
`sinC(arctan 1/5) ≃ (1/5)·cosC(arctan 1/5)`, i.e. the already-named
`ArctanTanInversion.ArctanTrigLink` at the genuine constructive-trig objects.

## What is genuinely done here (and what is NOT)

The direct `sin∘arctan` composition Cauchy product / Faà-di-Bruno double-array
grind is **bypassed entirely**.  Instead we observe the following asymmetry:

* the **ODE-side** tangent relation `sval ≃ (1/5)·cval` is **free** — it is the
  already-proved `QDivArctanSeries.tanLink_arctan_fifth` (pure `odeShift`
  coefficient content);
* the **trig-side** tangent relation `sinC ≃ (1/5)·cosC` (`link` below) is the
  genuine transcendental atom — carried here as an INPUT.

Given the trig-side link, the entire value identity collapses to a below-`DiffJTP`
algebraic package (`LinkReductionInputs`), and we discharge that package to
`ValueIdentityResidual` — hence to the atom `ArctanTrigConverges` — with three
genuinely-proved pieces plus one honest Type-level order residual:

* `sineLeg_of_cosineLeg` — **proved**: given the cosine value identity
  `cval ≃ cosC`, the sine value identity `sval ≃ sinC` is FREE (chain the free
  ODE-side tangent link `tanLink_arctan_fifth` with the trig-side `link`).  This
  is the real content of "Route A": the sine leg costs nothing beyond the link.
* `cosineLeg_of_inputs` — **proved (algebra) modulo one order residual**: from
  the trig Pythagorean `P1`, the link `P2`, and the ODE self-convolution
  Pythagorean `P3` (`(1+x²)·cval² ≃ 1`), a pure pointwise-`Q'` computation yields
  the **square identity** `cosC² ≃ cval²` (the whole `(1+x²)`-cancellation is a
  positive-rational cancellation, `cancelQPos`).  The passage `cosC² ≃ cval² ⟹
  cosC ≃ cval` is the CReal positive-square-root cancellation, carried as the
  Type-level `SqrtCancelPos` datum (the one order primitive not manufactured
  here).

## Honest depth verdict (unchanged)

This is a **structural dedup, NOT a transcendence discharge.**  `link` (P2) is the
tangent LINK at the genuine `sinC`/`cosC`; since the repo already proves the
forward `atom ⟹ link` (`ArctanSeriesTrigBridge.arctanTrigLink_at5`) and this
module supplies the converse `link + (below-DiffJTP) ⟹ atom`, the link is
**equi-transcendental** with the atom, not weaker.  The genuine value is: (a) the
`colLimSin` double-array / Moore–Osgood composition machinery is removed from the
critical path; (b) the two separately-named residuals `CompositionIdentity`
(B1) and `ArctanTrigLink` collapse into ONE atom; (c) the sine leg is proved
free of the link.  The irreducible atom (`link`) remains open.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  All witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.ArctanValueIdentity
import YMGap.Continuum.ArctanSeriesTrigBridge
import YMGap.Continuum.ArctanTanInversion
import YMGap.Constructive.QDivArctanSeries
import YMGap.Constructive.CRealExp
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.ArctanCompositionIdentity

open YMGap.Constructive
open YMGap.Constructive.QDivArctanSeries (sval cval xv tanLink_arctan_fifth)
open YMGap.Continuum.ArctanSeriesTrigBridge (sinCat5 cosCat5 At5Modulus ArctanTrigConverges)
open YMGap.Continuum.ArctanValueIdentity (ValueIdentityResidual atom_of_valueIdentity)

/-! ## 0. `CReal.Equiv` congruence glue (from the repo primitives) -/

/-- Reflexivity of `CReal.Equiv` (pointwise). -/
private theorem equivRefl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- Right multiplicative congruence: `B ≃ B' ⟹ A·B ≃ A·B'`. -/
private theorem mulCongrRight {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (CRealAlg.cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h) (CRealAlg.cmul_comm B' A))

/-- Two-sided multiplicative congruence: `A ≃ A'`, `B ≃ B' ⟹ A·B ≃ A'·B'`. -/
private theorem mulCongr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') :=
  CReal.Equiv.trans (CReal.mul_congr_left hA) (mulCongrRight hB)

/-! ## 1. Pointwise-`Q'` algebra atoms (all below `DiffJTP`: no limits) -/

/-- `Q'` four-factor commuting rearrangement: `(a·b)·(c·e) ≃ (a·c)·(b·e)`. -/
private theorem q_mul_mul_mul_comm (a b c e : Q') :
    ((a * b) * (c * e)).eqv ((a * c) * (b * e)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * e))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a (b * (c * e)) ((b * c) * e)
        (Q'.eqv_symm (Q'.mul_assoc_eqv b c e)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a ((b * c) * e) ((c * b) * e)
          (Q'.mul_eqv_congr_right (b * c) (c * b) e (Q'.mul_comm_eqv b c)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left a ((c * b) * e) (c * (b * e)) (Q'.mul_assoc_eqv c b e))
          (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * e))))))

/-- **`(x·c)² ≃ x²·c²`** at the CReal level, for a rational scalar `x` (pointwise). -/
private theorem sq_mul_ofQ (x : Q') (c : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' x) c) (CReal.mul (CReal.ofQ' x) c))
      (CReal.mul (CReal.ofQ' (x * x)) (CReal.mul c c)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_mul_mul_mul_comm x (c.approx n) x (c.approx n))

/-- **Factoring** `k·W + W ≃ (k+1)·W` for a rational scalar `k` (pointwise). -/
private theorem factor_add (k : Q') (W : CReal) :
    CReal.Equiv (CReal.add (CReal.mul (CReal.ofQ' k) W) W)
      (CReal.mul (CReal.ofQ' (k + 1)) W) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show ((k * W.approx n) + W.approx n).eqv ((k + 1) * W.approx n)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (k + 1) (W.approx n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (W.approx n) k 1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (W.approx n * k) (W.approx n * 1) (W.approx n)
        (Q'.mul_one_eqv (W.approx n))) ?_
    exact Q'.add_eqv_congr_right (W.approx n * k) (k * W.approx n) (W.approx n)
      (Q'.mul_comm_eqv (W.approx n) k))

/-- `a ≃ (1/k)·(k·a)` for `k > 0` (pointwise reciprocal collapse). -/
private theorem q_recip_left (k : Q') (hk : (0 : Q') < k) (a : Q') :
    a.eqv (Q'.recipPos k hk * (k * a)) :=
  Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recipPos k hk) k a))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.recipPos k hk * k) (k * Q'.recipPos k hk) a
          (Q'.mul_comm_eqv (Q'.recipPos k hk) k))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (k * Q'.recipPos k hk) 1 a (Q'.mul_recipPos_eqv k hk))
          (Q'.one_mul_eqv a))))

/-- **Positive-rational left cancellation** at the CReal level.
`k > 0` and `k·A ≃ k·B` ⟹ `A ≃ B`.  Multiply by the constant `1/k`. -/
private theorem cancelQPos {k : Q'} (hk : (0 : Q') < k) {A B : CReal}
    (h : CReal.Equiv (CReal.mul (CReal.ofQ' k) A) (CReal.mul (CReal.ofQ' k) B)) :
    CReal.Equiv A B := by
  have hA : CReal.Equiv A
      (CReal.mul (CReal.ofQ' (Q'.recipPos k hk)) (CReal.mul (CReal.ofQ' k) A)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => q_recip_left k hk (A.approx n))
  have hB : CReal.Equiv
      (CReal.mul (CReal.ofQ' (Q'.recipPos k hk)) (CReal.mul (CReal.ofQ' k) B)) B :=
    SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_symm (q_recip_left k hk (B.approx n)))
  exact CReal.Equiv.trans hA (CReal.Equiv.trans (mulCongrRight h) hB)

/-! ## 2. The CReal positive-square-root cancellation, as an honest datum -/

/-- **CReal positive-square-root cancellation** (the one order primitive not
manufactured here).  For `u, v` strictly positive, `u² ≃ v² ⟹ u ≃ v`.  This is
constructive and strictly below `DiffJTP` — factor `u²−v² = (u−v)(u+v)` and cancel
the positive `u+v` — but it needs concrete CReal-order primitives, so it is carried
as `Type`-level data (never `sorry`, never a custom axiom). -/
structure SqrtCancelPos (u v : CReal) : Type where
  /-- `u` is CReal-strictly-positive. -/
  posu : CReal.IsPositive u
  /-- `v` is CReal-strictly-positive. -/
  posv : CReal.IsPositive v
  /-- The positive-square-root cancellation itself. -/
  cancel : CReal.Equiv (CReal.mul u u) (CReal.mul v v) → CReal.Equiv u v

/-! ## 3. The "Route A" input package -/

/-- **The below-`DiffJTP` input package for Route A.**  Carries the transcendental
atom `link` (P2) together with the three below-`DiffJTP` facts P1, P3, P5. -/
structure LinkReductionInputs (d : At5Modulus) : Type where
  /-- **P2, the atom.**  The trig-side tangent LINK
  `sinC(arctan 1/5) ≃ (1/5)·cosC(arctan 1/5)` (= `ArctanTrigLink` at the genuine
  objects). -/
  link : ArctanTanInversion.ArctanTrigLink xv (cosCat5 d) (sinCat5 d)
  /-- **P1.**  The trig Pythagorean at the α-angle: `sinC² + cosC² ≃ 1`. -/
  pythTrig : CReal.Equiv
      (CReal.add (CReal.mul (sinCat5 d) (sinCat5 d)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      CReal.cone
  /-- **P3 (cosine).**  The ODE self-convolution Pythagorean `(1+x²)·cval² ≃ 1`,
  written with `1+x² = x·x + 1` as a rational scalar. -/
  sqOdeCos : CReal.Equiv
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul cval cval)) CReal.cone
  /-- **P5.**  Positive-square-root cancellation for `cosC` and `cval`. -/
  sqrtCancel : SqrtCancelPos (cosCat5 d) cval

/-! ## 4. The sine leg is FREE given the cosine leg (the real Route-A content) -/

/-- **`sineLeg_of_cosineLeg` — proved.**  Given the cosine value identity
`cval ≃ cosC` and the trig-side tangent link, the sine value identity
`sval ≃ sinC` is free: chain the free ODE-side link `sval ≃ (1/5)·cval`
(`tanLink_arctan_fifth`) with `(1/5)·cval ≃ (1/5)·cosC` (right-congruence) and the
trig link reversed `(1/5)·cosC ≃ sinC`. -/
theorem sineLeg_of_cosineLeg (d : At5Modulus)
    (link : ArctanTanInversion.ArctanTrigLink xv (cosCat5 d) (sinCat5 d))
    (hcos : CReal.Equiv cval (cosCat5 d)) :
    CReal.Equiv sval (sinCat5 d) := by
  have hP4 : CReal.Equiv sval (CReal.mul (CReal.ofQ' xv) cval) :=
    tanLink_arctan_fifth
  have hlink : CReal.Equiv (sinCat5 d) (CReal.mul (CReal.ofQ' xv) (cosCat5 d)) := link
  exact CReal.Equiv.trans hP4
    (CReal.Equiv.trans (mulCongrRight hcos) (CReal.Equiv.symm hlink))

/-! ## 5. The cosine leg, reduced to the square identity + positive-sqrt cancel -/

/-- **`cosineLeg_of_inputs` — proved (modulo the `SqrtCancelPos` datum).**
From P1 + P2 + P3 a pure pointwise-`Q'` computation gives the square identity
`cosC² ≃ cval²` (the `(1+x²)` is cancelled by `cancelQPos`); the datum P5 then
supplies `cosC ≃ cval`. -/
theorem cosineLeg_of_inputs (d : At5Modulus) (I : LinkReductionInputs d) :
    CReal.Equiv cval (cosCat5 d) := by
  have hlink : CReal.Equiv (sinCat5 d) (CReal.mul (CReal.ofQ' xv) (cosCat5 d)) := I.link
  -- (i) sinC² ≃ x²·cosC²
  have h_ss : CReal.Equiv (CReal.mul (sinCat5 d) (sinCat5 d))
      (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d))) :=
    CReal.Equiv.trans (mulCongr hlink hlink) (sq_mul_ofQ xv (cosCat5 d))
  -- (ii) sinC² + cosC² ≃ x²·cosC² + cosC²
  have h_sum : CReal.Equiv
      (CReal.add (CReal.mul (sinCat5 d) (sinCat5 d)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      (CReal.add (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d)))
                 (CReal.mul (cosCat5 d) (cosCat5 d))) :=
    CReal.add_congr_left h_ss
  -- (iii) x²·cosC² + cosC² ≃ (x²+1)·cosC²
  have h_fac : CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d)))
                 (CReal.mul (cosCat5 d) (cosCat5 d)))
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul (cosCat5 d) (cosCat5 d))) :=
    factor_add (xv * xv) (CReal.mul (cosCat5 d) (cosCat5 d))
  -- (iv) with P1: (x²+1)·cosC² ≃ 1
  have hcos_sq : CReal.Equiv
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      CReal.cone :=
    CReal.Equiv.trans (CReal.Equiv.symm (CReal.Equiv.trans h_sum h_fac)) I.pythTrig
  -- (v) with P3: (x²+1)·cosC² ≃ (x²+1)·cval²
  have hk1 : (0 : Q') < xv * xv + 1 := by decide
  have hsame : CReal.Equiv
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul cval cval)) :=
    CReal.Equiv.trans hcos_sq (CReal.Equiv.symm I.sqOdeCos)
  -- (vi) cancel (x²+1): cosC² ≃ cval²
  have hsqid : CReal.Equiv (CReal.mul (cosCat5 d) (cosCat5 d)) (CReal.mul cval cval) :=
    cancelQPos hk1 hsame
  -- (vii) positive-sqrt cancel: cosC ≃ cval, hence cval ≃ cosC
  exact CReal.Equiv.symm (I.sqrtCancel.cancel hsqid)

/-! ## 6. The assembled reduction: `LinkReductionInputs ⟹ ValueIdentityResidual ⟹ atom` -/

/-- **Route A assembled.**  The full value identity from the input package. -/
def valueIdentityResidual_of_link (d : At5Modulus) (I : LinkReductionInputs d) :
    ValueIdentityResidual d where
  sineLeg := sineLeg_of_cosineLeg d I.link (cosineLeg_of_inputs d I)
  cosineLeg := cosineLeg_of_inputs d I

/-- **The atom, discharged from the tangent LINK + below-`DiffJTP` package.**  This
merges `CompositionIdentity` (B1) and `ArctanTrigLink` into the single atom
`ArctanTrigConverges`, with the `colLimSin` double-array eliminated. -/
theorem atom_of_link (d : At5Modulus) (I : LinkReductionInputs d) :
    ArctanTrigConverges :=
  atom_of_valueIdentity d (valueIdentityResidual_of_link d I)

end YMGap.Continuum.ArctanCompositionIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanCompositionIdentity.q_mul_mul_mul_comm
#print axioms YMGap.Continuum.ArctanCompositionIdentity.sq_mul_ofQ
#print axioms YMGap.Continuum.ArctanCompositionIdentity.factor_add
#print axioms YMGap.Continuum.ArctanCompositionIdentity.cancelQPos
#print axioms YMGap.Continuum.ArctanCompositionIdentity.sineLeg_of_cosineLeg
#print axioms YMGap.Continuum.ArctanCompositionIdentity.cosineLeg_of_inputs
#print axioms YMGap.Continuum.ArctanCompositionIdentity.valueIdentityResidual_of_link
#print axioms YMGap.Continuum.ArctanCompositionIdentity.atom_of_link
