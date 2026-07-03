/-
# `ArctanTangentLink`: concentrating the arctan↔trig atom onto the single cosine
#  composition leg `compCos`

This module implements the sharp concentration verdict of the "Track 3-tanlink"
analysis: **the cosine composition leg `compCos` alone suffices for the whole
arctan↔trig atom** — the sine leg `compSin` is redundant, recovered for free
through the ODE-side tangent link.

## The chain, precisely

The two ends were already connected in the repo:

* the **series-level** link `sval ≃ (1/5)·cval` (`tanLink_arctan_fifth`) lives in
  x-space (ODE coefficients);
* the **value-level** link `sinCat5 ≃ (1/5)·cosCat5` (`ArctanTrigLink`) lives in
  angle-space (`lim_k sinNN θ_k`).

The middle bridge — the transcendental Cauchy-product rearrangement identifying
`lim_M cos_M(arctan 1/5)` with `Σ_j qc_j (1/5)^j` — is exactly the single
`ConvergesTo` residual

    compCos : ConvergesTo (fun M => colLimCos M) cval.

Given `compCos`, everything downstream closes here with proved algebra:

1. **`cosValue`** (proved) — `compCos` plus the already-PROVED Moore–Osgood leg
   `MooreOsgoodB2.interCos` give, by limit uniqueness (`Equiv_of_limit_of_equal`,
   both are limits of the SAME sequence `M ↦ colLimCos M`),
       `cval ≃ cosCat5 d`.
2. **`tangentLink`** (proved, modulo one positive-sqrt-cancel datum) — from
   `cval ≃ cosCat5`, the trig Pythagorean `P1`, and the ODE self-convolution
   Pythagorean `P3 = (1+x²)cval² ≃ 1`, a below-`DiffJTP` algebra computation gives
   the SQUARE link `sinCat5² ≃ (x·cosCat5)²` (additive cancellation of `cosCat5²`
   after `(1+x²)cosCat5² ≃ 1`); the datum `P5' = SqrtCancelPos` then yields the
   value LINK `sinCat5 ≃ x·cosCat5`.
3. **`valueIdentityResidual`** (proved) — the value link feeds the PROVED
   `ArctanCompositionIdentity.sineLeg_of_cosineLeg`, which recovers
   `sval ≃ sinCat5` FOR FREE by chaining the series link; together with the
   `cosValue` cosine leg this is a full `ValueIdentityResidual`.
4. **`atom`** (proved) — closes through `atom_of_valueIdentity`.

## Honest depth verdict

This is a **concentration, not a discharge.**  The transcendence is not removed —
it is compressed from the two composition legs (`compSin ∧ compCos`) down to the
SINGLE object `compCos = ConvergesTo (fun M => colLimCos M) cval`, plus three
strictly-cheaper below-`DiffJTP` residuals (`P1` trig-Pythagorean, `P3` ODE
self-convolution Pythagorean, `P5'` the positive-square-root order datum).  The
irreducible frontier is the single even-series Cauchy-product convergence
`compCos`.  It remains open (carried as `Type`-level `ConvergesTo` data, never
`sorry`, never a custom axiom).

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  The residual package is `Type`-level data (Rule 8),
never a `Prop`-∃.
-/

import YMGap.Continuum.MooreOsgoodB2
import YMGap.Continuum.ArctanCompositionIdentity

namespace YMGap.Continuum.ArctanTangentLink

open YMGap.Constructive
open YMGap.Constructive.QDivArctanSeries (sval cval xv)
open YMGap.Continuum.ArctanSeriesTrigBridge (sinCat5 cosCat5 At5Modulus ArctanTrigConverges)
open YMGap.Continuum.ArctanValueIdentity (ValueIdentityResidual atom_of_valueIdentity)
open YMGap.Continuum.ArctanCompositionTail (colLimCos)
open YMGap.Continuum.ArctanCompositionIdentity (SqrtCancelPos sineLeg_of_cosineLeg)

/-! ## 0. `CReal.Equiv` congruence glue (re-derived from repo primitives) -/

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

/-! ## 1. The additive-cancellation toolkit (pointwise + `add_congr`) -/

/-- `A + 0 ≃ A` at the CReal level (pointwise). -/
private theorem cAddZero (A : CReal) : CReal.Equiv (CReal.add A CReal.czero) A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n))

/-- `C + (−C) ≃ 0` at the CReal level (pointwise). -/
private theorem cAddNegSelf (C : CReal) :
    CReal.Equiv (CReal.add C (CReal.neg C)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (C.approx n))

/-- `(A + B) + C ≃ A + (B + C)` at the CReal level (pointwise). -/
private theorem cAddAssoc (A B C : CReal) :
    CReal.Equiv (CReal.add (CReal.add A B) C) (CReal.add A (CReal.add B C)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n))

/-- **Additive right cancellation** at the CReal level.
`A + C ≃ B + C ⟹ A ≃ B`.  Add `−C` on the right and collapse with associativity,
`C + (−C) ≃ 0`, and `· + 0 ≃ ·`. -/
private theorem addRightCancel {A B C : CReal}
    (h : CReal.Equiv (CReal.add A C) (CReal.add B C)) : CReal.Equiv A B :=
  CReal.Equiv.trans (CReal.Equiv.symm (cAddZero A))
    (CReal.Equiv.trans (CReal.add_congr_right (CReal.Equiv.symm (cAddNegSelf C)))
      (CReal.Equiv.trans (CReal.Equiv.symm (cAddAssoc A C (CReal.neg C)))
        (CReal.Equiv.trans (CReal.add_congr_left h)
          (CReal.Equiv.trans (cAddAssoc B C (CReal.neg C))
            (CReal.Equiv.trans (CReal.add_congr_right (cAddNegSelf C)) (cAddZero B))))))

/-! ## 2. Pointwise-`Q'` algebra atoms (below `DiffJTP`, no limits) -/

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

/-! ## 3. The single residual package -/

/-- **The `Track 3-tanlink` residual package.**  Carries the SINGLE sharp
composition leg `compCos` together with the three strictly-cheaper
below-`DiffJTP` order/Pythagorean residuals (`P1`, `P3`, `P5'`). -/
structure TangentLinkInputs (d : At5Modulus) : Type where
  /-- **The sharp residual `compCos`.**  The even-series Cauchy-product / Faà-di-Bruno
  rearrangement: `lim_M cos_M(arctan 1/5) = Σ_j qc_j (1/5)^j`, i.e.
  `ConvergesTo (fun M => colLimCos M) cval`. -/
  compCos : CReal.ConvergesTo (fun M => colLimCos M) cval
  /-- **P1.**  The trig Pythagorean `sinC² + cosC² ≃ 1`. -/
  pythTrig : CReal.Equiv
      (CReal.add (CReal.mul (sinCat5 d) (sinCat5 d)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      CReal.cone
  /-- **P3.**  The ODE self-convolution Pythagorean `(1+x²)·cval² ≃ 1`. -/
  sqOdeCos : CReal.Equiv
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul cval cval)) CReal.cone
  /-- **P5'.**  Positive-square-root cancellation for `sinC` and `x·cosC` — the one
  order primitive used to pass from the square link to the value link. -/
  sqrtLink : SqrtCancelPos (sinCat5 d) (CReal.mul (CReal.ofQ' xv) (cosCat5 d))

/-! ## 4. Step 1 — `compCos` + the PROVED Moore–Osgood leg ⟹ `cval ≃ cosCat5` -/

/-- **The cosine value identity, from `compCos` alone.**  `compCos` and the already
PROVED `MooreOsgoodB2.interCos` are two convergences of the SAME sequence
`M ↦ colLimCos M`; limit uniqueness gives `cval ≃ cosCat5 d`.  (This is exactly the
`cosineLeg` branch — it never touches `compSin`.) -/
theorem cosValue (d : At5Modulus) (I : TangentLinkInputs d) :
    CReal.Equiv cval (cosCat5 d) :=
  CReal.Equiv_of_limit_of_equal (fun _ => equivRefl _) I.compCos (MooreOsgoodB2.interCos d)

/-! ## 5. Step 2 — the value tangent LINK, from `cval ≃ cosCat5` + {P1, P3, P5'} -/

/-- **The value tangent LINK, from `compCos` + the cheap package.**
`ArctanTrigLink xv (cosCat5 d) (sinCat5 d)`, i.e. `sinCat5 ≃ (1/5)·cosCat5`.

Route: with `cval ≃ cosCat5` (Step 1), P3 becomes `(1+x²)·cosCat5² ≃ 1`; factoring
`(1+x²)·cosCat5² ≃ x²·cosCat5² + cosCat5²` and comparing with P1
`sinCat5² + cosCat5² ≃ 1` and cancelling `cosCat5²` gives the SQUARE link
`sinCat5² ≃ x²·cosCat5² ≃ (x·cosCat5)²`; the datum P5' extracts the value link. -/
theorem tangentLink (d : At5Modulus) (I : TangentLinkInputs d) :
    ArctanTanInversion.ArctanTrigLink xv (cosCat5 d) (sinCat5 d) := by
  have hcos : CReal.Equiv cval (cosCat5 d) := cosValue d I
  -- (i) cval² ≃ cosCat5²
  have hv2c2 : CReal.Equiv (CReal.mul cval cval)
      (CReal.mul (cosCat5 d) (cosCat5 d)) := mulCongr hcos hcos
  -- (ii) (x²+1)·cosCat5² ≃ 1  (rewrite P3 through cval² ≃ cosCat5²)
  have hc2big : CReal.Equiv
      (CReal.mul (CReal.ofQ' (xv * xv + 1)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      CReal.cone :=
    CReal.Equiv.trans (mulCongrRight (CReal.Equiv.symm hv2c2)) I.sqOdeCos
  -- (iii) x²·cosCat5² + cosCat5² ≃ 1  (unfactor)
  have hfac : CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d)))
                 (CReal.mul (cosCat5 d) (cosCat5 d)))
      CReal.cone :=
    CReal.Equiv.trans (factor_add (xv * xv) (CReal.mul (cosCat5 d) (cosCat5 d))) hc2big
  -- (iv) sinCat5² + cosCat5² ≃ x²·cosCat5² + cosCat5²  (both ≃ 1)
  have hsum : CReal.Equiv
      (CReal.add (CReal.mul (sinCat5 d) (sinCat5 d)) (CReal.mul (cosCat5 d) (cosCat5 d)))
      (CReal.add (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d)))
                 (CReal.mul (cosCat5 d) (cosCat5 d))) :=
    CReal.Equiv.trans I.pythTrig (CReal.Equiv.symm hfac)
  -- (v) cancel cosCat5²: sinCat5² ≃ x²·cosCat5²
  have hs2 : CReal.Equiv (CReal.mul (sinCat5 d) (sinCat5 d))
      (CReal.mul (CReal.ofQ' (xv * xv)) (CReal.mul (cosCat5 d) (cosCat5 d))) :=
    addRightCancel hsum
  -- (vi) x²·cosCat5² ≃ (x·cosCat5)²: the SQUARE link
  have hs2sq : CReal.Equiv (CReal.mul (sinCat5 d) (sinCat5 d))
      (CReal.mul (CReal.mul (CReal.ofQ' xv) (cosCat5 d))
                 (CReal.mul (CReal.ofQ' xv) (cosCat5 d))) :=
    CReal.Equiv.trans hs2 (CReal.Equiv.symm (sq_mul_ofQ xv (cosCat5 d)))
  -- (vii) positive-sqrt cancel (P5'): sinCat5 ≃ x·cosCat5 — the value LINK
  exact I.sqrtLink.cancel hs2sq

/-! ## 6. Steps 3–4 — the full value identity and the atom -/

/-- **The value identity, from `compCos` + the cheap package.**
The cosine leg is `cosValue`; the sine leg is FREE via
`ArctanCompositionIdentity.sineLeg_of_cosineLeg` fed the value link. -/
def valueIdentityResidual (d : At5Modulus) (I : TangentLinkInputs d) :
    ValueIdentityResidual d where
  sineLeg := sineLeg_of_cosineLeg d (tangentLink d I) (cosValue d I)
  cosineLeg := cosValue d I

/-- **The arctan↔trig atom, discharged from `compCos` alone (plus the cheap
package).**  This realises the concentration verdict: the single cosine
composition leg suffices for the whole atom, `compSin` never appearing. -/
theorem atom (d : At5Modulus) (I : TangentLinkInputs d) : ArctanTrigConverges :=
  atom_of_valueIdentity d (valueIdentityResidual d I)

end YMGap.Continuum.ArctanTangentLink

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanTangentLink.addRightCancel
#print axioms YMGap.Continuum.ArctanTangentLink.sq_mul_ofQ
#print axioms YMGap.Continuum.ArctanTangentLink.factor_add
#print axioms YMGap.Continuum.ArctanTangentLink.cosValue
#print axioms YMGap.Continuum.ArctanTangentLink.tangentLink
#print axioms YMGap.Continuum.ArctanTangentLink.valueIdentityResidual
#print axioms YMGap.Continuum.ArctanTangentLink.atom
