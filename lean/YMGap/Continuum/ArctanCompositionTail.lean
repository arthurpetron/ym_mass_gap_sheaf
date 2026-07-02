/-
# `ArctanCompositionTail`: the Moore–Osgood factoring of the arctan↔trig tail

This module sharpens the split of the load-bearing arctan↔trig atom
`ArctanSeriesTrigBridge.ArctanTrigConverges`.  Recall (from `ArctanValueIdentity`)
that closing the atom is inter-derivable with the value-identities
`sval ≃ sinC(arctan 1/5)`, `cval ≃ cosC(arctan 1/5)`, and that the residue lives
entirely in the *composition tail* `Equiv (limCReal γ) (sinCat5 d)`.

## The double array and the column limits (genuine, built here)

Write `θ_k := Pi.at5.approx k` for the `k`-th arctan(1/5) partial sum
(`0 ≤ θ_k ≤ 1`, `θ_k → arctan(1/5)`), and consider the rational double array

    a(k, M) := Trig.sinPartial θ_k M = Σ_{i<M} (−1)^i · θ_k^{2i+1} / (2i+1)!.

* **Row limit** (`M → ∞`, `k` fixed): `ofQ'(a k ·) → sinNN θ_k`, and
  `lim_k sinNN θ_k = sinCat5 d` — the leg already proved by `sinC_converges`.
* **Column limit** (`k → ∞`, `M` fixed): `a(·, M)` is a fixed degree-`(2M−1)`
  polynomial, Cauchy in `k` because `θ_k` is Cauchy with trig Lipschitz constant
  `sinSumBound M ≤ 3` (`CRealTrig.sinPartialDiff_le`).  This module **builds** the
  resulting `CReal` `colLimSin M = lim_k a(k, M)` (and its cosine twin), a genuine
  new object.

## The one nontrivial Moore–Osgood hypothesis (proved here)

`sinRowTail` / `cosRowTail` — the **uniform row tail**: for `M ≥ trigModulus 1 ε`
and EVERY `k`,

    |sinPartial θ_k (M+d) − sinPartial θ_k M| ≤ sinBlockAbs θ_k M d ≤ ε,

uniformly in `k`.  The uniformity is exactly the base-monotonicity
`sinBlockAbs θ_k M d ≤ sinBlockAbs 1 M d` (`sinBlockAbs_base_mono`, from
`ExpNeg.termAbs_base_mono`), which lets the `x = 1` block bound dominate every
`x = θ_k ≤ 1`.  This is the single genuinely-nontrivial Moore–Osgood hypothesis;
it is discharged in full.

## The honest three-way factoring of the tail

The atom's transcendental content factors, through the diagonal iterated limit
`Ssin := lim_M colLimSin M`, as two `ConvergesTo` legs of the SAME sequence
`M ↦ colLimSin M`:

* **(B2) angle-continuity / Moore–Osgood** — `ConvergesTo colLimSin (sinCat5 d)`:
  the iterated limit equals the genuine constructive `sinC` of the arctan angle.
  Provable from the uniform row tail above plus the diagonal-index bookkeeping of
  the `completeLimitCauchy` backbone; carried here as the Type-level residual
  `MooreOsgoodInterchange` (its sole nontrivial hypothesis, `sinRowTail`, is
  proved).
* **(B1) composition identity** — `ConvergesTo colLimSin QDivArctanSeries.sval`:
  the iterated limit equals the in-`x` ODE-series value `sval = Σ_j pc_j (1/5)^j`.
  This is the diagonal Cauchy-product rearrangement into `x`-powers — the true
  transcendental core, DiffJTP-adjacent.  Carried as the Type-level residual
  `CompositionIdentity`.

Both legs are limits of the *same* sequence `M ↦ colLimSin M`, so by limit
uniqueness (`Equiv_of_limit_of_equal`, `hterm = refl`) together they give the
value-identities `sval ≃ sinCat5 d`, `cval ≃ cosCat5 d`, hence the atom
(`atom_of_legs`).  This makes precise (constructively) that (B2) is the *easy
half* (Moore–Osgood, one nontrivial hypothesis proved) and (B1) is the *whole
transcendental budget* of the arctan↔trig bridge — they carry the same content
that `ArctanValueIdentity.ValueIdentityResidual` lumps into one `Equiv`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  Column limits are genuine `CReal` data; the residual
legs are `Type`-level `ConvergesTo` witnesses, never `Prop`-∃ manufactured.
-/

import YMGap.Continuum.ArctanValueIdentity
import YMGap.Constructive.CRealTrig
import YMGap.Constructive.QDivArctanSeries

namespace YMGap.Continuum.ArctanCompositionTail

open YMGap.Constructive
open YMGap.Continuum.ArctanSeriesTrigBridge
open YMGap.Continuum.ArctanValueIdentity

/-! ## 1. Base-monotonicity of the trig block magnitudes

`sinBlockAbs x k d` / `cosBlockAbs x k d` are sums of `ExpNeg.termAbs` at odd /
even indices; `ExpNeg.termAbs` is monotone in the sub-unit base, so the whole
block sum is dominated by its value at `x = 1`. -/

/-- **Sine block base-monotonicity.**  `sinBlockAbs x k d ≤ sinBlockAbs 1 k d`
for `0 ≤ x ≤ 1`. -/
theorem sinBlockAbs_base_mono {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    ∀ d, Trig.sinBlockAbs x k d ≤ Trig.sinBlockAbs 1 k d
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    simp only [Trig.sinBlockAbs_succ]
    exact ExpNeg.add_le_add2 (sinBlockAbs_base_mono hx0 hx1 k d)
      (ExpNeg.termAbs_base_mono hx0 hx1 (2 * (k + d) + 1))

/-- **Cosine block base-monotonicity.**  `cosBlockAbs x k d ≤ cosBlockAbs 1 k d`
for `0 ≤ x ≤ 1`. -/
theorem cosBlockAbs_base_mono {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    ∀ d, Trig.cosBlockAbs x k d ≤ Trig.cosBlockAbs 1 k d
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    simp only [Trig.cosBlockAbs_succ]
    exact ExpNeg.add_le_add2 (cosBlockAbs_base_mono hx0 hx1 k d)
      (ExpNeg.termAbs_base_mono hx0 hx1 (2 * (k + d)))

/-! ## 2. The uniform row tail (the nontrivial Moore–Osgood hypothesis) -/

/-- **Uniform row tail, sine.**  For `M ≥ trigModulus 1 ε` and EVERY `k`, the
`M`-truncated sine-in-angle partial sums are two-sided `ε`-close past `M`,
uniformly in the angle `θ_k = at5.approx k`.  Uniformity comes from
`sinBlockAbs_base_mono` dominating every `θ_k ≤ 1` block by the `x = 1` block,
whose tail is `≤ ε` by `Trig.sinBlock_bound`. -/
theorem sinRowTail (ε : Q') (hε : (0 : Q') < ε) (M : Nat)
    (hM : Trig.trigModulus 1 ε ≤ M) (k d : Nat) :
    Trig.sinPartial (Pi.at5.approx k) (M + d) ≤ Trig.sinPartial (Pi.at5.approx k) M + ε
    ∧ Trig.sinPartial (Pi.at5.approx k) M ≤ Trig.sinPartial (Pi.at5.approx k) (M + d) + ε := by
  have htail : Trig.sinBlockAbs (Pi.at5.approx k) M d ≤ ε :=
    Q'.le_trans' _ _ _ (sinBlockAbs_base_mono (at5_pos k) (at5_le1 k) M d)
      (Trig.sinBlock_bound 1 (by decide) ε hε M hM d)
  exact ⟨Q'.le_trans' _ _ _ (Trig.sin_block_upper (Pi.at5.approx k) (at5_pos k) M d)
           (Q'.add_le_add_left _ _ _ htail),
         Q'.le_trans' _ _ _ (Trig.sin_block_lower (Pi.at5.approx k) (at5_pos k) M d)
           (Q'.add_le_add_left _ _ _ htail)⟩

/-- **Uniform row tail, cosine.** -/
theorem cosRowTail (ε : Q') (hε : (0 : Q') < ε) (M : Nat)
    (hM : Trig.trigModulus 1 ε ≤ M) (k d : Nat) :
    Trig.cosPartial (Pi.at5.approx k) (M + d) ≤ Trig.cosPartial (Pi.at5.approx k) M + ε
    ∧ Trig.cosPartial (Pi.at5.approx k) M ≤ Trig.cosPartial (Pi.at5.approx k) (M + d) + ε := by
  have htail : Trig.cosBlockAbs (Pi.at5.approx k) M d ≤ ε :=
    Q'.le_trans' _ _ _ (cosBlockAbs_base_mono (at5_pos k) (at5_le1 k) M d)
      (Trig.cosBlock_bound 1 (by decide) ε hε M hM d)
  exact ⟨Q'.le_trans' _ _ _ (Trig.cos_block_upper (Pi.at5.approx k) (at5_pos k) M d)
           (Q'.add_le_add_left _ _ _ htail),
         Q'.le_trans' _ _ _ (Trig.cos_block_lower (Pi.at5.approx k) (at5_pos k) M d)
           (Q'.add_le_add_left _ _ _ htail)⟩

/-! ## 3. The column limits `colLimSin M = lim_k sinPartial θ_k M` (genuine `CReal`)

For a fixed truncation `M`, the sequence `k ↦ sinPartial θ_k M` is Cauchy in `k`:
the trig partial-sum Lipschitz bound `sinPartialDiff_le` (constant
`sinSumBound M ≤ 3`) turns the Cauchyness of `θ_k = at5.approx k` into Cauchyness
of the polynomial values.  Mirrors the `CRealTrig.sinCMC` bound, with the roles of
the angle-index `k` and the truncation-index swapped. -/

/-- **The sine column limit** `colLimSin M := lim_k sinPartial θ_k M`. -/
def colLimSin (M : Nat) : CReal where
  approx := fun k => Trig.sinPartial (Pi.at5.approx k) M
  cauchy := by
    intro ε hε
    have hd : (0 : Q') ≤ ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (ExpNeg.third_pos hε)
    obtain ⟨N, hN⟩ := Pi.at5.cauchy (ε * Q'.mkPos 1 3 (by decide)) (ExpNeg.third_pos hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨hab, hba⟩ := hN m n hm hn
    have habs : Q'.abs (Trig.sinPartial (Pi.at5.approx m) M
        + -(Trig.sinPartial (Pi.at5.approx n) M)) ≤ ε :=
      Q'.le_trans' _ _ _
        (CRealTrig.sinPartialDiff_le (at5_pos m) (at5_le1 m) (at5_pos n) (at5_le1 n) hd hab hba M)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (CRealTrig.sinSumBound_le_three M) hd)
          (Q'.le_of_eqv (ExpNeg.third_mul_three ε)))
    exact ⟨ExpNeg.le_add_of_abs_sub_le habs,
      ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm (Trig.sinPartial (Pi.at5.approx n) M)
          (Trig.sinPartial (Pi.at5.approx m) M))) habs)⟩

/-- **The cosine column limit** `colLimCos M := lim_k cosPartial θ_k M`. -/
def colLimCos (M : Nat) : CReal where
  approx := fun k => Trig.cosPartial (Pi.at5.approx k) M
  cauchy := by
    intro ε hε
    have hd : (0 : Q') ≤ ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (ExpNeg.third_pos hε)
    obtain ⟨N, hN⟩ := Pi.at5.cauchy (ε * Q'.mkPos 1 3 (by decide)) (ExpNeg.third_pos hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨hab, hba⟩ := hN m n hm hn
    have habs : Q'.abs (Trig.cosPartial (Pi.at5.approx m) M
        + -(Trig.cosPartial (Pi.at5.approx n) M)) ≤ ε :=
      Q'.le_trans' _ _ _
        (CRealTrig.cosPartialDiff_le (at5_pos m) (at5_le1 m) (at5_pos n) (at5_le1 n) hd hab hba M)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (CRealTrig.cosSumBound_le_three M) hd)
          (Q'.le_of_eqv (ExpNeg.third_mul_three ε)))
    exact ⟨ExpNeg.le_add_of_abs_sub_le habs,
      ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm (Trig.cosPartial (Pi.at5.approx n) M)
          (Trig.cosPartial (Pi.at5.approx m) M))) habs)⟩

@[simp] theorem colLimSin_approx (M k : Nat) :
    (colLimSin M).approx k = Trig.sinPartial (Pi.at5.approx k) M := rfl
@[simp] theorem colLimCos_approx (M k : Nat) :
    (colLimCos M).approx k = Trig.cosPartial (Pi.at5.approx k) M := rfl

/-! ## 4. The two residual legs (Type-level), and the atom by limit uniqueness -/

/-- **(B2) The Moore–Osgood interchange (angle-continuity leg).**  The iterated
limit `lim_M colLimSin M` equals the genuine constructive `sinC`/`cosC` of the
arctan angle.  Its sole nontrivial hypothesis, the uniform row tail
`sinRowTail`/`cosRowTail`, is PROVED above; what remains is the diagonal-index
bookkeeping of the `completeLimitCauchy` backbone.  Carried as `Type`-level data
(two `ConvergesTo` witnesses of the SAME sequence `M ↦ colLim· M`). -/
structure MooreOsgoodInterchange (d : At5Modulus) : Type where
  /-- `ConvergesTo (fun M => colLimSin M) (sinCat5 d)`. -/
  interSin : CReal.ConvergesTo (fun M => colLimSin M) (sinCat5 d)
  /-- `ConvergesTo (fun M => colLimCos M) (cosCat5 d)`. -/
  interCos : CReal.ConvergesTo (fun M => colLimCos M) (cosCat5 d)

/-- **(B1) The composition identity (the transcendental core).**  The SAME
iterated limit `lim_M colLimSin M` equals the in-`x` ODE-series value
`sval = Σ_j pc_j (1/5)^j` (resp. `cval`).  This is the diagonal Cauchy-product
rearrangement into `x`-powers — the true remaining transcendental content.
Carried as `Type`-level data. -/
structure CompositionIdentity : Type where
  /-- `ConvergesTo (fun M => colLimSin M) sval`. -/
  compSin : CReal.ConvergesTo (fun M => colLimSin M) QDivArctanSeries.sval
  /-- `ConvergesTo (fun M => colLimCos M) cval`. -/
  compCos : CReal.ConvergesTo (fun M => colLimCos M) QDivArctanSeries.cval

/-- **The value-identity residual from the two legs, by limit uniqueness.**  Both
legs are limits of the SAME sequence `M ↦ colLim· M`; `Equiv_of_limit_of_equal`
with the reflexive termwise hypothesis identifies the two limits `sval ≃ sinCat5 d`
and `cval ≃ cosCat5 d`. -/
def valueIdentityResidual_of (d : At5Modulus)
    (b1 : CompositionIdentity) (b2 : MooreOsgoodInterchange d) :
    ValueIdentityResidual d where
  sineLeg := CReal.Equiv_of_limit_of_equal
    (fun _ => equivRefl _) b1.compSin b2.interSin
  cosineLeg := CReal.Equiv_of_limit_of_equal
    (fun _ => equivRefl _) b1.compCos b2.interCos

/-- **The atom, discharged from the composition identity + the Moore–Osgood
interchange.**  Assembles the value-identity residual and closes through
`ArctanValueIdentity.atom_of_valueIdentity`. -/
theorem atom_of_legs (d : At5Modulus)
    (b1 : CompositionIdentity) (b2 : MooreOsgoodInterchange d) :
    ArctanTrigConverges :=
  atom_of_valueIdentity d (valueIdentityResidual_of d b1 b2)

/-! ## 5. Bridging to the existing `CompositionTail` packaging

The two legs also produce a `CompositionTail` around the trivial intermediary
`Csin := sval` (leg (A) reflexive), showing this factoring carries the same
content as the existing tail residual. -/

/-- The Moore–Osgood interchange alone gives the value-identity residual once the
composition identity supplies the `sval`/`cval` legs — recorded as the two
`Equiv`s in the `sinCat5`/`cosCat5` direction. -/
theorem sineLeg_of_legs (d : At5Modulus)
    (b1 : CompositionIdentity) (b2 : MooreOsgoodInterchange d) :
    CReal.Equiv QDivArctanSeries.sval (sinCat5 d) :=
  (valueIdentityResidual_of d b1 b2).sineLeg

/-- Cosine companion of `sineLeg_of_legs`. -/
theorem cosineLeg_of_legs (d : At5Modulus)
    (b1 : CompositionIdentity) (b2 : MooreOsgoodInterchange d) :
    CReal.Equiv QDivArctanSeries.cval (cosCat5 d) :=
  (valueIdentityResidual_of d b1 b2).cosineLeg

end YMGap.Continuum.ArctanCompositionTail

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanCompositionTail.sinBlockAbs_base_mono
#print axioms YMGap.Continuum.ArctanCompositionTail.cosBlockAbs_base_mono
#print axioms YMGap.Continuum.ArctanCompositionTail.sinRowTail
#print axioms YMGap.Continuum.ArctanCompositionTail.cosRowTail
#print axioms YMGap.Continuum.ArctanCompositionTail.colLimSin
#print axioms YMGap.Continuum.ArctanCompositionTail.colLimCos
#print axioms YMGap.Continuum.ArctanCompositionTail.valueIdentityResidual_of
#print axioms YMGap.Continuum.ArctanCompositionTail.atom_of_legs
#print axioms YMGap.Continuum.ArctanCompositionTail.sineLeg_of_legs
#print axioms YMGap.Continuum.ArctanCompositionTail.cosineLeg_of_legs
