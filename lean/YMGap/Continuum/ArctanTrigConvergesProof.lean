/-
# `ArctanTrigConverges`: the circularity theorem and the composition reduction

This module carries out, at the Lean level, the audit verdict on the load-bearing
transcendental atom `ArctanSeriesTrigBridge.ArctanTrigConverges` (the cross-series
convergence saying the sine/cosine *in-the-angle* Taylor series evaluated along the
arctan partial sums `Pi.at5.approx k` have the SAME limits as the in-`x` ODE series
values `QDivArctanSeries.sval`/`cval`).

## What is genuinely proved (no new residual is introduced by these)

* `convergesTo_of_equiv` — the transport lemma: a `CReal`-sequence limit may be
  moved along an `Equiv` of limits (`ConvergesTo s L → Equiv L L' → ConvergesTo s L'`).
  A clean ε/2 chase; fully constructive.

* **`atom_iff_valueIdent` — THE CIRCULARITY THEOREM.**  For every antitone-modulus
  datum `d : At5Modulus`,
  ```
  ArctanTrigConverges  ↔  (Equiv sval (sinCat5 d) ∧ Equiv cval (cosCat5 d)).
  ```
  Forward is the bridge's `sval_eqv_sinCat5`/`cval_eqv_cosCat5` (limit-uniqueness);
  backward transports the already-proved `sinC_converges`/`cosC_converges` (the
  `k`-limit leg the bridge discharges) along the value-identifications via
  `convergesTo_of_equiv`.  This makes precise that the "uniform-continuity route"
  is circular: the atom is *inter-derivable* with the two value-identifications
  `sval ≃ sin(arctan 1/5)`, `cval ≃ cos(arctan 1/5)` — supplying uniform continuity
  supplies only the already-discharged `k`-limit leg and re-poses the atom as the
  identification.

## The sharpest non-circular reduction (honest named Type-level residual)

`ComposedSeriesData d` factors each value-identification through an explicitly
supplied intermediary CReal — the composed-Taylor series limit `limCReal γ`
(`γ` = the Cauchy-product/Bell composition coefficients of `sin`, `arctan`):

* **(A) coefficient identity** — `coeffSin : Equiv sval Csin`, `coeffCos : Equiv cval Ccos`.
  The finite convolution identity `γ_j ≃ pc_j` (matched against `pc_rec`/`qc_rec`
  by two-step induction); non-transcendental, strictly below `DiffJTP` (it never
  differentiates a convergent product).

* **(B) composition tail** — `tailSin : Equiv Csin (sinCat5 d)`, `tailCos : Equiv Ccos (cosCat5 d)`.
  The genuine double-limit interchange (`k`-limit of the angle vs `N`-truncation of
  the composite); the irreducible transcendental residue, achievable constructively
  from the explicit geometric (arctan) and factorial (sine) majorants, still below
  `DiffJTP`.

`atom_of_composed` discharges the atom from such a datum (`Equiv.trans` of (A) and
(B), then `atom_iff_valueIdent`).  Honest note: a *trivial* intermediary `Csin := sval`
makes (A) reflexive and relocates the ENTIRE residue onto (B) — the split is only as
sharp as the intermediary is the genuine `limCReal γ`; taking the trivial one is not
fake closure, it just exposes (B) as the whole transcendental leg.  No `sorry`, no
custom axiom: the residual is carried as Type-level data (`Csin`, `Ccos`) plus Prop
witnesses, never manufactured.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (via reused `Nat`/`Int` helpers).  No
`Classical.*`, no `native_decide`, no `sorry`, no custom axiom.
-/

import YMGap.Continuum.ArctanSeriesTrigBridge
import YMGap.Constructive.CRealTrig
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.QDivArctanSeries

namespace YMGap.Continuum.ArctanTrigConvergesProof

open YMGap.Constructive
open YMGap.Continuum.ArctanSeriesTrigBridge

/-! ## 0. A rational two-step chain with a doubled tolerance -/

/-- `u ≤ v + q`, `v ≤ w + q`, and `(q + q) ≃ ε`  ⟹  `u ≤ w + ε`. -/
private theorem chain2gen {q ε : Q'} (htwo : (q + q).eqv ε) {u v w : Q'}
    (huv : u ≤ v + q) (hvw : v ≤ w + q) : u ≤ w + ε := by
  have s1 : u ≤ (w + q) + q := Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
  refine Q'.le_trans' _ _ _ s1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w q q)) ?_
  exact Q'.le_of_eqv (Q'.add_eqv_congr_left w _ _ htwo)

/-! ## 1. Transport of a `CReal`-limit along an `Equiv` of limits -/

/-- **`convergesTo_of_equiv`.**  If `s` converges to `L` and `L ≃ L'`, then `s`
converges to `L'`.  Standard ε/2 chase: `s_N ≤ L + q ≤ (L' + q) + q ≤ L' + ε` and
symmetrically, at `q = ½ε`. -/
theorem convergesTo_of_equiv {s : Nat → CReal} {L L' : CReal}
    (hconv : CReal.ConvergesTo s L) (hLL' : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  have htwo : (HalfPow.half * ε + HalfPow.half * ε).eqv ε := ExpNeg.two_halves ε
  obtain ⟨Nstage, hst⟩ := hconv (HalfPow.half * ε) hq
  obtain ⟨Ne, hNe⟩ := hLL' (HalfPow.half * ε) hq
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx, hcl⟩ := hst N hN
  refine ⟨max Napx Ne, fun n hn => ?_⟩
  have hnA : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnE : Ne ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hc1, hc2⟩ := hcl n hnA   -- s_N ≤ L + q ; L ≤ s_N + q
  obtain ⟨he1, he2⟩ := hNe n hnE   -- L ≤ L' + q ; L' ≤ L + q
  refine ⟨?_, ?_⟩
  · -- s_N ≤ L' + ε : s_N ≤ L + q, L ≤ L' + q
    exact chain2gen htwo hc1 he1
  · -- L' ≤ s_N + ε : L' ≤ L + q, L ≤ s_N + q
    exact chain2gen htwo he2 hc2

/-! ## 2. The circularity theorem -/

/-- **Backward leg (the already-discharged `k`-limit, transported).**  Given the two
value-identifications, the atom follows by transporting `sinC_converges` /
`cosC_converges` along them.  This is exactly the "uniform continuity supplies only
the proved leg" observation, made formal. -/
theorem valueIdent_to_atom (d : At5Modulus)
    (hs : CReal.Equiv QDivArctanSeries.sval (sinCat5 d))
    (hc : CReal.Equiv QDivArctanSeries.cval (cosCat5 d)) :
    ArctanTrigConverges := by
  refine ⟨?_, ?_⟩
  · exact convergesTo_of_equiv
      (CRealTrig.sinC_converges Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono)
      (CReal.Equiv.symm hs)
  · exact convergesTo_of_equiv
      (CRealTrig.cosC_converges Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono)
      (CReal.Equiv.symm hc)

/-- **THE CIRCULARITY THEOREM.**  For every antitone-modulus datum `d`, the atom is
inter-derivable with the two value-identifications `sval ≃ sinC(arctan 1/5)`,
`cval ≃ cosC(arctan 1/5)`.  Forward = limit-uniqueness (the bridge's Target A),
backward = transport of the proved `k`-limit leg.  So the "uniform-continuity route"
closes only the already-proved leg and re-poses the atom as the identification. -/
theorem atom_iff_valueIdent (d : At5Modulus) :
    ArctanTrigConverges ↔
      (CReal.Equiv QDivArctanSeries.sval (sinCat5 d)
       ∧ CReal.Equiv QDivArctanSeries.cval (cosCat5 d)) :=
  ⟨fun h => ⟨sval_eqv_sinCat5 d h, cval_eqv_cosCat5 d h⟩,
   fun h => valueIdent_to_atom d h.1 h.2⟩

/-! ## 3. The composition reduction (honest named Type-level residual) -/

/-- **`ComposedSeriesData d` — the sharpest non-circular reduction, as Type-level
data.**  Supplies the composed-Taylor series limits `Csin`, `Ccos` (`= limCReal γ`)
and factors each value-identification through them:

* `coeffSin`/`coeffCos` = **(A)** the finite Cauchy-product coefficient identity
  `γ_j ≃ pc_j` (non-transcendental, below `DiffJTP`), lifted to `Equiv sval Csin`;
* `tailSin`/`tailCos` = **(B)** the composition tail / double-limit interchange
  `Equiv Csin (sinCat5 d)` (the irreducible transcendental residue, below `DiffJTP`).

Type-level (an MLTT witness), never a `Prop`-∃: the residual reals `Csin`, `Ccos`
are carried as data, not asserted to exist. -/
structure ComposedSeriesData (d : At5Modulus) : Type where
  /-- The composed sine-Taylor series limit `limCReal γ`. -/
  Csin : CReal
  /-- The composed cosine-Taylor series limit. -/
  Ccos : CReal
  /-- (A) coefficient identity, sine leg: `sval ≃ Csin`. -/
  coeffSin : CReal.Equiv QDivArctanSeries.sval Csin
  /-- (A) coefficient identity, cosine leg: `cval ≃ Ccos`. -/
  coeffCos : CReal.Equiv QDivArctanSeries.cval Ccos
  /-- (B) composition tail, sine leg: `Csin ≃ sinC(arctan 1/5)`. -/
  tailSin : CReal.Equiv Csin (sinCat5 d)
  /-- (B) composition tail, cosine leg: `Ccos ≃ cosC(arctan 1/5)`. -/
  tailCos : CReal.Equiv Ccos (cosCat5 d)

/-- From a `ComposedSeriesData` the two value-identifications follow by `Equiv.trans`
of the (A) and (B) legs. -/
theorem valueIdent_of_composed (d : At5Modulus) (c : ComposedSeriesData d) :
    CReal.Equiv QDivArctanSeries.sval (sinCat5 d)
    ∧ CReal.Equiv QDivArctanSeries.cval (cosCat5 d) :=
  ⟨CReal.Equiv.trans c.coeffSin c.tailSin,
   CReal.Equiv.trans c.coeffCos c.tailCos⟩

/-- **The atom is discharged by the composition reduction.**  `(A) + (B)` through the
composed-series midpoint gives the value-identifications, and `atom_iff_valueIdent`
(backward) closes the atom. -/
theorem atom_of_composed (d : At5Modulus) (c : ComposedSeriesData d) :
    ArctanTrigConverges :=
  valueIdent_to_atom d (valueIdent_of_composed d c).1 (valueIdent_of_composed d c).2

end YMGap.Continuum.ArctanTrigConvergesProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanTrigConvergesProof.convergesTo_of_equiv
#print axioms YMGap.Continuum.ArctanTrigConvergesProof.valueIdent_to_atom
#print axioms YMGap.Continuum.ArctanTrigConvergesProof.atom_iff_valueIdent
#print axioms YMGap.Continuum.ArctanTrigConvergesProof.valueIdent_of_composed
#print axioms YMGap.Continuum.ArctanTrigConvergesProof.atom_of_composed
