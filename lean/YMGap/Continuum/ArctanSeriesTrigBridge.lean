/-
# The arctan-series ↔ trig-series bridge at `1/5` (honest reduction)

This module connects the *in-`x` ODE power series* values
`QDivArctanSeries.sval = sin(arctan(1/5))`, `cval = cos(arctan(1/5))`
(limits of the Taylor-in-`x` series with coefficients `pc`/`qc`) to the *real*
constructive-trig objects `sinC`/`cosC` evaluated along the arctan partial sums
`Pi.at5.approx k = cPart 5 _ k → arctan(1/5)`.

## What is genuinely proved here

* `at5_pos`, `at5_le1` — the range side-conditions `0 ≤ at5.approx k ≤ 1`
  (monotonicity + the global majorant `cPart ≤ H = 1/4 ≤ 1`).  Axiom-clean.
* `sval_eqv_sinCat5`, `cval_eqv_cosCat5` (**Target A**) — the well-posed bridge
  `sval ≃ sinC(arctan(1/5))`, `cval ≃ cosC(arctan(1/5))`, obtained by
  **limit-uniqueness** (`Equiv_of_limit_of_equal`) from the two convergence
  witnesses.  This is the *easy* half and it is genuine (a few lines).
* `tanLink_arctan_fifth_trig` (**Target B**) — the final identity
  `sinC(arctan(1/5)) ≃ (1/5)·cosC(arctan(1/5))`, i.e. `tan(arctan(1/5)) = 1/5`,
  transported from the already-proven `QDivArctanSeries.tanLink_arctan_fifth`
  across Target A.
* `arctanTrigLink_at5`, `tanLink_at5_trig` — the **unification**: Target B *is*
  the named residuals `ArctanTanInversion.ArctanTrigLink` and
  `TanArctan.TanLink` instantiated at the genuine `sinC`/`cosC` objects.

## The two honest inputs (Type-level residuals, never `sorry`)

The bridge is **conditional on two Type-level data**, and both are honest:

1. `ArctanTrigConverges` (the load-bearing transcendental atom) — the cross-series
   convergence
   `ConvergesTo (k ↦ sinNN (at5.approx k)) sval`  ∧  `… cosNN … cval`.
   This asserts the sine-Taylor-*in-the-angle* series evaluated along the arctan
   partial sums has the SAME limit as the sine-*in-`x`* ODE series.  It is exactly
   the composed-Taylor / arctan↔trig link the Mathlib-free layer cannot manufacture
   from the two coefficient recurrences alone; it is the same atom the repo already
   names (`TanArctan`, `ArctanTanInversion.ArctanTrigLink`).

2. `At5Modulus` — a **monotone (antitone) Cauchy modulus** for `at5`, packaged as
   the `(Mw, hMw, hMwmono)` triple `CRealTrig.sinC`/`cosC` require.  NOTE (honest
   correction to the naive plan): the natural modulus `Mw ε := ε.den` is a valid
   Cauchy stage but is **NOT antitone** in `ε` (e.g. `1/2 ≤ 2/3` yet
   `den(1/2)=2 < den(2/3)=3`), so it does not satisfy `hMwmono`.  A genuinely
   antitone modulus for `at5` provably exists (take `Mw ε = ⌈1/ε⌉`; then
   `half^(Mw ε) ≤ invSucc(Mw ε) ≤ ε` and `⌈1/·⌉` is antitone), but its explicit
   construction is a separate `Nat`/`Int` arithmetic obligation — non-transcendental
   glue — carried here as an explicit datum rather than fabricated.  The datum is
   therefore non-vacuous.

Net: the *easy* half (limit-uniqueness) is genuine; the *load-bearing* half is the
already-named transcendental atom `ArctanTrigConverges`, and the only extra surface
is the (elementary, non-transcendental) antitone-modulus datum.
-/

import YMGap.Constructive.QDivArctanSeries
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealAlg
import YMGap.Continuum.ArctanTanInversion

namespace YMGap.Continuum.ArctanSeriesTrigBridge

open YMGap.Constructive

/-! ## 0. Local reflexivity / right-multiplicative congruence for `CReal.Equiv` -/

/-- `CReal.Equiv A A`. -/
theorem equivRefl (A : CReal) : CReal.Equiv A A :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- Right multiplicative congruence: `B ≃ B' ⇒ A·B ≃ A·B'` (commute + left
congruence). -/
theorem cmul_congr_right {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (CRealAlg.cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h) (CRealAlg.cmul_comm B' A))

/-! ## 1. The range side-conditions for `Pi.at5` (proved) -/

/-- `0 ≤ at5.approx k` — the arctan partial sums are nonnegative (monotone from
`cPart 5 _ 0 = 0`). -/
theorem at5_pos : ∀ k, (0 : Q') ≤ Pi.at5.approx k := by
  intro k
  rw [Pi.at5_approx]
  -- `cPart 5 _ 0` is definitionally `0`; monotonicity does the rest.
  exact Pi.cPart_mono 5 (by decide) (Nat.zero_le k)

/-- `at5.approx k ≤ 1` — the global majorant `cPart 5 _ k ≤ H = 1/4 ≤ 1`. -/
theorem at5_le1 : ∀ k, Pi.at5.approx k ≤ (1 : Q') := by
  intro k
  rw [Pi.at5_approx]
  exact Q'.le_trans' _ _ _
    (Pi.cPart_le_H (by decide) (Q'.mkPos 1 4 (by decide)) (by decide) (by decide) k)
    (by decide)

/-! ## 2. The antitone-modulus datum for `at5` (Type-level input; non-vacuous) -/

/-- **A monotone (antitone) Cauchy modulus for `at5`.**  Exactly the
`(Mw, hMw, hMwmono)` triple `CRealTrig.sinC`/`cosC` consume.  Non-vacuous (a valid
antitone modulus exists — see the module header) but carried as an explicit datum
because the natural `ε.den` modulus fails `hMwmono`. -/
structure At5Modulus : Type where
  Mw : Q' → Nat
  hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
          Pi.at5.approx m ≤ Pi.at5.approx n + ε ∧ Pi.at5.approx n ≤ Pi.at5.approx m + ε
  hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ

/-- `sinC(arctan(1/5))` — the genuine constructive sine of the arctan angle. -/
def sinCat5 (d : At5Modulus) : CReal :=
  CRealTrig.sinC Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono

/-- `cosC(arctan(1/5))` — the genuine constructive cosine of the arctan angle. -/
def cosCat5 (d : At5Modulus) : CReal :=
  CRealTrig.cosC Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono

/-! ## 3. The single load-bearing residual: the cross-series convergence -/

/-- **`ArctanTrigConverges` — the composed-Taylor / arctan↔trig atom.**  Asserts
that the sine and cosine *in-the-angle* Taylor series evaluated along the arctan
partial sums `at5.approx k` converge to the sine and cosine *in-x* ODE values
`sval`/`cval`.  This is the genuinely transcendental content (Cauchy-product +
rearrangement) the two coefficient recurrences do not supply. -/
def ArctanTrigConverges : Prop :=
  CReal.ConvergesTo (fun k => Trig.sinNN (Pi.at5.approx k) (at5_pos k))
      QDivArctanSeries.sval
  ∧ CReal.ConvergesTo (fun k => Trig.cosNN (Pi.at5.approx k) (at5_pos k))
      QDivArctanSeries.cval

/-! ## 4. Target A — the well-posed bridge (limit-uniqueness, genuine) -/

/-- **Target A (sine).**  `sval ≃ sinC(arctan(1/5))`.  Both are limits of the SAME
sequence `k ↦ sinNN (at5.approx k)` — `sval` by the residual, `sinCat5` by
`sinC_converges` — so limit-uniqueness identifies them. -/
theorem sval_eqv_sinCat5 (d : At5Modulus) (h : ArctanTrigConverges) :
    CReal.Equiv QDivArctanSeries.sval (sinCat5 d) :=
  CReal.Equiv_of_limit_of_equal
    (fun _ => equivRefl _)
    h.1
    (CRealTrig.sinC_converges Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono)

/-- **Target A (cosine).**  `cval ≃ cosC(arctan(1/5))`. -/
theorem cval_eqv_cosCat5 (d : At5Modulus) (h : ArctanTrigConverges) :
    CReal.Equiv QDivArctanSeries.cval (cosCat5 d) :=
  CReal.Equiv_of_limit_of_equal
    (fun _ => equivRefl _)
    h.2
    (CRealTrig.cosC_converges Pi.at5 d.Mw at5_pos at5_le1 d.hMw d.hMwmono)

/-! ## 5. Target B — the final identity, transported -/

/-- **Target B.**  `sinC(arctan(1/5)) ≃ (1/5)·cosC(arctan(1/5))`, i.e.
`tan(arctan(1/5)) = 1/5` for the genuine constructive-trig objects.

Chain: `sinCat5 ≃ sval` (Target A, reversed) `≃ (1/5)·cval`
(`tanLink_arctan_fifth`) `≃ (1/5)·cosCat5` (right-congruence of Target A). -/
theorem tanLink_arctan_fifth_trig (d : At5Modulus) (h : ArctanTrigConverges) :
    CReal.Equiv (sinCat5 d)
      (CReal.mul (CReal.ofQ' QDivArctanSeries.xv) (cosCat5 d)) := by
  -- the QDiv-level tangent link, read as a genuine `CReal.Equiv` (defeq unfolding
  -- of `TanLink` and the model projections `.cval = cval`, `.sval = sval`).
  have hlink : CReal.Equiv QDivArctanSeries.sval
      (CReal.mul (CReal.ofQ' QDivArctanSeries.xv) QDivArctanSeries.cval) :=
    QDivArctanSeries.tanLink_arctan_fifth
  exact CReal.Equiv.trans (CReal.Equiv.symm (sval_eqv_sinCat5 d h))
    (CReal.Equiv.trans hlink (cmul_congr_right (cval_eqv_cosCat5 d h)))

/-! ## 6. Unification with the already-named residuals -/

/-- **Unification with `ArctanTanInversion.ArctanTrigLink`.**  Target B *is* the
named LINK residual instantiated at the genuine `sinC`/`cosC` objects — so the
repo carries ONE atom (`ArctanTrigConverges`) rather than a lookalike. -/
theorem arctanTrigLink_at5 (d : At5Modulus) (h : ArctanTrigConverges) :
    ArctanTanInversion.ArctanTrigLink QDivArctanSeries.xv (cosCat5 d) (sinCat5 d) :=
  tanLink_arctan_fifth_trig d h

/-- **Unification with `TanArctan.TanLink`.**  Same identity, read through the
`TanArctan` interface. -/
theorem tanLink_at5_trig (d : At5Modulus) (h : ArctanTrigConverges) :
    TanArctan.TanLink QDivArctanSeries.xv (cosCat5 d) (sinCat5 d) :=
  tanLink_arctan_fifth_trig d h

end YMGap.Continuum.ArctanSeriesTrigBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.at5_pos
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.at5_le1
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.sval_eqv_sinCat5
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.cval_eqv_cosCat5
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.tanLink_arctan_fifth_trig
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.arctanTrigLink_at5
#print axioms YMGap.Continuum.ArctanSeriesTrigBridge.tanLink_at5_trig
