/-
# The value-level bridge `VAL` for the arctan↔trig link, discharged

This module closes the **`VAL`** field of `TanArctanModel`
(`YMGap.Continuum.TanArctan`) — the convergence/tail bridge that lifts the formal
coefficient identity `p_{n+1} ≃ qₙ` (`P = x·Q`, proved green by `odeShift`) to the
genuine `CReal` values.  The single sharp cut is:

    `valBridge_target` = `Equiv_of_limit_of_equal` ∘ `shiftMulX`,

gated only by two mechanical convergence sub-lemmas:

  * **V1** `convergesTo_shift` — index-shift invariance of `ConvergesTo`
    (a one-off reindex), used to pass `Σ_{n<N+1} pₙ xⁿ` (the sine partial sum,
    shifted by one) to the limit `sval`;
  * **V2** = `CReal.convergesTo_mul` fed with the CONSTANT factor `ofQ' x`
    (`convergesTo_const`), the scalar-multiple continuity.

`shiftMulX` (green in `TanArctan`) supplies the exact termwise equality
`Σ_{n<N+1} pₙ xⁿ ≃ x·Σ_{n<N} qₙ xⁿ`; lifting it to `CReal` uses `ofQ'`
congruence (`SumOfSquares.Equiv_of_approx_eqv`) and the `ofQ'` multiplicative
homomorphism (`CRealAlg.ofQ'_mul`).  There is **no transcendental content** here.

## What this collapses

Given a `SeriesData x` (the honest `Type`-level carrier of the REC coefficient
recurrences + the two power-series convergence witnesses + a uniform approximation
bound on the cosine value), `tanArctanModel_of_data` produces a genuine
`TanArctanModel x` whose `valBridge` field is `valBridge_target` — no longer an
open field.  Composing with the green `tanArctan_of_model` yields the tangent link
`sin(arctan x) ≃ x·cos(arctan x)` unconditionally *modulo the `SeriesData`*.

The `SeriesData` carrier is proven **non-vacuous** (`seriesData_zero`): the
degenerate all-zero coefficient sequence satisfies every REC recurrence and both
convergence witnesses, so the reduction is real (a satisfiable obligation, not a
disguised falsehood).

## The single named residual

The ONLY thing not discharged here is the construction of a `SeriesData` for the
*actual* arctan coefficients `pc/qc` (the artanh-style geometric-majorant series
build + the solved recurrence `p_{n+2} = (q_{n+1} − n·pₙ)/(n+2)`, `q_{n+2} =
(−p_{n+1} − n·qₙ)/(n+2)`).  That build needs `Q'` division (absent in the current
rational layer) and is left as the honest residual `SeriesData` — a `Type`-level
obligation, never a `sorry`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  `SeriesData` is `Type`-level data (Rule 8).
-/

import YMGap.Continuum.TanArctan
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.SeriesComposition

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TanArctan

/-! ## 1. The two mechanical convergence sub-lemmas (V1, V2-helper) -/

/-- **V1 — index-shift invariance of `ConvergesTo`.**  If `s → L`, then the
shifted sequence `N ↦ s (N+1)` also `→ L`: the convergence stage is reused
verbatim (`N ≥ Nstage ⟹ N+1 ≥ Nstage`).  This is the one-off reindex that lets
the sine partial sum of length `N+1` be passed to its own limit. -/
theorem convergesTo_shift {s : Nat → CReal} {L : CReal} (h : ConvergesTo s L) :
    ConvergesTo (fun N => s (N + 1)) L := by
  intro ε hε
  obtain ⟨Nstage, hst⟩ := h ε hε
  exact ⟨Nstage, fun N hN => hst (N + 1) (Nat.le_trans hN (Nat.le_succ N))⟩

/-- **The constant sequence converges to its value.**  `ConvergesTo (fun _ => c)
c` — the scalar factor `ofQ' x` in the V2 mul-continuity step is constant. -/
theorem convergesTo_const (c : CReal) : ConvergesTo (fun _ => c) c := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun n _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg (c.approx n) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg (c.approx n) ε (Q'.le_of_lt hε)

/-! ## 2. `valBridge_target` — the sharp cut (VAL, fully proved) -/

/-- **The value-level bridge, discharged.**  From the two power-series
convergence witnesses (`hsval`, `hcval`), the formal coefficient identity
`p_{n+1} ≃ qₙ` (`hshift`) with `p₀ ≃ 0` (`h0`), and a uniform approximation bound
`B` on the cosine value and on `x`, the CReal values satisfy
`sval ≃ x·cval` — i.e. `sin(arctan x) ≃ x·cos(arctan x)` at the value level.

Proof = `Equiv_of_limit_of_equal` fed by:
  * termwise equality `ofQ'(Σ_{n<N+1} pₙxⁿ) ≃ (ofQ' x)·ofQ'(Σ_{n<N} qₙxⁿ)`
    (`shiftMulX` + `ofQ'` congruence + `ofQ'_mul`),
  * `convergesTo_shift hsval` (V1) on the sine side,
  * `convergesTo_mul` with the constant factor `ofQ' x` (V2) on the cosine side.
No transcendental input. -/
theorem valBridge_target
    (p q : Nat → Q') (x : Q') (sval cval : CReal) (B : Q') (hB : (0 : Q') ≤ B)
    (hxB : Q'.abs x ≤ B) (hcB : ∀ n, Q'.abs (cval.approx n) ≤ B)
    (hsval : ConvergesTo (fun N => ofQ' (series p x N)) sval)
    (hcval : ConvergesTo (fun N => ofQ' (series q x N)) cval)
    (hshift : ∀ n, (p (n + 1)).eqv (q n)) (h0 : (p 0).eqv 0) :
    CReal.Equiv sval (CReal.mul (CReal.ofQ' x) cval) := by
  -- Step 1: the green partial-sum shift identity.
  have hshiftmul : ∀ N, (series p x (N + 1)).eqv (x * series q x N) :=
    shiftMulX p q x hshift h0
  -- Step 2: lift termwise to CReal equality.
  have hterm : ∀ N,
      CReal.Equiv (ofQ' (series p x (N + 1)))
        (CReal.mul (ofQ' x) (ofQ' (series q x N))) := by
    intro N
    refine CReal.Equiv.trans ?_ (CRealAlg.ofQ'_mul x (series q x N))
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => hshiftmul N)
  -- Step 3 (V1): the shifted sine partial sums converge to sval.
  have hA : ConvergesTo (fun N => ofQ' (series p x (N + 1))) sval :=
    convergesTo_shift hsval
  -- Step 4 (V2): the scaled cosine partial sums converge to (ofQ' x)·cval.
  have hBseq : ConvergesTo
      (fun N => CReal.mul (ofQ' x) (ofQ' (series q x N)))
      (CReal.mul (ofQ' x) cval) :=
    CReal.convergesTo_mul hB (fun _ _ => hxB) hcB (convergesTo_const (ofQ' x)) hcval
  -- Step 5: uniqueness of limits.
  exact Equiv_of_limit_of_equal hterm hA hBseq

/-! ## 3. The honest `Type`-level carrier and the model constructor -/

/-- **`SeriesData x`** — the `Type`-level data that upgrades `TanArctanModel`'s two
open fields (`REC` = the coefficient recurrences, `VAL` = the convergence bridge)
to proved statements.  A concrete arctan model supplies:

  * `p`, `q`               — the formal power-series coefficients;
  * `cval`, `sval`         — the actual `CReal` cosine/sine values;
  * `B`, `hB`, `hxB`, `hcB`— a uniform approximation bound (`|x| ≤ B`, and every
                             cosine approximation `|cval.approx n| ≤ B`), the only
                             analytic input `convergesTo_mul` needs;
  * `hsval`, `hcval`       — the two power-series convergence witnesses;
  * `hp0`/`hp`/`hq0`/`hq`/`hp0init` — (REC) the ODE coefficient recurrences.

Given a `SeriesData`, `valBridge_target` discharges `VAL` outright. -/
structure SeriesData (x : Q') where
  p : Nat → Q'
  q : Nat → Q'
  cval : CReal
  sval : CReal
  B : Q'
  hB : (0 : Q') ≤ B
  hxB : Q'.abs x ≤ B
  hcB : ∀ n, Q'.abs (cval.approx n) ≤ B
  hsval : ConvergesTo (fun N => ofQ' (series p x N)) sval
  hcval : ConvergesTo (fun N => ofQ' (series q x N)) cval
  hp0 : (p 1).eqv (q 0)
  hp : ∀ n, (Q'.ofNat (n + 2) * p (n + 2) + Q'.ofNat n * p n).eqv (q (n + 1))
  hq0 : (q 1).eqv (-(p 0))
  hq : ∀ n, (Q'.ofNat (n + 2) * q (n + 2) + Q'.ofNat n * q n).eqv (-(p (n + 1)))
  hp0init : (p 0).eqv 0

/-- **The model constructor.**  A `SeriesData x` yields a genuine
`TanArctanModel x` whose `valBridge` field is `valBridge_target` — the entire
`VAL` obligation is now a proved lemma, not an open field.  `REC` is carried
verbatim from the `SeriesData`. -/
def tanArctanModel_of_data {x : Q'} (d : SeriesData x) : TanArctanModel x where
  p := d.p
  q := d.q
  cval := d.cval
  sval := d.sval
  hp0 := d.hp0
  hp := d.hp
  hq0 := d.hq0
  hq := d.hq
  hp0init := d.hp0init
  valBridge := fun hshift =>
    valBridge_target d.p d.q x d.sval d.cval d.B d.hB d.hxB d.hcB
      d.hsval d.hcval hshift d.hp0init

/-- **The tangent link from series data.**  `sin(arctan x) ≃ x·cos(arctan x)`,
unconditional modulo the `SeriesData` (which packages `REC` + convergence).  The
algebraic middle `p_{n+1} ≃ qₙ` is `odeShift`; the tail bridge is
`valBridge_target`. -/
theorem tanLink_of_data {x : Q'} (d : SeriesData x) :
    TanLink x (tanArctanModel_of_data d).cval (tanArctanModel_of_data d).sval :=
  tanArctan_of_model (tanArctanModel_of_data d)

/-! ## 4. Non-vacuity: the degenerate all-zero series data -/

/-- The all-zero coefficient series is literally `0` at every truncation, up to
`Q'`-`eqv`. -/
theorem series_zero_eqv (x : Q') : ∀ N, (series (fun _ => (0 : Q')) x N).eqv 0
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
    show (series (fun _ => (0 : Q')) x N + (0 : Q') * qpow x N).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (series_zero_eqv x N) (Q'.zero_mul_eqv (qpow x N))) ?_
    decide

/-- The `ofQ'`-lift of the all-zero partial sums converges to `czero`. -/
theorem convergesTo_series_zero (x : Q') :
    ConvergesTo (fun N => ofQ' (series (fun _ => (0 : Q')) x N)) CReal.czero := by
  intro ε hε
  refine ⟨0, fun N _ => ⟨0, fun n _ => ⟨?_, ?_⟩⟩⟩
  · -- series 0 x N ≤ czero.approx n + ε = 0 + ε
    show series (fun _ => (0 : Q')) x N ≤ (0 : Q') + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (series_zero_eqv x N))
      (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
  · -- czero.approx n = 0 ≤ series 0 x N + ε
    show (0 : Q') ≤ series (fun _ => (0 : Q')) x N + ε
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
      (Q'.add_le_add_right 0 (series (fun _ => (0 : Q')) x N) ε
        (Q'.ge_of_eqv (series_zero_eqv x N)))

/-- **`SeriesData` is non-vacuous.**  The all-zero coefficient sequence satisfies
every REC recurrence (`0 ≃ 0`) and both convergence witnesses (to `czero`), with
bound `B = |x|`.  So the carrier `SeriesData` is a satisfiable obligation. -/
def seriesData_zero (x : Q') : SeriesData x where
  p := fun _ => 0
  q := fun _ => 0
  cval := CReal.czero
  sval := CReal.czero
  B := Q'.abs x
  hB := Q'.abs_nonneg x
  hxB := Q'.le_refl' (Q'.abs x)
  hcB := fun _ => by
    show Q'.abs (0 : Q') ≤ Q'.abs x
    have h0 : Q'.abs (0 : Q') = 0 := by decide
    rw [h0]; exact Q'.abs_nonneg x
  hsval := convergesTo_series_zero x
  hcval := convergesTo_series_zero x
  hp0 := Q'.eqv_refl 0
  hp := fun n => by
    show (Q'.ofNat (n + 2) * 0 + Q'.ofNat n * 0).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv (Q'.ofNat (n + 2)))
        (Q'.mul_zero_eqv (Q'.ofNat n))) ?_
    decide
  hq0 := by
    show (0 : Q').eqv (-(0 : Q'))
    decide
  hq := fun n => by
    show (Q'.ofNat (n + 2) * 0 + Q'.ofNat n * 0).eqv (-(0 : Q'))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv (Q'.ofNat (n + 2)))
        (Q'.mul_zero_eqv (Q'.ofNat n))) ?_
    decide
  hp0init := Q'.eqv_refl 0

/-- The degenerate tangent link, exhibited concretely: `0 ≃ x·0`. -/
theorem tanLink_zero (x : Q') :
    TanLink x (tanArctanModel_of_data (seriesData_zero x)).cval
      (tanArctanModel_of_data (seriesData_zero x)).sval :=
  tanLink_of_data (seriesData_zero x)

end YMGap.Continuum.SeriesComposition

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SeriesComposition.convergesTo_shift
#print axioms YMGap.Continuum.SeriesComposition.convergesTo_const
#print axioms YMGap.Continuum.SeriesComposition.valBridge_target
#print axioms YMGap.Continuum.SeriesComposition.tanArctanModel_of_data
#print axioms YMGap.Continuum.SeriesComposition.tanLink_of_data
#print axioms YMGap.Continuum.SeriesComposition.series_zero_eqv
#print axioms YMGap.Continuum.SeriesComposition.convergesTo_series_zero
#print axioms YMGap.Continuum.SeriesComposition.seriesData_zero
#print axioms YMGap.Continuum.SeriesComposition.tanLink_zero
