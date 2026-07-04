/-
Track 11.7-fusion / R2 — **the RE-BASED bulk eigenvalue-shift carrier: correcting the
reference rate of the discrete SU(2) fusion local-CLT residual for `p ≥ 2`.**

# The bug this module fixes (read first)

`FusionKernelStatement.SaddleLocalCLT.bulkShiftBound` measures the `p`-fold fusion
eigenvalue against the **bare `p = 1` heat rate** `eigA w s = w^{C₄(s)}`:

    bulkShiftBound : ∀ s, fusionEig N w p s (h0' s) − eigA w s ≤ 1/12.

This reference is correct ONLY at `p = 1` (where `fusionEig = eigA` and the shift is
identically `0`).  For `p ≥ 2` the `p`-fold kernel decays at the AGGREGATE, vacuum-
renormalized rate `≈ w_eff^{C₄(s)}` with `w_eff = exp(−A_p)`, NOT at the bare `w`; a
sum of `p` Casimirs has curvature `2p`, so the naive shift against the bare rate is
`≈ p`, blowing past `1/12` for every weight (the pilot's `literal_shift`, Table 2, is
`>1/12` on the whole grid at `p ≥ 2`).  The saddle `estimate` field of `SaddleLogForm`
is ALREADY re-based (it uses `A·C₂(s)`, i.e. `log(w_eff^{C₂(s)})`); only the Q'-level
`bulkShiftBound` hard-codes the wrong reference.

# What this module does

It supplies the CORRECTED Q'-level carrier `RebasedLocalCLT`, whose load-bearing field
measures the shift against the RE-BASED rate

    rateP w_eff s = eigA w_eff s = w_eff^{C₄(s)}          (`w_eff : Q'`, pure data)

so that

    rebasedBulkShift : ∀ s, fusionEig N w p s (h0' s) − rateP w_eff s ≤ 1/12

is the EXACT SAME Q' shape as the original field (no `CReal` plumbing — the genuine
`exp` fact `w_eff ≈ exp(−A_p)` is confined to the named-open bridge, below).

  * At `p = 1` (`w_eff := w`) `rateP w s = eigA w s` DEFINITIONALLY, so re-basing is a
    definitional identity and the corrected carrier is INHABITED from the existing
    `saddleLocalCLT_p1` (`rebasedLocalCLT_p1`).  This is the anchor.
  * For `p ≥ 2`, re-basing is a genuine weakening.  The conversion of the (already
    re-based) `CReal` saddle `estimate` into the Q' `rebasedBulkShift` is the single
    irreducible analytic core (one `CReal.exp`-Lipschitz step); it is named as the
    residual `ExpShiftBridge` and is NAMED-OPEN — NOT inhabited, NOT faked (Rule 5).

The pilot re-confirms satisfiability for `p ≥ 2`: `rebased_shift ≤ 0.0121` on the whole
grid vs the `1/12 = 0.0833` budget (Table 3), worst saddle modulus `eta = 0.00246` at
`(w = 1/2, p = 2)` (33.9× margin), with `eta_p` worst at `p = 2` and strictly
decreasing in `p`.  Structurally `p = 2` is extremal-yet-tight (the single
autoconvolution `acN w (s+1) s`, Casimir `Δ²C₄ = 2` pinning `d2x ≤ 1`); for `p ≥ 3`
the curvature `2p` is exactly what the `w_eff = exp(−A_p)` vacuum re-normalization
absorbs, restoring the `≤ 1/12` bound.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` re-basing over the already-green `FusionKernelStatement` interface plus
the `p = 1` definitional recovery.  Every load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`, no custom `axiom`.  All witnesses are `Type`-level data;
the open core `ExpShiftBridge` (for `p ≥ 2`) is a named UNINHABITED interface.
-/

import YMGap.Continuum.FusionKernelStatement

namespace YMGap.Continuum.RebasedBulkShift

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement

/-! ## 1. The re-based rate `rateP` (rational vacuum re-normalization; pure `Q'`)

`rateP w_eff s = eigA w_eff s = w_eff^{C₄(s)}` — the `p`-fold aggregate heat rate with
the effective weight `w_eff : Q'` (a rational under-approximant of `exp(−A_p)`; the
`exp` step is confined to the named-open bridge).  Keeping `w_eff : Q'` keeps the
corrected shift bound the SAME `Q'` shape as the original `bulkShiftBound` — no `CReal`
subtraction, so the wiring re-attaches with zero `CReal` plumbing. -/
def rateP (weff : Q') (s : Nat) : Q' := eigA weff s

/-- **`p = 1` recovery (definitional).**  With `w_eff := w` the re-based rate IS the bare
heat rate: `rateP w s = eigA w s`.  So at `p = 1` re-basing changes nothing. -/
theorem rateP_one_eq_eigA (w : Q') (s : Nat) : rateP w s = eigA w s := rfl

/-- `rateP` is `≥ 0` for `0 ≤ w_eff` (heat-rate nonnegativity, inherited from `eigA`). -/
theorem rateP_nonneg {weff : Q'} (h : (0 : Q') ≤ weff) (s : Nat) :
    (0 : Q') ≤ rateP weff s :=
  eigA_nonneg h s

/-- `rateP` is `≤ 1` for `0 ≤ w_eff ≤ 1` (the re-based rate never exceeds the vacuum). -/
theorem rateP_le_one {weff : Q'} (h0 : (0 : Q') ≤ weff) (h1 : weff ≤ (1 : Q'))
    (s : Nat) : rateP weff s ≤ (1 : Q') :=
  eigA_le_one h0 h1 s

/-! ## 2. The corrected load-bearing carrier `RebasedLocalCLT`

Same fields as `FusionKernelStatement.SaddleLocalCLT` — `A`, `eta` (saddle moduli,
data) — plus the effective weight `w_eff : Q'` (data), and the CORRECTED shift bound
`rebasedBulkShift` referenced against `rateP w_eff` instead of the bare `eigA w`. -/

/-- **`RebasedLocalCLT` — the re-based Q'-level wiring carrier.**  Carries the saddle
moduli `A`, `eta` and the effective weight `w_eff` (all data), and THE LOAD-BEARING
FIELD `rebasedBulkShift`: the vacuum-normalized `p`-fold eigenvalue-shift, measured
against the RE-BASED aggregate rate `rateP w_eff s = w_eff^{C₄(s)}`, is below the
localization margin `1/12` for every mode.  `p = 1` inhabited (`rebasedLocalCLT_p1`,
`w_eff := w`); `p ≥ 2` produced only via the named-open `ExpShiftBridge`. -/
structure RebasedLocalCLT (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- `A_p(w)` — leading exponent (data; `A = −log w_eff`). -/
  A : Q'
  /-- `eta_p(w)` — curvature / remainder modulus (data). -/
  eta : Q'
  /-- `w_eff` — effective `p`-fold weight (data; `≈ exp(−A_p)`). -/
  weff : Q'
  /-- **THE LOAD-BEARING FIELD** — the RE-BASED eigenvalue-shift stays below the
  localization margin: `fusionEig s − rateP w_eff s ≤ 1/12` for every mode. -/
  rebasedBulkShift : ∀ s, fusionEig N w p s (h0' s) - rateP weff s ≤ q112

/-- **Re-basing is a definitional identity at `p = 1`, a genuine weakening at `p ≥ 2`.**
With `w_eff := w` the re-based shift statement `fusionEig − rateP w s ≤ 1/12` is
DEFINITIONALLY the original bare-referenced statement `fusionEig − eigA w s ≤ 1/12`
(`rateP w s = eigA w s` by `rfl`).  Honest witness that the correction is a `p ≥ 2`
weakening and coincides with the original at `p = 1`. -/
theorem rebased_p1_eq_bare (N : Nat) (w : Q') (s : Nat)
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w 1 0) :
    (fusionEig N w 1 s h0' - rateP w s ≤ q112)
      = (fusionEig N w 1 s h0' - eigA w s ≤ q112) := rfl

/-! ## 3. The `p = 1` INHABITANT — the corrected carrier is genuinely satisfiable

At `p = 1` the shift is `0` and the re-based rate coincides with the bare rate
(`w_eff := w`), so the corrected `rebasedBulkShift` is discharged directly from the
already-proved `saddleLocalCLT_p1.bulkShiftBound` (types coincide by `rateP_one_eq_eigA`
/ `rfl`). -/

/-- **`rebasedLocalCLT_p1` — the `p = 1` inhabitant of the corrected carrier.**  The
heat-kernel input inhabits `RebasedLocalCLT` unconditionally in `s`, with
`A := 0, eta := 0, w_eff := w`.  `rebasedBulkShift` is `saddleLocalCLT_p1.bulkShiftBound`
verbatim (the re-based rate equals the bare rate at `w_eff = w`).  So the CORRECTED
residual is satisfiable — the correction did not break the anchor. -/
def rebasedLocalCLT_p1 {N : Nat} {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w 1 0) :
    RebasedLocalCLT N w 1 h0' where
  A := 0
  eta := 0
  weff := w
  rebasedBulkShift := (saddleLocalCLT_p1 hw0 hw1 h0').bulkShiftBound

/-! ## 4. The named-open bridge `ExpShiftBridge` — the single irreducible analytic core

The conversion of the (already re-based) `CReal` saddle `estimate` of `SaddleLogForm`
into the Q'-level `rebasedBulkShift` is ONE `CReal.exp`-Lipschitz step (`w_eff ≈
exp(−A_p)`).  It is named here as the residual and left UNINHABITED for `p ≥ 2` (Rule 5);
`rebasedLocalCLT_of_saddle` REDUCES the corrected carrier to it. -/

/-- **`ExpShiftBridge` — THE NAMED-OPEN analytic core (`p ≥ 2`).**  Carries the effective
weight `w_eff : Q'` and the exp-Lipschitz consequence of `SaddleLogForm.estimate`: the
re-based Q'-level shift bound.  This is the single `CReal.exp` step that converts the
`eta·C₂²` `CReal` saddle remainder into the `Q'` margin.  NAMED-OPEN: NOT inhabited for
`p ≥ 2`, NOT faked. -/
structure ExpShiftBridge (N : Nat) (w : Q') (p : Nat) (weff : Q')
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- The re-based Q'-level eigenvalue-shift bound (exp-Lipschitz image of the saddle
  estimate). -/
  rebasedBulkShift : ∀ s, fusionEig N w p s (h0' s) - rateP weff s ≤ q112

/-- **`rebasedLocalCLT_of_saddle` — the driver bridge (REDUCTION, `p ≥ 2`).**  Given the
`CReal` saddle mechanism `SaddleLogForm` (carrying `A`, `eta`) together with a witness of
the named-open `ExpShiftBridge` at an effective weight `w_eff`, assemble the corrected
carrier `RebasedLocalCLT`.  This is a pure re-packaging: it INHABITS nothing new — it
reduces the corrected carrier to the single exp-Lipschitz residual `ExpShiftBridge`,
which stays UNINHABITED for `p ≥ 2`.  The saddle moduli `A`, `eta` are recorded as the
carrier data. -/
def rebasedLocalCLT_of_saddle {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (S : SaddleLogForm N w p h0') {weff : Q'}
    (B : ExpShiftBridge N w p weff h0') :
    RebasedLocalCLT N w p h0' where
  A := S.A
  eta := S.eta
  weff := weff
  rebasedBulkShift := B.rebasedBulkShift

/-! ## 5. Wiring back to `SaddleLocalCLT` at a re-based reference

For the DOWNSTREAM localization (`SpectralLocalization.pert` hard-codes `eigA w` as the
true gap edge), a re-based carrier still needs its shift phrased against the bare `eigA w`.
When the effective weight equals the bare weight (`p = 1`, `w_eff = w`), the two are
definitionally identical, so a `RebasedLocalCLT` at `w_eff = w` yields a `SaddleLocalCLT`
directly.  (For `p ≥ 2`, `w_eff ≠ w` and closing the localization needs the auxiliary
`eigA w_eff s ≤ 2/3` on the bulk window — a separate downstream step, out of scope.) -/

/-- **`rebasedToSaddle_at_bare` — recover the original `SaddleLocalCLT` carrier from a
re-based one whose effective weight is the bare weight.**  Since `rateP w s = eigA w s`,
the re-based field IS the bare-referenced `bulkShiftBound`; the `A`/`eta` moduli carry
over.  This shows the correction is conservative at `w_eff = w`. -/
def rebasedToSaddle_at_bare {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (R : RebasedLocalCLT N w p h0') (hw : R.weff = w) :
    SaddleLocalCLT N w p h0' where
  A := R.A
  eta := R.eta
  bulkShiftBound := fun s => by
    have h := R.rebasedBulkShift s
    rw [hw] at h
    exact h

end YMGap.Continuum.RebasedBulkShift

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RebasedBulkShift.rateP_one_eq_eigA
#print axioms YMGap.Continuum.RebasedBulkShift.rateP_nonneg
#print axioms YMGap.Continuum.RebasedBulkShift.rateP_le_one
#print axioms YMGap.Continuum.RebasedBulkShift.rebased_p1_eq_bare
#print axioms YMGap.Continuum.RebasedBulkShift.rebasedLocalCLT_p1
#print axioms YMGap.Continuum.RebasedBulkShift.rebasedLocalCLT_of_saddle
#print axioms YMGap.Continuum.RebasedBulkShift.rebasedToSaddle_at_bare
