# The OPE / vacuum-condensate positivity route — sign-fixing the renormalon ambiguity

**Deliverable Lean file:** `lean/YMGap/Continuum/OPECondensatePositivity.lean` (wired into
`YMGap.lean`; full `lake build` **green = 724 jobs** (723 → 724); `YMGapGuard`
**frontier-guard OK = 5** Clay-frontier types unconditionally uninhabited). MAIN tree, NEW
file, Lean-core only (`Q'`/`Nat` + the `CReal`/`ExpNeg` backbone), no
Mathlib/`ring`/`native_decide`/`Classical`/`sorry`. Axiom gate `propext`/`Quot.sound` only
on all 13 load-bearing decls. **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The OPE sign-fixing SCAFFOLD is built AND the FIXED-SPACING condensate positivity is
PROVED — but the CONTINUUM condensate positivity is the SEVENTH independent confirmation of
`singleStep`, not a genuinely different (more tractable) route.**

- **OPE structure BUILT.** The physical amplitude `z_phys = PV + ⟨G²⟩·exp(−t₀/g²)`; the
  condensate term IS the Laplace renormalon ambiguity magnitude
  (`ope_fixes_ambiguity_magnitude`, `rfl`), is EXACTLY RG-self-similar
  (`condensateContribution_selfSimilar_step`), equals `⟨G²⟩·condensateCReal`
  (`condensateContribution_eq_condensate`), and — GIVEN `⟨G²⟩ ≥ 0` — has a DEFINITE
  nonnegative sign (`condensateContribution_nonneg`). The OPE resolves the signed `±`
  ambiguity to the `+` branch via the condensate positivity.
- **FIXED-SPACING condensate positivity PROVED (genuinely new).** The lattice dim-4
  condensate `⟨1−χ⟩ = plaqActivity` is `> 0` at strong coupling: bounded BELOW by its
  leading excited-rep term `coeffW w 1 = 2w³` (`latticeCondensate_ge_head`) — floor `1/4`
  at the anchor `w = 1/2` (`latticeCondensate_floor_anchor`, `latticeCondensate_pos_anchor`)
  — and ABOVE by `4w³` (`latticeCondensate_le`). A bona-fide PROVED `0 < ⟨G²⟩a⁴ ≤ 4w³`.
- **CONTINUUM condensate positivity = `singleStep`.** The continuum `⟨G²⟩ ~ Λ⁴` is
  DEFINITIONALLY the same essential singularity `exp(−c/β₀g²) = condensateCReal`
  (`continuumCondensate_is_condensate_scale`, `rfl`); its nonzero `a→0` generation is
  `ContinuumCondensatePositivity := SingleStepDefectBound` (UNINHABITED). The `⟨G²⟩ ≥ 0`
  sign-fixing is the TRIVIAL red herring; the GENUINE content (real continuum `⟨G²⟩ ≠ 0`)
  reduces EXACTLY to `singleStep`.

**No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.**

---

## 1. THE OPE STRUCTURE (task point 1) — the condensate fixes the ambiguity sign

The confining-theory amplitude has the OPE form

    z_phys(g²)  =  (perturbative principal value)  +  ⟨(α/π)G²⟩·Cₒₚₑ·exp(−t₀/g²) .

The perturbative Borel/Laplace series has a positive-`t`-axis renormalon pole giving a
SIGNED ambiguity `Δz = ±(πC/s)·exp(−t₀/g²)` (PROVED essential-singularity CReal,
`LaplaceRenormalonSelfSimilar`). The OPE's dimension-4 term supplies exactly the missing
non-perturbative piece, cancelling the perturbative ambiguity and leaving a definite real
result. The Lean scaffold pins this:

- `condensateContribution G2 k := ambiguityAmplitude G2 k` — the OPE dim-4 term
  `⟨G²⟩·exp(−t₀/g_k²)` is DEFINITIONALLY the Laplace ambiguity amplitude (same object).
- `opeAmplitude pv G2 k := pv k + condensateContribution G2 k` — the physical amplitude.
- `ope_fixes_ambiguity_magnitude` (`rfl`): the OPE non-perturbative piece has EXACTLY the
  magnitude of the ambiguity it resolves.
- `condensateContribution_nonneg` (`CReal.mul_nonneg` on `⟨G²⟩ ≥ 0` and `exp ≥ 0`): the
  condensate term has a DEFINITE nonnegative sign — the OPE picking the `+` branch. This is
  the sign-fixing, **explicitly flagged as the red herring** (see §4).
- `condensateContribution_selfSimilar_step` / `condensateContribution_eq_condensate`: the
  OPE condensate term is EXACTLY RG-self-similar (`·ρ`, `ρ = exp(−6/11)`) and equals
  `⟨G²⟩·condensateCReal` — the self-similar RG-invariant Λ scale.

---

## 2. THE STRONG-COUPLING CONDENSATE (task point 2) — PROVED positive (the IR anchor)

At fixed spacing the dimension-4 condensate is the vacuum-subtracted plaquette expectation
`⟨1 − χ⟩ = ⟨G²⟩·a⁴`, i.e. the excited-rep plaquette activity `plaqActivity w M` (a sum of
NONNEGATIVE character coefficients over spins `s ≥ 1`). It is genuinely POSITIVE at strong
coupling — **a new PROVED theorem this module supplies:**

- `latticeCondensate_ge_head` — `coeffW w 1 ≤ plaqActivity w (M+1)` (∀ `M`, `0 ≤ w`): the
  activity is `≥` its leading term `coeffW w 1 = dim(1)·w³ = 2w³`, by monotonicity of
  `finSum` over the nonnegative excited coefficients (`finSum_monotone_of_nonneg`).
- `latticeCondensate_floor_anchor` — `1/4 ≤ plaqActivity anchorW (M+1)` at `w = 1/2`
  (`coeffW (1/2) 1 = 2·(1/2)³ = 1/4`, kernel `decide`).
- `latticeCondensate_pos_anchor` — `0 < plaqActivity anchorW (M+1)` (strict).
- `latticeCondensate_le` — re-export of the PROVED `plaqActivity_le`: `⟨1−χ⟩ ≤ 4w³`.

So the FIXED-SPACING condensate is a bona-fide **PROVED** `0 < ⟨G²⟩a⁴ ≤ 4w³` — the
confinement analog of the proved fixed-spacing `107/108` gap. This is the IR anchor, and it
is genuine (not the trivial exp-positivity).

---

## 3. THE DECISIVE CHECK (task point 3) — does continuum ⟨G²⟩ > 0 follow, or is it the residual?

**Adversarial answer: it does NOT follow; the continuum condensate positivity is the
residual `singleStep`.**

The physical continuum condensate is `⟨G²⟩ ~ Λ⁴ = (μ·exp(−1/2β₀g²))⁴` — dimensional
transmutation. The lattice measures `⟨G²⟩a⁴ = plaqActivity` (dimensionless, proved `> 0` at
fixed spacing). To take `a→0` at a finite physical `⟨G²⟩`, one runs `g→0` along the AF
trajectory, and `plaqActivity` must vanish at exactly the rate `a⁴·⟨G²⟩ ~ (aΛ)⁴ =
exp(−2c/β₀g²)·poly` — **not faster**. That "not faster" is a spacing-uniform LOWER bound on
the condensate surviving the continuum limit — precisely the gap-survival.

In Lean this is pinned definitionally:

- `continuumCondensate k := condensateCReal k`;
- `continuumCondensate_is_condensate_scale` (`rfl`): the continuum `⟨G²⟩` IS the same
  essential singularity `exp(−c/β₀g²)` as the fluctuation / Borel / string-tension routes;
- `continuumCondensate_selfSimilar_step`: same self-similar `·ρ` kinematics;
- `ContinuumCondensatePositivity := SingleStepDefectReduction.SingleStepDefectBound`
  (UNINHABITED) — the continuum `⟨G²⟩ ≠ 0` IS `singleStep` (`realδ_k ≤ δ_model_k`, the
  spacing-uniform gap-survival);
- `OPESignDetermination := LaplaceRenormalonSelfSimilar.RenormalonDetermination`
  (= `IRRenormalonPositiveAxis`, UNINHABITED) — the all-order sign-cancellation, a physics
  expectation.

The RG "preserving positivity" is exactly the matched-flow dial (`hmatch` / `singleStep`),
the ideal `ε ≡ 0` self-similar trajectory; the real 4D flow's deviation is the additive
erosion `ε_k = singleStep`.

---

## 4. HONEST FOUNDATIONAL ASSESSMENT (task point 4) — 7th confirmation, NOT genuinely different

**The OPE/condensate positivity route is a SEVENTH independent confirmation of the SAME
irreducible core `singleStep`** (after block-spin, interacting-measure/Borel, curvature,
OS/confinement, RG-invariant-Λ, and Laplace–self-similar). Precisely:

| object | status | Lean |
|---|---|---|
| OPE structure `z_phys = PV + ⟨G²⟩·exp(−t₀/g²)` | **BUILT** | `opeAmplitude`, `ope_fixes_ambiguity_magnitude` |
| condensate term = ambiguity magnitude, self-similar, = ⟨G²⟩·Λ | **PROVED** | `condensateContribution_{selfSimilar_step,eq_condensate}` |
| sign-fixing (definite `+` sign given `⟨G²⟩ ≥ 0`) | **PROVED — but TRIVIAL red herring** | `condensateContribution_nonneg` (`exp ≥ 0`, `⟨G²⟩ ≥ 0` assumed) |
| **fixed-spacing condensate `0 < ⟨1−χ⟩ = plaqActivity ≤ 4w³`** | **PROVED (genuinely new)** | `latticeCondensate_pos_anchor`, `latticeCondensate_ge_head`, `latticeCondensate_le` |
| continuum `⟨G²⟩ ~ Λ⁴ = exp(−c/β₀g²)` (same essential singularity) | **PROVED identification (`rfl`)** | `continuumCondensate_is_condensate_scale` |
| **continuum condensate positivity `⟨G²⟩ ≠ 0` (a→0)** | **OPEN = `singleStep`** | `ContinuumCondensatePositivity := SingleStepDefectBound` (uninhabited) |
| OPE sign-determination (all-order cancellation) | **OPEN** | `OPESignDetermination := IRRenormalonPositiveAxis` (uninhabited) |

**Is the continuum condensate positivity constructible from the proved pieces?** NO. A
proved fixed-spacing condensate `⟨1−χ⟩ > 0` is NOT the continuum condensate: it is
dimensionful (`⟨G²⟩a⁴`), and its `a→0` survival at a nonzero physical `⟨G²⟩` is exactly the
spacing-uniform lower bound = `singleStep`. The RG "preserving positivity" is the dial, not
a theorem. The `⟨G²⟩ ≥ 0` positivity the task worried about splits, as in every prior route,
into a TRIVIAL part (`exp(−x) ≥ 0`, free) and the GENUINE part (the real theory's continuum
scale is a nonzero `Λ`) — the mass gap is the genuine part, and it is `singleStep`.

**Is the route genuinely different or more tractable?** Genuinely different FRAMING (the OPE
/ vacuum gluon condensate `⟨G²⟩ > 0`, a distinct physical quantity from the fluctuation
defect, string tension, or curvature), but NOT more tractable: the continuum condensate is
DEFINITIONALLY the same `exp(−c/β₀g²)` essential singularity, inheriting the identical
renormalon obstruction. What it *adds*, genuinely, is the PROVED fixed-spacing
lattice-condensate positivity (`plaqActivity > 0`, a new lower-bound theorem) as a clean IR
anchor for the confining condensate.

---

## 5. Cascade / STOP audit (MANDATORY — this is the mass gap) — NOT tripped

No STOP condition tripped; no guarded bundle inhabited; no cascade. The module builds the
OPE sign-fixing scaffold, PROVES the fixed-spacing condensate positivity, RESTATES the
continuum condensate positivity as `Type`s (`ContinuumCondensatePositivity`,
`OPESignDetermination`) WITHOUT inhabiting them, and produces `ope_condensate_verdict :
OPECondensateVerdict` (an informational bundle of PROVED facts only). It inhabits NONE of the
5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
`ClayTargetPinned`, `FrontierDAG`) and no unconditional `SingleStepDefectBound`,
`IRRenormalonPositiveAxis`, or continuum `⟨G²⟩ ≠ 0`. Because the real `⟨G²⟩ ≠ 0` is NOT
constructed (only its kinematics + the fixed-spacing anchor), the STOP-and-exhaustively-audit
condition (triggered only on a cascade to a guarded bundle) is **not met**.

---

## 6. Build / guard / `#print axioms`

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (724 jobs).
```

All 13 load-bearing decls `#print axioms ⊆ {propext, Quot.sound}` (no `Classical.*`, no
`sorryAx`, no `native_decide`, no `ring`; banned tokens appear only in docstring prose):

```
ope_fixes_ambiguity_magnitude            : [propext, Quot.sound]
condensateContribution_nonneg            : [propext, Quot.sound]   ← sign-fixing (red herring)
ope_sign_fixed                           : [propext, Quot.sound]
condensateContribution_selfSimilar_step  : [propext, Quot.sound]
condensateContribution_eq_condensate     : [propext, Quot.sound]
latticeCondensate_ge_head                : [propext, Quot.sound]   ← ⟨1−χ⟩ ≥ leading term (NEW)
latticeCondensate_floor_anchor           : [propext, Quot.sound]   ← 1/4 ≤ ⟨1−χ⟩ at w=1/2
latticeCondensate_pos_anchor             : [propext, Quot.sound]   ← 0 < ⟨1−χ⟩ (fixed-spacing)
latticeCondensate_le                     : [propext, Quot.sound]   ← ⟨1−χ⟩ ≤ 4w³
continuumCondensate_is_condensate_scale  : [propext, Quot.sound]   ← 7th-confirmation identity
continuumCondensate_nonneg               : [propext, Quot.sound]
continuumCondensate_selfSimilar_step     : [propext, Quot.sound]
ope_condensate_verdict                   : [propext, Quot.sound]
```

---

## 7. HONEST FINAL VERDICT

**CONSTRUCTED (the genuine new pieces):** (i) the OPE sign-fixing scaffold — the physical
amplitude is the perturbative principal value plus the dim-4 condensate term, which IS the
renormalon ambiguity magnitude, is exactly RG-self-similar, equals `⟨G²⟩·condensateCReal`,
and has a definite `+` sign given `⟨G²⟩ ≥ 0`; (ii) the FIXED-SPACING lattice-condensate
POSITIVITY — `0 < ⟨1−χ⟩ = plaqActivity ≤ 4w³`, a bona-fide PROVED positive lattice
`⟨G²⟩a⁴ > 0`, the confinement analog of the proved fixed-spacing gap.

**RESIDUAL (NOT closed):** the CONTINUUM condensate positivity. The continuum `⟨G²⟩ ~ Λ⁴` is
DEFINITIONALLY the same essential singularity `exp(−c/β₀g²)`; its nonzero `a→0` generation is
`SingleStepDefectBound.singleStep`, and its all-order sign-determination is
`IRRenormalonPositiveAxis`. The `⟨G²⟩ ≥ 0` sign-fixing is the trivial red herring; the
GENUINE content (real continuum `⟨G²⟩ ≠ 0`) reduces EXACTLY to `singleStep`.

**So the OPE / vacuum-condensate positivity route is a SEVENTH independent confirmation of
the same irreducible core `singleStep`** — a genuinely different physical framing (the vacuum
gluon condensate) but NOT a more tractable one — PLUS the genuinely new machine-checked
fixed-spacing lattice-condensate positivity. The essential-singularity KINEMATICS and the IR
anchor are constructed; the GENERATION (real flow → nonzero, sign-fixed continuum `⟨G²⟩`) is
the foundational Clay substrate. No guarded frontier bundle is inhabited; nothing is faked;
the 4D Yang–Mills mass gap remains **OPEN**.
