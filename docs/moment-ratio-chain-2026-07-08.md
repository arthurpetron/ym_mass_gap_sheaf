# The moment-ratio reduction chain — build result, sharp re-diagnosis, honest verdict

**Date:** 2026-07-08. Lean-core (`Q'`/`CReal`), axiom gate `propext`/`Quot.sound`, guard 5.
Owner files: `R1CurvatureEnvelope.lean` (edited), `JacobiModularCReal.lean`, `AbelianMomentEnvelope.lean`
(read). Main tree, no `EnterWorktree`, nothing committed.

Target: wire the θ two-sided bracket (built) ⟹ M1 (`V·(1−w)≤2`) + M2 (`Var·(1−w)²≤8`) ⟹
`CurvatureEnvelope` `s ≥ 7` tail ⟹ `hlocalize`. Prior grep confirmed this connective algebra was
UNBUILT (the θ bounds had no downstream consumer).

---

## 1. What I built (PROVED, axiom-clean, `#print axioms ⊆ {propext, Quot.sound}`)

New in `R1CurvatureEnvelope.lean §3.8` — the genuine ring step that turns the envelope's
transcendental-looking boundary factor into a rational scalar the moment bracket can meet:

| decl | statement | role |
|---|---|---|
| `eval_singleton` | `eval [c] w ≃ c` | helper |
| `envMarginP_nonneg` | `0 ≤ eval ((36/25)(1−2w²)²)` | perfect-square nonneg |
| `eval_envConstP` | `eval envConstP w ≃ (144/25)·w²·(1−w²)` | boundary factor as a poly |
| **`envConst_le`** | **`(144/25)·w²·(1−w²) ≤ 36/25`, EVERY `w`** | the perfect-square cap |
| **`envBound_le_marginConst`** | **`envBound w s ≤ (36/25)·(A_s·A_{s+1}·A_{s+2})`** | per-mass connective interface |

`envConst_le` is the exact ring identity `36/25 − (144/25)w²(1−w²) = (36/25)·(1−2w²)²` (i.e.
`w²(1−w²) ≤ 1/4`), discharged by a single `decide` on the coefficient identity
`[36/25] = envConstP + envMarginP` — the "polynomial step via the ring normaliser" the task asked for.
`envBound_le_marginConst` lifts it to the real SU(2) moment object `envBound w s`
(`= (144/25)·w²(1−w²)·acNfull_s·acNfull_{s+1}·acNfull_{s+2}`), collapsing the boundary factor to the
rational cap `36/25` against the mass product. This is genuine moment algebra on the exact `acNfull`
defs, not assumed.

- `lake build`: **exit 0, 787 jobs**, `Build completed successfully`.
- Frontier **guard 5** OK: `5 Clay-frontier types unconditionally uninhabited`. M1/M2/`hlocalize`
  did **not** react (correct — not discharged).
- `scripts/lean_axiom_audit.py`: **PASS** (7570 theorems observed, 7426 tracked).
- Banned tokens (`native_decide`/`sorry`/`Classical`/`:= True`): NONE in code (only the honest-scope
  docstrings name them as absent).

---

## 2. THE CHAIN RE-DIAGNOSES — the sharp further gate (named, not papered over)

Building the connective algebra exposed that **the chain as literally stated does not compose**, for
two independent, machine/numerically-verified reasons. Both are stated sharply below.

### 2a. `envConst_le` proves the "reduce-to-constant-floor" route is DEAD (matched vanishing).

The natural hope is: `envConst_le` caps the envelope RHS at `36/25 < 2`, so the tail should reduce to
a CONSTANT second-difference floor `Δ²V(s) ≥ 36/25 − 2 = −14/25`, stronger than the standing `≥ −2`
but window-uniform. **This is refuted.** Numerics (mpmath dps 50, `coeffW w s = (s+1)w^{s(s+2)}`
matching the Lean defs), `min_w (Δ²V(s)+2)`:

| s | `min_w (Δ²V+2)` | at w | s | `min_w (Δ²V+2)` | at w |
|---|---|---|---|---|---|
| 7 (odd) | 1.8226 | 0.943 | 8 (even) | **0.00002** | 0.001 |
| 15 (odd) | 1.8325 | 0.982 | 10 (even) | **0.00002** | 0.001 |
| | | | 20 (even) | **0.00002** | 0.001 |

For **even `s`**, `Δ²V(s)+2 → 0` as `w → 0`: by parity the tilted measure concentrates at the
antidiagonal centre and `Δ²V(s) → −2` exactly. So `Δ²V(s) ≥ −14/25` is **false** at the corner. The
`w²(1−w²)` vanishing in the envelope RHS is genuinely load-bearing — it matches the corner where
`Δ²V+2` itself vanishes. Hence `envConst_le` **sharpens but cannot close** the tail; it is the honest
rational interface, not a bypass. (Per the SZZ-surrogate lesson, I did **not** build a residual on the
refuted constant floor.)

### 2b. M1/M2 (upper bounds on the ratio) provably cannot supply the envelope (a LOWER 2nd-difference).

The envelope is `Δ²V(s)+2 ≥ (144/25)w²(1−w²)`, i.e. a **lower** bound on the second difference of the
moment ratio `V(t)=dmomNfull/acNfull`. M1/M2 (`V·(1−w)≤2`, `Var·(1−w)²≤8`) and the θ two-sided bracket
are **upper/magnitude** bounds on `V` (and on the partition sum `ϑ₃`). An upper bound on a sequence
carries **no** lower bound on its discrete second difference (convexity is independent of magnitude):
one can perturb `V` within any magnitude envelope to make `Δ²V` arbitrarily negative. The `−2` floor
(and its `(144/25)w²(1−w²)` refinement) is precisely the **log-concavity/positivity** content of the
theta measure — orthogonal to what M1/M2 bound. So even a *sharp* M1/M2 does not imply the envelope
tail. This is the structural gate the "θ ⟹ M1/M2 ⟹ envelope" phrasing hides.

### 2c. M1/M2 themselves are not built, and need a SECOND θ leg (not just the bracket).

Even the magnitude bound M1 needs BOTH an upper bound on the numerator `Σ_D D²q^{D²}` AND a lower
bound on the denominator `ϑ₃(q)=Σ_D q^{D²}`. The built θ bracket
(`thetaS_geRat_geomChord`/`thetaHalf_ge_twoBlock`) supplies only the **denominator lower leg**, and
its constant (`0.880` of sharp) lives NUMERICALLY — extracting it needs the transcendental scale
`M ∼ 0.75/√(−ln q)` (outside `Q'`/`CReal`). The D²-weighted **numerator upper bound** is not built at
all. So M1/M2 are two-leg objects of which the θ bracket is one loose leg.

---

## 3. The sharp residual (renamed precisely)

The single open analytic core is unchanged in location but now precisely characterized:

    ThetaTailSecondDiffMargin :  ∀ s ≥ 7,  Δ²V(s) + 2  ≥  (144/25)·w²·(1−w²)
    (equivalently CurvatureEnvelope w s on s≥7; true inf-ratio ≥ 7.957 vs required 5.76).

It is a **LOWER bound on the theta-moment second difference with matched `w²(1−w²)` corner vanishing**,
carrying the discrete-Gaussian **log-concavity**, NOT a magnitude bound. It is:
- **not** reducible to a constant floor (§2a, refuted),
- **not** implied by M1/M2 or the θ magnitude bracket (§2b, structural),
- the genuine saddle content (theta-ratio second-difference control, `q→1` local CLT).

Each fixed window `s` is still discharged mechanically by `curvatureEnvelope_of_sqCert` (Bernstein
in `w²`); `s = 0..6` are PROVED. The open content is the **uniform-in-`s`** statement — the core that
has persisted through every reduction.

## 4. hlocalize

`hlocalize` (`GradedBondMovingBudget`: `∀ k, gapDefect k ≤ gradedBudget(w_k)`) is downstream of R1
(`SaddleVarianceFloor`) via the fusion local-CLT. It consumes the envelope tail through
`saddleVarianceFloor_of_envelopeTail`. Since the tail is open (§3), `hlocalize` **stays OPEN**. No
part of it closed this session; nothing was faked toward it. The SU(2) lift is exact and unchanged
(`coeffW_prod_eq_weyl_abel`, Weyl `1/(s+2)²`).

---

## 5. HONEST VERDICT

- **Did the moment-ratio chain close M1/M2 / the `s≥7` envelope / `hlocalize`?** **No.**
- **Genuine advance:** the connective ring step is now machine-checked (`envConst_le`,
  `envBound_le_marginConst`) — the envelope's boundary factor `w²(1−w²)` is provably capped by the
  rational `36/25`, giving the tail a clean rational moment-bracket interface where before there was none.
- **Re-diagnosis (named, per the task's instruction):** the chain does not compose. (i) The
  reduce-to-constant-floor route is REFUTED by the matched corner vanishing (`envConst_le` makes this
  precise). (ii) M1/M2 / the θ bracket are magnitude/upper bounds and structurally **cannot** produce
  the required second-difference **lower** bound — that is log-concavity content, a different object.
  (iii) M1/M2 are themselves unbuilt and need a second (numerator) θ leg plus the transcendental
  `M∼0.75/√(−ln q)` scale for the constant.
- **The sharp gate:** `ThetaTailSecondDiffMargin` — a uniform-in-`s` LOWER bound on the theta-moment
  second difference with `w²(1−w²)` vanishing (log-concavity / `q→1` saddle), NOT a magnitude bound.
- Nothing faked: no `Prop := True`, no assumed hypothesis passed as proof, no vacuous inhabitant; the
  refuted constant floor was NOT turned into a residual. Clay YM mass gap remains OPEN.
