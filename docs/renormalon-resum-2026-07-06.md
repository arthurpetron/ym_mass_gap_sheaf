# The Laplace-of-geometric-Borel renormalon ambiguity, IDENTIFIED with the self-similar RG-invariant Λ

**Deliverable Lean file:** `lean/YMGap/Continuum/LaplaceRenormalonSelfSimilar.lean` (wired into
`YMGap.lean`; full `lake build` **green = 723 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Numerics `computations/verify_laplace.py`
(mpmath dps 50) + `computations/verify_selfsimilar.py` (sympy exact, mpmath dps 50).
**Commits: none** (per instruction). MAIN tree, NEW file, Lean-core only (`Q'`/`Nat` + the
`expNeg`/`CReal` backbone), no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`; axiom gate
`propext`/`Quot.sound` only.

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**A GENUINE new foundational piece is built: the explicit Borel↔self-similar identification.
The Laplace positive-axis renormalon ambiguity factor `exp(−t₀/g²)` for the confining su(2)
theory — with the leading IR-renormalon pole PINNED at `t₀ = c/β₀ = 6/11` by `β₀ = 22/3` and
the OPE dim-4 condensate — is PROVED to be the SAME irrational CReal as the self-similar RG
condensate `condensateCReal k`, EXACTLY self-similar per RG step (`ρ = exp(−6/11)`),
prefactor-independent, and its dimensionful form is the conserved RG-invariant Λ. So the
perturbative series, Borel-tamed (finite radius `1/16`) + Laplace-resummed (pole at `t₀`),
CONSTRUCTS the geometric essential-singularity amplitude as a concrete CReal.**

**BUT the ASSEMBLY `real z_1 = the resummed geometric Λ` is NOT closed: it reduces exactly to
`singleStep`. What remains is (1) the ambiguity's DETERMINATION — the sign/OPE resolution
making the real `z_1` a definite nonzero condensate (`IRRenormalonPositiveAxis`, UNINHABITED,
a physics expectation about the all-order YM series), and (2) the matched real flow (the
`hmatch` dial vs the real erosion `ε_k`). This is a SIXTH independent confirmation that the
binding residual is `singleStep`, plus the genuinely new machine-checked bridge lemmas. No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.**

---

## 1. THE LAPLACE-OF-GEOMETRIC closed form (task point 1) — the ambiguity `(πC/s)exp(−t₀/g²)`

For a geometric Borel transform `B(t) = Σ_k b_k t^k`, `|b_k| = C·s^k` (radius `1/s`), the
closed form is `B(t) = C/(1−s t)`, a single pole at `t₀ = 1/s > 0` ON the positive `t`-axis.
The Laplace sum `z(g) = ∫_0^∞ e^{−t/g²} B(t) dt` therefore acquires a non-perturbative
ambiguity from the pole. Analytically (residue) and **mpmath dps 50 (`verify_laplace.py`,
reldiff `1e−12` across three `(C,s,g²)`):**

    Δz  =  (π C / s) · exp(−t₀ / g²) ,        t₀ = 1/s .

- The PV real part is `∓(C/s)e^{−1/(sg²)}Ei(1/(sg²))`; the imaginary/ambiguity part is
  `±(πC/s)exp(−t₀/g²)` — the discontinuity across the pole (verified as `2×|Im|`).
- The ambiguity's EXPONENTIAL part `exp(−t₀/g²)` is the essential-singularity CReal; the
  prefactor `πC/s` is a positive constant (irrational, kept symbolic in Lean as a rational
  stand-in `P`) that does NOT affect the RG self-similarity.

**su(2) numbers.** SU(2) one-loop `β₀ = (11/3)·C₂(adj=2) = 22/3 > 0` (asymptotic freedom).
The OPE dimension-4 gluon condensate fixes the leading IR renormalon at the Borel-plane pole
`t₀ = c/β₀ = 4/(22/3) = 6/11` (sympy-EXACT; `renormalon_t0_beta0` proves `t₀·β₀ ≃ c`, i.e.
`(6/11)(22/3) = 4`). The ambiguity magnitude is `~ exp(−t₀/g²) = exp(−(6/11)/g²)` = the
non-perturbative condensate / mass-gap scale.

---

## 2. THE SELF-SIMILAR RESUMMATION (task point 2) — the ambiguity IS the geometric Λ

Under the one-loop AF running matched so `1/g_k² = k + B` (`B = condOffset = 12`; the inverse
coupling grows by exactly `1` per block-spin RG step), the ambiguity exponent is

    t₀ / g_k²  =  (6/11)(k + 12)  =  condExponent k        (sympy-EXACT, `verify_selfsimilar.py`).

So the Laplace ambiguity factor `exp(−t₀/g_k²)` equals `condensateCReal k` EXACTLY, and per RG
step it multiplies by the SAME ratio `ρ = exp(−6/11) = 0.5796…` as the condensate (verified to
`1e−40`). **The Borel/Laplace-resummed ambiguity IS the self-similar geometric condensate Λ.**

This is proved in Lean by transporting the PROVED `condensate_selfSimilar_step` across the
exponent equality:

- `renormalonAmb_eq_condensate` — `renormalonAmbCReal k ≃ condensateCReal k` (THE BRIDGE).
- `renormalonAmb_selfSimilar_step` — `renormalonAmbCReal (k+1) ≃ renormalonAmbCReal k · ρ`.
- `ambiguityAmplitude_selfSimilar_step` — for ANY prefactor `P` (i.e. `πC/s`),
  `P·exp(−t₀/g_k²)` obeys the same step (self-similarity is prefactor-independent).
- `renormalonLambda_eq_rgScaleLambda` / `renormalonLambda_conserved` — the dimensionful
  resummed amplitude `Λ^ren_k = μ_k·exp(−t₀/g_k²)` EQUALS the RG-invariant `rgScaleLambda` and
  is CONSERVED on the matched flow.

---

## 3. THE DECISIVE FOUNDATIONAL CHECK (task points 3–4) — is Λ constructed, or is it `singleStep`?

**Adversarial answer: the essential-singularity KINEMATICS is constructed; the GENERATION
(the real theory sitting on it) is `singleStep`.**

| object | status | evidence |
|---|---|---|
| Laplace ambiguity `(πC/s)exp(−t₀/g²)`, `t₀=1/s` | **PROVED (analytic + mpmath 1e−12)** | `verify_laplace.py` |
| su(2) pole `t₀ = c/β₀ = 6/11` (β₀=22/3, dim-4 OPE) | **PROVED (sympy exact)** | `renormalon_t0_beta0` |
| ambiguity factor `exp(−t₀/g_k²)` = condensate `condensateCReal k` | **PROVED** | `renormalonAmb_eq_condensate` |
| ambiguity EXACTLY self-similar (`·ρ`, ρ=exp(−6/11)) | **PROVED** | `renormalonAmb_selfSimilar_step` |
| resummed Λ = RG-invariant `rgScaleLambda`, conserved | **PROVED (conditional on hmatch)** | `renormalonLambda_conserved` |
| Λ ≥ 0 / > 0 (the positivity) | **TRIVIAL — red herring** | `exp` positive (free) |
| **ambiguity DETERMINATION (sign/OPE, condensate ≠ 0)** | **OPEN — physics expectation** | `IRRenormalonPositiveAxis` UNINHABITED |
| **matched real flow (real z_1 on the trajectory)** | **OPEN = `singleStep`** | `hmatch` = dial; real deviation `ε_k` |

The Borel/Laplace does NOT by itself construct the real `Λ ≠ 0`, for two coinciding reasons:

1. **The ambiguity is SIGNED.** The positive-axis pole gives `Δz = ±(πC/s)exp(−t₀/g²)`.
   Constructing its essential-singularity factor and self-similarity is DONE. That the REAL
   confining theory resolves the sign to a DEFINITE nonzero condensate — the OPE /
   non-perturbative cancellation making the full `z_1` unambiguous — is `IRRenormalonPositiveAxis`
   (UNINHABITED; a bound on a free function field, vacuously fakeable, REFUSED inhabitation).
   The GENUINE content (the real theory's Λ = the resummed amplitude, nonzero AND sign-fixed) is
   the residual, NOT the trivial `exp > 0` positivity that was always free.
2. **The identification is with the DIALED trajectory.** `renormalonLambda_conserved`'s
   `hmatch` (matched spacing `ρ·μ_{k+1} ≃ μ_k`) is the ideal `ε ≡ 0` self-similar flow; the
   real 4D flow's deviation is the additive erosion `ε_k = singleStep`.

Both residuals coincide with the additive erosion budget `ε_k` of `TrueMarginRecursionPhysical`
(the CAPSTONE's sole open Clay core) and with the renormalon ambiguity itself: the perturbative
Borel sum provably CANNOT produce a sign-fixed condensate; it must come from the genuine
non-perturbative construction.

---

## 4. Cascade / STOP audit (MANDATORY — this is the mass gap) — NOT tripped

**No STOP condition tripped. No guarded bundle inhabited. No cascade.**

- The module proves the identification / self-similarity of the ambiguity factor and CONDITIONAL
  conservation, and RESTATES the renormalon determination as a `Type`
  (`RenormalonDetermination := IRRenormalonPositiveAxis`) WITHOUT inhabiting it. It inhabits NONE
  of the 5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
  `ClayTargetPinned`, `FrontierDAG`) and produces NO unconditional inhabitant of
  `IRRenormalonPositiveAxis`, `SinglePolymerActivity`, `SingleStepDefectBound`, or any real `z_1`.
- `renormalonLambda_conserved` is a CONDITIONAL producer (open `mu`, `hmatch`).
- Because the real `Λ ≠ 0` is NOT constructed (only its kinematics), the STOP-and-exhaustively-
  audit condition (triggered only on a cascade to a guarded bundle) is **not met**.
- Full build: `frontier-guard OK: 5 … unconditionally uninhabited`, **723 jobs** (722 → 723).

---

## 5. `#print axioms` (all 11 load-bearing decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
beta0_pos                         : (none)
renormalonT0_pos                  : (none)
renormalon_t0_beta0               : (none)                 ← t₀·β₀ ≃ c  (su(2) pole = OPE dim/β₀)
renormalonT0_eqv_condRateExp      : (none)                 ← t₀ = condRateExp = 6/11
renormalonAmbExp_nonneg           : [propext, Quot.sound]
renormalonAmbExp_eqv_condExponent : [propext]
renormalonAmb_eq_condensate       : [propext, Quot.sound]  ← THE BRIDGE
renormalonAmb_selfSimilar_step    : [propext, Quot.sound]  ← ambiguity self-similar (·ρ)
ambiguityAmplitude_selfSimilar_step : [propext, Quot.sound] ← prefactor-independent
renormalonLambda_eq_rgScaleLambda : [propext, Quot.sound]  ← resummed Λ = RG-invariant Λ
renormalonLambda_conserved        : [propext, Quot.sound]  ← Λ conserved (conditional)
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring`, no `sorry`/`admit` (banned
tokens appear only in docstring prose). All witnesses `Type`-level.

---

## 6. HONEST FINAL VERDICT — what new piece is built + what foundational substrate remains

**BUILT (the genuine new piece — the Borel↔self-similar connection).** The Laplace-of-geometric-
Borel closed form gives an ambiguity `(πC/s)exp(−t₀/g²)` with the pole at `t₀ = 1/s` (mpmath
`1e−12`); for su(2) the leading IR renormalon sits at `t₀ = c/β₀ = 6/11` (β₀ = 22/3, dim-4 OPE;
sympy exact). Under one-loop running `1/g_k² = k+12` the ambiguity factor `exp(−t₀/g_k²)` is
PROVED to BE the self-similar RG condensate `condensateCReal k` (`renormalonAmb_eq_condensate`),
EXACTLY self-similar per RG step (`renormalonAmb_selfSimilar_step`, `ρ = exp(−6/11)`),
prefactor-independently, with its dimensionful form the conserved RG-invariant Λ. So the
perturbative series — Borel-tamed and Laplace-resummed — genuinely CONSTRUCTS the geometric
essential-singularity amplitude as a concrete irrational CReal, and IDENTIFIES it with the
self-similar Λ.

**REMAINS (the foundational substrate).** The ASSEMBLY of the REAL theory onto this trajectory
is NOT closed: (1) the ambiguity's sign/OPE DETERMINATION (the condensate `≠ 0`, sign-fixed —
`IRRenormalonPositiveAxis`, UNINHABITED, a physics expectation about the all-order YM series and
its confined-phase cancellation), and (2) the matched real flow (`hmatch` dial vs the real
erosion `ε_k`). Both coincide with `singleStep`. So the assembly `real z_1 = the resummed
geometric Λ` IS `singleStep` — the SAME irreducible interacting-measure / renormalon core,
confirmed here by a SIXTH independent route (the explicit Borel-self-similar identification),
plus the genuinely new machine-checked bridge lemmas. The essential-singularity KINEMATICS is
constructed; the GENERATION (real flow → nonzero sign-fixed Λ) is the foundational Clay
substrate. No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass
gap remains OPEN. The next attack is still the interacting per-step fluctuation bound
(`singleStep` / fusion-local-CLT / the OPE sign-resolution), now sharpened to: resolve the
positive-axis renormalon ambiguity to the definite self-similar condensate that the kinematics
already provides.

---

## 7. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (723 jobs).
```
