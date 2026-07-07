# The analyticity / dispersion tool on z₁: circular, and reduces exactly to `singleStep`

**Deliverables.** `lean/YMGap/Continuum/IRRegulatorAnalyticity.lean` (wired into `YMGap.lean`;
full `lake build` **green = 729 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier
types unconditionally uninhabited). Numerics `analyticity_numerics.py` + `closed_form.py`
(mpmath dps 45). **Committed: nothing** (per instruction). MAIN tree, NEW file, Lean-core only
(`Q'`/`Nat` + reuse of the PROVED `GenuineResummation` toolkit); no
Mathlib/`ring`/`native_decide`/`Classical`/`sorry`; axiom gate `propext`/`Quot.sound` only.

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The analyticity/dispersion resolution is NOT a new independent route. It splits exactly into a
CIRCULAR continuum version (the IR regulator IS the mass gap) and a NON-CIRCULAR fixed-spacing
version (PROVED, but precisely where there is no renormalon), whose `a→0` uniformity is
`singleStep`. A genuine new piece is built and machine-checked: the FIXED-CUTOFF Borel
analyticity — the massive-propagator IR regulator removes the positive-axis Borel pole and makes
`z₁` a definite analytic value at fixed cutoff. But the CONTINUUM resolution is circular /
`singleStep`. This is an EIGHTH independent confirmation that the binding residual is `singleStep`.
No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.**

The task's most adversarial branch is **CONFIRMED**: the analyticity resolution, taken in the
continuum, assumes the gap to regulate the renormalon to get the gap — a circle. The only
non-circular content is the fixed-spacing analyticity, which does not resolve the *continuum* `z₁`;
its `a→0` uniformity is exactly `singleStep`.

---

## 1. THE IR-RENORMALON MECHANISM AND ITS MASS REGULARIZATION (task point 1) — verified

The positive-axis Borel singularity comes from the deep-IR region of the perturbative integrals
`∫ d⁴k / k⁴ · α_s(k²)ⁿ`. The standard (Beneke) IR-renormalon model of a dimension-`2p` operator:

```
d_n = ∫_0^1 dξ ξ^{p-1}(−ln ξ)^n = n!/p^{n+1}     (ξ = k²/Q², β₀=1)
```

— FIXED-SIGN FACTORIAL ⟹ Borel transform `B(u) = Σ dₙ uⁿ/n! = 1/(p−u)` with a **POLE at u₀ = p > 0**
(the renormalon). Its Laplace sum `∫₀^∞ e^{−u/a}B(u)du` hits the pole; the two `±iε` prescriptions
differ by the ambiguity `Δz = ±π·e^{−p/a}` (mpmath dps 45: `0.0575402…` at `a=1/2`). This is the
signed `±(πC/s)exp(−t₀/g²)` of `LaplaceRenormalonSelfSimilar`.

**The mass gap / IR cutoff removes it.** In the confined phase there are no modes below the gap
`m`: the massive propagator `k² → k²+m²` cuts the deep-IR region `ξ < μ²` (`μ = m/Q`). Then

```
d_n(μ) = ∫_{μ²}^1 ξ^{p-1}(−ln ξ)^n dξ = γ(n+1, pΛ)/p^{n+1},   Λ = −ln μ².
```

Two verified consequences (mpmath dps 45):

- **Factorial → geometric.** `d_{n+1}/d_n ~ (n+1)/p → ∞` (massless, radius-0 Borel) becomes
  `d_{n+1}(μ)/d_n(μ) → Λ` **bounded** (e.g. `Λ = ln 10 = 2.3026` at `μ²=0.1`). The factorial is
  gone.
- **The pole is cancelled — EXACT CLOSED FORM** (`closed_form.py`, series vs closed form reldiff
  `< 1.4·10⁻⁴⁵`):

  ```
  B_μ(u) = ∫_{μ²}^1 ξ^{p-1-u} dξ = (1 − μ^{2(p−u)}) / (p − u).
  ```

  This is **ENTIRE**: the numerator has a simple zero at `u = p` that EXACTLY cancels the
  renormalon pole `1/(p−u)`, with finite value `B_μ(p) = −ln μ² = Λ` (verified `2.30258509299…` at
  `μ²=0.1`). No positive-axis singularity ⟹ the Laplace path is clear ⟹ the ambiguity vanishes ⟹
  a DEFINITE analytic `z₁`. **The IR regulator kills the renormalon.**

This is precisely why at FIXED lattice spacing every activity is entire and there is no renormalon
(`NonpertActivityHeatKernel`: `coeffW = dim·e^{−tC₂}` entire; `clay_fixed_spacing_met`).

---

## 2. THE CIRCULARITY CHECK (task points 2–3, the crux) — three versions, all circular or `singleStep`

The tool asserts: `m>0 ⟹ analytic z₁ ⟹ definite z₁ (= the gap)`.

| version | regulator | status |
|---|---|---|
| **V1** continuum massive propagator `m = m_phys` | the physical gap | **CIRCULAR** — the regulating mass IS the gap being proved |
| **V2** fixed-spacing cutoff `a > 0` | lattice spacing | **NON-CIRCULAR but VACUOUS for the continuum** — PROVED analytic, but no renormalon there |
| **V3** dispersion relation | spectral support edge = `m` | CIRCULAR (=V1) unless the edge is supplied by `a→0` uniformly (=`singleStep`) |

- **V1 is a pure circle.** The IR mass `m` that cancels the pole (`B_μ` entire) is the physical
  continuum gap `m_phys > 0`. Building a continuum `z₁` with an *assumed* `m>0` is the Rule-9 fake:
  you inject the conclusion as the hypothesis. Encoded (uninhabited):
  `ContinuumRegulatorIsGap := SingleStepDefectBound`.

- **V2 is genuinely non-circular — and that is exactly the content proved in Lean.** At a fixed IR
  cutoff the Borel transform is entire and its evaluated terms decay geometrically, so
  `GenuineResummation` is inhabited (`irRegulator_makes_analytic`, reusing the PROVED
  `borel_transform_genuineResummation`). No gap input is used. **But at fixed spacing there is no
  renormalon** — this is the codebase's own established finding (`BorelRenormalonScaffold`
  lines 302–304). The fixed-spacing analyticity is analyticity of a *different* (regulated) object;
  it does not fix the *continuum* `z₁`.

- **V3** fixes the ambiguity from the spectral discontinuity, but the dispersion integral's
  convergence/edge is the gap `m>0` again — the same circle, unless the edge comes from the proved
  fixed-spacing input made uniform in `a`.

**The decisive `a→0` fact (task point 3, verified — `analyticity_numerics.py §4`).** As the cutoff
is removed (`μ² → 0`, `Λ → ∞`), the entire `B_μ(u) → 1/(p−u)` **NON-UNIFORMLY**: `d_n(μ)/d_n → 1`
(the factorial returns) and the pole reforms on the positive axis (`B_μ(u) → ∞` for `u > p`; e.g.
`B_μ(3): 9 → 99 → 9999 → 10⁸` as `μ² : 0.1 → 0.01 → 10⁻⁴ → 10⁻⁸`). So the mass-regulated
analyticity holds at *every fixed* cutoff but is **non-uniform in the cutoff removal**. **The
uniformity of positive-axis analyticity as `a→0` IS the residual — exactly `singleStep`** (the
spacing-uniform gap survival). Encoded (uninhabited):
`ContinuumAnalyticityUniformity := SingleStepDefectBound`.

The non-circular escape the task probes — "does the PROVED fixed-spacing gap regulate the continuum
renormalon?" — fails at the scale-matching: the fixed-spacing gap is `m_lat(a)` with `m_lat·a ~
O(1)` at strong coupling; to kill the *continuum* renormalon you need the PHYSICAL gap
`m_phys = m_lat(a)/a` bounded below as `a→0`, which is the mass gap itself. So the regulator that
would non-circularly kill the continuum renormalon is precisely the object being proved.

---

## 3. THE DECISIVE VERDICT (task point 4) — is it circular, `singleStep`, or new?

**BOTH, split cleanly:**

- **Circular** in the continuum-massive-propagator (V1) and dispersion (V3) versions — the regulator
  is the gap.
- **Reduces to `singleStep`** in the only non-circular (V2, fixed-spacing) version — the `a→0`
  uniformity of the pole-removal is `SingleStepDefectBound.singleStep`, and the sign-determination
  is `IRRenormalonPositiveAxis` (a physics expectation, uninhabited).
- **Genuinely new only as a REFRAMING + one PROVED lemma:** the fixed-cutoff Borel analyticity
  (`irRegulator_makes_analytic`, the closed-form pole cancellation) is a real, machine-checked
  positive fact — the analytic-continuation counterpart of `massless_renormalon_not_analytic`. It
  sharpens the residual to: *prove the positive-axis Borel analyticity of `z₁` is UNIFORM as
  `a→0`* ⟺ `singleStep`. It closes nothing.

So the analyticity/dispersion tool is the **EIGHTH** independent confirmation of the same
irreducible core `singleStep` (after: Borel/renormalon, self-similar Λ, condensate erosion, OPE
condensate positivity, field-space contraction, config-space measure, string tension), reached
through a genuinely different (analytic-continuation) lens but NOT a more tractable one.

---

## 4. HONEST accounting (task point 4 — refuse dodges)

| object | status | evidence |
|---|---|---|
| massless renormalon = positive-axis Borel pole, ambiguous `z₁` | **PROVED (model)** | `d_n=n!/p^{n+1}`, `B=1/(p−u)`, `Δz=±πe^{−p/a}`; `massless_renormalon_not_analytic` |
| massive propagator `k²+m²` ⟹ IR-finite, factorial→geometric | **PROVED (numeric+Lean ratio)** | `d_n(μ)` ratio→Λ; `regMaj_step` |
| massive Borel transform ENTIRE (pole cancelled) | **PROVED (exact closed form)** | `B_μ=(1−μ^{2(p−u)})/(p−u)`, reldiff `<1e−45` |
| fixed-cutoff `z₁` analytic/definite | **PROVED (Lean, non-circular)** | `irRegulator_makes_analytic` (`GenuineResummation borelTerm`) |
| continuum regulator `m=m_phys>0` kills continuum renormalon | **CIRCULAR** | `ContinuumRegulatorIsGap = SingleStepDefectBound` (uninhabited) |
| pole-removal UNIFORM as `a→0` | **OPEN = `singleStep`** | non-uniform limit verified; `ContinuumAnalyticityUniformity = SingleStepDefectBound` |
| sign determination | **OPEN — physics expectation** | `AnalyticityDetermination = IRRenormalonPositiveAxis` (uninhabited) |
| Λ, `⟨G²⟩ ≥ 0`, `exp>0` positivity | **TRIVIAL — red herring** | free `exp` nonnegativity |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types and
produces no unconditional inhabitant of `SinglePolymerActivity`, `SingleStepDefectBound`,
`IRRenormalonPositiveAxis`, or any continuum `z₁`. Guard stays at 5.

---

## 5. `#print axioms` (all 5 load-bearing decls ⊆ {[propext], [propext, Quot.sound]})

```
massless_renormalon_not_analytic : [propext]
regMaj_step                      : [propext]
irRegulator_makes_analytic       : [propext, Quot.sound]   ← fixed-cutoff analyticity (non-circular)
irRegulator_removes_renormalon   : [propext, Quot.sound]   ← massless-vs-regulated, side by side
analyticity_verdict              : [propext, Quot.sound]
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring`, no `sorry`/`admit` (banned tokens in
docstring prose only). All witnesses `Type`-level.

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (729 jobs).
```

---

## 6. HONEST FINAL VERDICT

The confined-phase IR regularization **does** make `z₁` analytic on the positive Borel axis — the
massive propagator `k²+m²` cancels the renormalon pole (exact closed form, machine-checked
fixed-cutoff analyticity). **But that analyticity, in the continuum, IS the mass gap:** the
regulating mass `m` is the physical gap `m_phys > 0` being proved (V1/V3 circular), and the only
non-circular version is the fixed-spacing analyticity — precisely where there is no renormalon —
whose `a→0` uniformity is `singleStep` (the pole demonstrably reforms non-uniformly as the cutoff
is removed). So the analyticity/dispersion tool is **circular in the continuum and reduces to
`singleStep` in the non-circular fixed-spacing form** — an eighth confirmation of the same
irreducible core, plus a genuinely new PROVED fixed-cutoff Borel-analyticity lemma. Nothing is
faked; no guarded frontier bundle is inhabited; the 4D Yang–Mills mass gap remains OPEN. The next
attack is unchanged: the spacing-uniform gap survival `singleStep` — now sharpened to "prove the
positive-axis Borel analyticity of `z₁` is uniform as `a→0`."
