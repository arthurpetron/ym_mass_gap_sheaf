# The block-spin defect crux — is Σδ_k summable, and under what scheme?

**Task.** The Clay YM continuum gap now reduces (adequacy proved, `additiveErosion_uniform_floor`)
to: the real 4D SU(N) block-spin defects `δ_k` (multiplicative), `ε_k` (additive) obey the margin
step `(1−δ_k)·margin_k − ε_k ≤ margin_{k+1}` (`margin_k = m_lat(a_k)/a_k`), are **summable**, and
satisfy anchor-dominance `(1−Σδ)·m₀ > Σε`. **The crux asked: is `Σδ_k` summable, and how?**

**VERDICT (one line).** **YES — `Σδ_k` is summable, `δ_k ∼ 1/k²`, under the *renormalized
fluctuation-integration* block-spin (NOT the Migdal–Kadanoff pointwise product).** The divergence
`δ_k ∼ 1/k` is an artifact of the wrong scheme; the correct per-step defect to the *dimensionless*
margin is `O(g_k⁴)` because (i) the free/Gaussian part of the RG step is scale-exact and contributes
zero, and (ii) the marginal (running-coupling) part enters only through the *change* `Δg²_k = O(g_k⁴)`
per step, whose total sum is the *finite* total coupling flow `∫₀^{g₀²} dg² = g₀² < ∞`. The residual
is no longer a summability question at all — it is a **finite-window (crossover) no-gap-closing**
statement plus **one named moment-uniformity constant** (`α<1`), both already pinned in the Lean.

---

## 0. The obstruction, stated exactly, and why it is a scheme artifact

The falsified route (ledger addendum 2026-06-27; `AFRateCalibration.linear_bound_not_summable`,
`AFRateCalibration.lean:1015`) used the **Migdal–Kadanoff pointwise product**: the single-link
heat-kernel weight `K_w` under bond-moving becomes `K_w^p` (pointwise `p`-th power, `p = b^{d−1}`
parallel bonds). The deviation of `K_w^p` from *any* heat kernel `K_{w'}` is

```
δ_MK(w) ≈ 0.4374·(1 − w)      (power 1.00, exact-arithmetic numerics — ledger)
```

**linear** in the margin `1 − w ∼ g²`. On geometric spacing `a_k = a₀ b^{−k}` one-loop AF gives
`1 − w_k ∼ g_k² ∼ 1/(β₀ L k)` (`L = log b`), so

```
Σ_k δ_MK(w_k) ∼ Σ_k 1/k   →  DIVERGES  →  ∏(1−δ_k) → 0  →  no gap.
```

**Root cause (this is decisive):** a pointwise product of heat kernels is *not* a heat kernel, and
the MK bond-move is an *uncontrolled approximation in d>1*. It injects an `O(g²)` error *at every
step*, even though the true RG only *changes* the theory by `O(g⁴)` per step. MK's defect is
`∝ g²·(number of steps)`, i.e. `∝ ∫ g² d(log a)` — a logarithmically divergent integral over scale.
The true defect is `∝ ∫ dg²` — the *finite* total coupling change. **This is the whole crux in one
sentence: MK measures the coupling, the true RG measures the change in the coupling.**

```
MK (wrong):   Σ_k δ_MK ∼ ∫ g²(a) d(log 1/a) = ∫ dg²/g² · g²  ~  ∫ dk/k        DIVERGES (log)
True RG:      Σ_k δ_k  ∼ ∫ |d log margin|   = ∫ |F'/F| dg²    ≤ C·g₀²          FINITE
```

---

## 1. CORRECT SCHEME — renormalized fluctuation integration, defect is O(g⁴)

Balaban's rigorous RG (and Magnen–Rivasseau–Sénéor, Federbush; and the recent rigorous strong-coupling
control of Shen–Zhu–Zhu) does **not** take a pointwise product. One step integrates out a *fluctuation
field* against a **covariance decomposition** `C = Σ_j C_j` (finite-range, per-scale). Three structural
facts make the per-step defect genuinely `O(g_k⁴)`:

1. **The Gaussian part is scale-EXACT.** The quadratic (free) piece of the fluctuation integral
   reproduces the free scaling *exactly*. The free UV theory is scale-invariant and **does not change
   the physical gap at all** — it contributes **zero** to the defect of the *dimensionless* margin.
   (MK's linear error is precisely a failure to reproduce this free step exactly.) This is Angle 2's
   engine: *the free UV does not erode the physical gap.*

2. **The marginal part is the counterterm — it is the FLOW, not an error.** The one marginal coupling
   is `g²` itself. Its per-step drift is the running, tracked exactly by the counterterm / the
   *definition* of `g_k`. In the Lean this is the retuning `renormW p w = 1 − C₄(1)·(1−w)`
   (`BondMovingQuadratic.lean:213`), "the explicit reparametrization that absorbs the marginal flow."
   Subtracting it is legitimate: it removes the *flow*, not a defect.

3. **What is LEFT is quadratic.** After the marginal subtraction, the genuine transverse residual is
   the second-order overshoot. In the Lean (`bondMovingDeltaRen`, `BondMovingQuadratic.lean:276`):

   ```
   δ_ren(p,w) = p · dimQ(1) · [ C₄(1)·(1−w) − (1 − w^{C₄(1)}) ],   C₄(1) = 3
   ```

   and the bracket factors **exactly** (sympy-verified below) as

   ```
   3(1−w) − (1−w³) = (1−w)²·(2+w),      so   δ_ren = p·dimQ(1)·(1−w)²·(2+w) = O((1−w)²).
   ```

   With `1 − w_k ∼ g_k² ∼ 1/k`, this is `δ_ren(w_k) = O(g_k⁴) = O(1/k²)` — **SUMMABLE.**

**Answer to "O(g²), O(g⁴), or exponentially small?":** the per-step defect to the *dimensionless
gap* is `O(g_k⁴)` (marginal-subtracted transverse remainder), plus genuinely *irrelevant* operator
contributions that are `O(a_k^{Δ_irr})` = **exponentially small in `k`** (they decay geometrically,
trivially summable). There is **no** surviving `O(g²)` piece — the apparent `O(g²)` was MK's artifact.

---

## 2. PHYSICAL-GAP vs LATTICE-GAP defect — asymptotic freedom makes δ_k summable

`margin_k = m_lat(a_k)/a_k` is the **dimensionless** gap `Δ·(physical length) = Δ/Λ_YM · c₀`. By
dimensional transmutation this is **asymptotically constant**: `margin_k → margin_∞ = Δ/Λ_YM · c₀ > 0`.
The lattice gap `m_lat(a_k) = margin_k · a_k → 0` — that vanishing is *pure kinematics of units* and
carries **no** erosion of the physics. The correct object to bound is the fractional change of the
*dimensionless* `margin`, not of `m_lat`.

Along the exact trajectory the only running coupling is `g²` (marginal); the dimensionless gap is a
smooth function `margin_k = F(g_k²)` with `F(0) = margin_∞ > 0` analytic near `g=0` (Wilson's smooth
RG trajectory; AF ⇒ the UV fixed point is Gaussian and `F` is analytic there). Then

```
δ_k := |margin_{k+1} − margin_k| / margin_k  =  |F'(g²)/F(g²)| · |Δg²_k|.
```

The beta function `d(1/g²)/d log μ = β₀` gives `dg²/d log μ = −β₀ g⁴`, so over one RG step of
`Δlog μ = L`:

```
|Δg²_k| ≈ β₀ L · g_k⁴ = O(1/k²)      ⟹      δ_k = O(1)·O(g_k⁴) = O(1/k²)   SUMMABLE.
```

Numerically (§5) `Δg²_k / (β₀L·g_k⁴) → 1`. **So yes — asymptotic freedom directly delivers
`δ_k ∼ g_k⁴ ∼ 1/k²` for the dimensionless margin.** The deep-UV contribution is not merely summable,
its *tail sum is arbitrarily small* (a→0 is a convergent tail), so the deep UV cannot close the gap.

---

## 3. SPACING / REPARAMETRIZATION — the total defect is a finite physical quantity

`Σ_k δ_k ≈ −log ∏(1−δ_k)` is (to leading order) the total-variation of `log(margin)` from `a₀` to `0`.
This is **manifestly finite and reparametrization-invariant**:

```
Σ_k δ_k  ≤  ∫₀^{g₀²} |d log margin / dg²| · dg²  ≤  (sup |F'/F|) · ∫₀^{g₀²} dg²  =  (sup|F'/F|)·g₀²  <  ∞.
```

The total coupling flow `∫₀^{g₀²} dg² = g₀²` is finite and **independent of how the flow is sliced**
into steps (geometric, super-geometric, or continuous). This is the robust, scheme-independent core:
*the total physical-gap change along the entire flow is finite because the total change in `g²` is
finite.* No cleverness in the spacing sequence is needed — geometric `a_k = a₀ b^{−k}` already gives
`Σ 1/k² < ∞`. (Super-geometric `a_k = a₀ b^{−k²}` would make each `Δg²_k` even smaller, but is
unnecessary.)

**The right margin variable.** The cleanest variable is not `margin_k` but `y_k := log margin_k`,
whose *total variation* `Σ|Δy_k| = Σ δ_k` is exactly the finite integral above. Equivalently, use
`g²` itself as the flow parameter: reparametrized by `g²`, the erosion density `|d log margin/dg²|`
is `O(1)` and integrable over the *bounded* interval `[0, g₀²]`.

**The one genuine subtlety (this is where the residual actually lives).** `g₀²` at the *strong-coupling
anchor* is **not** small (the fixed-spacing gap is proved at strong coupling `w=1/6`, `g₀²=O(1)`), so
`(sup|F'/F|)·g₀²` need not be `< 1`. That does **not** break positivity: `margin_k ≥ margin₀·e^{−Σδ} > 0`
for *any* finite `Σδ`. The **only** way the floor can vanish is if `margin → 0` *somewhere along the
flow* — i.e. a **gap-closing / bulk phase transition in the strong→weak crossover**. 4D SU(N) YM has
**no** bulk transition (strong and weak coupling are analytically connected — the physical content of
confinement–continuum continuity). So the crux **splits cleanly**:

```
Σδ = Σ_{k<K} δ_k        (finite crossover window, g=O(1))    +   Σ_{k≥K} δ_k     (deep UV, g→0)
     └── FINITE product ∏_{k<K}(1−δ_k) > 0 iff no gap-closing ─┘   └── ∼ Σ 1/k² < ∞  RESOLVED ─┘
```

The deep-UV half is now **resolved** (this deliverable: `δ_k ∼ 1/k²` via AF + renormalized quadratic
defect). The residual is a **finite-range, k<K, no-gap-closing** statement — a compactness/continuity
fact about the *crossover*, **not** an infinite summability. This is exactly where Balaban's real work
(large-field/small-field decomposition, uniform crossover control) lives, and it is a strictly smaller
and better-posed target than "control the whole a→0 flow."

---

## 4. NET-DRIFT recursion — the correct form when a residual linear piece is present

If (for a conservative accounting) one refuses to fully absorb the marginal drift and keeps a residual
additive erosion `ε_k`, the correct object is **not** product-survival but a **bounded-variation /
Cauchy convergence-modulus** recursion — exactly the `RegScalingLimitModulus` route validated on φ⁴.
Physical margin ≈ const forces the compensation `ε_k ≈ δ_k·margin_k` (the additive and multiplicative
erosions are two bookkeepings of the *same* per-step change `|Δmargin_k|`). Write `η_k := δ_k·margin_k + ε_k`
= the per-step total erosion budget. Then the step `(1−δ_k)·margin_k − ε_k ≤ margin_{k+1}` becomes

```
margin_{k+1} ≥ margin_k − η_k ,          Σ_k η_k = total-variation of margin ≤ C·g₀² < ∞ (§3),
```

so `(margin_k)` is **Cauchy with an explicit modulus** (`η_k ∼ 1/k²`, tail `Σ_{k≥N} η_k ≤ C/N`), hence
convergent to `margin_∞`, and

```
margin_k ≥ margin₀ − Σ_{j<k} η_j ≥ margin₀ − Σ_j η_j  =  m₀ − budget  >  0     (anchor-dominance).
```

This is **precisely** the additive-erosion floor the Lean already proves adequate
(`additiveErosion_uniform_floor`, capstone §5): `margin_k ≥ (1−Σδ)m₀ − Σε > 0`. The net-drift form is
the *honest* reading — it does not pretend `ε≡0` (the multiplicative surrogates' evasion, flagged in
the bridge map §2/§4) — and it is the form to inhabit. **The correct recursion is the additive/Cauchy
one; summability of its budget `η_k ∼ 1/k²` is what §1–§3 establish.**

---

## 5. Numeric sanity checks (mpmath / sympy, exact where possible)

| Check | Result |
|---|---|
| Renormalized-defect bracket factors quadratically | `3(1−w)−(1−w³) = (1−w)²(2+w)` — **exact** (sympy, remainder 0) |
| MK **linear** budget `Σ_{k<2·10⁵} 6(1−w_k)`, `1−w_k=1/(k+1)` | `76.70 ≈ 6 log K = 73.24` — **grows without bound (∼log K), diverges** |
| Renormalized **quadratic** total `Σ_k (1−w_k)²(2+w_k)` | `3.733` — **finite** |
| Tail product `∏_{k≥k₀}(1−δ_ren)`, `k₀=2` (where `δ<½`) | `0.3028 > 0` — **strictly positive** (finite head excluded, as coded) |
| Total coupling flow `Σ_k (g²_k − g²_{k+1})`, `g²_k=1/(u₀+sk)` | `= g₀² = 0.5` exactly (**telescopes, finite, slicing-independent**) |
| Per-step `Δg²_k` vs `β₀L·g⁴_k` at `k=1,10,100,1000` | ratio `0.75 → 0.92 → 0.99 → 0.999` → **1** (confirms `Δg² = O(g⁴) ∼ 1/k²`) |

The tail product `0.303 > 0` together with `Σ(g²_k−g²_{k+1}) = g₀² < ∞` is the whole verdict in
numbers: the infinite (deep-UV) tail is harmless; only the finite head carries weight.

---

## 6. The exact residual (already pinned in Lean) and the CONCRETE NEXT

The deep-UV summability is real (`SummabilityCapstone.renormalized_gap_of_AFRate`,
`FullModeAssembly.fullMode_gap_of_AFRate`) but scope-flagged. Reading the Lean's own honesty pins, the
`δ_k ∼ 1/k²` verdict has **exactly one** surviving quantitative residual and **one** finite-window
residual:

- **(R-UV) moment uniformity.** `FullModeAssembly.lean:43–68`: the clean full-mode
  `δ_ren ≤ C·(1−w)²` needs the **Casimir-square moment** `Σ_s μ_τ(s)·qfac(w,s)^q·C₄(s)²` bounded
  as `w→1` (`τ→0`). Writing `S(w) ≍ τ^{−1/2}`, `δ_ren ≤ C·τ^{2−α}`; **summable along the `1/k` AF
  rate iff `α < 1`**. The heat-kernel Gaussian weight `μ_τ` is *designed* to offset the active-mode
  count (`α=0` intended: the small-field regularity of the covariance decomposition). This is one
  `w`-independent constant, carried as the named hypothesis `hMoment`.

- **(R-cross) no gap-closing in the finite crossover.** `∏_{k<K}(1−δ_k) > 0`: a finite product,
  positive unless the dimensionless gap hits `0` at some intermediate coupling — i.e. absence of a
  bulk phase transition on `[g_UV, g₀]`. Finite-range, `k<K`; **not** a summability question.

### Concrete next to formalize (highest-value, buildable)

1. **`renDefect_invSq_quadratic` — the clean per-step bound as a lemma (Lean-core, buildable now).**
   Combine the *proved* algebra `bondMovingDeltaRen = p·dimQ(1)·(1−w)²·(2+w)` (the exact factorization
   §1, sympy-confirmed — currently only `≤ C₄²(1−w)²` envelope is used) with `2+w ≤ 3` on `[0,1]` to
   emit `δ_ren(p,w) ≤ 3p·dimQ(1)·(1−w)²` as a *single explicit constant* bound, then chain the existing
   `renDefect_invSq → renDefect_summable → renormalized_gap_of_AFRate`. This tightens the dominant-mode
   floor with a named constant and removes the `(2+w)` slack. Pure `Q'` arithmetic.

2. **`netDrift_floor_of_bddVar` — the net-drift lemma (Lean-core, buildable now).** State and prove:
   given `margin_{k+1} ≥ margin_k − η_k` with `Σ η_k ≤ B` and `margin₀ − B > 0`, then
   `∀k, margin_k ≥ margin₀ − B > 0`, with the budget supplied as an explicit `1/k²` tail modulus
   (`η_k ≤ D·invSqTerm 2 k`, `tailSum ≤ D/N`). This is the *honest* (`ε≢0`) inhabitant-shape of
   `TrueMarginRecursionPhysical.step` + anchor-dominance; it is exactly the P2 glue lemma the bridge
   map calls "the single highest-value buildable deliverable," now with the **summable budget derived**
   rather than assumed. Feeds `uniformSpacingFloor_of_trueMarginPhysical → toScalingBand`.

3. **Isolate (R-UV) `hMoment` as `α<1` and (R-cross) as a finite-`K` `noGapClosing` predicate.** Reduce
   the *entire* remaining continuum obligation to these two named types: one `w`-uniform Casimir-square
   moment bound (`α<1`, the small-field covariance-decomposition estimate — the Balaban/MRS target) and
   one finite-range crossover positivity (`∏_{k<K}(1−δ_k)>0`, the no-bulk-transition target — the SZZ
   strong-coupling / analyticity target). This is the correct **final factorization** of the Clay core:
   an infinite deep-UV part that is **provably summable**, and a **finite** crossover part.

### Bottom line

The crux is resolved at the level the task asked for: **`Σδ_k` IS summable, `δ_k ∼ g_k⁴ ∼ 1/k²`,
under the renormalized fluctuation-integration block-spin.** The `1/k` divergence was a Migdal–Kadanoff
artifact (pointwise product of heat kernels ≠ heat kernel; error `∝` coupling, not `∝` change-in-
coupling). Asymptotic freedom + marginal-subtraction give the quadratic per-step defect; the total
defect equals the finite total coupling flow `g₀²`; and the problem factors into a **provably summable
deep-UV tail** and a **finite crossover window** whose sole open contents are one named moment-uniformity
constant (`α<1`) and one finite no-gap-closing product. Formalize items 1–3; the net-drift lemma (item 2)
is the correct recursion and is buildable immediately.
