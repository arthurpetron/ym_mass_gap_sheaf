# Spectral-stability / Kato–Temple attack on `singleStep` (`realδ_k ≤ 6(1−w_k)²`)

Deliverable class: **(iii) a sharply-quantified perturbation-strength residual**, backed by a
**genuinely-new proved inequality** (the Temple 2×2 second-order bound), plus an adversarial
verdict. It does **not** close `singleStep` (the ledger's atomic F=1 core), and it is **not** a
`:= SingleStepDefectBound` alias.

Lean: `lean/YMGap/Continuum/TempleSpectralStabilityDefect.lean`. Axiom-clean
(`propext`/`Quot.sound`), LEAN-CORE only, builds green.

---

## 1. The unperturbed gap (PROVED, reused)

From `PeterWeylEigenvalueResummation`: the fixed-spacing transfer at coupling `w` has a
**located gap** with separator the eigenvalue `w³ = heatKernelSep w` and multiplicity `dim = 2`
(the fundamental doublet), Casimir-protected. The unperturbed gap is

    g(w) := heatKernelMargin w = 1 − w³ ,     g(w) > 0  for all 0 ≤ w < 1
            (`heatKernelMargin_pos`, `peterWeyl_margin_pos`).

This is the correct (Peter–Weyl, character-vs-eigenvalue-corrected) unperturbed gap. Reused
verbatim as the resolvent denominator in Temple's bound.

## 2. The perturbation (gauge-invariance ⇒ no first-order splitting)

The gauge-invariant block-spin step maps `T_k → T_{k+1} = T_k + P_k`. Decompose (this is exactly
the free/marginal/transverse split already PROVED in `SingleStepDefectReduction` §Task 2 and
`CharFunCumulantDefect`):

* **(A) free / 0th cumulant** — scale-EXACT, zero defect at `w=1` (`freeEnd_defect_scaleExact` +
  `_nonneg` ⇒ pinned to `0`, `charFun_freeEnd_zero`).
* **(B) marginal / 1st cumulant** — the running-coupling drift `1 − renormW p w ≃ 3(1−w)`,
  LINEAR, **subtracted exactly by the counterterm** `renormW` (`renormW_margin`,
  `trueDev_eq_counterterm_sub_transverse`). Because gauge invariance forces `P_k` to commute with
  the rep structure, the first-order shift is a **uniform rescaling of the degenerate sector** — a
  pure coupling renormalization, absorbed. **No first-order multiplicity splitting.**
* **(C) transverse / 2nd cumulant** — the residual `P_k^⊥` (off-diagonal, multiplicity-preserving,
  s=1 ↔ s≥2). This is the piece Temple must control.

## 3. The Temple / Kato second-order bound (NEW, PROVED exactly)

Model the surviving transverse coupling as the 2×2 symmetric block on the {fundamental, first
excited} sub-space, fundamental normalized to the gap top:

    M = [[0, b], [b, g]] ,      b := ‖P_k^⊥‖ ,   g := 1 − w³ .

Characteristic polynomial (sympy, exact): `λ² − g λ − b² = 0`. The fundamental eigenvalue moves
**down** by `δ := −λ_- ≥ 0`, and `λ_- = −δ` satisfies the polynomial, i.e. the **exact identity**

    δ · (δ + g) = b² .           (`temple_char_relation` form; sympy: residual 0)

Since `δ ≥ 0` gives `g ≤ δ + g`, this yields the **Temple product bound**

    δ · g ≤ δ · (δ + g) = b²  ⟹  δ ≤ b² / g .        (`temple_shift_le`, PROVED in Q')

The one-line core (`δ·g ≤ b²`, division-free) captures the genuine Temple content: the eigenvalue
erosion times the gap is at most the squared off-diagonal. Verified exactly in sympy and
numerically (mpmath dps 40) over many `(b,g)`.

## 4. The threshold conversion — the sharp perturbation-strength residual

Combine with `g = 1 − w³ > 0`:

    δ ≤ 6(1−w)²   ⟸   b² ≤ 6(1−w)² · (1 − w³) .      (`temple_threshold`, PROVED)

So the target per-step defect bound `realδ_k ≤ 6(1−w_k)²` is **exactly equivalent** (given the
2×2 Temple structure) to the **off-diagonal norm threshold**

    ┌────────────────────────────────────────────────────────────────┐
    │  ‖P_k^⊥‖  ≤  √6 · (1 − w_k) · √(1 − w_k³)  =: b_max(w_k)        │   (the residual)
    └────────────────────────────────────────────────────────────────┘

This is **strictly sharper than "the interacting measure"**: it is one scalar norm per scale with
an explicit closed-form threshold, not a whole measure. It is the perturbation-strength object the
whole continuum core reduces to under spectral stability.

## 5. Numerical characterization (mpmath dps 45)

**Threshold vs. the PROVED model off-diagonal.** The proved renormalized model defect (the
counterterm-subtracted transverse part) is, exactly (`renDefect_factor` × `dimQ 1`),

    δ_model(w) = bondMovingDeltaRen · = 2(1−w)²(2+w) ,

with implied off-diagonal `b_model² := δ_model · g`. Then, exactly,

    b_model / b_max = √( (2+w)/3 )  ∈ [√(2/3), 1) ,

so **`b_model ≤ b_max` for every `w`**, with margin shrinking monotonically to 1 as `w → 1`:

| w     | g = 1−w³   | b_max        | δ_model      | b_model      | b_model/b_max |
|-------|------------|--------------|--------------|--------------|---------------|
| 0.3   | 0.973      | 1.6913       | 2.254        | 1.4809       | 0.8756        |
| 0.5   | 0.875      | 1.1456       | 1.25         | 1.0458       | 0.9129        |
| 0.7   | 0.657      | 0.5956       | 0.486        | 0.5651       | 0.9487        |
| 0.9   | 0.271      | 0.1275       | 0.058        | 0.1254       | 0.9832        |
| 0.99  | 0.029701   | 0.0042214    | 5.98e-4      | 0.0042144    | 0.9983        |
| 0.999 | 0.0029970  | 1.3410e-4    | 5.998e-6     | 1.3407e-4    | 0.99983       |

So the Temple route **reproduces the proved model bound** (`b_model ≤ b_max ⟺ δ_model ≤ 6(1−w)²`,
the `(2+w)≤3` slack), and pins the exact margin factor `√((2+w)/3)`.

**The genuinely-interacting off-diagonal is far below threshold.** The non-Gaussian connected
remainder of the fused SU(2) heat-kernel measure `p_m(θ) ∝ K_w(θ)^m sin²θ`,
`Cdef_m = r2(m) − 3(r1(m)/2)^{8/3}`, is `O((1−w)⁴) ≪ (1−w)²` (two independent methods,
class-angle integral shown; `Cdef_m/(1−w)⁴` bounded and decreasing in `m`):

| w    | m=2 Cdef/(1−w)⁴ | m=3    | m=5     | m=10    |
|------|------------------|--------|---------|---------|
| 0.7  | 0.798            | 0.550  | 0.217   | 0.0416  |
| 0.9  | 0.714            | 0.325  | 0.0946  | 0.0145  |
| 0.99 | 0.671            | 0.269  | 0.0704  | 0.00998 |

i.e. the interacting excess implies an off-diagonal `≪ b_max` (safety factor ≈ 45, matching the
`UniformMFoldConcentration` finding).

**The linear wall lives entirely in the marginal part.** The *raw* fundamental erosion
`2 − r1(m)` is `O(1−w)` (LINEAR): at `w=0.9`, `2−r1 = 0.30 > 6(1−w)² = 0.06` — it VIOLATES the
quadratic threshold. This is precisely the marginal drift (B) that the counterterm `renormW`
removes. It also *concentrates* in `m` (`0.30, 0.21, 0.13, 0.066` for `m=2,3,5,10`), but stays
linear at fixed `m`. **Answer to crux (4):** the Peter–Weyl multiplicity does NOT by itself make
the off-diagonal sub-linear; the linear-in-`m` part is handled by the counterterm, and only the
*connected* remainder (C) is `O((1−w)⁴)`, safely sub-threshold. So the "linear wall" is dissolved
by renormalization (B) + connectedness (C), **not** by multiplicity resummation.

## 6. Adversarial verdict — does this close `singleStep`?

**No.** Maximally adversarially:

1. **`b = ‖P_k^⊥‖` is the interacting content.** The threshold `b² ≤ 6(1−w)²(1−w³)` is only a
   *reformulation* of `δ ≤ 6(1−w)²`; via the exact `δ(δ+g)=b²` the map `δ ↔ b` is a bijection at
   fixed `g`. Bounding the *physical* (RG-generated, over the full recursion, at the true margin)
   off-diagonal `‖P_k^⊥‖` a-priori requires the unconstructed interacting block-spin effective
   action — exactly the object `singleStep` names. The Temple reframing is therefore
   **EQUI-INHABITING** with `singleStep`, in the same class as `ResummedClustering` and the
   `uniform_in_m` node — a genuine sharp re-framing, **not a strictly-weaker sub-obligation**.
   Ledger status is unchanged: **F = 1, D = 0, guard = 5**.

2. **The gap is non-uniform.** `g = 1−w³ → 0` as `w → 1` (`fixedSpacing_margin_not_uniform`), so
   the resolvent denominator degenerates; the threshold `b_max = √6(1−w)√(1−w³) → 0` faster than
   `(1−w)`. Controlling `‖P^⊥‖` uniformly to `O((1−w)^{3/2})` across the whole AF trajectory is
   the continuum content — not supplied by any fixed-scale spectral fact.

3. **What IS genuinely new and proved here (not a loop):** the Temple 2×2 second-order inequality
   `δ·g ≤ b²` and its threshold corollary `δ ≤ 6(1−w)²  ⟸  b² ≤ 6(1−w)²(1−w³)`, both axiom-clean
   in Q'; the exact model-consistency `b_model ≤ b_max` with the pinned margin `√((2+w)/3)`
   (reproving `bondMovingDeltaRen_le_sixp` via the spectral route); and the numeric
   characterization placing the interacting off-diagonal `≪ b_max`.

**Net:** the spectral-stability synthesis converts the atomic core into the sharpest scalar form
seen so far — a single per-scale off-diagonal norm with the explicit closed threshold
`‖P_k^⊥‖ ≤ √6(1−w_k)√(1−w_k³)` — and proves the enabling Temple inequality outright. It reproduces
the proved model bound with the exact `√((2+w)/3)` margin and places the interacting excess far
below threshold, but the a-priori bound on the real interacting off-diagonal over the full RG
recursion remains the open content. **`singleStep` is NOT closed; F=1 stands; nothing faked.**
