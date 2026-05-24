# Fiducial Constants — Audit and Provenance

> **Purpose.** Project-wide single source of truth for the literature
> provenance of every "fiducial" constant in Phase 3. For each constant
> we record:
>
> 1. What value the code currently uses.
> 2. Where the *shape* of the formula comes from.
> 3. Whether the specific numerical value is **directly extracted** from
>    a paper, a **literature-shape** approximation, or a **heuristic**
>    introduced by this project.
> 4. What a refinement would require and how it would propagate.
> 5. How to cite it in `formal/`, Lean (`lean/`), and Python
>    (`computations/`).
>
> All references resolved against verified citation metadata (May 2026
> WebSearch pass); BibTeX entries are in
> [`formal/references.bib`](../formal/references.bib).

---

## Honest framing

> The author of this audit (Claude) does **not** have physical access to
> the cited journal articles or textbooks. Verification of citation
> *metadata* (author, journal, volume, year, DOI) was done via WebSearch
> against publicly indexed sources. Verification of the *specific
> numerical values* extracted from those papers comes from training-data
> knowledge plus standard-textbook conventions; it has **not** been
> cross-checked against the physical journals.
>
> Each fiducial below carries a `status` field marking how strong its
> provenance is. Two values are flagged as **HEURISTIC** — they should
> be the first refinement targets.

---

## 1. `BAŁABAN_SPECTRAL_GAP_COEFF = 1/2`

**Location.** `computations/small_field_kp.py`.

**Used in.** The small-field activity-decay rate

$$
\rho_{\mathrm{sf}}(g_k) \;=\; \frac{c_\lambda \cdot \text{convention}}{g_k^2},
\qquad c_\lambda := \text{BAŁABAN\_SPECTRAL\_GAP\_COEFF} = \tfrac{1}{2}
\quad(\text{fiducial}).
$$

**Status: LITERATURE-SHAPE, FIDUCIAL VALUE.**

**Shape source.** The Bałaban RG series establishes a small-field
activity bound of the form
$$
|a_k^{\mathrm{sf}}(X)| \;\le\; \exp\!\Bigl(-\tfrac{c_\lambda(P_k)}{g_k^2} \cdot
\tfrac{|X|_{\text{phys}}}{a_k}\Bigr),
$$
where $c_\lambda(P_k)$ is the spectral gap of the small-field Laplacian
$\Delta_k$ restricted to a Gribov-safe patch $P_k$. This is the SHAPE
of the bound; see [Balaban1987RG-I, Balaban1988RG-II].

**Specific value 1/2 — provenance.** The value $c_\lambda = 1/2$ is
**not** directly extracted from a single inequality in those papers.
It is a *literature-shape fiducial*: an order-of-magnitude value
consistent with what one encounters in the Bałaban literature, chosen
so that:

- the formula type-checks at Q' (it's a rational);
- the convergence threshold $g_{\max}^{\mathrm{sf}} \approx 0.40$
  (canonical) lands at a physically-meaningful weak-coupling boundary;
- downstream Phase-3 modules don't silently degenerate.

The actual value of $c_\lambda$ in any specific Bałaban paper depends
on three things, none of which this project has settled to satisfaction:
1. the Gribov-patch geometry (parameterized by $\delta_k$);
2. the choice of Killing-form normalization (P1.1 picks physics-spin);
3. the patch atlas (still abstract per work_plan 2.2 open question).

**Refinement strategy.** Direct extraction would mean reading the
specific small-field convergence theorem in [Balaban1987RG-I] or
[Balaban1988RG-II] under matched conventions, recording the exact
coefficient, and updating `BAŁABAN_SPECTRAL_GAP_COEFF`. The shape
of the formula does not change; only the numerical value shifts and,
with it, the convergence threshold $g_{\max}^{\mathrm{sf}}$.

**Citations.**
- TeX: `\cite{Balaban1987RG-I,Balaban1988RG-II,BrydgesFederbush1978}`
- Lean (planned quantitative closure): import `YMGap.Constructive.Rationals`
  and use `Q'.mkPos 1 2 (by decide)` for the rational value.
- Python: `computations.small_field_kp.BAŁABAN_SPECTRAL_GAP_COEFF`
  (currently `Fraction(1, 2)`).

---

## 2. `MU_CONNECTIVITY_4D = log(8e) ≈ 3.0794`

**Location.** `computations/small_field_kp.py`.

**Used in.** The small-field cluster-expansion convergence threshold:
$$
K_{\mathrm{sf}} \;=\; \frac{1}{1 - e^{-(\rho_{\mathrm{sf}} - \mu)}}
\quad\text{when}\;\rho_{\mathrm{sf}} > \mu, \qquad
\mu := \log(2d \cdot e) = \log(8e) \;\text{for } d = 4.
$$

**Status: LITERATURE FORMULA, SPECIFIC VALUE FOLLOWS FROM d = 4.**

**Shape source.** The connectivity / "tree-graph" bound for site-polymer
counting on a d-dimensional cubic lattice: the number of connected
n-element polymers containing a fixed site is bounded by $\mu^n$ for
$\mu = 2d \cdot e$. The factor $e$ comes from Cayley's tree formula
applied to the tree-graph identities of [BrydgesFederbush1978];
see also [Cammarota1982] for refined criteria and
[GlimmJaffe1987 Ch.18] for the textbook treatment.

**Specific value at $d = 4$.** $\mu = 8e \approx 21.7$,
$\log \mu \approx 3.0794$. This is the *standard* connectivity bound,
not a fiducial — it follows from the geometry.

**Refinement strategy.** Tighter polymer-counting bounds exist (for
specific polymer geometry definitions, restricted-class arguments, or
non-tree corrections), and they would *shrink* $\mu$ and *enlarge* the
convergent regime $g < g_{\max}^{\mathrm{sf}}$. None of the relevant
sharper bounds change the *shape* of $K_{\mathrm{sf}}$.

**Citations.**
- TeX: `\cite{BrydgesFederbush1978,Cammarota1982,GlimmJaffe1987}`
- Lean: not currently a Lean constant; if needed, an approximation
  $\log(8e) \approx 3079/1000$ as `Q'` suffices for per-step bounds.
- Python: `computations.small_field_kp.MU_CONNECTIVITY_4D` (float).

---

## 3. `MU_PLAQUETTE_4D = 16`

**Location.** `computations/large_field_kp.py`.

**Used in.** The large-field cluster-expansion convergence threshold:
$$
K_{\mathrm{lf}} \;=\; \frac{q}{1 - q}
\quad\text{with}\;q = \mu_{\text{plaq}} \cdot Z_t,
\qquad \mu_{\text{plaq}} = 16 \;\text{for } d = 4.
$$

**Status: LITERATURE-SHAPE VALUE; FORMULA $5d-4$ COMMONLY CITED BUT
NOT VERIFIED BY DIRECT WEB SEARCH.**

**Shape source.** The plaquette-polymer connectivity bound on a
d-dimensional cubic lattice: the number of connected plaquette-polymers
of size $n$ containing a fixed plaquette is bounded by
$\mu_{\text{plaq}}^n$. The specific *shape*
$\mu_{\text{plaq}} \le 5d - 4$ is widely repeated in lattice gauge
theory references and is associated with [Seiler1982 LNP 159], the
canonical text on constructive lattice gauge theory; see also the
related plaquette-polymer counting discussions in [DrouffeItzykson1978]
and [ItzyksonDrouffe1989].

**HOWEVER**: the specific formula `5d-4 = 16` (for $d=4$) was **not**
directly verifiable from the project's WebSearch pass — none of the
returned excerpts contained the formula verbatim. It is widely cited
in the field but the project does not (yet) have a primary-source
verification.

**Two honest options:**

1. **Keep `MU_PLAQUETTE_4D = 16` as a literature-shape value.** Mark
   it as such in the code provenance (currently does); refinement
   awaits direct access to Seiler 1982 (or equivalent) to verify
   the bound and possibly tighten.
2. **Use the conservative site-connectivity bound
   $\mu_{\text{site}} = 8e \approx 21.7$.** This is the
   [BrydgesFederbush1978] bound, which holds for site polymers and
   *a fortiori* for plaquette polymers (plaquettes have fewer
   neighbors than sites). Conservative; loses the tightness but is
   rigorous. Would shift the lf convergence threshold
   $g_{\max}^{\mathrm{lf}}$ down by a factor of $\sqrt{\log 16 / \log(8e)} \approx 0.97$
   (canonical: $0.4245 \to 0.4098$; Wilson: $0.8491 \to 0.8195$).

**Both are available in code** (as of 2026-05-24):

```python
from computations.large_field_kp import (
    MU_PLAQUETTE_4D,                 # 16.0, default (option 1)
    MU_PLAQUETTE_CONSERVATIVE_4D,    # 8e ≈ 21.7, rigorous fallback (option 2)
    compute_large_field_kp,
)
kp_default  = compute_large_field_kp(g, mu_plaq=MU_PLAQUETTE_4D)
kp_rigorous = compute_large_field_kp(g, mu_plaq=MU_PLAQUETTE_CONSERVATIVE_4D)
```

Sensitivity sweep: `computations/fiducial_sensitivity.py::sweep_mu_plaq`.

**Refinement strategy.** Direct extraction from [Seiler1982 LNP 159]
of the plaquette-polymer connectivity bound for $d = 4$ (or any tighter
bound from later literature, e.g. for restricted polymer classes
in [DrouffeItzykson1978] / [ItzyksonDrouffe1989]). Refinement
*enlarges* the lf convergent regime. The shape of $K_{\mathrm{lf}}$
does not change.

**Citations.**
- TeX: `\cite{Seiler1982,DrouffeItzykson1978,ItzyksonDrouffe1989}`
- Lean: not currently a Lean constant; if needed, encode as a `Q'` or
  `Nat` (since $16 \in \mathbb{N}$, this is trivial).
- Python: `computations.large_field_kp.MU_PLAQUETTE_4D` (float = 16.0).

---

## 4. `J_MAX_DEFAULT = 12` (heat-kernel character-tail truncation)

**Location.** `computations/large_field_kp.py`.

**Used in.** Truncation of the SU(2) heat-kernel character sum
$Z_t = \sum_{2j \ge 1} (2j+1)^2 \exp(-t \cdot j(j+1))$ at $2j \le 12$
(so $j \le 6$), with an explicit geometric tail bound at the cutoff
ratio.

**Status: ENGINEERING PARAMETER, NOT A LITERATURE FIDUCIAL.**

This is a numerical-analysis truncation parameter, not a physically
meaningful constant. At $j = 6$ the omitted-tail factor is
$\exp(-t \cdot 42) \cdot 13^2$; for $t \ge 1$ (canonical $g \le 1$)
this is below $10^{-15}$. The tail bound (geometric series at the
cutoff ratio) is rigorous, so the truncation does not introduce
soundness issues — only conservatism.

**Refinement.** Increase if the project ever needs `Z_t` at very
small $t$ (very strong coupling, where the convergent regime is far
exited anyway).

---

## 5. `BALABAN_POLYMER_RESIDUAL = 2.0`

**Location.** `computations/sigma_hat_trajectory.py`.

**Used in.** The σ̂-transport η-coupling derivation:
$$
\eta_k \;\le\; \frac{c_{\text{polymer}}}{A_{\min}^{\text{dimensionless}}}
\cdot \Delta_\cap(b, g_k), \qquad c_{\text{polymer}} = 2.
$$

**Status: DERIVED (reclassified 2026-05-25).** Previously HEURISTIC.

**First-principles derivation** (full argument in
`notes/sigma-hat-derivation.md` §2.3-derivation; surfaced in code as
`derive_polymer_boundary_channel_count() → 2`).

Under the block-spin coarsening $T_b$, each scale-$k$ polymer $X$ maps
to a deterministic scale-$(k+1)$ image $X' = T_b(X)$. The per-polymer
contribution to the σ-residual is the change in the cluster-expansion
truncated correlation:
$$
\Delta T(X) \;:=\; T_{k+1}(X'; C') - T_k(X; C).
$$
The triangle inequality gives the cleanest possible bound:
$$
\bigl|\Delta T(X)\bigr|
\;\le\; \bigl|T_{k+1}(X')\bigr| + \bigl|T_k(X)\bigr|
\;\le\; |a_{k+1}(X')| + |a_k(X)|
\;\le\; 2 \cdot \max\bigl(|a_{k+1}(X')|,\,|a_k(X)|\bigr).
$$
The factor of 2 is the **channel multiplicity**: the per-polymer change
is bounded by the sum of *two* activity terms — one at scale $k$, one
at scale $k+1$ — and there's no further reduction without additional
analytic input.

**Tightness.** The triangle inequality $|a - b| \le |a| + |b|$
saturates when $a$ and $b$ have opposite signs. Sign-preservation of
$T_k(X)$ under $T_b$ is **not generic** for cluster-expansion polymer
activities (truncation orders can flip signs). So $c_{\text{polymer}}
= 2$ is the **optimal worst-case** constant from first principles.

**Refinement (open analytic target).** A sign-preservation lemma for
the SU(2) heat-kernel polymer activities under $T_b$ would tighten the
constant to $c_{\text{polymer}} = 1$, halving the σ-budget consumption.
This is a real pilot-window enlargement opportunity, but it requires a
genuinely new analytic input (signed cluster-expansion control).
Without that lemma, the worst-case 2 is correct.

The historical match $2/4 = 1/2$ with the previous placeholder is now
**coincidence** rather than design: the placeholder was 1/2, and the
independently-derived worst-case happens to equal 1/2 with the
spec-mandated $A_{\min} = 4$.

**Citations.**
- TeX: `\cite{Balaban1988convergent,BrydgesFederbush1978}`
- Lean (planned quantitative closure): import
  `YMGap.Constructive.Rationals`, use `Q'.ofNat 2`.
- Python: `computations.sigma_hat_trajectory.BALABAN_POLYMER_RESIDUAL`.

---

## 6. `WILSON_LOOP_MIN_AREA_DIMENSIONLESS = 4`

**Location.** `computations/sigma_hat_trajectory.py`.

**Used in.** Same η-coupling derivation (denominator).

**Status: DIRECTLY EXTRACTED from project spec.**

This is the dimensionless area $A_{\min} = (2)^2 = 4$ of a 2×2 Wilson
loop at the coarse scale, given the area-law convention of
`docs/outline.md` §7.1 ("Wilson loops with sides at least $2 a_k$").
Not from external literature; from the project's own specification.

**Refinement.** Only if the area-law convention changes (it shouldn't).

---

## 7. Pilot-trajectory parameters (`standard_su2_trajectory`)

**Location.** `computations/overlap_measure.py`.

**Status: ENGINEERING DEFAULTS for the test trajectory; not fiducial
physics constants.**

- Block factor $b = 2.0$ (standard binary block-spinning).
- Initial coupling $g_0 = 1.2$ default (designed to exhibit Landau-pole
  truncation across realistic RG steps; pilot fails at this default
  since post-3.1-upgrade only weak coupling converges).
- One-loop SU(2) $\beta$-function: $b_0 = (11/3) \cdot C_2(\text{adj}) =
  22/3$. **This IS directly extracted** — it is the standard one-loop
  YM coefficient.
- $\delta_k$ smallness exponent $\alpha = 0.5$ (default, per
  `outline.md` §6.4's "$\delta_k \sim g_k^\alpha$, $\alpha \in (0,1)$").

---

## Summary table

| Constant | Value | Status | Refine? | Sweep entry point |
| --- | --- | --- | --- | --- |
| `BAŁABAN_SPECTRAL_GAP_COEFF` | 1/2 | literature-shape fiducial | first target | `fiducial_sensitivity.sweep_spectral_gap_coeff` |
| `MU_CONNECTIVITY_4D` | log(8e) | literature formula | already standard | — |
| `MU_PLAQUETTE_4D` | 16 | literature-shape (5d-4) | rigorous fallback `MU_PLAQUETTE_CONSERVATIVE_4D = 8e` available | `fiducial_sensitivity.sweep_mu_plaq` |
| `J_MAX_DEFAULT` | 12 | engineering | only if needed | — |
| `BALABAN_POLYMER_RESIDUAL` | 2.0 | **DERIVED 2026-05-25** | tighter c=1 via sign-preservation lemma (open) | `fiducial_sensitivity.sweep_polymer_residual` |
| `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` | 4 | from project spec | n/a | — |
| Trajectory defaults | various | engineering | n/a | — |

**One flagged HEURISTIC value remaining (after 2026-05-25 derivation pass):**
1. `BAŁABAN_SPECTRAL_GAP_COEFF = 1/2` (literature-shape, but the
   number itself was chosen for order-of-magnitude plausibility).

**One value flagged as "widely cited but not directly verified":**
2. `MU_PLAQUETTE_4D = 16` (the $5d-4$ formula is standard but the
   project's web-search pass did not surface a primary-source verbatim).
   Rigorous fallback `MU_PLAQUETTE_CONSERVATIVE_4D = 8e ≈ 21.7` available
   (Brydges–Federbush site-connectivity bound), costs only −0.2% in the
   pilot window.

**Reclassified from HEURISTIC to DERIVED (2026-05-25):**
3. `BALABAN_POLYMER_RESIDUAL = 2.0` — now derived from a triangle-inequality
   argument on the per-polymer activity change under block-spin coarsening
   (`derive_polymer_boundary_channel_count() → 2`). See §5 for the
   first-principles derivation. The tighter `c = 1` requires a
   sign-preservation lemma (open analytic refinement).

---

## How to use this file

- **In LaTeX** (`formal/`): cite via the keys in
  [`formal/references.bib`](../formal/references.bib). Each formula
  using a fiducial should be accompanied by a footnote pointing here
  (e.g., "constant fiducial; see
  [`notes/fiducials_notes.md`](fiducials_notes.md) §N").

- **In Lean** (`lean/`): when lifting Python constants to `Q'` for the
  quantitative closures (planned), add a docstring line citing the
  relevant entry here. The arithmetic in Q' is exact, but the
  *source* of the rational is the relevant fiducial. For the SU(2)
  pilot σ̂-budget closure, see
  [`lean/YMGap/RG/SigmaHatPilot.lean`](../lean/YMGap/RG/SigmaHatPilot.lean):
  it instantiates the `RationalTail.sigma_hat_budget_closure` framework
  on a Q'-rational upper bound `η_max = 11/10000` matching the Python
  pilot at the canonical wire-in parameters
  `(g_0 = 0.30, K = 3, denominator = 10000)`.

- **In Python** (`computations/`): the module-level docstring of each
  module already names the constants and their status. The provenance
  dict on each `*KP` dataclass records per-constant origin. This file
  is the audit; the module docstrings are the per-use citations.

  Run sensitivity sweeps via
  [`computations/fiducial_sensitivity.py`](../computations/fiducial_sensitivity.py)
  (`python -m computations.fiducial_sensitivity` from the repo root) to
  see how each fiducial moves the pilot's convergence thresholds and
  budget closure.  As of 2026-05-24 all three flagged fiducials —
  `BAŁABAN_SPECTRAL_GAP_COEFF`, `MU_PLAQUETTE_4D`,
  `BALABAN_POLYMER_RESIDUAL` — are threaded through
  `sigma_hat_trajectory` (via `spectral_gap_coeff`, `mu_plaq`,
  `polymer_residual` parameters), so the sweep tables report each
  fiducial's real impact on `Σ_k η_k` rather than the constant default.

  For "what does adopting this refinement cost in pilot window?"
  questions, use `fiducial_sensitivity.max_g0_closure(...)`.  Sample
  output (canonical, K = 3, σ̂_0 = 1):

  | refinement                       | g_0_max | delta |
  | --- | --- | --- |
  | default fiducials                | 0.3912  | baseline |
  | conservative μ_plaq = 8e         | 0.3905  | −0.2% |
  | tighter sf (c_λ = 1.0)           | 0.4133  | +5.6% |
  | looser  sf (c_λ = 0.3)           | 0.3054  | −22.0% |

  The pilot window is dominated by the small-field fiducial; the
  conservative large-field fallback is essentially free.

---

## Bibliography (mirror of `formal/references.bib`)

| Key | Paper / Book |
| --- | --- |
| `Balaban1987RG-I` | Bałaban, "RG approach to lattice gauge field theories. I", CMP 109 (1987), 249–301. |
| `Balaban1988RG-II` | Bałaban, "RG approach to lattice gauge field theories. II. Cluster expansions", CMP 116 (1988), 1–22. |
| `Balaban1988convergent` | Bałaban, "Convergent renormalization expansions for lattice gauge theories", CMP 119 (1988), 243–285. |
| `BrydgesFederbush1978` | Brydges & Federbush, "A new form of the Mayer expansion...", JMP 19 (1978), 2064–2067. |
| `Seiler1982` | Seiler, *Gauge Theories as a Problem of Constructive QFT...*, LNP 159, Springer 1982. |
| `DrouffeItzykson1978` | Drouffe & Itzykson, "Lattice gauge fields", Phys. Rep. 38 (1978), 133–175. |
| `ItzyksonDrouffe1989` | Itzykson & Drouffe, *Statistical Field Theory* (Vol. 1 & 2), Cambridge 1989. |
| `Cammarota1982` | Cammarota, "Decay of correlations for infinite range interactions in unbounded spin systems", CMP 85 (1982), 517–528. |
| `GlimmJaffe1987` | Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed.), Springer 1987. |
