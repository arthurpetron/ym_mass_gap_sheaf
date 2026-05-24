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
2. **Replace with the conservative site-connectivity bound
   $\mu_{\text{site}} = 8e \approx 21.7$.** This is the
   [BrydgesFederbush1978] bound, which holds for site polymers and
   *a fortiori* for plaquette polymers (plaquettes have fewer
   neighbors than sites). Conservative; loses the tightness but is
   rigorous. Would shift the lf convergence threshold
   $g_{\max}^{\mathrm{lf}}$ down by a factor of $\sqrt{16/21.7} \approx 0.86$.

The current code uses option 1.

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
\cdot \Delta_\cap(b, g_k), \qquad c_{\text{polymer}} := 2
\quad(\text{fiducial}).
$$

**Status: HEURISTIC, NOT EXTRACTED FROM A SPECIFIC PAPER.**

**Shape source.** The polymer-expansion residual on the Wilson-loop
expectation $\langle W_R(C)\rangle$ relative to its naive-rescaling
pulled-back value, in the style of the Bałaban / Brydges cluster
expansion ([Balaban1988convergent], [BrydgesFederbush1978]). The shape
$\eta_k \le (\text{const}) \cdot \Delta_\cap / A_{\min}$ is genuine and
comes from a standard dimensional argument (`notes/sigma-hat-derivation.md`
§2). The two-sided "polymer can sit on either side of the loop
boundary" symmetry that picks out the coefficient 2 is **my heuristic
interpretation**, not a quoted line from a paper.

The value 2 was chosen so that, with the smallest Wilson loop area
$A_{\min}^{\text{dimensionless}} = 4$ (which IS extracted, from
`outline.md` §7.1), the derived $\eta$-coupling $2/4 = 1/2$ matches
the previous **placeholder** value. This was a deliberate design
choice to preserve the numerical behavior of the upgraded code while
giving the coupling an explicit derivational structure.

**Refinement strategy.** A real extraction of the polymer-residual
coefficient from [Balaban1988convergent] (or one of the "Large field
renormalization" papers in the same series) would replace this. The
shape of the derivation does not change; only the coefficient (and
therefore the η-coupling and consequently the budget-closure margin)
shifts.

The current value is the most-likely-overestimate side of the
heuristic range; refinement could go either way:
- A larger $c_{\text{polymer}}$ → larger η-coupling → tighter
  budget-closure (harder to satisfy $\sum_k \eta_k < \widehat\sigma_0$).
- A smaller $c_{\text{polymer}}$ → easier budget closure → wider
  pilot-success window.

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

| Constant | Value | Status | Refine? |
| --- | --- | --- | --- |
| `BAŁABAN_SPECTRAL_GAP_COEFF` | 1/2 | literature-shape fiducial | first target |
| `MU_CONNECTIVITY_4D` | log(8e) | literature formula | already standard |
| `MU_PLAQUETTE_4D` | 16 | literature-shape (5d-4) | second target |
| `J_MAX_DEFAULT` | 12 | engineering | only if needed |
| `BALABAN_POLYMER_RESIDUAL` | 2.0 | **heuristic** | second target |
| `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` | 4 | from project spec | n/a |
| Trajectory defaults | various | engineering | n/a |

**Two flagged HEURISTIC values that should be refined first:**
1. `BAŁABAN_SPECTRAL_GAP_COEFF = 1/2` (literature-shape, but the
   number itself was chosen for order-of-magnitude plausibility).
2. `BALABAN_POLYMER_RESIDUAL = 2.0` (no specific paper, chosen to
   match the placeholder value the upgrade preserved).

**One value flagged as "widely cited but not directly verified":**
3. `MU_PLAQUETTE_4D = 16` (the $5d-4$ formula is standard but the
   project's web-search pass did not surface a primary-source verbatim).

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
  *source* of the rational is the relevant fiducial.

- **In Python** (`computations/`): the module-level docstring of each
  module already names the constants and their status. The provenance
  dict on each `*KP` dataclass records per-constant origin. This file
  is the audit; the module docstrings are the per-use citations.

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
