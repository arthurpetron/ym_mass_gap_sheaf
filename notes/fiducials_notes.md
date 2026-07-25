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
> **Update 2026-05-25**: the user supplied PDFs in
> `docs/pdf_references/` for the following primary sources, which have
> been directly audited (extractions cited per-fiducial below):
> [Balaban1987RG-I] (CMP 109), [Balaban1988RG-II] (CMP 116),
> [Balaban1985UV3D] (CMP 102), [BrydgesFroehlichSeiler1978IHES]
> (IHES preprint), [JaffeWitten2006] (Clay statement),
> [Jorgensen1986AnalyticContinuation] (Pac. J. Math. 125).
> The audit conclusions: (a) Bałaban's `c_λ` is qualitative
> (existence-only); (b) BFS confirms our direct per-bond plaquette
> count; (c) the Seiler 1982 $5d - 4 = 16$ formula remains unverified
> (LNP 159 not in the PDF set); (d) no sign-preservation lemma for the
> $c_{\text{polymer}} = 1$ tightening was found in any audited PDF.
>
> **Update 2026-07-24 (corpus file-identity correction).** The PDF
> filenames in `docs/pdf_references/` are swapped relative to their
> contents: `docs/pdf_references/Balaban 116.pdf` actually contains
> **CMP 109 (1987) 249–301** (RG I, small-field effective actions,
> d = 4), and `docs/pdf_references/Renormalization Group Approach to
> Lattice Gauge Field Theories.pdf` actually contains **CMP 116 (1988)
> 1–22** (RG II, cluster expansions). `Balaban 102.pdf` is CMP 102
> (1985) 255–275 as labeled. **CMP 119 (1988) 243–285 is not in the
> corpus.** Any per-fiducial citation of "[Balaban1988RG-II] (CMP 116)"
> that was read from the file named `Balaban 116` was in fact read from
> CMP 109; the 2026-05-25 audit's content attributions
> ((0.27)/(1.18) → CMP 109; (1.32)/(1.36) → CMP 116) are nevertheless
> correct — the audit evidently keyed on content, not filenames.
> (Evidence: direct reads of the OCR corpus `_generated/pdf_text/`,
> 2026-07-24 SL.1 pass.)
>
> **Update 2026-07-24/25 (SL.1 extraction pass + retrieval pass).**
> Three provenance upgrades merged below, each dated and
> evidence-pointed: (a) the Seiler "$5d-4$" formula is **RESOLVED
> (negative)** by exact enumeration — see §3.3–§3.4; the code default
> flipped to the rigorous $20e$ (2026-07-24). (b) The historical
> $c_\lambda = 1/2$ is **SHAPE-LOCATED** to CMP 109 eq. (0.27) — a
> proof-device rate split, not an extracted coefficient — see §1.2.
> (c) A CMP 119 / CMP 122 open-access retrieval attempt (2026-07-25)
> ended in a **precise null**; the polymer residual 2.0 continues to
> rest on the internal derivation — see §5.1 and
> `notes/cmp119_extraction.md`.
>
> **Update 2026-07-25 (later pass — CMP 119 unblocked and read in
> full).** The retrieval null of the same morning was unblocked by a
> human fetch, and the complete text of CMP 119 (1988) 243–285 was
> extracted and hunted. Verdict for the polymer residual:
> **SHAPE-CONFIRMED, constant unpinned** — the paper's central object
> is precisely a difference of polymer-localized cluster-expansion
> terms, and it uses the two-channel triangle device with an explicit
> factor 2 (p. 283), but for a configuration-difference at fixed
> scale, not the repo's cross-scale residual; the only pinned numeric
> in a main bound is R₁ = 1 in (2.44). `BALABAN_POLYMER_RESIDUAL =
> 2.0` remains internally derived. See §5.2 and
> `notes/cmp119_extraction.md` §5. Note also: the fetched corpus file
> `docs/pdf_references/communications-in-mathematical-physics_volume-119_issue-2.pdf`
> is the issue **front matter only** (2 pages), not the article — the
> article PDF still needs to be added to the corpus.
>
> Each fiducial below carries a `status` field marking how strong its
> provenance is. One value remains flagged **HEURISTIC** — see the
> summary table below. *(Superseded 2026-07-24: the flagged-value
> bookkeeping is updated in the dated addendum under the summary
> table.)*

---

## 1. `BAŁABAN_SPECTRAL_GAP_COEFF = 3/4` (DERIVED 2026-05-26)

**Location.** `computations/small_field_kp.py`.

**Used in.** The small-field activity-decay rate

$$
\rho_{\mathrm{sf}}(g_k) \;=\; \frac{c_\lambda \cdot \text{convention}}{g_k^2},
\qquad c_\lambda := \text{BAŁABAN\_SPECTRAL\_GAP\_COEFF} = \tfrac{3}{4}
\quad(\text{DERIVED 2026-05-26}).
$$

**Status: DERIVED — identified with the SU(2) Casimir gap $C_2(1/2) = 3/4$ (2026-05-26).**
**Status addendum (2026-07-24): + SHAPE-LOCATED — the historical "1/2"
is now traced to a specific display in the primary source (CMP 109
eq. (0.27)) and confirmed to be a bookkeeping split, not an extracted
coefficient. See §1.2.**

**Previous value $c_\lambda = 1/2$ replaced.**  The previous value was a
pilot-tolerance fiducial supported by the 2026-05-25 PDF audit's
finding that Bałaban's primary sources prove the *existence* of
$c_\lambda$ without pinning a numerical value.  The 2026-05-26
derivation identifies $c_\lambda$ with the smallest nonzero SU(2)
Casimir $C_2(1/2) = 3/4$ — the leading spectral-gap scale that
governs the small-field activity decay in the project's heat-kernel
normalization (`computations/heat_kernel.py`).  This makes the
small-field $c_\lambda$ and the buffer-shell $\kappa$ (T6.1)
**consistently parameterized** by the same SU(2) Casimir input, which
is the manuscript-grade hygiene Milestone 3.1 was scoped to provide.

**Downstream impact (canonical pilot, $g_0 = 0.30, K = 3$):**

| Quantity                           | $c_\lambda = 1/2$ (old) | $c_\lambda = 3/4$ (new) | Change |
| ---                                | ---                     | ---                     | ---    |
| $g_{\max}^{\mathrm{sf}}$ canonical | 0.4029                  | 0.4935                  | +22.5% |
| $g_{\max}^{\mathrm{sf}}$ Wilson    | 0.8059                  | 0.9870                  | +22.5% |
| $\eta_{\mathrm{total}}$ at canonical pilot | 33/10000        | 9/10000                 | -73%   |
| $\eta_{\mathrm{total}}$ at Wilson pilot    | 12/10000        | 3/10000                 | -75%   |
| canonical $m_0$ lower bound        | 998/1000 = 0.998        | 999/1000 = 0.999        | +0.1pp |
| Lean SU2KP `c_lambda`              | `Q'.mkPos 1 2`          | `Q'.C2_oneHalf` (= 3/4) | derived link to RepTheory |

**Status: DERIVED — confirmed by the 2026-05-25 PDF audit + 2026-05-26 project-internal Casimir-gap identification.**

**Shape source.** The Bałaban RG series establishes a small-field
activity bound of the form
$$
|a_k^{\mathrm{sf}}(X)| \;\le\; \exp\!\Bigl(-\tfrac{c_\lambda(P_k)}{g_k^2} \cdot
\tfrac{|X|_{\text{phys}}}{a_k}\Bigr),
$$
where $c_\lambda(P_k)$ is the spectral gap of the small-field Laplacian
$\Delta_k$ restricted to a Gribov-safe patch $P_k$. This is the SHAPE
of the bound; see [Balaban1987RG-I, Balaban1988RG-II].

**Direct PDF audit (2026-05-25)** of [Balaban1987RG-I] and
[Balaban1988RG-II] (PDFs in `docs/pdf_references/`):

  - **CMP 109 (Part I)** activity bound appears as eqs.~(0.27) and (1.18):
    `|E_ω(X, U_k)| ≤ E_0 · exp(-κ · d_j(X))` (with `d_j` a tree-distance
    measuring polymer extent). The bound rate is `κ`, Bałaban's analog
    of our `c_λ`.
  - **CMP 109 Theorem 3 (precise statement of the main bound)**:
    "There exist positive constants $\kappa_0, M(\kappa), \gamma,
    \varepsilon_0, \varepsilon_1, \alpha_0, \alpha_1$ such that
    if $\kappa \le \kappa_0$, $M \ge M(\kappa)$, $0 < g_k \le \gamma$
    for $k = 0, 1, \ldots, K$, then the sequence of actions $A_k$
    [...] satisfy all the inductive assumptions [...]"
  - **CMP 109 Theorem 2 (SU(2) specialization)**: "Let $d = 4, G =
    SU(2)$, and let $\gamma$ be a sufficiently small positive constant,
    then for a sufficiently small positive $g$ there exists a bare
    coupling constant $g_0 = g_0(\varepsilon, \gamma)$ such that the
    sequence of effective coupling constants $g_k$ is contained [...]."
  - **CMP 116 (Part II)** cluster-expansion convergence theorems
    invoke a SECOND constant $\kappa_1$ ("sufficiently big positive
    number") satisfying ordering constraints like $\tfrac{1}{8}\kappa_1
    \ge (1 - 2\delta)\kappa$ (eq.~1.32) — i.e., `κ` and `κ_1` are linked
    by inequalities, not equalities.

> *(Editorial note 2026-07-24: the file named `Balaban 116.pdf` in the
> corpus is in fact CMP 109 — see the corpus file-identity correction
> in the Honest framing. The content attributions in the bullets above
> are correct as stated.)*

**Verdict of the audit.** Bałaban's framework establishes the
**existence** of a positive `κ` satisfying a system of upper-bound
constraints (`κ ≤ κ_0`, plus compatibility with `κ_1, M, γ, ε_i, α_i`).
The primary sources do NOT pin down a numerical value for `κ`.

> *(Historical text — the two paragraphs below describe the
> pre-2026-05-26 value 1/2 and are retained for the audit trail. The
> current wire-in is 3/4; see the derivation at the top of §1 and the
> located ancestor of the 1/2 in §1.2.)*

The project's `BAŁABAN_SPECTRAL_GAP_COEFF = 1/2` is correctly labeled
fiducial: it is a representative value within Bałaban's qualitative
range, not a number extracted from a primary inequality. The
2026-05-25 audit thus CONFIRMS the existing fiducial status; it does
not refine the numerical value.

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

### 1.1. Empirical lower bound: pilot-tolerance threshold (2026-05-25)

> *(Dated note 2026-07-24: the threshold table below was computed
> against the historical default $c_\lambda = 1/2$; its "default 0.5
> margin" column reads relative to that value. The thresholds
> themselves — smallest $c_\lambda$ at which the pilot closes — are
> unchanged by the 3/4 wire-in; the current default's margin at the
> canonical wire-in is correspondingly larger (3/4 vs threshold
> ≈ 0.289 ⇒ ≈ +160%).)*

Although we cannot derive $c_{\lambda}$ from first principles within
this project (it depends on Gribov-patch geometry, Killing-form
normalization, and the patch atlas — all undecided in Phase 3), we can
bisect for the **smallest $c_{\lambda}$ at which the SU(2) pilot still
closes** at a given operating point. This gives an empirical defensibility
lower bound: any $c_{\lambda}$ above this threshold makes the pilot work.

Computed via `fiducial_sensitivity.c_lambda_pilot_tolerance_threshold`
(default $K = 3$, $\widehat\sigma_0 = 1$, canonical):

| $g_0$ | threshold | default 0.5 margin |
| --- | --- | --- |
| 0.10 | $\approx 0.031$ | $+94$% |
| 0.20 | $\approx 0.127$ | $+75$% |
| 0.30 (canonical wire-in) | $\approx 0.289$ | $+42$% |
| 0.35 | $\approx 0.397$ | $+21$% |
| 0.40 | $\approx 0.525$ | $-5$% (fails) |

The fiducial $c_{\lambda} = 1/2$ has a comfortable $+42$% margin at
the canonical wire-in $g_0 = 0.30$. The pilot's defensibility against
$c_{\lambda}$ uncertainty is robust: even if the true $c_{\lambda}$
were as low as $0.29$, the pilot still closes at the wire-in.

This empirical lower bound does **not** establish that $c_{\lambda} \ge
0.289$ as a theorem; it establishes that the project's pilot is
*tolerant* of $c_{\lambda}$ values down to that point. The numerical
value $0.5$ is consistent with that constraint, but the BOUND comes
from operational behavior, not from a first-principles derivation.

### 1.2. SHAPE-LOCATED: the historical 1/2 traced to CMP 109 eq. (0.27) (SL.1, 2026-07-24)

**SL.1 direct-text extraction (2026-07-24), CMP 109 p. 258, eq. (0.27).**
The display in which the factor 1/2 literally appears is (OCR-faithful
quote from `_generated/pdf_text/Balaban 116.txt` — the file that
actually contains CMP 109; page 10 of the PDF = p. 258 of CMP 109):

> "If its localization domain X is large, for example it is not
> contained in any cube □ ∈ π_k, then the inequality (0.25) ensures that
> |E^(j)(X, U_k)| ≤ E_0 exp(−κ(L^j η)^…) exp(−(1/2)κ d_j(X)),  (0.27)
> and the first exponential can be bounded by an arbitrary positive
> power of L^j η, e.g. by (5!/κ^5)(L^j η)^5.  This power is enough to
> control the sums in (0.23), (0.24)."

The 1/2 in (0.27) is therefore a **decay-rate split**: half of the
inductive rate κ is spent extracting the small prefactor
exp(−κ(L^jη)^…), the other half retained as polymer-size decay.  It is
a proof device, valid for ANY κ satisfying the inductive assumptions —
not a determination of κ.  The value of κ itself is existence-only:

> **Theorem 3** (CMP 109, p. 264, verbatim): "There exist positive
> constants κ_0, M(κ), γ, ε_0, ε_1, α_0, α_1 such, that if κ ≤ κ_0,
> M ≥ M(κ), 0 < g_k ≤ γ for k = 0, 1, …, K, then the sequence of
> actions A_k, defined inductively by the small field renormalization
> transformations (0.17)–(0.20), satisfy all the inductive assumptions
> described between (1.1)–(1.22)."

and the SU(2) specialization defers even its own proof:

> **Theorem 2** (CMP 109, p. 259): "Let d = 4, G = SU(2), and let γ be
> a sufficiently small positive constant, then for a sufficiently small
> positive g there exists a bare coupling constant g_0 = g_0(ε, γ) such
> that the sequence of the effective coupling constants g_k is
> contained in the interval ]0, γ], and g_K = g. […] A proof of this
> theorem, based on perturbative calculations, will be given in a
> separate paper."

**Upgraded verdict (2026-07-24).**  The 2026-05-25 audit conclusion
("existence-only, no numerical κ") is CONFIRMED at quote level, and
sharpened: the project's historical c_λ = 1/2 shape now has a located
ancestor — the (0.27) rate-split — which makes explicit that 1/2 was
never a property of the gauge group or the Laplacian, only of
Bałaban's bookkeeping.  This retroactively strengthens the 2026-05-26
decision to re-derive the value internally as the SU(2) Casimir gap
C_2(1/2) = 3/4: the primary sources supply no number that could
contradict (or support) any specific rational.  Nothing in CMP
109/116/102 pins c_λ.

**CMP 119 cross-check (2026-07-25, full-text read — see §5.2).**  The
newly extracted CMP 119 further confirms this reading: its Theorem 1
is again existence-only ("There exist constants, introduced in the
above description … The constants satisfy numerous restrictions
introduced in the proof", p. 262–263, explicitly inheriting [I]'s
restrictions on κ, M, ε_j, α_{0,j}, α_{1,j}), and it **reuses the
exp(−(1/2)κ d) rate-split** of CMP 109 (0.27) in at least two places:
eq. (3.48), p. 280 ("|E^(j)(X,z)| ≤ E₀ exp(−κ(L^jL^{−n})^{−1})
exp(−(1/2)κ d_j(X))") and the p. 283 two-class polymer split.  The ½
is a recurring bookkeeping device across the whole series; κ is never
pinned.  Nothing in CMP 109/116/119/102 pins c_λ.

**Citations.**
- TeX: `\cite{Balaban1987RG-I,Balaban1988RG-II,BrydgesFederbush1978}`
- Lean (planned quantitative closure): import `YMGap.Constructive.Rationals`
  and use `Q'.mkPos 1 2 (by decide)` for the rational value.
- Python: `computations.small_field_kp.BAŁABAN_SPECTRAL_GAP_COEFF`
  (currently `Fraction(1, 2)`).
- Empirical lower bound: `computations.fiducial_sensitivity.c_lambda_pilot_tolerance_threshold`.
- *Addendum 2026-07-24: the Lean and Python lines above are the
  historical 1/2 wiring retained for the audit trail; the current
  wire-in is `Q'.C2_oneHalf` (= 3/4) in Lean and `Fraction(3, 4)` in
  Python, per the 2026-05-26 derivation and the downstream-impact
  table at the top of §1. Shape-location witness: §1.2 quotes from
  `_generated/pdf_text/` (SL.1 pass).*

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

**Status update (2026-07-24): the $5d - 4$ question is RESOLVED
(negative) by exact enumeration — see §3.3–§3.4. The formula matches
no natural plaquette-adjacency notion at any $d$; the $d = 4$ value 16
coincides with the non-coplanar edge-neighbor count $8(d-2)$ and only
there. `MU_PLAQUETTE_4D = 16` is downgraded from "widely cited but not
verified" to "UNSUPPORTED for the code-consumed counting statement".
The KP-consumed adjacency graph has max-degree exactly 20 at $d = 4$,
so the rigorous derivable constant is
`MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e` (§3.2). Disposition: the
**$20e$ default was adopted 2026-07-24** (see §3.4); 16 is retained
only as an explicitly-caveated literature-shape option.**

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
verification. *(Superseded 2026-07-24: §3.3 shows the formula cannot
be a plaquette-adjacency count at all; primary-source verification is
no longer the blocking question.)*

**Three honest options:**

1. **Keep `MU_PLAQUETTE_4D = 16` as a literature-shape value.** Mark
   it as such in the code provenance (currently does); refinement
   awaits direct access to Seiler 1982 (or equivalent) to verify
   the bound and possibly tighten.
2. **Use the site-bound $8e \approx 21.7$** as a fallback. ~~This is the
   [BrydgesFederbush1978] bound, which holds for site polymers and
   *a fortiori* for plaquette polymers (plaquettes have fewer neighbors
   than sites).~~ **The a-fortiori argument is invalid** (the 2026-05-25
   audit in §3.1 below shows plaquettes have *more* edge-neighbors than
   sites at d = 4: 20 vs 8). The 8e value is preserved in code under
   the historical name `MU_PLAQUETTE_CONSERVATIVE_4D` for backwards
   compatibility but is **not** a true BF-conservative bound on
   plaquette-polymer connectivity; it is the site bound, not transferred.
3. **Use the genuinely-BF-conservative $20e \approx 54.4$** (per §3.2
   below, landed 2026-05-25). The honest plaquette-polymer BF universal
   bound from a direct edge-neighbor count. Strictly looser than the
   literature 16 but truly conservative — derivable from first
   principles, no paper-specific argument required. Shifts canonical
   $g_{\max}^{\mathrm{lf}} \to 0.374$ (~12% reduction), with the SU(2)
   pilot still closing because the sf threshold (≈ 0.40) is binding.

*(Disposition 2026-07-24: option 3 adopted as the project default,
on the strength of the §3.3–§3.4 enumeration. Option 1 survives only
with an explicit "restricted-class, unverified" caveat; option 2
remains deprecated.)*

**All three are available in code** (as of 2026-05-25):

```python
from computations.large_field_kp import (
    MU_PLAQUETTE_4D,                     # 16.0, default literature-shape (option 1)
    MU_PLAQUETTE_CONSERVATIVE_4D,        # 8e ≈ 21.7, site-bound (option 2; not true BF-conservative)
    MU_PLAQUETTE_BF_CONSERVATIVE_4D,     # 20e ≈ 54.4, genuine BF-conservative (option 3)
    mu_plaquette_bf_conservative,        # parameterized helper for any d
    compute_large_field_kp,
)
kp_default  = compute_large_field_kp(g, mu_plaq=MU_PLAQUETTE_4D)
kp_site_alt = compute_large_field_kp(g, mu_plaq=MU_PLAQUETTE_CONSERVATIVE_4D)
kp_rigorous = compute_large_field_kp(g, mu_plaq=MU_PLAQUETTE_BF_CONSERVATIVE_4D)
```

*(Note 2026-07-24: the inline comment "default" above reflects the
pre-flip state; per the §3.4 disposition the adopted default is
`MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e`.)*

Sensitivity sweep: `computations/fiducial_sensitivity.py::sweep_mu_plaq`
(includes all three values in the default sweep).

**Refinement strategy.** Direct extraction from [Seiler1982 LNP 159]
of the plaquette-polymer connectivity bound for $d = 4$ (or any tighter
bound from later literature, e.g. for restricted polymer classes
in [DrouffeItzykson1978] / [ItzyksonDrouffe1989]). Refinement
*enlarges* the lf convergent regime. The shape of $K_{\mathrm{lf}}$
does not change. *(2026-07-24: any such extraction must now also
explain which restricted class or counting weight the $5d-4$ refers
to, since §3.3 rules out all unrestricted adjacency counts.)*

### 3.1. Direct edge-neighbor count — audit note (2026-05-25)

A first-principles attempt to derive $\mu_{\text{plaq}}$ at $d = 4$
in the same spirit as §5's $c_{\text{polymer}}$ derivation gives a
**looser** bound than either of the cited values. Recording the count
for audit transparency.

**Direct combinatorial count.** A 4D plaquette has 4 edges. For each
edge in direction $\mu$, the perpendicular directions are $\{x,y,z,w\}
\setminus \{\mu\}$ (3 choices); for each perpendicular direction $\nu$,
the edge sits in 2 plaquettes (the one extending in $+\nu$ and the one
in $-\nu$). So $3 \times 2 = 6$ plaquettes contain a given edge,
including the current plaquette, leaving 5 other plaquettes per edge.

Total edge-neighbors per plaquette:
$$
4 \text{ edges} \times 5 \text{ other plaquettes per edge} = 20.
$$

In general $d$-dim: edges have $d-1$ perpendicular directions × 2 sides
$= 2(d-1)$ plaquettes through them, minus the current = $2d - 3$ other
plaquettes per edge, $\times 4$ edges $= 8d - 12$ edge-neighbors per
plaquette. For $d = 4$: $20$; for $d = 3$: $12$; for $d = 2$: $4$.

**BF implication.** The Brydges–Federbush universal bound for connected
$n$-subgraphs of a max-degree-$\Delta$ graph through a fixed vertex is
$\le (e \Delta)^n$ (up to lower-order factors). With $\Delta = 20$:
$$
\mu_{\text{plaq, 4D, direct}} \;\le\; 20 \cdot e \;\approx\; 54.4.
$$
This is **strictly looser** than both:
- Seiler 1982's cited $5d - 4 = 16$ (which the direct count does not
  reproduce — Seiler must use a refinement specific to plaquette
  polymers beyond the BF universal bound).
- The project's conservative fallback $8e \approx 21.7$.

**Apparent issue with the 8e fallback's justification.** The note
above says "plaquette polymers have fewer neighbors than sites" as
the basis for the $8e$ fallback's a-fortiori claim. The direct count
gives plaquette degree $20$ vs site degree $2d = 8$ at $d = 4$ —
the *opposite* relation. Either the fallback's justification needs
re-derivation under a different mapping (e.g., centroid-of-plaquette
sublattice with a non-standard adjacency), or the fallback is not
genuinely a-fortiori from BF.

**Implication for the pilot.** Numerically, the pilot was already
using $\mu_{\text{plaq}} = 16$ as the default (literature-shape); the
$8e$ fallback was available as a "more conservative" option. The
audit shows:
- The literature value $16$ remains unverified from first principles,
  but is *tighter* than any value the project can directly derive.
- The conservative fallback $8e \approx 21.7$ is *less conservative*
  than the direct BF bound $20e \approx 54.4$, and the "a fortiori"
  justification for it is questionable.
- A genuinely-rigorous-from-direct-count default would be $\mu_{\text{plaq}}
  = 20 e$, which would substantially shrink the pilot's convergent
  window (canonical $g_{\max}^{\text{lf}} \to \sqrt{3/(4 \log 20 e)}
  \approx 0.33$, vs current $0.42$).

**Recommendation.** Keep $16$ as the default (Seiler-cited; the project
runs in this regime). Document the conservative fallback's justification
as pending re-derivation. Treat the direct count $20e$ as a verified
upper bound for sanity-checking — not as a default.
*(Superseded 2026-07-24: recommendation reversed by the §3.3–§3.4
enumeration; $20e$ adopted as default.)*

**Code exposure (2026-05-25).** `computations/large_field_kp.py` now
provides `plaquette_edge_neighbor_count(d) → 8d - 12` as the direct
combinatorial count.

**Primary-source confirmation of the per-edge count (PDF audit 2026-05-25).**
[BrydgesFroehlichSeiler1978IHES] (PDF in `docs/pdf_references/`),
Section 4 eq.~(4.24), states explicitly:

> "Given a bond $\langle x, y \rangle$, there are $2(\nu - 1)$
> plaquettes, $P_1, P'_1, \ldots, P_{\nu-1}, P'_{\nu-1}$ with
> $\langle x, y \rangle$ as a common bond and such that $P_i$ and
> $P'_i$ are in the same plane, $i = 1, \ldots, \nu - 1$."

(BFS uses $\nu$ for the lattice dimension; we use $d$.) For $d = 4$,
$2(d-1) = 6$ plaquettes share a given bond, INCLUDING the current
plaquette in the same plane (counted in the $P_i / P'_i$ pairing).
Per-edge other-plaquette count: $2(d-1) - 1 = 2d - 3 = 5$ at $d = 4$.
Total edge-neighbors per plaquette: $4 \cdot (2d - 3) = 8d - 12 = 20$
at $d = 4$. ✓ Direct confirmation of `plaquette_edge_neighbor_count(4) = 20`.

**What the audit does NOT confirm.** The Seiler 1982 $5d - 4 = 16$
plaquette-polymer **connectivity constant** is NOT in the BFS PDF
(which deals with diamagnetic inequalities and bond-level
combinatorics, not aggregate polymer counts). The original 5d-4
formula remains pending verification against [Seiler1982] LNP 159
(not in the project's PDF collection). The
$\mu_{\text{plaq}}^{\text{BF}} = e(8d - 12) = 20e$ direct-from-BFS
fallback (§3.2) is rigorously derivable from this confirmed
per-bond count alone.

### 3.2. Genuinely-BF-conservative fallback `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e` (2026-05-25)

Building on the §3.1 audit: the project now exposes a
**genuinely-BF-conservative** plaquette-polymer connectivity bound,
replacing the (incorrectly-justified) `MU_PLAQUETTE_CONSERVATIVE_4D = 8e`
as the project's preferred rigorous-fallback option.

**Derivation.** The Brydges–Federbush universal bound:

> For polymer activities $|a(X)| \le e^{-\rho|X|}$ on a graph with
> max-degree $\Delta$, the cluster-expansion sum
> $\sum_{X \ni p_0} |a(X)| e^{\rho |X|}$ converges iff $\rho > \log(e
> \cdot \Delta)$. Equivalently, the polymer-counting "connectivity
> constant" satisfies $\mu \le e \cdot \Delta$.

(Brydges 1986 Les Houches lecture notes, §IV; Glimm–Jaffe 1987 §18.5.)

Applied directly to the **plaquette-edge-adjacency** graph at dimension
$d$, with $\Delta = $ `plaquette_edge_neighbor_count(d) = 8d - 12` from
§3.1:

$$
\boxed{\quad \mu_{\text{plaq}}^{\text{BF}}(d) \;=\; e \cdot (8d - 12). \quad}
$$

For $d = 4$: $\mu_{\text{plaq}}^{\text{BF}}(4) = 20 e \approx 54.366$.

**Why this is genuinely-conservative.** Unlike the site-bound transfer
attempt (the 8e false-conservative claim refuted in §3.1), this
derivation:

  - Applies the BF universal bound directly to the plaquette-polymer
    graph, not via a transfer from another lattice.
  - Uses the actual plaquette edge-degree $20$, derivable from a direct
    combinatorial count (no paper-specific argument).
  - Is rigorously an upper bound (BF is a theorem; the only assumption
    is the convergent regime, which holds wherever the project uses
    the cluster expansion).

**Why this is loose.** $20 e \approx 54.4$ is strictly greater than
both:

  - Seiler's literature $5d - 4 = 16$ (which requires a refinement
    beyond the BF universal bound — likely exploiting planarity or
    lattice structure specific to plaquette-polymers; not derivable
    from first principles here).
  - The deprecated $8e \approx 21.7$ site-bound (which is the
    *site*-polymer BF bound, not the plaquette one).

So the genuine-conservative bound costs pilot window: canonical
$g_{\max}^{\text{lf}}$ drops from $0.4245$ (literature 16) to $0.3733$
(BF 20e), a ~12% reduction.

**Pilot impact.** The SU(2) pilot's small-field window is binding at
canonical $g_{\max}^{\text{sf}} \approx 0.40$, so the lf-window
shrinkage from 0.4245 → 0.3733 is largely inactive for the canonical
$g_0 = 0.30$ wire-in. The pilot still closes; the BF-conservative
default is essentially free at the wire-in operating point.

**Recommendation.** Use `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e` when:

  - You need a genuinely-rigorous upper bound (audit margin, paper
    draft's "we can also defend $\mu = 20e$" footnote).
  - The pilot's lf-window margin matters and you want the honest
    cost figure.

Use `MU_PLAQUETTE_4D = 16` (default) when:

  - You're working in the literature-shape regime and willing to cite
    Seiler 1982 for the unverified $5d - 4$ count.

Avoid `MU_PLAQUETTE_CONSERVATIVE_4D = 8e` for new code: it's preserved
as a backwards-compat alias but its "conservative for plaquettes"
justification is invalid.

*(2026-07-24: the first recommendation is now the adopted default;
the second survives only with the "restricted-class, unverified"
caveat of §3.4.)*

**Generalizes to arbitrary $d$.** The helper `mu_plaquette_bf_conservative(d)`
returns `e · (8d - 12)` for any $d \ge 2$:

  - $d = 2$: $4 e \approx 10.87$
  - $d = 3$: $12 e \approx 32.62$
  - $d = 4$: $20 e \approx 54.37$
  - $d = 5$: $28 e \approx 76.11$

### 3.3. Exact enumeration of all adjacency notions — the $5d-4$ formula RESOLVED negative (SL.1, 2026-07-24)

`computations/plaquette_connectivity.py` (developed in the 2026-07-24
SL.1 pass as `sl1/plaquette_connectivity.py`, pinned by the 15 tests of
`sl1/test_plaquette_connectivity.py`) enumerates, in exact integer
arithmetic with a provable bounding-box exhaustiveness certificate
(base coordinates of any vertex-sharing plaquette lie in {−1, 0, 1};
the scan runs over [−2, 2]^d and asserts no qualifier touches the
boundary), every plaquette of every orientation adjacent to a fixed
unit xy-plaquette P₀ at the origin:

| notion                              | d=2 | d=3 | d=4 | d=5 | exact formula |
| ---                                 | --- | --- | --- | --- | ---           |
| share ≥ 1 edge                      | 4   | 12  | 20  | 28  | 8d − 12       |
| … coplanar                          | 4   | 4   | 4   | 4   | 4             |
| … non-coplanar                      | 0   | 8   | 16  | 24  | 8(d − 2)      |
| share ≥ 1 vertex                    | 8   | 32  | 72  | 128 | 8(d − 1)²     |
| … vertex-only (no edge)             | 4   | 20  | 52  | 100 | 8d² − 24d + 20 |
| ≥ 2 shared vertices without an edge | 0   | 0   | 0   | 0   | 0             |
| plaquettes containing a fixed bond  | 2   | 4   | 6   | 8   | 2(d − 1) ✓ BFS (4.24) |
| plaquettes containing a fixed vertex| 4   | 12  | 24  | 40  | 2d(d − 1)     |
| **formula 5d − 4 (Seiler-cited)**   | 6   | 11  | 16  | 21  | —             |

Formula-in-d proofs (three-point exact polynomial fits, verified at a
fourth d where the count is defined): an edge in direction μ lies in
2(d−1) plaquettes (one per perpendicular direction and side; BFS 1978
eq. (4.24), already confirmed in §3.1), so each of P₀'s 4 edges
contributes 2(d−1) − 1 = 2d − 3 other plaquettes, all distinct across
edges: 4(2d − 3) = 8d − 12.  Of these, exactly one per edge is coplanar
(the reflected square), giving 4 and 8d − 16 = 8(d − 2) for the split.
For vertex-sharing: 2d(d−1) plaquettes contain a given vertex (choose
the plane, C(d,2) ways, and the quadrant, 4 ways); inclusion–exclusion
over P₀'s 4 vertices (no plaquette shares ≥ 2 vertices with P₀ without
sharing an edge — enumerated 0 in all d) gives 8(d−1)².

**Conclusion 1 — the 5d − 4 formula matches NO adjacency notion at any
d.**  The single numerical agreement is at d = 4, where 5d − 4 = 16
coincides with the non-coplanar edge-neighbor count 8(d − 2) — and only
there (d = 3: 8 vs 11; d = 5: 24 vs 21).  A coincidence, not a formula.

### 3.4. The code-consumed counting statement, tested directly (SL.1, 2026-07-24)

What `computations/large_field_kp.py` actually consumes (via
K_lf = q/(1−q), q = μ_plaq·Z_t) is

    N_n(P₀) := #{edge-connected plaquette polymers X, |X| = n, P₀ ∈ X}
             ≤ μ_plaq^n.

Exact enumeration of N_n (same module, duplicate-free connected-subgraph
enumeration):

| d = 4 | N_n     | N_n / N_{n−1} | 16^n      | N_n ≤ 16^n |
| ---   | ---     | ---           | ---       | ---        |
| n = 1 | 1       | —             | 16        | OK         |
| n = 2 | 20      | 20.0          | 256       | OK         |
| n = 3 | 458     | 22.9          | 4096      | OK         |
| n = 4 | 11 132  | 24.3          | 65 536    | OK         |
| n = 5 | 280 175 | 25.2          | 1 048 576 | OK         |

(d = 3: N_n = 1, 12, 158, 2148, 29685; ratios 12.0 → 13.8.)

**Conclusion 2 — 16 holds for n ≤ 5 but is not asymptotically
defensible.**  The one-step growth ratios exceed 16 from n = 2 onward
and increase monotonically (20.0, 22.9, 24.3, 25.2 → the animal growth
constant λ from below).  Unless growth saturates below 16 — implausible
given the monotone ratios and the degree-20 graph — N_n ≤ 16^n fails at
some finite n (naive extrapolation at ratio ≈ 25.5: first violation
near n ≈ 8).  This is evidence, not a theorem: the enumerated n ≤ 5
give a rigorous λ lower bound of only (N_5/5)^{1/5} ≈ 8.9.  What IS a
theorem is: (i) 5d − 4 counts none of the natural adjacency notions,
and (ii) the code-consumed graph has max-degree exactly 20, so the
rigorous derivable constant is `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e`
(§3.2), unchanged.

**Disposition (2026-07-24): 20e default adopted.**  If Seiler's LNP 159
(still not in the corpus; not openly accessible) proves a 5d − 4 bound,
it must concern a restricted polymer class or a different counting
weight, not the unrestricted N_n above.  Accordingly the code default
flips to `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e`; 16 is retained only
with an explicit "restricted-class, unverified" caveat.  Downstream
touch-points of `MU_PLAQUETTE_4D` (grep 2026-07-24):
`compute_large_field_kp` / `eps_lf` / `first_few_rg_steps` /
`convergence_threshold_g_lf` defaults in
`computations/large_field_kp.py`; the `mu_plaq` parameter of
`sigma_hat_trajectory`; `fiducial_sensitivity.sweep_mu_plaq` and
`max_g0_closure`.  Cost of the flip (already measured in §3.2):
canonical g_max^lf 0.4245 → 0.3733 (≈ −12%); pilot closure at the
canonical g₀ = 0.30 wire-in unchanged (sf window ≈ 0.40/0.49 binding).

**Citations.**
- TeX: `\cite{Seiler1982,DrouffeItzykson1978,ItzyksonDrouffe1989}`
- Lean: not currently a Lean constant; if needed, encode as a `Q'` or
  `Nat` (since $16 \in \mathbb{N}$, this is trivial).
- Python: `computations.large_field_kp.MU_PLAQUETTE_4D` (float = 16.0).
- *Addendum 2026-07-24:*
  - *Enumeration witness: `computations/plaquette_connectivity.py`
    (SL.1; developed as `sl1/plaquette_connectivity.py` with 15 pinned
    tests in `sl1/test_plaquette_connectivity.py`).*
  - *Per-bond count: [BrydgesFroehlichSeiler1978IHES] eq. (4.24)
    (unchanged, ✓).*
  - *5d − 4 attribution: [Seiler1982] LNP 159 — cited-but-unverified,
    now additionally shown incompatible with every natural adjacency
    count; a 2026-07-24 web pass again surfaced no verbatim statement.*
  - *Adopted default: `computations.large_field_kp.MU_PLAQUETTE_BF_CONSERVATIVE_4D`
    (= 20e), per the §3.4 disposition.*

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

**Status update (2026-07-24/25): DERIVED (project-internal
triangle-inequality channel count, unchanged). The literature
shape-source citation [Balaban1988convergent] (CMP 119) is demoted to
"motivating, not supplying": the SL.1 reconnaissance (2026-07-24) and
the follow-up open-access retrieval pass (2026-07-25) established that
the constant cannot currently be extracted from any locally held or
openly accessible primary source. Precise-null record in §5.1.**

**Status update (2026-07-25, later pass): DERIVED (internal,
unchanged) + SHAPE-CONFIRMED at quote level. CMP 119 was unblocked by
a human fetch and read in full; the "motivating, not supplying"
demotion is partially reversed — the paper genuinely carries the
difference-of-polymer-terms shape and the factor-2 triangle device
(explicitly, p. 283), so the shape citation is upgraded back to
quote-level. What it does NOT carry is the repo's cross-scale
(k → k+1) residual inequality or any numeric for it; the constant 2.0
remains internally derived. Full extraction record in §5.2.**

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

**PDF audit 2026-05-25.** Neither [Balaban1988RG-II] CMP 116
(Part II) nor [BrydgesFroehlichSeiler1978IHES] contains a
sign-preservation lemma of the form needed for the $c_{\text{polymer}}
= 1$ tightening. CMP 116's cluster-expansion bounds carry absolute
values throughout (e.g., eq.~1.36: $|V_i(y, U, J, B)| \le B_0 e^{C_1 M}
\exp(C_2 \kappa_1) \exp(-(1 - 2\delta) \kappa d_t(y))$); the argument
does not invoke sign-preservation. The conjectured $c_{\text{polymer}}
= 1$ tightening remains a project-level open analytic target, not a
direct extraction.

The historical match $2/4 = 1/2$ with the previous placeholder is now
**coincidence** rather than design: the placeholder was 1/2, and the
independently-derived worst-case happens to equal 1/2 with the
spec-mandated $A_{\min} = 4$.

### 5.1. CMP 119 / CMP 122 extraction reconnaissance — precise null (SL.1 2026-07-24, retrieval pass 2026-07-25)

**Reconnaissance record.**

1. **CMP 119 (1988) 243–285 is absent from the local corpus** —
   `docs/pdf_references/` contains CMP 102, CMP 109, CMP 116 (see the
   file-identity correction in the Honest framing), BFS-IHES, the Clay
   statement, and Jørgensen; no CMP 119.  Bibliographic identity
   confirmed externally: T. Bałaban, "Convergent renormalization
   expansions for lattice gauge theories", Commun. Math. Phys. 119
   (1988) 243–285, DOI 10.1007/BF01217741.  Full text is
   subscription-gated at Springer; the Project Euclid open archive is
   bot-walled (Incapsula) from this container, so no legitimate open
   extraction path was available.

2. **CMP 116 (present) supplies no numerical residual factor.**  Its
   cluster-expansion bounds carry named-but-unpinned absolute
   constants and inequality-linked rates, e.g. (quotes from
   `_generated/pdf_text/Renormalization Group Approach to Lattice
   Gauge Field Theories.txt` — the file that actually contains CMP 116;
   pp. 9–10 of CMP 116):

   > "exp(−(1 − δ)κ d_k(Y) − δκ d_j(X)),  (1.32)  if
   > ½(κ₁ − 1) ≥ (1 − δ)κ, 0 < δ < 1."

   > "**Lemma 1.** […] There exist absolute constants C₁, C₂, q, for
   > which |V′_k(Y, U, J, B)| ≤ B₀ ε₁ C₁ M^q exp(C₂κ₁)
   > exp(−(1 − 2δ)κ d_k(Y)).  (1.36)"

   plus the further ordering assumption "(1/8)κ₁ ≥ (1 − 2δ)κ" (p. 9;
   OCR partially garbled, consistent with the 2026-05-25 audit's
   reading of the same constraint).  Everything is existence-only; no
   factor-2 (or any numeric) per-polymer residual appears.

3. **Dedicated open-access retrieval pass (2026-07-25) — precise null
   upheld and strengthened.**  Full log in
   `notes/cmp119_extraction.md`.  Summary:
   - **Exact identities pinned** (Springer DOI pages): CMP 119 as
     above; the companions are T. Bałaban, "Large field
     renormalization. I. The basic step of the ℝ operation", Commun.
     Math. Phys. **122** (1989) 175–202, DOI 10.1007/BF01257412, and
     "Large field renormalization. II. Localization, exponentiation,
     and bounds for the R operation", Commun. Math. Phys. **122**
     (1989) 355–392, DOI 10.1007/BF01238433.
   - The **direct Project Euclid open-archive PDF URL for CMP 119 was
     located** (`euclid.cmp/1104162401`, via the crawlable search
     index) but returns an Incapsula bot-challenge instead of the PDF;
     the issue TOC page fails the same way.  Wayback-Machine copies
     are proxy-blocked (HTTP 403 at the agent proxy);
     api.fatcat.wiki timed out; scholar.archive.org rate-limited;
     GDZ/DigiZeitschriften shows **no CMP holdings at all** (dead end,
     not merely blocked).  Springer pages are reachable but
     subscription-gated (USD 39.95/PDF).
   - Abstract-level content (Springer): CMP 119 introduces "an
     inductive description of the complete effective densities
     including large field domains" and yields convergent expansions
     for superrenormalizable models; CMP 122-I constructs the
     large-field ℝ operation; CMP 122-II supplies its localization,
     exponentiation, and bounds, completing the UV-stability proof
     (its Theorem 1).  Nothing at abstract level asserts a numeric
     residual constant.
   - Dimock's open-access review series "The Renormalization Group
     According to Balaban" (arXiv 1108.1335 / 1212.5562 / 1304.0705)
     treats the scalar φ⁴ model in d = 3 as an expository
     reconstruction of the *method* — it is not a source for the
     gauge-theory residual constants.

4. **Consequence.**  The constant 2.0 continues to rest entirely on the
   project-internal derivation of §5 (triangle inequality on the
   per-polymer activity change under T_b; channel multiplicity 2;
   optimal worst-case absent a sign-preservation lemma).  What
   extraction WOULD require: CMP 119 §§ on the R-operation /
   large-field–small-field recombination (pages 243–285), plus its
   companions CMP 122 I/II (175–202, 355–392), under matched
   conventions — with the realistic expectation, given the uniform
   pattern of Theorems 1–3 (CMP 109) and Lemma 1 (CMP 116) and the
   qualitative framing of the CMP 122 abstracts, that those papers
   also supply existence-constants only, in which case the internal
   derivation remains the strongest available provenance.  Concrete
   unblock: a human fetch of the Euclid PDF from a normal browser (the
   archive is genuinely open access), or institutional Springer access
   for the three DOIs, followed by a rerun of the extraction hunt
   against `_generated/pdf_text/`.

### 5.2. CMP 119 read in full — SHAPE-CONFIRMED, constant unpinned (2026-07-25, unblocked)

**Unblock and provenance.** A human fetch from the Project Euclid
issue page landed
`docs/pdf_references/communications-in-mathematical-physics_volume-119_issue-2.pdf`
— which turned out to be the issue **front matter only** (2 pages;
Euclid's issue-level link is the "Miscellaneous front pages"
document).  The article itself (pp. 243–285) was then extracted via an
in-memory fetch+OCR-layer read executed on the user's machine (whose
residential egress passes the bot wall; nothing was written to the
Mac).  Complete quote-level record with OCR-faithful displays:
`notes/cmp119_extraction.md` §5; full text archived as
`cmp119_fulltext.txt` alongside it.  Identity confirmed from the text
(header "Commun. Math. Phys. 119, 243-285 (1988)"; references [I] =
CMP 109, [II] = CMP 116; communicated by A. Jaffe).

**What CMP 119 supplies for this fiducial (hunt results).**

1. **The shape is really there.**  "The basic expression to analyze,
   either in the proof of Theorem 2, or in the analysis of
   renormalization, is the difference E^(j)(Λ_j, U_k, z) −
   E^(j)(Λ_j, 1, z)" (p. 279) — a difference of polymer-localized
   cluster-expansion terms, bounded polymer-by-polymer.
2. **The factor-2 two-channel triangle device appears explicitly**
   (p. 283, second proof of Theorem 2): the difference over polymers
   in the far class "can be estimated by 2E₀ exp(−(1/2)κ[·−j])
   exp(−(1/2)κ d_j(X))" — i.e., |A − B| ≤ 2·(single-activity bound),
   Bałaban's own use of the same device that yields the project's
   channel multiplicity 2.  **Scope caveat:** his difference compares
   two background *configurations* (U_k vs 1) at fixed scale j; the
   project's residual compares scales k and k+1 under block-spin
   transport.  Same device and constant, different inequality
   instance — so the 2.0 stays internally derived, now with
   primary-source precedent.
3. **Exactly one pinned numeric in a main bound:** Theorem 2, p. 263 —
   "there exists an absolute constant R₁ such that [(2.44)] … (In
   fact the constant R₁ can be taken as equal to 1 for g_j
   sufficiently small.)"  All other constants are the familiar
   existence chain: Theorem 1 ("There exist constants … numerous
   restrictions introduced in the proof"), E₁ of (2.43) ("grows to ∞
   if β → 1"), B₀ of (2.42), E₀ of (1.1.18)/(3.48), E₋/E₊ of
   Corollary 3 (UV stability), B₀ → O(p_k²(g_k)) after one step
   (p. 278).  Proof-device numerics only: β = 1/4 ("e.g., we can
   take"), (1+4β)κ, the boundary ratio 2^{−(j−1−n)}, powers of 1/2 in
   (2.36)–(2.39), and the ½κ rate-splits.
4. **The R-operation is deferred:** "The operation R serves this
   purpose.  We will not describe it here, we will only assume that
   it has some properties…" (p. 244); its construction is "given in
   the next paper" (p. 260–261) — i.e., CMP 122 I/II, still not held.
   The residual's natural primary-source home therefore remains
   unread; extraction frontier unchanged.
5. **No sign-preservation lemma** appears (differences handled by
   absolute values and the factor-2 split throughout) — the
   c_polymer = 1 tightening stays a project-level open target.

**Net effect.**  §5's constant and derivation are unchanged; the shape
citation [Balaban1988convergent] is upgraded from "motivating, not
supplying" (§5.1) to **quote-level SHAPE-CONFIRMED** (pp. 279, 280,
283; displays (2.43), (2.44), (3.48), (3.67)).  The 2026-07-25-morning
prediction in §5.1(4) — "those papers also supply existence-constants
only" — is confirmed verbatim for CMP 119, modulo the single pinned
R₁ = 1.

**Citations.**
- TeX: `\cite{Balaban1988convergent,BrydgesFederbush1978}`
- Lean (planned quantitative closure): import
  `YMGap.Constructive.Rationals`, use `Q'.ofNat 2`.
- Python: `computations.sigma_hat_trajectory.BALABAN_POLYMER_RESIDUAL`.
- *Addendum 2026-07-24/25: mark `\cite{Balaban1988convergent}` as
  *shape/motivation only*; the constant's provenance citation is
  `notes/sigma-hat-derivation.md` §2.3-derivation. Retrieval log:
  `notes/cmp119_extraction.md`.*
- *Addendum 2026-07-25 (later pass): supersedes the previous line's
  demotion — cite `\cite{Balaban1988convergent}` as the quote-level
  SHAPE source (pp. 279/283, displays (2.43)/(2.44)/(3.48)/(3.67));
  the NUMERIC provenance citation remains
  `notes/sigma-hat-derivation.md` §2.3-derivation. Extraction record:
  `notes/cmp119_extraction.md` §5.*

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

*(Table rows updated 2026-07-25 to reflect the current wire-ins; the
superseded row contents are quoted in the dated note below the table,
so no history is lost.)*

| Constant | Value | Status | Refine? | Sweep entry point |
| --- | --- | --- | --- | --- |
| `BAŁABAN_SPECTRAL_GAP_COEFF` | 3/4 | DERIVED (SU(2) Casimir $C_2(1/2)$, 2026-05-26); historical 1/2 SHAPE-LOCATED to CMP 109 eq. (0.27) rate-split (2026-07-24); primary sources numerical-value-free (quote-confirmed); pilot-tolerance lower bound 0.289 at canonical wire-in (§1.1) | further refinement requires Gribov-patch / atlas analytics, not paper extraction (§1.2) | `fiducial_sensitivity.sweep_spectral_gap_coeff`, `c_lambda_pilot_tolerance_threshold` |
| `MU_CONNECTIVITY_4D` | log(8e) | literature formula | already standard | — |
| `MU_PLAQUETTE_4D` | 16 (option only; **default now `20e`**, adopted 2026-07-24) | **RESOLVED-negative for 5d−4 (2026-07-24)**: matches no adjacency notion at any d; d = 4 agreement with 8(d−2) = 16 coincidental; N_n ≤ 16^n verified only for n ≤ 5 with growth ratios already > 16; rigorous default `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e` (§3.3–§3.4) | only via a restricted-class extraction from Seiler LNP 159 (still inaccessible) | `fiducial_sensitivity.sweep_mu_plaq` |
| `J_MAX_DEFAULT` | 12 | engineering | only if needed | — |
| `BALABAN_POLYMER_RESIDUAL` | 2.0 | **DERIVED 2026-05-25** (internal triangle-inequality, unchanged); CMP 119 read in full 2026-07-25: **SHAPE-CONFIRMED, constant unpinned** — factor-2 triangle device located at quote level (p. 283) but for a fixed-scale configuration-difference, not the cross-scale residual; only pinned numeric is R₁ = 1 in (2.44); R-operation deferred to CMP 122 (still unheld) (§5.2) | tighter c=1 via sign-preservation lemma (open); or CMP 122 I/II extraction (R-operation construction) | `fiducial_sensitivity.sweep_polymer_residual` |
| `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` | 4 | from project spec | n/a | — |
| Trajectory defaults | various | engineering | n/a | — |

> **Dated note (2026-07-25) — superseded row contents, for the audit
> trail.** Before this update the table's `BAŁABAN_SPECTRAL_GAP_COEFF`
> row still read "1/2 — literature-shape fiducial; pilot-tolerance
> lower bound 0.289 at canonical wire-in (§1.1) — refinement requires
> Bałaban paper extraction". That row was stale on two counts: (i) the
> value had been 3/4 since the 2026-05-26 Casimir derivation recorded
> at the top of §1 (the table was simply never updated); (ii) the
> "refinement requires Bałaban paper extraction" pointer is obsolete —
> §1.2 shows at quote level that the papers contain no extractable
> number (the 1/2 in CMP 109 (0.27) is a rate-split proof device).
> The `MU_PLAQUETTE_4D` row previously read "16 — literature-shape
> (5d-4)" with the 20e fallback listed as refinement; superseded by
> the §3.3–§3.4 resolution and the 2026-07-24 default flip. The
> `BALABAN_POLYMER_RESIDUAL` row previously cited only the 2026-05-25
> derivation; the precise-null extraction record (§5.1) is appended.
> *(Second update, 2026-07-25 later pass: that row's "precise null"
> was superseded same-day by the completed CMP 119 extraction —
> SHAPE-CONFIRMED, constant unpinned; see §5.2.)*

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

> **Dated supersession of the flagged-value bookkeeping (2026-07-25).**
> The three numbered items above are the 2026-05-25 state, retained
> verbatim for the audit trail. Current state:
> 1. **No HEURISTIC value remains.** `BAŁABAN_SPECTRAL_GAP_COEFF` is
>    3/4, DERIVED (Casimir, 2026-05-26), with the historical 1/2
>    SHAPE-LOCATED to CMP 109 eq. (0.27) (2026-07-24, §1.2).
> 2. The "widely cited but not directly verified" flag on
>    `MU_PLAQUETTE_4D = 16` is superseded by **RESOLVED-negative**
>    (2026-07-24, §3.3): 5d−4 is not a plaquette-adjacency count.
>    Default flipped to `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e`; note
>    also that item 2's "−0.2%" figure referred to the deprecated 8e
>    fallback, whereas the adopted 20e default costs ≈ −12% of the lf
>    window — inactive at the canonical wire-in (sf-binding, §3.4).
> 3. `BALABAN_POLYMER_RESIDUAL = 2.0` unchanged (DERIVED, internal);
>    literature extraction attempt closed as a precise null (§5.1,
>    `notes/cmp119_extraction.md`) — then reopened and completed the
>    same day after a human unblock: CMP 119 read in full,
>    **SHAPE-CONFIRMED at quote level, constant unpinned** (§5.2);
>    the remaining extraction frontier is CMP 122 I/II.

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

  *(Dated note 2026-07-25: the sample table above predates the
  2026-05-26 c_λ = 3/4 wire-in and the 2026-07-24 μ_plaq = 20e default
  flip; rerun `max_g0_closure` for current figures. The qualitative
  conclusion — sf-fiducial-dominated pilot window — is unchanged, per
  the §3.4 cost measurement.)*

---

## Bibliography (mirror of `formal/references.bib`)

| Key | Paper / Book |
| --- | --- |
| `Balaban1987RG-I` | Bałaban, "RG approach to lattice gauge field theories. I", CMP 109 (1987), 249–301. |
| `Balaban1988RG-II` | Bałaban, "RG approach to lattice gauge field theories. II. Cluster expansions", CMP 116 (1988), 1–22. |
| `Balaban1988convergent` | Bałaban, "Convergent renormalization expansions for lattice gauge theories", CMP 119 (1988), 243–285. DOI 10.1007/BF01217741; Project Euclid `euclid.cmp/1104162401`. *(2026-07-25: read in full after human unblock — quote-level SHAPE source for §5, constant unpinned; see §5.2 and `notes/cmp119_extraction.md` §5. NB the corpus file `communications-in-mathematical-physics_volume-119_issue-2.pdf` is front matter only; the article PDF still needs to be added.)* |
| `Balaban1989LargeField-I` | Bałaban, "Large field renormalization. I. The basic step of the ℝ operation", CMP 122 (1989), 175–202. DOI 10.1007/BF01257412. *(Added 2026-07-25; identity confirmed via Springer; not locally held.)* |
| `Balaban1989LargeField-II` | Bałaban, "Large field renormalization. II. Localization, exponentiation, and bounds for the R operation", CMP 122 (1989), 355–392. DOI 10.1007/BF01238433. *(Added 2026-07-25; identity confirmed via Springer; not locally held.)* |
| `BrydgesFederbush1978` | Brydges & Federbush, "A new form of the Mayer expansion...", JMP 19 (1978), 2064–2067. |
| `Seiler1982` | Seiler, *Gauge Theories as a Problem of Constructive QFT...*, LNP 159, Springer 1982. |
| `DrouffeItzykson1978` | Drouffe & Itzykson, "Lattice gauge fields", Phys. Rep. 38 (1978), 133–175. |
| `ItzyksonDrouffe1989` | Itzykson & Drouffe, *Statistical Field Theory* (Vol. 1 & 2), Cambridge 1989. |
| `Cammarota1982` | Cammarota, "Decay of correlations for infinite range interactions in unbounded spin systems", CMP 85 (1982), 517–528. |
| `GlimmJaffe1987` | Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed.), Springer 1987. |

> **Corpus filename caveat (2026-07-24).** In `docs/pdf_references/`,
> the file `Balaban 116.pdf` contains `Balaban1987RG-I` (CMP 109) and
> `Renormalization Group Approach to Lattice Gauge Field Theories.pdf`
> contains `Balaban1988RG-II` (CMP 116); see the Honest framing for
> the full correction.
