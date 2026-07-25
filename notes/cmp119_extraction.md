# CMP 119 / CMP 122 Open-Access Retrieval + Residual-Extraction Attempt

> **SUPERSEDED SAME-DAY (2026-07-25, later pass): the null was unblocked
> by a human fetch and the CMP 119 extraction is now COMPLETE — see §5
> below. Verdict: SHAPE-CONFIRMED, constant unpinned.** §§1–4 are the
> morning retrieval-null record, retained unchanged as history.

**Date:** 2026-07-25 (extends the 2026-07-24 SL.1 reconnaissance).
**Goal:** obtain readable body text of Bałaban's CMP 119 and CMP 122 papers
from legitimate open archives and extract, at quote level, any numeric
per-polymer / large-field residual constant matching the shape the repo
codes as `BALABAN_POLYMER_RESIDUAL = 2.0`
(`computations/sigma_hat_trajectory.py`).
**Result: PRECISE NULL for body text; bibliographic identities and
abstracts pinned; no numeric residual extracted; no constants invented.**

---

## 1. Target identities (confirmed 2026-07-25, Springer DOI pages)

| Paper | Exact title | Ref | DOI | Euclid ID |
| --- | --- | --- | --- | --- |
| CMP 119 | "Convergent renormalization expansions for lattice gauge theories" | Commun. Math. Phys. **119** (1988) 243–285 | 10.1007/BF01217741 | `euclid.cmp/1104162401` |
| CMP 122-I | "Large field renormalization. I. The basic step of the ℝ operation" | Commun. Math. Phys. **122** (1989) 175–202 | 10.1007/BF01257412 | (not resolved; article page walled) |
| CMP 122-II | "Large field renormalization. II. Localization, exponentiation, and bounds for the R operation" | Commun. Math. Phys. **122** (1989) 355–392 | 10.1007/BF01238433 | (not resolved; article page walled) |

The CMP 122 page ranges match the 2026-07-24 draft's expectation
(175–202 and 355–392) exactly. The Euclid identifier for CMP 119 was
newly located this pass via the Project Euclid search index (which is
crawlable even though the site itself is bot-walled); for reference,
CMP 116 part II is `euclid.cmp/1104161193` in the same archive.

## 2. Retrieval log (every URL tried, with failure mode)

All fetches via the sanctioned WebSearch/WebFetch path (no bash/python
fetching). Agent-proxy egress.

| # | URL | Outcome |
| --- | --- | --- |
| 1 | `https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-119/issue-2` | Incapsula bot-challenge page returned instead of the issue TOC. |
| 2 | `https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-119/issue-2/Convergent-renormalization-expansions-for-lattice-gauge-theories/cmp/1104162401.pdf` | **Direct open-archive PDF URL located** (via search index) — but the fetch returns the Incapsula challenge, not the PDF. The open archive exists; it is bot-walled from this egress. |
| 3 | `https://web.archive.org/web/2024/<URL #2>` | Agent proxy rejected: HTTP 403 (PROXY_REJECTED — web.archive.org blocked at the proxy, not by the target). |
| 4 | `https://web.archive.org/web/2020id_/https://projecteuclid.org/download/pdf_1/euclid.cmp/1104162401` | Same: proxy HTTP 403. |
| 5 | `https://api.fatcat.wiki/v0/release/lookup?doi=10.1007/bf01217741&expand=files` | robots.txt fetch ConnectTimeout (unreachable). |
| 6 | `https://scholar.archive.org/search?q="Convergent renormalization expansions for lattice gauge theories"` | Rate-limit page ("You've reached the limit…"); no bibliographic content returned. |
| 7 | `https://gdz.sub.uni-goettingen.de/gcs/search?q=Communications+in+Mathematical+Physics` | 404. |
| 8 | `https://www.digizeitschriften.de/en/search?facets[collection][0]=Communications+in+Mathematical+Physics` | 404. WebSearch surfaced **no evidence that GDZ/DigiZeitschriften holds CMP at all** — CMP's open backfile lives at Project Euclid only. GDZ fallback: dead end, not merely blocked. |
| 9 | `https://link.springer.com/article/10.1007/BF01217741` | Reachable. Metadata + abstract retrieved. Full text subscription-gated (USD 39.95/PDF). |
| 10 | `https://link.springer.com/article/10.1007/BF01257412` | Reachable. Metadata + abstract retrieved. Gated. |
| 11 | `https://link.springer.com/article/10.1007/BF01238433` | Reachable. Metadata + abstract retrieved. Gated. |
| 12 | `https://ar5iv.arxiv.org/html/1304.0705` and `https://arxiv.org/abs/1304.0705` (Dimock, "The Renormalization Group According to Balaban", part III) | Openly readable — but the series treats the **scalar φ⁴ model in d = 3** as an expository reconstruction of Balaban's *method*, not the gauge-theory papers CMP 119/122. No gauge-theory residual constants available there. |

## 3. What WAS obtained (abstract-level, via Springer pages)

As relayed by the fetch pipeline (summaries of the Springer abstract
pages, not verbatim journal text):

- **CMP 119** introduces "an inductive description of the complete
  effective densities including large field domains," shows the
  renormalization transformations preserve that density structure, and
  completes the RG analysis **for superrenormalizable models**, giving
  convergent expansions in those cases.
- **CMP 122-I** constructs the large-field renormalization operation ℝ,
  which "removes the main obstacle to prove the ultraviolet stability
  of four-dimensional gauge field theories," with the complete proof
  deferred to a subsequent paper.
- **CMP 122-II** completes the properties of and bounds for the R
  operation, enabling the UV-stability proof stated as its Theorem 1.

Nothing at abstract level asserts a numeric per-polymer residual or a
channel-multiplicity constant.

## 4. Extraction verdict

**No quote-level extraction of a polymer/large-field residual factor
was possible: the body text of CMP 119 and CMP 122 I/II was not
obtainable through any legitimate open channel tried (log above).**

Consequences for `BALABAN_POLYMER_RESIDUAL = 2.0`:

1. The constant continues to rest **entirely** on the project-internal
   triangle-inequality derivation
   (`notes/sigma-hat-derivation.md` §2.3-derivation; channel
   multiplicity 2; optimal worst-case absent a sign-preservation
   lemma). This pass neither confirms nor contradicts it from the
   primary source.
2. The 2026-07-24 demotion of `[Balaban1988convergent]` (CMP 119) to
   "shape/motivation only" in the fiducials note stands, now with a
   stronger evidentiary record: the exact open-archive PDF URL is
   known and confirmed walled, so the null is a wall, not a search
   failure.
3. The realistic expectation is unchanged: given the uniform
   existence-constant pattern of Theorems 1–3 (CMP 109) and Lemma 1
   (CMP 116, constants C₁, C₂, q unpinned at (1.32)/(1.36)), and given
   the CMP 122 abstracts' qualitative framing, CMP 119/122 most likely
   also supply existence constants only — in which case the internal
   derivation would remain the strongest available provenance even
   with the papers in hand.
4. **Concrete unblock paths** (for a human operator): (i) fetch URL #2
   from a normal browser (the archive is genuinely open access —
   Incapsula only blocks datacenter/bot egress); (ii) institutional
   Springer access for DOIs 10.1007/BF01217741, BF01257412, BF01238433;
   (iii) drop the PDFs into `docs/pdf_references/` and rerun the
   extraction hunt against `_generated/pdf_text/`.

**No constants were invented; nothing in the repo's numeric state
changes as a result of this pass.**

---

## 5. CMP 119 direct extraction (2026-07-25, unblocked)

**Unblock.** A human fetched a PDF from the Project Euclid issue page
into `docs/pdf_references/communications-in-mathematical-physics_volume-119_issue-2.pdf`.
**Caveat discovered:** that file is the issue *front matter only* (2
pages, 302 KB — cover TOC + editorial boilerplate; Euclid's issue-level
link is the "Miscellaneous front pages" document). The article itself
was then obtained by an in-memory fetch executed *on the user's Mac*
(residential egress passes the Incapsula wall that blocks the
container): `curl <URL #2 of the §2 log> | gs -sDEVICE=txtwrite`
— piped, no file written to the Mac. The Euclid scan carries an OCR
text layer; the complete paper (pp. 243–285) extracted to 2,307 text
lines, archived cloud-side at `/home/claude/fid/cmp119_fulltext.txt`
(pp. 243–~279) with the tail (pp. 279–285) captured in-session.
Identity confirmed from the text itself: header "Commun. Math. Phys.
119, 243-285 (1988)"; references list "[I] ... Commun. Math. Phys.
109, 249-301 (1987)" and "[II] ... Commun. Math. Phys. 116, 1-22
(1988)"; communicated by A. Jaffe; received June 5, 1987.

All quotes below are OCR-faithful from the ghostscript text layer;
`[garbled]` marks unreadable spans, with bracketed reconstructions
justified by surrounding text.

### 5.1. The residual-relevant structure (hunt target 1)

The central analytic object of the Proof of Theorem 2 (pp. 279–284) is
**exactly a difference of polymer-localized cluster-expansion terms
between two configurations**:

> "The basic expression to analyze, either in the proof of Theorem 2,
> or in the analysis of renormalization, is the difference
> E^(j)(Λ_j, U_k, z) − E^(j)(Λ_j, 1, z)."  (p. 279)

and the second proof of Theorem 2 bounds this difference, polymer by
polymer, with an **explicit numeric factor 2 — the triangle-inequality
two-channel device**:

> "We divide the localization domains X into two classes: [X ⊂ □̃^~,
> or X ∩ (□̃^~)^c ≠ ∅]. For X in the second class the difference of the
> corresponding expressions can be estimated by
> 2E₀ exp(−(1/2)κ[garbled: ·−j]) exp(−(1/2)κ d_j(X)), and
> exp(−(1/2)κ[·−j]) < (L^j L^{−n})^5, hence these terms can be treated
> as before."  (p. 283; raw OCR: "2Eexp(-(1/2)>φ -j))exp
> (-(l/2)κd(X)l and exp(-(l/2)/φ -j)) <(Z/ZΓ")^5", with the E₀
> subscript on the following line)

That is: |A − B| ≤ |A| + |B| ≤ 2·(single-term activity bound) — the
same channel-multiplicity-2 device as the repo's §5 derivation, in the
primary source, with the 2 written out. **Scope caveat (decisive for
the fiducial):** Bałaban's difference is between two *background
configurations* (U_k vs 1) at a fixed scale j; the repo's
`BALABAN_POLYMER_RESIDUAL` bounds the *cross-scale* (k → k+1)
per-polymer change under block-spin transport. The device and constant
coincide; the inequality instance is different. The single-term bound
being doubled is (1.1.18)/(3.48):

> "|E^(j)(X, z)| ≤ E₀ exp(−κ(L^j L^{−n})^{−1}) exp(−(1/2)κ d_j(X)) .
> (3.48)"  (p. 280; raw OCR: "\E (X,z)\^E exp(-KiUL'")- )exp(-^κdj(X))";
> the first exponent's argument is confirmed by the following line
> "the sum over X is bounded by O(1)exp(−κ(L^jL^{−n})^{−1}) ≤
> O(1)(L^jL^{−n})^5")

— note the recurring exp(−(1/2)κ d) **rate-split**, the same
bookkeeping device as CMP 109 eq. (0.27).

The first proof's renormalized version of the difference is display
(3.67), p. 283:

> "E^(j)(Λ_j, U_k, z) − E^(j)(Λ_j, 1, z) − β_j A(h_z, U_k) =
> O((L^j L^{−n})^{5−ε})"

with O(·) unpinned.

### 5.2. Explicit numeric constants — complete inventory (hunt target 2)

**Pinned numeric in a main bound (the only one):**

> "Similarly, there exists an absolute constant R₁ such, that
> Σ [R^(j)(·, U_k) − R^(j)(·, 1)] ≤ R₁ g_j² Σ_n |Γ_n ∩ Ω|  (2.44)
> for the regular configurations U_k. **(In fact the constant R₁ can
> be taken as equal to 1 for g_j sufficiently small.)**"  (Theorem 2,
> p. 263; raw OCR of the display: "ύRigf Σ l * l")

R₁ = 1 bounds the *configuration-difference* of R-terms — again not
the cross-scale residual.

**Proof-device numerics (choices, not determinations):**

- "The number β is a small positive constant, but not too small,
  e.g., we can take β = 1/4."  (p. 261–262, after the analyticity
  conditions (2.34)–(2.39).)
- Improved post-transformation decay: "with the number κ replaced,
  for example, by (1 + 4β)κ"  (p. 262) — with the β = 1/4 example
  this is 2κ.
- Boundary-term geometric ratio: "the remaining factor exp(−d_j(X))
  is used to get an additional small factor, e.g. for j > n it can be
  bounded by 2^{−(j−1−n)}"  (pp. 263–264, feeding (2.47)/(2.48); raw
  OCR "2~u~1~n").
- Per-step analyticity shrinkage: "This is the reason for putting the
  powers of 1/2 in the conditions (2.36)–(2.39). The analyticity
  domains become smaller after each step, but the difference is very
  small and exponentially decreasing in the number of steps."  (p. 277)
- Rate-splits exp(−(1/2)κ·): (3.48) p. 280 and the p. 283 display of
  §5.1 — both spend half the inductive rate on a small prefactor,
  identically to CMP 109 (0.27).
- Large-field suppression, first step (p. 243–244): the Wilson-action
  term for a large plaquette gives
  "exp[−(1/g₀²)(1 − Re tr U(∂p))] ≤ exp(−(1/(2g₀²)) p₀²(g₀)) ≤
  g₀^[garbled]", with p₀(g₀) = A₀(log g₀^{−1})^{p₀}, A₀ and the
  integer p₀ unpinned.

**Unpinned existence-constant chain (the CMP 116 pattern, again):**

- Theorem 1 (p. 262–263): "There exist constants, introduced in the
  above description, such that if the sequence of coupling constants
  {g_k} ... satisfies the inequalities (1.0.33), then the sequence of
  densities {ρ_k} ... satisfies all the inductive assumptions. **The
  constants satisfy numerous restrictions introduced in the proof.**"
  Plus: "some of the restrictions on constants, e.g. on constants κ,
  M, ε_j, α_{0,j}, α_{1,j}, come from the paper [I] ... and we will
  introduce some new restrictions also."
- E₁ in (2.43): "there exists a constant E₁ independent of j, k, Ω,
  {Ω_j}, {Λ_j}, T (but dependent on the other constants occurring in
  the formulation of this theorem)" ... "The constant E₁ depends on β
  also, and grows to ∞ if β → 1."  (p. 263)
- B₀ in the boundary-term inductive bound:
  "|B^(j)(X, (U,J), A, {S_i})| ≤ B₀ exp(−κ d_j(X)) . (2.42)"  (p. 262)
- Per-step constant degradation: "the terms of the sum above satisfy
  the bounds (2.42), with the constant B₀ replaced by O(p_k²(g_k))"
  (p. 278) — O(·) unpinned.
- Corollary 3 (Ultraviolet Stability), p. 264: "there exist constants
  E₋, E₊ independent of η and T, but depending on g_k" — existence
  only.
- (2.38): "with an absolute constant B" — unpinned.

### 5.3. Logical structure of the residual (hunt target 3)

The paper's own summary theorem (p. 245): "**Theorem.** If ρ_k
satisfies the assumptions described in detail in Sect. 2, then Tρ_k
satisfies also the corresponding assumptions." The whole paper is
form-preservation of the inductive density description under T, with
constants held in the Theorem-1 existence chain. Critically for the
residual question, **the large-field renormalization operation R — the
natural home of any per-polymer residual constant — is not constructed
in CMP 119**:

> "The operation R serves this purpose. We will not describe it here,
> we will only assume that it has some properties incorporated in the
> inductive description of the effective actions."  (p. 244)

> "The above property will follow immediately from the construction of
> the R-terms given in the next paper."  (p. 260–261, after (2.32))

i.e., the R-operation content is genuinely deferred to CMP 122 I/II
(still not held; see §2 log — Springer-gated, and the Euclid IDs for
volume 122 were not resolved). What would pin the constants: solving
the "numerous restrictions" system of Theorem 1's proof together with
the [I]-inherited constraints on κ, M, ε_j, α_{0,j}, α_{1,j} — CMP 119
nowhere collapses this system to numeric values.

### 5.4. Verdict for `BALABAN_POLYMER_RESIDUAL = 2.0`

**SHAPE-CONFIRMED (constant unpinned for the repo's inequality), with
a quote-level located ancestor of the factor-2 device.**

1. CMP 119's central object is a difference of polymer-localized
   cluster-expansion terms, bounded per-polymer — the repo's ΔT(X)
   shape is genuinely Bałaban's shape. The shape citation
   [Balaban1988convergent] is upgraded from "motivating, not
   supplying" to quote-level (p. 279, p. 283, (3.48), (3.67)).
2. The explicit factor 2 appears at p. 283 in exactly the repo's
   two-channel triangle role — but for a configuration-difference at
   fixed scale, not the cross-scale (k → k+1) σ̂-transport residual.
   **No display in CMP 119 bounds the cross-scale per-polymer change;
   the constant 2.0 therefore remains internally derived**
   (`notes/sigma-hat-derivation.md` §2.3-derivation), now with primary-
   source precedent that the device and its constant are Bałaban-native.
3. The 2026-07-25-morning expectation (§4.3 above) is confirmed
   verbatim: the paper supplies existence constants (Theorem 1, E₁,
   B₀, E₀, E₋/E₊) with exactly one pinned numeric, R₁ = 1 in (2.44) —
   and that display is not the residual.
4. No sign-preservation lemma (for the c = 1 tightening) appears;
   differences are handled by absolute values and the factor-2 split
   throughout. That refinement target stays open.
5. Remaining extraction frontier: CMP 122 I/II (the R-operation
   construction). Unchanged unblock paths per §4.4.

**c_λ cross-check (bonus target).** CMP 119 contains nothing that pins
κ (Theorem 1 is existence-only, inheriting [I]'s restrictions), and it
*reuses* the exp(−(1/2)κ d) rate-split of CMP 109 (0.27) at (3.48) and
p. 283 — further confirming the fiducials note §1.2 reading that the
historical c_λ = 1/2 shape descends from a recurring bookkeeping
device, not a spectral constant.

**Corpus hygiene note.** The repo file
`docs/pdf_references/communications-in-mathematical-physics_volume-119_issue-2.pdf`
is NOT the Bałaban paper — it is the 2-page issue front matter. For
the corpus, the article PDF should be downloaded (browser, same URL as
§2 log entry #2) and dropped into `docs/pdf_references/`, then OCR'd
into `_generated/pdf_text/`.

---

## 6. CMP 122 I/II extraction (2026-07-25, second unblock — the R-operation papers)

**Fetch record.** The CMP 119 lesson (Mac residential egress + browser
UA passes the Incapsula wall) was applied to the remaining frontier.
Euclid IDs located from the cloud via the crawlable search index:
paper I = `euclid.cmp/1104178393`, paper II = `euclid.cmp/1104178467`.
Fetched Mac-side (`curl -L`, browser UA, referer
`https://projecteuclid.org/`, URL form
`https://projecteuclid.org/download/pdf_1/euclid.cmp/<id>`), written
to the repo (authorized, gitignored):

| File | Size | Pages | Magic | Journal pages |
| --- | --- | --- | --- | --- |
| `docs/pdf_references/Balaban_CMP122_I_175-202.pdf` | 2,826,369 B | 28 | %PDF-1.2 | 175–202 ✓ (28 pp.) |
| `docs/pdf_references/Balaban_CMP122_II_355-392.pdf` | 4,030,232 B | 38 | %PDF-1.2 | 355–392 ✓ (38 pp.) |

Text archives (gs txtwrite of the OCR layer, matching the
`_generated/pdf_text/` convention): `Balaban 122-I.txt` (1,615 lines),
`Balaban 122-II.txt` (2,047 lines). Identities confirmed from the
headers ("Commun. Math. Phys. 122, 175-202 (1989)" / "122, 355-392
(1989)") and paper II's reference list, which fixes Bałaban's internal
numbering: **[I] = CMP 109, [II] = CMP 116, [III] = CMP 119,
[IV] = CMP 122-I**. Both communicated by A. Jaffe.

All quotes OCR-faithful; `[garbled]` marks unreadable spans.

### 6.1. What the R operation is, and its basic step (paper I)

Definition by density-replacement quotients, normalized: "a large
field expression is replaced by the corresponding small field
expression in such a way, that integrals of the densities are
unchanged" (p. 176), with the basic normalization property
"∫dV (Rρ)(V) = ∫dV ρ(V) . (0.4)". The large-field small factor being
renormalized is (0.1), p. 175: "exp[−(1/g₀²)[1 − Re tr U(∂p)]] ≤
exp(−p₀²(g₀)) = [garbled: g₀^{A₀²(log g₀)...}]", with p₀(g₀) =
A₀(log g₀⁻¹)^{p₀}, A₀ and integer p₀ unpinned. Geometric setup with
explicit numerics: component sizes > 20MR_k, > 40MR_k, minimal ≈
42(L/(L−1))MR_k, admissible class ≤ 100MR_k (p. 177) — the origin of
paper II's (100R_k)^d factors.

### 6.2. Hunt (b): the constants of the localization/exponentiation chain

**Paper I is the constraint-solving paper of the series** — it
actually *solves* its small constraint systems with concrete choices,
a step beyond the pure existence style of CMP 109/116/119:

- "0 < β ≤ 1/2, but not too small, e.g., we can take β = 1/2. The
  number L₀ satisfies 2^{L₀} < [garbled](1/2)L, e.g., we can take
  L₀ = (1/2)(L−1)."  (I, p. ~181)
- "β₀ ≤ 1/2, β ≤ 1/2, L₀ < (1/2)L), and α ≤ 1/4. **Thus taking
  α = 1/8 in (1.48) we satisfy all the conditions.**"  (I, p. 187;
  with "the last inequality implies (1.49) if 8α ≤ 1" just above)
- "We choose M large enough, so that δ(M/M₁)[^?] ≥ 2."  (I, p. 186)
- "The constant C above is a positive integer. It is usually small,
  because of geometric constraints on the cubes, for example we can
  assume that C ≤ 2. The constant B is a fixed absolute constant, for
  example we can take the constant B = B₃ from Theorem 1 [16]."
  (I, p. 191)
- "c_m = 1 for m < k, and c_m = 3 for m = k"  (I, p. 191, condition
  (iii) of the analyticity spaces)
- "they form a descending sequence … if β ≤ 1/4 and L₀² ≤ (1/3)L"
  (I, p. 191)
- "taking α ≤ 1/8, we estimate the right-hand side of (1.98) [of
  paper I] by (21/8)ε ≤ 3(1 − β(1/2))ε"  (I, p. ~198; OCR partly
  garbled)

**Paper II's exponentiation chain** (Sect. 1, displays (1.88)–(1.100))
mixes explicit device numerics with O(1)'s:

- Activity bounds (1.92)–(1.95): decay rates (1+2β)κ, then (1+β)κ;
  smallness driver α with "α ≤ exp(−(1+β)κ2^d)" (p. 388) and the
  recurring α^{1/3}; tree-graph sums closed by "O(1)α^{1/3} ≤ 1 ≤
  [garbled](β−2^d)βκ **for κ large enough**" (p. 389) — κ unpinned,
  as everywhere in the series.
- The g-smallness closure with an explicit example choice: "We assume
  that g_k is so small that −2(1+β₀)⁻¹p₀(g_k) + 1 + 2κ(100R_k)^d ≤
  −[garbled: (3/2)]p₀(g_k) **(for example, take β₀ = 1/7, then this
  means that −(1/4)p₀(g_k) + 1 + 2κ(100R_k)^d ≤ 0**, and before we
  had stronger restrictions on p₀(g_k))."  (p. 389)
- Final activity bound (1.97) with c₁ = exp(−p₀(g_k)) if X′ misses
  the ∪Y_i, else c₁ = α^{1/3}; "The estimate (1.97) is sufficient for
  convergence of the exponentiated cluster expansion" and "{···} =
  exp R′^{(k)} = exp Σ R′^{(k)}(X). (1.98)".
- (1.99): "|R′^{(k)}(X,(U,J))| ≤ O(1)c₁ exp(−(1+½β)κ d(X))" — O(1)
  unpinned.
- **(1.100), the final inductive R-term bound — constant exactly 1:**
  "|R^{(k)}(X,(U,J))| ≤ exp(−p₀(g_k)) exp(−κ d_k(X)) . (1.100)"
  (p. 390).  In Bałaban's final normal form the per-polymer R-term
  carries **no O(1) multiplier at all**; every looseness is absorbed
  into the suppression exp(−p₀(g_k)) and the rate κ.
- Second-pass degradations (p. 391, the (1.103)–(1.104)
  representation): "the number β is replaced by (1/4)β, and α by
  O(1)[garbled: α^?]".

### 6.3. Hunt (a)+(c): the cross-scale residual instance

**The k → k+1 scale-comparison inequality — the instance CMP 119 did
not contain — does not appear in CMP 122 either, in the repo's
per-polymer activity-difference form.** What the papers do across
scales is a **suppression-budget recursion** in the exponent: each
large-field component Z carries a number κ_j(Z), and the step j → j+1
updates it by (paper II, pp. 385–387, displays (1.83)–(1.87)):

> "κ_{j+1}(Z) = Σ(κ_j(Z^{(n)}) + **2p₀(g_j)**) +
> Σ(γ₀A₁p₀²(g_{j+1})(d′_{j+1}(Z^f_{j+1}) + 1) + **2p₀(g_{j+1})**) −
> O(1)M^dR^d_{j+1}d′_{j+1}(Z) − **2p₀(g_{j(Z)})** . (1.85)"

closed by a tree-graph induction ((1.86)–(1.87)) and yielding the
**fundamental large-field suppression inequality**:

> "T_k(X)[garbled: |·|] ≤ exp(−**2**(1+β₀)⁻¹ p₀(g_k)) . (1.89)"
> (p. 387: "we have the fundamental inequality")

with the explicit example β₀ = 1/7 making the retained rate
2(1+1/7)⁻¹ = 7/4 (of which 1/4 is spent on the (100R_k)^d volume
factors, leaving 3/2 — the p. 389 closure above). **This is the
closest cross-scale factor-2 in the whole corpus**: each large-field
region's budget carries increments of exactly 2p₀ per merged region
across the scale step, and the final per-region suppression keeps the
prefactor 2 (shaved to 2(1+β₀)⁻¹). It is a *budget/bookkeeping* 2 in
an exponent — a per-region reservation of two units of suppression —
not a bound on |T_{k+1}(X′) − T_k(X)| or on any truncated-correlation
change under block-spin. No display in either paper bounds the repo's
σ̂-transport per-polymer change.

### 6.4. Hunt (d): retroactive pinning of the CMP 119 chain

- The logical link is pinned: "an improved bound (1.89), with the
  additional term −κd(X) in the exponential. **This implies the
  inequality (2.50) [III], hence Corollary 3.**" (II, p. 387) — CMP
  119's UV-stability corollary is discharged by (1.89)+decay.
- The final stability constants stay existence-only: "(0.1) … with
  the constants E₋, E₊ independent of k, T_η, U_k" (II, p. 356).
- κ is never pinned ("for κ large enough", p. 389); E₀, E₁, B₀ of
  CMP 119 are not revisited numerically.
- **Audit-critical honesty item** (II, p. 355–356, Introduction):
  "Theorem 2 of [I] allows us to remove the assumption on the
  effective coupling constants in the above theorem … **The proof of
  Theorem 2, which is based on second order perturbative
  calculations, is very awkward and long … and has not been published
  yet, so we have Theorem 1 with the assumption.**"  I.e., the
  removal of the weak-coupling assumption in the final UV-stability
  theorem rests on an **unpublished** proof (CMP 109's Theorem 2,
  whose "proof … will be given in a separate paper" — see §5 and the
  fiducials note §1.2). The published chain proves Theorem 1 *with*
  the assumption g_k ∈ ]0, γ].

### 6.5. Verdict for `BALABAN_POLYMER_RESIDUAL = 2.0` (final, full-chain)

**SHAPE-CONFIRMED — constant unpinned for the repo's inequality —
now on the complete published chain (CMP 109, 116, 119, 122 I/II, all
read).** The k → k+1 per-polymer activity-difference instance appears
nowhere in the corpus; the constant 2.0 rests definitively on the
project-internal triangle-inequality derivation
(`notes/sigma-hat-derivation.md` §2.3-derivation). The primary
sources supply two quote-level cousins of the factor 2, strengthening
the shape citation without supplying the constant:

1. the fixed-scale configuration-difference bound "2E₀…" (CMP 119
   p. 283 — §5.1 above), and
2. the cross-scale suppression-budget increments 2p₀(g_j) and the
   fundamental per-region bound exp(−2(1+β₀)⁻¹p₀(g_k)) (CMP 122-II
   (1.85)/(1.89) — §6.3 above).

Notable for any future tightening argument: Bałaban's own final
normal-form R-term bound (1.100) carries **constant exactly 1** by
absorbing all looseness into exp(−p₀(g_k)) — precedent that a
clean-constant normal form is achievable when a dedicated small
factor is available. This does not transfer to the repo's residual
without such a factor; the c_polymer = 1 tightening still requires
the (absent) sign-preservation lemma or an analogous absorbed small
factor. No invented constants; extraction frontier for this fiducial
is now **closed** — there are no further primary-source papers in the
chain to read.
