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
