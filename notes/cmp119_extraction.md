# CMP 119 / CMP 122 Open-Access Retrieval + Residual-Extraction Attempt

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
