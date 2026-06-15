# Lifting the proof program into category theory — assessment (2026-06-15)

Cited, critical assessment of what a category-theoretic lift buys the constructive
SU(2) Yang–Mills mass-gap Lean formalization, and how to do it under the
MLTT/HoTT-valid + CReal-setoid constraints. Based on a deep-research pass
(23 sources, 25 adversarially-verified claims) plus project-specific reasoning.
**Speculation is flagged.** Two corrections to the original brief are recorded
in §0.

## 0. Corrections to the brief

- **arXiv:1612.09375 is Tom Leinster's *Basic Category Theory* (CUP 2014)** — a
  classical pedagogical textbook (universal properties via adjoints/representables/
  limits), **not** a HoTT/Rezk-completion paper. It contributes standard
  definitions, nothing on formalization discipline. The univalent-categories
  evidence the brief wanted is **Ahrens–Kapulkin–Shulman, arXiv:1303.0584**
  (MSCS 2015, mechanized in Coq).
- **The QFT-categorification angle is unverified here.** Sources were fetched
  (Costello–Gwilliam factorization algebras; Brunetti–Fredenhagen–Verch locally
  covariant QFT; dagger-compact RP: arXiv:2304.02928, 1802.09555) but no claim
  from that angle survived the top-25 verification budget. So "is monoidal/dagger
  RP genuine proof leverage or decoration" is an **open question** — §3 answers it
  with reasoned speculation, not verified sourcing.

## 1. Verified findings (high confidence unless noted)

1. **Constructive category theory without UIP is feasible, and the established
   way is setoid-enriched Hom-equality** — internalize a per-category equivalence
   relation `_≈_` on each Hom with an `IsEquivalence` proof, require composition
   to respect it (`◦-resp-≈`). agda-categories does exactly this, proof-relevant,
   under `--without-K --safe`, *because* "propositional equality does not work
   very well in MLTT without further axioms (e.g. funext)". This is structurally
   identical to morphisms valued in CReal (whose equality is already a setoid
   `eqv`, not definitional). [agda/agda-categories; Hu–Carette CPP'21, 2005.07059]

2. **Setoid-Hom is the principled choice for this program; Mathlib's Type-Hom +
   propositional-`Eq` + kernel proof-irrelevance design is a structural mismatch**
   for the strictly-constructive constraint (though Mathlib is fine for classical
   math). Palmgren (TYPES'17, 1708.01924) makes the obstruction precise: in MLTT
   there is **no** general way to put equality-on-objects on a setoid-Hom category
   unless UIP holds; classically iso-as-equality needs choice → PEM (Diaconescu) →
   UIP (Hedberg), all forbidden here. *(Sound but extrapolated: the sources call
   Mathlib's design "very close to classical"; they don't literally pronounce it
   unsuitable for this project. 3 supporting sub-claims were 2-1 votes.)*
   [mathlib4 CategoryTheory.Category.Basic; 2005.07059; 1708.01924]

3. **The ceremony cost is real and partly quantified.** Kreitz–Kozen–Richter
   (Nuprl, IJCAR'06): the "mathematically trivial" functor-category iso
   `Fun[C×D,E] ≅ Fun[C,Fun[D,E]]` takes **~30,000 inference steps** without cuts,
   cut to **~3,000** via proof-reuse wrappers. Proof-relevance forces explicit
   insertion of coherence isomorphisms (agda-categories Monad def). Gross–Chlipala–
   Spivak (Coq, ITP'14, 1401.7694): setoid-everywhere → **~3× slower compiles**;
   "every type needs a relation + equivalence proof, every function a congruence
   proof." *(Figures are system/era-specific — Nuprl and 2014-Coq, not Lean 4 —
   directional, not transferable constants.)*

4. **Pay setoid cost selectively, not globally.** Gross–Chlipala–Spivak used
   `Eq`-based (UIP) morphisms by default + HITs/quotients "only where needed",
   because propositional equality "carries none of the overhead of setoids."
   Also: bundling categorical data as **record fields** rather than type
   parameters gave a **3× whole-development speedup** in Coq. [1401.7694]

5. **Basic categorical reasoning is essentially first-order** — functors/natural
   transformations reduce to first-order object+arrow component equations, the
   higher-order existence "generated automatically in the background." This aligns
   with the project's mandate to carry witnesses as **Type-level Σ-component data**
   (`F1`/`F2`-style maps), not opaque `Prop`-∃. [Kreitz et al., IJCAR'06]

6. **Univalent/Rezk-complete categories (equality-of-objects = isomorphism) are
   formalizable** (Ahrens–Kapulkin–Shulman, Coq+HoTT lib, Rezk completion) **but
   heavier** — they impose hSet/contractibility burden agda-categories'
   setoid setting deliberately avoids. Only pays off if the program needs to
   **transport theorems along equivalences of categories**. Not required here.
   [1303.0584; 1708.01924]

7. **Proof-relevance is a genuine structural win, not just ceremony, in ≥1
   concrete case:** proof-relevant setoid-Hom lets you define the (large) category
   of all categories — using natural isomorphisms as the equivalence between
   functors — **without escalating to 2-categories or John-Major equality**. This
   directly tempers the program's instinct to "move up to 2-categories" for RG
   flow: a proof-relevant **1-functor may already host** what `HigherCategorical
   .lean`'s `rg_flow_2_functor` reaches for. [2005.07059]

8. **Lean 4 (the actual host) has no HoTT mode and HAS kernel definitional
   proof-irrelevance for `Prop`.** So "MLTT/HoTT-valid" is a **self-imposed
   discipline**, not a kernel guarantee — anything routed through `Prop` can
   silently use proof-irrelevance. A setoid-Hom (E-category) discipline, which
   does **not** depend on UIP, is the faithful encoding of that discipline.
   [van Doorn–von Raumer–Buchholtz, ITP'17, 1704.06781 — describes Lean 2 HoTT]

## 2. What categorical lifting concretely buys THIS program (payoff vs cost)

| Structure | Buys | Payoff | Cost | Verdict |
|---|---|---|---|---|
| **Site/sheaf of RG scales** (block-spin morphisms, presheaves A_k/S_k, `domGlue_preserves_KP` as gluing) | Modular RG layer; gluing stated once, reused per scale; restriction = functorial coarsening (already `ProbFunctional.restrict` along an `ObsHom`!) | **High** — genuine reuse across all scales; the coarsening functoriality is *already present* | Moderate (site axioms) | **REAL — build it** |
| **Symmetric-monoidal / tensor structure for per-bond→product RP** (`prodWeighted_pos_of_perEdge`) | States "RP of a tensor product = tensor of per-bond RP" as a monoidal-functor-of-states property | **Medium** *(speculative — see §3)* | Low–moderate | **Promising; verify leverage first** |
| **2-functorial RG** `F_RG : RG → SheafBudget`, Θ_k as 2-cells | Naturality of degradation for free; "gap as universal/terminal object" | **Low now** — finding #7 says proof-relevant 1-functor likely suffices; 2-cell coherence is pure ceremony until a second 2-cell instance exists | **High** (2-cell coherence) | **DECORATIVE until forced** |
| **Operad for budget composition** (PolyAtlas/ModuliAlgebra) | Composition law for σ̂-budget across steps | **Low** — the budget is already a clean `finSum` monotonicity (`truncatedConst_le`); operad adds notation, not theorems | Moderate | **DECORATIVE** |
| **Codynamic EKF↔YM transfer** | A shared categorical *interface* discharging two developments at once | **Medium IF the interface is reused** — this is the one place with a genuine 2nd instance (EKF), the threshold at which abstraction pays | Low (it's a type-signature iso) | **REAL — the clearest reuse case** |

**Decision rule (from findings #3,#4,#6,#7):** categorical abstraction pays for
itself only when there are **≥2 genuine instances**, a **theorem to transport
along an equivalence**, or a **universal property that discharges an obligation**.
By that rule: site/sheaf (∞ scale instances) and Codynamic (2 instances: EKF, YM)
clear the bar; the 2-functor and operad do not yet.

## 3. Reflection positivity & monoidal structure — reasoned speculation

*(Flagged: not verified by the research pass; the dagger-compact-RP sources didn't
survive verification.)* The just-completed `prodWeighted_pos_of_perEdge` — RP of a
decoupled product functional factorizes into per-bond RP — is **literally a
monoidal statement**: states are objects of a (symmetric monoidal) category of
functionals, `⊗` is the product functional, and "RP" is a sub-property closed
under `⊗`. The honest question is whether encoding this as a monoidal functor
**discharges any OS2 obligation** or is re-notation. My assessment: for the
*decoupled* product it is **re-notation** — the Lean proof is already one line
(`prodE_nonneg`), and a monoidal wrapper adds coherence obligations without
shortening it. It would become **real leverage** only for an *interacting*
(coupled) measure, where a monoidal/Markov-category (or the dagger structure of
Chiribella-style RP) might give the cross-plane gluing structurally — but the
program's interacting case currently factorizes through the *same* per-bond input,
so the payoff is not yet present. **Recommendation: do not monoidalize RP yet.**

## 4. Lean-4 formalization recommendation

1. **Setoid-Hom, localized — not global.** Adopt agda-categories-style
   hom-setoids (`_≈_` + `IsEquivalence` + congruence) **only** for morphism types
   whose equality is genuinely CReal-`eqv` (the analytic/positivity layer).
   Everywhere the equality is `Q'`-decidable or structural, keep `Eq`-based
   Type-Hom — propositional equality has none of the setoid overhead (#4).
2. **Do not build on Mathlib `CategoryTheory`** for the constructive core (#2):
   its Type-Hom + `Prop` proof-irrelevance design is the opposite discipline.
   *Mirror* its ergonomics (data in record fields, `ext`-style lemmas) without
   inheriting proof-irrelevance reliance.
3. **Bundle categorical data as record fields**, not type parameters (#4) — the
   one cost optimization with a measured 3× payoff.
4. **Prefer proof-relevant 1-categories over 2-categories** (#7) — re-examine
   whether `rg_flow_2_functor` needs 2-cells at all; natural isomorphisms in a
   proof-relevant 1-category may host the degradation Θ_k.
5. **Do NOT adopt univalence/Rezk** (#6) unless a concrete need to transport
   theorems across equivalent categories-of-scales appears. It is strictly heavier.
6. **Run a Lean-4 spike before committing** (open question #4): the ~3× and
   ~30k→3k figures are Coq/Nuprl; Lean 4's elaborator may differ. Build one
   setoid-Hom category over CReal-morphisms and one `Eq`-Hom analogue, compare
   compile cost, before lifting anything load-bearing.

## 5. Where it does NOT help (honest list)

- **It does not shorten any analytic/positivity proof.** The hard content
  (`reflSchwinger_nonneg`, the σ̂-budget closure, the character-tail antitonicity,
  the SU(N) cap) is inequality-pushing on CReal/Q'; categories add interface, not
  analysis. The mass gap is not blocked on a *structural* gap.
- **It does not touch the genuine open holes** — the SU(N) uniform character-tail
  cap (real analysis) and the OS-reconstruction/cluster-to-gap operator theory
  (deliberately paper-level). No categorical lift discharges these.
- **2-categorical and operadic scaffolding is decorative** until a second instance
  forces it (#3,#7). Carrying it now is coherence-proof ceremony with no theorem
  payoff — and a measured compile cost.
- **MLTT/HoTT-validity is not kernel-enforced in Lean 4** (#8). Category code
  routed through `Prop` can silently lean on proof-irrelevance; the discipline
  must be audited, not assumed — same as the existing axiom-gate audit.

## 6. Bottom line

Lift the **RG site/sheaf** (already half-built via `ProbFunctional.restrict`) and
keep the **Codynamic transfer** (genuine 2nd instance) — these clear the
"≥2 instances / transport / universal property" bar. Use **localized setoid-Hom**
over CReal-morphisms, `Eq`-Hom elsewhere, data in record fields, proof-relevant
**1**-categories. Treat the **2-functor, operad, and monoidal-RP** as decorative
until a concrete reuse/transport need materializes, and **spike the Lean-4 setoid
cost** before committing anything load-bearing. The lift improves *structure and
reuse*; it does **not** advance the analytic frontier, which remains the real
bottleneck.

### Sources
agda/agda-categories; Hu–Carette CPP'21 (2005.07059); Kreitz–Kozen–Richter
IJCAR'06; Gross–Chlipala–Spivak ITP'14 (1401.7694); Ahrens–Kapulkin–Shulman
MSCS'15 (1303.0584); Palmgren TYPES'17 (1708.01924); van Doorn–von Raumer–
Buchholtz ITP'17 (1704.06781); mathlib4 CategoryTheory docs; Leinster *Basic
Category Theory* (1612.09375). QFT-categorification sources (Costello–Gwilliam;
Brunetti–Fredenhagen–Verch; dagger-compact RP 2304.02928, 1802.09555) fetched
but unverified — §3 is reasoned speculation.
