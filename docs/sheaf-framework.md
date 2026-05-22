# The Sheaf-Theoretic Framework — Prose Companion

> **Companion to** `formal/sheaf-framework.tex` (formal statements + proofs) and `lean/YMGap/Sheaf/` (Lean formalization).
>
> **Milestone.** 2.1 of `work_plan.md` (Phase 2, sheaf framework).
>
> This document is the *prose argument* for the framework. It does not introduce content beyond `formal/sheaf-framework.tex`; it explains the same content in connected paragraphs, with cross-references to the formal labels. The formal file is the spec.

---

## 1. What this framework is for

The classical Bałaban-style construction of lattice Yang–Mills runs into the small-field / large-field obstruction: the small-field activity bound is derived from a Gaussian/perturbative expansion of the action, while the large-field bound is derived from a heat-kernel character expansion. These are two *different upper bounds* on the same polymer activity, derived under two different approximations. They are not restrictions of a single function to two subsets of $\Omega_k$, and they do not in general agree where their regions overlap. `docs/context.md` §3.1 phrases this crisply:

> The gluing on the overlap is not "the function on $X \cap Y$ is well-defined"; it is "we have two different upper bounds that need to be reconciled." That is a *cocycle* problem, not a *restriction* problem.

The sheaf reformulation in `docs/context.md` §3.2 takes this observation seriously. Instead of pretending the bounds glue by equality, we define a Grothendieck site over $\Omega_k$ on which the bounds glue **by domination**: on the overlap, take the pointwise max. The whole framework is built around making this work without losing the analytic content.

The framework has two presheaves on the same site:

- **$\mathcal{A}_k$**, the *bound-witness presheaf*: it records, for each open $U \subseteq \Omega_k$ and each polymer $X$, which functions $f \colon U \to \mathbb{R}_{\ge 0}$ are admissible upper bounds for the polymer activity $|a_k(X)|$ on $U$. Sections are partially ordered: a larger function is a *looser* bound.

- **$\mathcal{S}_k$**, the *summability-certificate presheaf*: it records, for each $(U, X)$, which Kotecký–Preiss pairs $(\rho, K)$ satisfy the summability condition $\sum_{X' \ni x} |a_k(X')|\, e^{\rho |X'|} \le K$.

The cocycle observation forces a **three-element cover**: $\Omega_k^{\mathrm{sf}}$ (small-field), $\Omega_k^{\mathrm{lf}}$ (large-field), and the buffer $\Omega_k^\cap$. The buffer is **not** the intersection of the first two — it is a strictly larger open absorbing every plaquette in the indeterminate annulus $\delta_k/2 < d(U_p, 1) < 2\delta_k$. Treating $\Omega_k^\cap$ as a first-class element of the cover, rather than as a derived overlap, is what lets the two bounds be reconciled by a domination glue (`formal/sheaf-framework.tex` Definition 2.2 = `def:three-cover`).

## 2. Why the framework is *structurally trivial yet analytically rich*

The single most useful observation about $\mathcal{A}_k$ is that it is **flabby in the domination sense** (`formal/sheaf-framework.tex` Theorem 3.4 = `thm:flabbiness`): every local bound is dominated by the restriction of some global bound. The proof is one line: take the constant section $t \equiv \infty$. It is admissible everywhere (since $|a_k(X)|(u) \le \infty$ trivially), and it dominates any other section pointwise.

This means $\mathcal{A}_k$'s sheaf condition is automatic and carries no analytic content. The framework's content lives elsewhere — specifically, in the **compatibility predicate** that binds a bound $s \in \mathcal{A}_k(U, X)$ to a KP pair $(\rho, K) \in \mathcal{S}_k(U, X)$:

$$
  \sum_{X' \supseteq X,\ X' \ni x} s_{X'}(u)\, e^{\rho |X'|} \le K
  \qquad \text{for all } u \in U,\ x \text{ a plaquette of } X.
$$

This is `formal/sheaf-framework.tex` Definition 5.1 (= `def:compatibility`), the named definition Milestone 2.1 requires. The compatibility predicate is where the analytic obligations of the program crystallize:

- **Existence of a compatible pair** at small-field is Milestone 3.1.
- **Existence of a compatible pair** at large-field is Milestone 3.2.
- **Existence of a compatible pair** on the overlap, with $s^\cap$ built by domination gluing, is Milestone 3.3.
- **Persistence of compatible pairs** along the block-spin pushforward, with controlled degradation $\Delta_\cap(b, g_k)$ summable in $k$, is the inductive step (work_plan.md Phase 3).

So the framework isolates the analytic problem (compatibility, regime-by-regime, with summable degradation across RG steps) without entangling it with the small-field/large-field obstruction. The sheaf condition on $\mathcal{A}_k$ comes for free; the cocycle on the overlap is dissolved by domination; what is left is a clean inductive obligation.

## 3. Why $\mathbb{R}_{\ge 0}$ should be read constructively

The math paper takes the value type of $\mathcal{A}_k$-sections to be $\overline{\mathbb{R}}_{\ge 0} = [0, \infty]$. The reader is expected to interpret this **Bishop-constructively**: every value $f(u)$ is presented with a computable modulus (a Cauchy modulus when finite; an explicit witness when $\infty$). Under that reading, every bound $s \in \mathcal{A}_k(U, X)$ is a function-with-computable-presentation, and the inequality $|a_k(X)|(u) \le s(u)$ is a constructive estimate, not an existence claim.

This is the option recommended by Milestone 2.1's open-question paragraph in `work_plan.md` ("use constructive reals with explicit modulus"). It is also forced by AGENTS.md Rule 3 (no classical reals) on the Lean side. The Lean formalization in `lean/YMGap/Sheaf/BoundWitness.lean` works at one level of abstraction higher: it parametrizes over an arbitrary type $T$ with a partial order, top element, and binary sup, and proves flabbiness and domination-gluing at that abstract level. The math paper's $\overline{\mathbb{R}}_{\ge 0}$ instantiates that abstraction once `YMGap/Constructive/Reals.lean` lands.

The practical consequence: the structural lemmas of this section have **empty axiom dependency sets** in Lean, and they will continue to have empty axiom sets after the value-type instantiation, because the instantiation is a typeclass-resolution issue and not a re-proof.

## 4. Map of formal labels

| Concept | Formal label (`formal/sheaf-framework.tex`) | Lean target (`lean/YMGap/Sheaf/`) |
| --- | --- | --- |
| Polymer | Definition 2.1 (`def:polymer`) | `Site.lean`: a parameter type |
| Three-element cover | Definition 2.2 (`def:three-cover`) | `Site.lean`: `ThreeCover` structure |
| Configuration site | Definition 2.3 (`def:site`) | `Site.lean`: `Object`, `Morphism` |
| Polymer activity | Definition 3.1 (`def:activity`) | (abstract parameter throughout) |
| Bound-witness presheaf | Definition 3.2 (`def:Akpresheaf`) | `BoundWitness.lean`: `Section`, `BoundValues` |
| Restriction stability | Lemma 3.3 (`lem:restriction-stability`) | `BoundWitness.lean`: implicit (sections are functions) |
| Flabbiness of $\mathcal{A}_k$ | Theorem 3.4 (`thm:flabbiness`) | `BoundWitness.lean`: `flabby`, `flabbyWitness` |
| Summability-certificate presheaf | Definition 4.1 (`def:Skpresheaf`) | `Summability.lean`: `KPCertificate` |
| Compatibility | Definition 5.1 (`def:compatibility`) | `Gluing.lean`: `CompatibilityRule` |
| Domination glue | Definition 6.1 (`def:domGlue`) | `Gluing.lean`: `domGlue` |
| Domination glue admissible | Proposition 6.2 (`prop:domGlue-admissible`) | `Gluing.lean`: `domGlue_dominates_*` |

## 5. What this milestone deliberately does *not* close

Per the cross-cutting policy in `work_plan.md` and the AGENTS.md Rule 5 (Lean mirrors the rest of the repo), Milestone 2.1 establishes the *framework* and leaves the *constants* to later phases:

- The polymer activity $|a_k(X)|$ is an abstract parameter here. The small-field, large-field, and overlap activity forms are pinned in Milestones 1.3, 1.4, and 3.1–3.3.
- The compatibility predicate (Definition 5.1) is stated but no specific KP pair $(\rho, K)$ is exhibited. Existence-with-witnesses is the job of Milestones 3.1–3.3.
- The block-spin pushforward and the 2-cell degradation $\Theta_k$ are deferred to Milestones 2.2 (inductive state) and 2.3 (block-spin sheaf morphism).
- The Lean value type for $\mathcal{A}_k$-sections is abstract `[BoundValues T]`; the instantiation $T = \overline{\mathbb{R}}_{\ge 0}$ awaits `YMGap/Constructive/Reals.lean`.

This is the right scope. The framework defined here will be cited by every subsequent milestone in Phase 2 and Phase 3, so its statements must be stable. Closing too much too early would mean rewriting the framework when the constants from Phase 1 come in.

## 6. Pointers

- The formal statements: [`formal/sheaf-framework.tex`](../formal/sheaf-framework.tex), compile with `cd formal && latexmk -pdf sheaf-framework.tex`.
- The Lean formalization: [`lean/YMGap/Sheaf/`](../lean/YMGap/Sheaf/), build with `cd lean && lake build`.
- The diagram of the three-region cover and the gluing: [`visualizations/structure/sheaf-gluing.tikz`](../visualizations/structure/sheaf-gluing.tikz).
- Motivation and program-level reasoning: [`docs/context.md`](context.md) §3.1 (cocycle observation), §3.2 (sheaf reformulation).
- Authoritative specification: [`docs/outline.md`](outline.md) §8 (sheaf framework) and §9 (buffer-overlap estimate).
