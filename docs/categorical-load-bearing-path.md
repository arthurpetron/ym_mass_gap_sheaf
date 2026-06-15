# Making the categorical framings load-bearing — path + execution (2026-06-15)

`docs/category-theory-lift-assessment.md` rated three categorical framings
"decorative": the 2-functorial RG, the operad/monoidal RP, and the gap
universal property.  This note records the **path** taken to make them
load-bearing and provide **mathematical closure alongside the analytical
evidence** — two concurring sets of evidence for the mass-gap-relevant facts.

## The non-circularity criterion

A categorical re-statement that calls the analytic theorem at its last step is
decorative.  Genuine *concurring evidence* requires the categorical derivation
to rest on a **structurally different fact**, so the two proofs fail
differently (the way the `rho_sf` constant bug was caught by a second route).
We classify each upgrade by how independent it is.

## Upgrade B — OS2 via the Markov semigroup square (ARITHMETICALLY INDEPENDENT)

`lean/YMGap/Continuum/ReflectionDagger.lean`.

The reflection Schwinger form `R_t(c) = Σ_s e^{−t·C₂(s)}·c_s²` is `≥ 0` because
each weight `e^{−t·C₂(s)} ≥ 0`.  Two structurally different reasons:

| route | fact used | file |
|-------|-----------|------|
| analytic | `e^{−x}` is a nonnegative series → `≥ 0` | `ReflectionPositivity.reflWeight_nonneg` |
| **dagger / Markov** | `e^{−x} = (e^{−x/2})²` (semigroup `K_t = K_{t/2}·K_{t/2}`) → it is a **perfect square** | `ReflectionDagger.reflWeight_is_square` |

These are *different facts about `e^{−x}`* (nonneg-series vs perfect-square), so
this is **genuine concurring evidence**, not re-notation.  `reflWeight_is_square`
proves the square via the exponential addition law (`expNeg_add_equiv`) and
`(x/2 + x/2) ≃ x`; `reflWeight_nonneg_via_square` then gives the weight
positivity from `geRat_sq_nonneg`; `reflSchwinger_nonneg_via_square` re-derives
OS2.  In dagger-category terms the reflection functional is `φ†φ` with `φ = √K_t`
(the GNS/Stinespring dilation, `θ` = dagger) — the canonical
reflection-positivity mechanism.  `reflSchwinger_nonneg_concur` packages both
derivations.  **Independence: full (different arithmetic atom).**

## Upgrade A — SU(2) as the terminal worst-case object (LOAD-BEARING ORGANIZATION)

`lean/YMGap/Categorical/BudgetDomination.lean`.

The all-admissible-groups σ̂-budget closure is recast as a **universal
property**: in the budget-domination category `GroupBudgetCat`, SU(2) is the
object every admissible group maps INTO (`eta_dominated` **is** the morphism
`repGB_to_su2`), and `GroupBudget.transportCloses` carries SU(2)'s closure
(`su2GB_closes`) to all of them (`all_admissible_close_via_terminal`).  This is
the categorical form of "SU(2) is the worst case ⇒ all simple groups close,"
and it puts the categorical transport on the critical path of the all-groups
result.  `all_admissible_close_concur` packages it with the analytic
`budget_closes_of_witness`.

**Independence: partial.**  The transport shares the monotonicity atom
`RG.truncatedConst_le` with the analytic `monotone_budget`, so this is *not*
arithmetically independent.  Its value is the **mathematical-closure narrative**
(terminal worst-case object) concurring with the **numerical** all-groups
evidence (the `U.4` sweep over 19 group types) — and the universal-property
organization itself.  Labeled honestly as such.

## Upgrade C — genuine 2-functoriality (DECORATIVE → PROVED)

`lean/YMGap/HigherCategorical.lean`.

The Θ-cell composition coherence `Theta s 0 (k+n) ≃ Theta s 0 k + Theta s k n`
(the natural-2-transformation law making `F_RG` a genuine 2-functor) was
flagged "ornamental / deferred" because Q' addition is not strictly
associative.  It is now **PROVED** at `eqv`: `finSum_split` (a new finite-sum
split lemma, induction on the upper index with `add_assoc_eqv` +
`Nat.add_comm`) gives `theta_compose_natural_transformation`, and
`rg_flow_2_functor_genuine` packages the full 2-functor (boundary + positivity
property + universal-property gap + **functoriality coherence**).  This
upgrades `F_RG` from an object map to a 2-functor with verified functoriality —
removing the decorative caveat.

**Independence: n/a** (this proves a previously-unproved coherence, not a second
route to an existing fact).

## What is now load-bearing vs still honest-decorative

- **Load-bearing**: Upgrade B (OS2 has two concurring proofs, the dagger one
  arithmetically independent); Upgrade A (all-groups closure organized as a
  terminal-object universal property, on the critical path); Upgrade C (the
  2-functor coherence is now a theorem).
- **Still honest about**: Upgrade A is narrative + organization, not
  arithmetic independence (shares `truncatedConst_le`).  The operad framing was
  NOT pursued — the budget monoid is already the `finSum`; an operad adds no
  theorem.  The full monoidal/dagger *category* (objects = states, `⊗` = product,
  RP as a closed monoidal sub-property) is sketched via the per-bond square
  (B) + the existing `prodWeighted_pos_of_perEdge`, but a `MonoidalCat`
  structure was not built (it would re-derive the product positivity already
  proved).

## Bottom line

Two concurring sets of evidence now stand for OS2 (the deepest case): the
analytic nonneg-weight proof and the arithmetically-independent
Markov-semigroup-square proof.  The all-groups closure is organized as a
terminal-object universal property concurring with the numerical sweep, and the
RG 2-functor's functoriality is genuinely proved.  These are **mathematical
closure** sitting alongside the project's **numerical/analytical evidence** —
the goal.  None of this advances the genuinely-open analytic frontier (SU(N)
uniform cap, OS reconstruction); it strengthens *corroboration and structure*.
