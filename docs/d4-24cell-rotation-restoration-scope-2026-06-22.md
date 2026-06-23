# Scope: the D₄/24-cell reduction of the rotation-restoration input (2026-06-22)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).

Target: `RepTheory/Spin4Reflection.lean`'s `O4ConnectedInput.rotationRestored` — currently a bare named
`Prop` ("continuum O(4)-rotation is restored"). Question: can the D₄/24-cell discretization turn it into a
QUANTITATIVE, strictly-weaker named input — with the group-theory part PROVED — rather than an opaque
assumption? Verdict: **YES, partially — the group-theory crux is cleanly formalizable; the RG-irrelevance
itself stays named but becomes sharper.**

## The mechanism (standard RG)

A lattice has point-symmetry `G_lat ⊂ O(4)` (finite). The continuum recovers full O(4) iff every operator
that is `G_lat`-invariant but NOT O(4)-invariant ("rotation-breaking") is RG-IRRELEVANT (operator dimension
> 4, coefficient ∝ a^{d−4} → 0). The LEADING such operator — the lowest-degree `G_lat`-invariant that O(4)
forbids — controls the restoration rate. Larger `G_lat` ⇒ fewer surviving invariants ⇒ leading breaking
operator pushed HIGHER ⇒ faster restoration.

## What D₄/24-cell buys (exact, and the formalizable crux)

Basic-invariant degrees (Weyl-group degrees = exponents + 1):
- **B₄ (hypercubic), order 384:** degrees **{2, 4, 6, 8}** — a degree-4 anisotropy invariant exists.
- **F₄ (24-cell), order 1152:** degrees **{2, 6, 8, 12}** — NO degree-4 invariant; first above the
  isotropic quadratic is degree 6.

So the leading rotation-breaking operator: degree **4** (hypercubic) vs degree **≥6** (24-cell). The
hypercubic O(a²) rotation-breaking corrections become O(a⁴) on the 24-cell — a genuine, known improvement.

**The crux is a trivial finite computation.** Let `A₄(x) = x₁⁴+x₂⁴+x₃⁴+x₄⁴` (the leading hypercubic
anisotropy; its O(4)-traceless part is the actual breaking operator) and `Q₂(x) = Σx_i²` (the O(4)
quadratic). The extra 24-cell/D₄ generator beyond signed permutations is the orthogonal Hadamard map
`H₄ = ½·[[1,1,1,1],[1,−1,1,−1],[1,1,−1,−1],[1,−1,−1,1]]` (`H₄ᵀH₄ = I`). On `x = (1,0,0,0)`:
- `Q₂(H₄x) = 4·(½)² = 1 = Q₂(x)` — the isotropic quadratic is preserved (H₄ ∈ O(4)). ✓
- `A₄(H₄x) = 4·(½)⁴ = ¼ ≠ 1 = A₄(x)` — the degree-4 anisotropy is BROKEN by the larger symmetry. ✓

That single rational witness proves: the leading hypercubic breaking operator is **forbidden** on the
24-cell lattice. Combined with B₄-invariance of `A₄` (signed permutations obviously preserve `Σx_i⁴`), it
establishes the strict improvement degree-4 → degree-≥6, rigorously, with pure `Q'` arithmetic.

## What is PROVABLE vs what stays NAMED

PROVABLE (finite group/invariant theory, axiom-clean):
1. `A₄` is invariant under the hypercubic group B₄ (signed permutations) — it IS the genuine leading
   hypercubic breaking operator.
2. `Q₂` is invariant under `H₄` (H₄ ∈ O(4)) — the isotropic quadratic survives the larger symmetry.
3. `A₄` is NOT invariant under `H₄` — concrete witness `x=(1,0,0,0)`: `A₄=1`, `A₄(H₄x)=¼`. So the 24-cell
   symmetry FORBIDS the degree-4 anisotropy.
4. Conclusion datum: the 24-cell leading-breaking degree is `≥ 6 > 4` — strictly higher than hypercubic.

STILL NAMED (the genuine continuum wall, now SHARPER):
- "A rotation-breaking operator of dimension `d > 4` is RG-irrelevant (its contribution ∝ a^{d−4} → 0)."
  This is the actual continuum analysis and is NOT closed here — but it is now PARAMETERIZED by the
  explicit leading degree, which the group theory shows is larger for the 24-cell. So `rotationRestored`
  becomes a degree-indexed irrelevance input with a provably larger margin on D₄.

## Build decomposition (moderate cost; new but bounded machinery)

1. A tiny 4-variable polynomial + finite-matrix-action layer over `Q'`: vectors `Fin 4 → Q'`, the maps
   `Q₂`, `A₄`, the matrix action, the signed-permutation generators and `H₄`. [moderate — NEW machinery,
   but small and concrete; `decide`/rational arithmetic discharges the identities]
2. PROVE (1)–(3) above: `A₄` B₄-invariant; `Q₂` H₄-invariant; `A₄` not H₄-invariant (the `(1,0,0,0)`
   witness). [small once layer exists]
3. A `LatticeAnisotropy` datum carrying the point group's `leadingBreakDegree` with the two instances —
   `hypercubicAnisotropy` (degree 4, witnessed by surviving `A₄`) and `cell24Anisotropy` (degree ≥6,
   witnessed by `A₄` broken) — and the PROVED strict inequality `4 < cell24.leadingBreakDegree`. [small]
4. Recast `O4ConnectedInput.rotationRestored`: a `RotationRestorationInput` parameterized by
   `leadingBreakDegree` + the named irrelevance `Prop` FOR THAT DEGREE; the D₄ instance carries the larger
   degree. Feed it back into `O4ConnectedInput` so the O(4) accounting now exposes the explicit margin
   instead of an opaque Prop. [small]

New file: `RepTheory/LatticeAnisotropy.lean` (or `Continuum/RotationRestoration.lean`). Axiom-clean target.

## Honest caveats

- This does NOT close the continuum rotation-restoration wall. It proves the GROUP-THEORY input that
  *selects* the leading breaking operator, and shows the 24-cell pushes it strictly higher — converting an
  opaque `Prop` into a degree-parameterized, provably-weaker named input. The RG-irrelevance of the
  higher-degree operator remains the genuine analytic obligation.
- We do NOT reprove the full F₄ invariant-ring classification ({2,6,8,12}) — that is Chevalley/Shephard–Todd
  and heavy. We prove the LEADING-ORDER fact concretely (degree-4 anisotropy killed by `H₄`), which suffices
  for the strict improvement at the controlling order. The full higher-degree classification is cited.
- The 24-cell/D₄ gauge discretization is a legitimate but LESS-STANDARD regulator (root-lattice / simplicial
  / "quantum finite element" lattice gauge theory). Its yielding the SAME continuum universality class as the
  hypercubic regulator is standard lore but is itself a (believed, unproven) universality input — note it.
- New polynomial/matrix-action machinery is required (4-var `Q'` polynomials under a finite matrix group).
  Bounded and concrete, but it is genuinely new scaffolding, not reuse.

## Recommendation

Build it (steps 1–4). Moderate cost, low risk; the crux is a single exact `Q'` witness. It is the rigorous
realization of the original intuition — 4D's exceptional 24-cell symmetry pushes rotation-breaking to higher
order — and it upgrades `rotationRestored` from an opaque assumption to a quantitative, provably-weaker
named wall. It does not, and does not claim to, close the continuum limit.
