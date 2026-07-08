# A2-quadratic: repairing the SU(2) {6j} pentagon by changing the number system

**File:** `lean/YMGap/Continuum/QuadraticKernel.lean` (new, imported in `YMGap.lean`)
**Status:** full `lake build` green (765 jobs); `YMGapGuard` OK — 5 Clay-frontier types
unconditionally uninhabited. Axiom-clean: every declaration `[propext]` or
`[propext, Quot.sound]`. No `sorry`/`admit`/`native_decide`/`Classical`/new `axiom`.

## What was built (all genuine, axiom-clean)

### 1. `√` as a well-defined operation (the substrate of the number-system change)
- `sqPos_unique` / `sqrtPos_unique` — a positive real has a UNIQUE positive square
  root (pointwise proof, mirroring `CubeRoot.cubeRoot_unique` with the factorisation
  a²−b²=(a−b)(a+b)). This is the mathematical fact that makes `Q·√Q` a well-defined
  number system.
- `sqrtPos_mul` : √r·√s ≃ √(rs);  `sqrtPos_extract` : c·√s ≃ √(c²s);
  `sqrtPos_congr` : √ respects `Q'.eqv`.

### 2. `QSqrt = Q·√Q` — the exact multi-quadratic kernel
- `QSqrt := List (Q' × Q')` (formal Σ qᵢ·√rᵢ), with `qadd`/`qmul`/`qneg`/`qone`.
- `toCReal : QSqrt → CReal`, proved a `+`/`neg` homomorphism (`toCReal_qadd`,
  `toCReal_qneg`) — so a `QSqrt` equality transports into the `CReal` equality the
  pentagon residual lives in.
- `DecidableEq QSqrt` (structural) + `termEqv` (decidable EXACT value-equality of a
  single formal term — the pair of decidable `Q'` facts).

### 3. The REAL signed 6j inside `QSqrt`
- `sixjQ a b c d e f := [(racahSum a b e c d f, triSqProd a b c d e f)]` — the genuine
  signed `{a b e; c d f}` = racahSum·√triSqProd (NOT a constant/shape witness).
- `sixjQ_bridge : toCReal (sixjQ …) ≃ sixjCReal …` — the QSqrt 6j embeds to the
  existing CReal 6j, so QSqrt proofs discharge CReal residuals.
- `toCReal_sixjQ_sq` — an EXACT QSqrt-multiplication (`sixjQ · sixjQ`, radicand r·r,
  r=triSqProd GENERALLY IRRATIONAL) collapsing through the √-arithmetic to
  racahSum²·triSqProd (the proved rational {6j}²), re-deriving `sixjCReal_sq` through
  the QSqrt layer.

### 4. A genuine transported IRRATIONAL {6j} identity (the payoff)
- `sixjQ_column_symm_exact` : `termEqv … := by decide` — the column-1↔3 symmetry
  {a b e;c d f}={e b a;f d c} at the nondegenerate tetrahedron (½,½,1;2,2,3/2)
  ({6j}=−√5/10) is an EXACT single-term QSqrt equality (racahSum-coeffs and
  triSqProd-radicands agree, each by pure `Q'` `decide`).
- `sixjCReal_column_symm : sixjCReal 1 1 4 4 2 3 ≃ sixjCReal 2 1 3 4 1 4` — a `CReal`
  equality of two IRRATIONAL numbers, established by `decide` over `QSqrt` + the
  bridge. This is exactly what "change the number system, not the identity" buys:
  a `CReal`-undecidable equation becomes a finite exact `Q'` decision.

### 5. The named residual
- `BiedenharnElliottCReal (a…f p q r D)` — the §8 pentagon arrangement
  (Σ_x (−1)^{…}(2x+1){a b x;c d p}{c d x;e f q}{e f x;b a r} = {p q r;e a d}{p q r;f b c})
  written as an ACTUAL Lean `Prop` over the genuine `sixjCReal` — finally naming the
  residual the audit referenced. UNINHABITED (∀-spins), honestly.

## A2 verdict: STRONGLY REDUCED, not closed

- **NOT closed.** `PentagonRelation.PentagonNumericCore` / `BiedenharnElliottCReal`
  have no inhabitant. This is NOT a D-move: the a2 scorecard slot is unchanged; the
  guard remains at 5 (Tier0Scorecard etc. still uninhabited).
- **Strongly reduced.** The pentagon's number system is repaired from `Q` (where the
  signed {6j} provably ∉ Q) to the exact `QSqrt = Q·√Q`, where: the signed 6j is
  exactly representable (`sixjQ`), `√` is well-defined (uniqueness PROVED), the
  embedding to the physical CReal 6j is PROVED (`sixjQ_bridge`), and single-term
  equality is DECIDABLE per tetrahedron (`termEqv`/`decide`) and transports to CReal.
  A concrete irrational-6j identity is closed exactly this way.

## Honest ∀-spins vs finite

- What is proved exactly and transported: single-term `{6j}` equalities (e.g. the
  column symmetry) — genuine, irrational-valued, per-tetrahedron.
- What is NOT proved: the multi-term pentagon SUM. Closing a pentagon instance by
  `decide` needs a value-preserving squarefree-MERGE canonicaliser on `QSqrt` (so the
  Σ_x of three-6j products and the two-6j product reduce to a common squarefree key);
  `sqrtPos_extract`/`sqrtPos_mul` are the per-step lemmas for it, but the list-level
  merge+sort soundness theorem was NOT built (the sharp remaining step). The ∀-spins
  identity is left as the NAMED `BiedenharnElliottCReal` residual.
- No ∀-spins closure is claimed from finitely many `decide`s.

## Guard / axioms
- `lake build` exit 0 (765 jobs); `YMGapGuard`: "frontier-guard OK: 5 … uninhabited".
- `#print axioms` on all load-bearing lemmas ⊆ {propext, Quot.sound}.
- Pentagon-carrier and identities reference the REAL 6j (racahSum/triSqProd), not a
  constant; equality is exact `Q'` (`termEqv`), not a CReal approximation.
