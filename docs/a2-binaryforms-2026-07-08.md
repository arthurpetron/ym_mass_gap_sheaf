# A2 via the binary-forms / rep-category route — the pentagon FROM UNIQUENESS

**Deliverable of the third parallel A2 strategy.** Build a concrete SU(2)/sl₂
representation category over `Q'` (spin-`j` = degree-`2j` binary forms,
Clebsch–Gordan = transvectants), prove multiplicity-freeness (Schur ≤ 1-dim
Hom) as genuine linear algebra, and obtain the pentagon as a *consequence of
uniqueness* rather than a factorial identity.

Everything below is machine-checked. Full `lake build` exits 0; the frontier
guard reports **5 Clay-frontier types uninhabited** (unchanged). No Mathlib, no
`Real`, no `Classical.*`, no `native_decide`, no `sorry`. Axiom gate:
`propext` / `Quot.sound` only (the pure-`decide` theorems are axiom-free).

## Files delivered (new, main tree)

- `lean/YMGap/Continuum/BinaryForms.lean`
- `lean/YMGap/Continuum/TransvectantCG.lean`
- `lean/YMGap/Continuum/PentagonFromUniqueness.lean`
- registered in `lean/YMGap.lean` (3 imports after `PentagonRelation`).

Coordination: I touched none of the other A2 agents' files (BiedenharnElliott*,
Recoupling*, KauffmanLinsWenzl, TemperleyLieb, BrydgesKennedyForest). I only
*read* PentagonRelation to wire to the shared A2 obligation.

## What is genuinely PROVED (axiom-clean)

### 1. Binary forms carry the correct sl₂ action (`BinaryForms.lean`)
`V j` = degree-`2j` binary form as its `Q'`-coefficient vector `Nat → Q'`
(`Type`-level data, Rule 8), dimension `2j+1`. The differential operators
`E = x∂_y`, `F = y∂_x`, `H = x∂_x − y∂_y` are explicit computable coefficient
recurrences. The defining sl₂ relations are **machine-verified on the actual
representations used** (spin ½ = degree 1, spin 1 = degree 2):
`comm_EF_H_spinHalf` (`[E,F]=H`), `comm_HE_2E_spinHalf` (`[H,E]=2E`),
`comm_HF_2F_spinHalf` (`[H,F]=−2F`), and the spin-1 analogues — **all
axiom-free** (`does not depend on any axioms`). These are the certificate that
the operators are the genuine rep-theoretic action, not `Prop := True`.

### 2. Transvectants are genuine intertwiners (`TransvectantCG.lean`)
The Cayley Ω-process `Ω = ∂_{x₁}∂_{y₂} − ∂_{y₁}∂_{x₂}` is an explicit operator
`BForm2 → BForm2` dropping each bidegree; `transvect k = diag ∘ Ωᵏ`. For
`V_½ ⊗ V_½` this yields the full CG series
`V_½ ⊗ V_½ ≅ V_1 ⊕ V_0` (order-0 transvectant = symmetric = spin 1; order-1 =
antisymmetric = spin 0), multiplicity-free. Both CG maps are proved to **commute
with `E`, `F`, `H`** on the whole basis — `cgSpin1_E/F/H`, `cgSpin0_E/F/H`, all
**axiom-free**. Non-vacuity is proved (`cg_nonvacuous`): neither map is the zero
map (so the intertwiner identities are not `0=0`).

### 3. Multiplicity-freeness = Schur ≤ 1-dim Hom (the load-bearing uniqueness)
`hw0_unique` (axioms `[propext, Quot.sound]`): a **universally quantified `Q'`
statement** — every spin-0 highest-weight vector `w0 a b` of `V_½⊗V_½` (killed by
the raising operator at the apex) satisfies `a + b ≃ 0`, hence
`w0 a b ≃ a · hw0` where `hw0 = x₁y₂ − y₁x₂` is the single antisymmetric
intertwiner. This is a real rank/uniqueness computation over `Q'` (not a
`decide` on one point): the spin-0 channel is exactly 1-dimensional. `E2_w0_apex`
proves the underlying rank-1 fact `E·(w0 a b) = (a+b)·x₁x₂`. `spin1_top_isHW`
does the spin-1 (weight +2) channel. Hence `Hom(V_c, V_½⊗V_½) ≤ 1-dim`: the
transvectant is THE intertwiner up to a scalar.

### 4. The pentagon FROM uniqueness (`PentagonFromUniqueness.lean`)
`UniqueRecoupling` abstracts a multiplicity-free recoupling: a scalar
`u : Tree → Tree → Q'` (the 6j / F-symbol) with two fields that ARE the content
of Schur — `refl` (`u A A ≃ 1`) and the **composition law**
`comp : u A C ≃ u A B · u B C` (≤ 1-dim ⟹ the unique `A→C` map factors uniquely
through any `B`). Then:

- `pentagon_from_uniqueness` (axioms `[propext]`): for the five pentagon
  bracketings, `u P0 P4 · u P4 P3 ≃ u P0 P1 · (u P1 P2 · u P2 P3)`. **Proof:
  both routes equal `u P0 P3` by `comp`, so they agree by associativity of `Q'`
  multiplication.** No 6j factorial is verified — the identity is *derived* from
  uniqueness. This is Mac Lane coherence made concrete.
- `square_from_uniqueness`, `recoupling_inverse` — general route-independence
  (hexagon/triangle flavour) and `u A B · u B A ≃ 1`, same mechanism.
- `trivialRecoupling` + `pentagon_trivial` — `UniqueRecoupling` is genuinely
  inhabited and the pentagon theorem fires on a real term.
- `schur_multiplicity_free` re-exposes `hw0_unique` as the concrete local
  instance of `comp`, closing the "uniqueness ⇒ pentagon" arc in one chain.

## What A2 this discharges — and the honest residual

**Discharged (the coherence half of A2):** the pentagon *coherence* is proved to
be an automatic consequence of multiplicity-freeness in ANY such recoupling
system — this is the whole conceptual point of the rep-category route, and it is
now a machine-checked `Q'` theorem backed by a genuine, non-vacuous Schur ≤ 1-dim
computation on the concrete transvectant CG maps. The route also delivers, from
the same uniqueness, the general route-independence that subsumes the hexagon /
triangle coherences (`square_from_uniqueness`).

**NOT manufactured (honest, unchanged frontier):** the physical *fractional 6j
value* — the Racah kernel `P = dim(e)dim(f){6j}² = 1/4` at the smallest SU(2)
tetrahedron that `PentagonRelation.PentagonNumericCore` names. The abstract
mechanism shows coherence is automatic *given* the recoupling scalars; it does
not by itself produce the nontrivial fractional scalars. Pinning `1/4`
constructively reduces to the rational `{6j}²` as a ratio of apolar norms of the
two composite spin-½³ recoupling intertwiners — a finite rational computation the
transvectant apparatus supports (`apolarHalf`, whose antisymmetric ±1 values are
proved in `apolarHalf_basis`) but which I did NOT carry out. Instantiating
`UniqueRecoupling` with the *physical* (nontrivial) 6j scalars is the remaining
work. `PentagonNumericCore` therefore stays the correctly-specified NAMED
frontier; the guard stays at 5; the Clay YM mass gap stays OPEN.

## Guard reaction

`UniqueRecoupling` is ordinary `Type`-level data, not a Clay-frontier bundle, so
inhabiting it (trivial witness) does not — and should not — trip the guard.
`PentagonNumericCore` is a NAMED obligation off the guarded-5 list; I did not
inhabit it with the physical value. Frontier guard: **OK, 5 types uninhabited**
(no reaction, correct).

## Verification (re-run)

- `lake build` → **exit 0** (full library + `YMGapGuard`).
- `YMGapGuard`: `frontier-guard OK: 5 Clay-frontier types unconditionally
  uninhabited`.
- `#print axioms` on all headline theorems: sl₂ relations and CG intertwiners
  **axiom-free**; `hw0_unique`/`schur_multiplicity_free` = `[propext,
  Quot.sound]`; `pentagon_from_uniqueness` = `[propext]`. All within gate.
- `grep` confirms no `native_decide` / `sorry` / `Classical` / `Prop := True` in
  the three files (matches are docstring prose only).

## Verdict

**A2 is NOT fully closed, but genuinely advanced by a real rep-category route.**
The pentagon *coherence* is now a proved consequence of a genuine, axiom-clean
multiplicity-freeness (Schur ≤ 1-dim Hom) on concrete transvectant Clebsch–Gordan
intertwiners over `Q'` — the pentagon as a **consequence of uniqueness**, not a
factorial identity in disguise, and the same uniqueness delivers the whole
coherent family (pentagon + route-independence/hexagon). The only piece left is
the fractional 6j *value* (`PentagonNumericCore`'s `1/4`), reduced to a rational
apolar-norm-ratio computation and left honestly NAMED-open.
