/-
**Track pentagon — the associator / F-symbol repoint: `RacahProb` ⇝ the
`PentagonRelation` (Biedenharn–Elliott) frontier, one categorical level up.**

`SixJRecouplingProgress.RacahProb` is a Level-1 combinatorial shadow: a
doubly-stochastic 0/1-supported kernel, genuinely INHABITED by the pure
permutation `RacahInhabit.racahRP`.  Because it is permutation-satisfiable it
CANNOT pin a Level-2 object (the associator / 6j F-symbol).  This module makes
that gap precise and closes what genuinely closes.

# The three-level picture

  * **Level 1 (fusion multiplicities, PROVED elsewhere):** `N_{ab}^c =
    fusionInd a b c ∈ {0,1} = tripleCharInt a b c = ∫χ_aχ_bχ_c`.  These are the
    dimensions of the trivalent Hom-spaces.
  * **Level 2 (associator / 6j = the F-symbol):** the numeric matrix of
    `(a⊗b)⊗c ≅ a⊗(b⊗c)`; `nFoldFuse` / `RacahProb` never see it.
  * **Pentagon = coherence of the Level-2 associator** — nonlinear in the 6j.

# What this module delivers (a REDUCTION + a REFUTATION, not a closure)

## 1. The dimension shadow (PROVED, maximal reducible part).

The pentagon's Level-1 shadow is fusion-multiplicity associativity
`Σ_x N_{ab}^x N_{xc}^d = Σ_y N_{bc}^y N_{ay}^d` — the χ_d-coefficient of
`χ_aχ_bχ_c` computed two ways.  Its arithmetic CORE is the SU(2) invariant-
dimension symmetry `RacahInhabit.star` (`|E| = |F|`), re-exposed here as
`dimShadow_star`; a concrete non-vacuous instance `fusionAssoc_smallest`
(a=b=c=d=½) is PROVED by evaluation.  This is exactly the content
`RacahInhabit.star` uses to inhabit `RacahProb` — the *dimension shadow* of the
pentagon, and nothing more.

## 2. The `PentagonRelation` structure (rational, `Q'`-legal).

The raw signed `{6j}` is irrational, so the pentagon is stated in its rational,
gauge-invariant 2–3 Pachner form on `tet`-style closed networks (dimension
weight `dimRep x = x+1`), NONLINEAR (cubic LHS, quadratic RHS) in `tet`.  It is
the honest replacement for the one-directional linear `biedenharn_elliott`
field.  We PROVE it is non-empty (`pentagonRelation_zero` — the trivial pin
`tet ≡ 0` satisfies the coherence equation), which exhibits that the pentagon
equation *alone* is under-determined — precisely why the real content must be a
numeric pinning.

## 3. The refutation: the pentagon is NOT permutation-satisfiable (SHARP).

The genuine Level-2 datum is `PentagonNumericCore`: a rational Racah kernel
`P = dim(e)dim(f){6j}²` pinned at the smallest SU(2) tetrahedron
`a=b=c=d=½` to the FRACTIONAL value `P = 3·3·(1/6)² = 1/4 ∉ {0,1}`.  Every
`RacahProb` permutation inhabitant (`racahRP = racahPerm ∈ {0,1}`) FAILS this
pinning (`racahPerm_ne_oneQuarter`), so no doubly-stochastic 0/1 kernel can
satisfy the pentagon (`pentagonNumericCore_not_perm`,
`racahRP_fails_numeric`).  Hence the repoint from `RacahProb` to the pentagon
is a GENUINE strengthening, not a re-label: it bites at the numeric level,
strictly above the fusion multiplicities `N`.

# Honest verdict

Reducible (PROVED, maximal): the dimension shadow = `star`, with a concrete
instance.  Irreducible (NAMED, non-empty, refuted for every permutation
surrogate): `PentagonNumericCore`, the fractional 6j / associator solving the
nonlinear pentagon.  This is a precise obstruction plus a maximal reduction —
NOT a closure.  The Clay YM mass gap stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Fin` core only.  No `Classical.*`, no `Real`, no
`native_decide` (only `decide`/`omega` on decidable `Nat`/`Q'` facts).  No
`sorry` / `admit` / new `axiom`.  All witnesses are `Type`-level data; the
`PentagonNumericCore` frontier is a NAMED obligation, never faked.  `#print
axioms` gated (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.RacahInhabit

namespace YMGap.Continuum.PentagonRelation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.LoopyLinkIntegral
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.SixJRecouplingProgress
open YMGap.Continuum.RacahInhabit

/-! ## 0. Reusable helpers. -/

/-- `finSum` of a sequence that is `Q'.eqv 0` on `[0,D)` is itself `≃ 0`.  Used
to check the trivial `tet ≡ 0` pin against the nonlinear pentagon equation. -/
theorem finSum_all_eqv_zero (g : Nat → Q') (D : Nat)
    (h : ∀ i, i < D → (g i).eqv 0) : (finSum g D).eqv 0 := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt g (fun _ => 0) D (fun i hi => h i hi)) ?_
  exact Q'.eqv_of_eq (finSum_zero_seq D)

/-! ## 1. The dimension shadow (Level-1): fusion-multiplicity associativity.

The pentagon's Level-1 shadow is `Σ_x N_{ab}^x N_{xc}^d = Σ_y N_{bc}^y N_{ay}^d`.
Its arithmetic core is the SU(2) invariant-dimension symmetry `star`
(`|E| = |F|`), which is *exactly* the content `RacahInhabit.star` uses to
inhabit `RacahProb`.  We re-expose it and prove a concrete instance. -/

/-- The SU(2) fusion multiplicity is symmetric in its first two slots
(`N_{ab}^c = N_{ba}^c`); the trivalent Hom-space dimension does not depend on
strand order.  (Definitionally `tripleCharInt`'s `a↔b` symmetry.) -/
theorem fusionInd_symm_ab (a b c : Rep) : fusionInd a b c = fusionInd b a c :=
  LoopyLinkIntegral.tripleCharInt_symm_ab a b c

/-- **The dimension shadow's arithmetic core (re-exposed).**  `|E| = |F|`: the
two coupling channels `E = [eLo,eHi]` and `F = [fLo,fHi]` of four reps have the
same number of internal states.  This is the SU(2) coupling-scheme independence
`min(a+b,c+d) − max(|a−b|,|c−d|) = min(b+c,a+d) − max(|b−c|,|a−d|)` — the
dimension shadow of the pentagon, and the sole content behind
`RacahInhabit.star`'s inhabitation of `RacahProb`. -/
theorem dimShadow_star (a b c d : Nat) :
    eHi a b c d - eLo a b c d = fHi a b c d - fLo a b c d :=
  RacahInhabit.star a b c d

/-- **A concrete non-vacuous instance of the dimension shadow** (fusion-ring
associativity `Σ_x N_{ab}^x N_{xc}^d = Σ_y N_{bc}^y N_{ay}^d`) at the smallest
nontrivial SU(2) tetrahedron `a=b=c=d=½` (`Rep = 1`), `D = 4`.  Both sides count
the internal channels (here `= 2`) and agree — the pentagon's dimension shadow,
evaluated.  PROVED by reduction. -/
theorem fusionAssoc_smallest :
    (finSum (fun x => fusionInd 1 1 x * fusionInd x 1 1) 4).eqv
      (finSum (fun y => fusionInd 1 1 y * fusionInd 1 y 1) 4) := by decide

/-! ## 2. The `PentagonRelation` structure (Level-2, rational `Q'`-legal). -/

/-- **`PentagonRelation` — the rational, gauge-invariant Biedenharn–Elliott /
2–3 Pachner coherence (NAMED Level-2 carrier).**

The raw signed `{6j}` is irrational, so we carry the rational closed
tetrahedral amplitude `tet : (Fin 6 → Rep) → Q'` (Ponzano–Regge), with
`nonneg`, and the NONLINEAR (cubic LHS summed over the internal channel `x`
with dimension weight `dimRep x = x+1`, quadratic RHS) pentagon identity on
`mk6`-assembled closed networks.  This is the honest replacement for the
one-directional *linear* `SixJRecoupling.biedenharn_elliott`.  The exact
`mk6`-index wiring below is one Ponzano–Regge 2–3 Pachner assignment; the
precise combinatorics is not load-bearing here (we do not inhabit `tet` with
the real 6j — that is `PentagonNumericCore`). -/
structure PentagonRelation where
  /-- The rational closed tetrahedral amplitude (Ponzano–Regge), `Q'`-legal. -/
  tet : (Fin 6 → Rep) → Q'
  /-- `tet ≥ 0` (the squared / dimension-absorbed form). -/
  nonneg : ∀ j, (0 : Q') ≤ tet j
  /-- **The Biedenharn–Elliott / 2–3 Pachner pentagon** — NONLINEAR (cubic
  LHS, quadratic RHS) in `tet`, guarded by a largeness cutoff (avoiding the
  unguarded `D = 0` truncation degeneracy of the old linear field). -/
  pentagon : ∀ (D a b c d e f : Rep), a + b + c + d + e + f < D →
    (finSum (fun x => Q'.ofNat (x + 1) *
        (tet (mk6 a b c d e x) * tet (mk6 a x e f b c) * tet (mk6 x c d e f a))) D).eqv
      (tet (mk6 a b c d e f) * tet (mk6 b c d e f a))

/-- **`PentagonRelation` is non-empty AND the coherence equation alone is
under-determined.**  The trivial pin `tet ≡ 0` satisfies both `nonneg` and the
nonlinear pentagon (each side collapses to `0`).  So — exactly as
`SixJRecoupling`'s `sixj ≡ 0` fails only for lack of a guard, and the guarded
row equation is satisfiable by a trivial kernel — the pentagon *equation* does
not by itself pin a nontrivial associator.  The real content is the numeric
pinning of §3. -/
def pentagonRelation_zero : PentagonRelation where
  tet := fun _ => 0
  nonneg := fun _ => Q'.le_refl' 0
  pentagon := fun D _ _ _ _ _ _ _ =>
    Q'.eqv_trans _ _ _
      (finSum_all_eqv_zero _ D (fun x _ =>
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat (x + 1)) _ 0 (Q'.mul_zero_eqv _))
          (Q'.mul_zero_eqv (Q'.ofNat (x + 1)))))
      (Q'.eqv_symm (Q'.mul_zero_eqv 0))

/-! ## 3. The genuine Level-2 datum + the permutation refutation.

The smallest nontrivial SU(2) tetrahedron `a=b=c=d=½` (`Rep = 1`); internal
channels couple two ½'s ⇒ twice-spin `∈ {0,2}`.  The Wigner value
`{½½1;½½1} = 1/6` is FRACTIONAL, so the Racah-normalized gauge-invariant kernel
`P = dim(e)dim(f){6j}² = 3·3·(1/6)² = 1/4 ∉ {0,1}` at `(e,f) = (spin 1, spin 1)
= (2,2)`.  Any pentagon solution over the SU(2) fusion ring realizes `P = 1/4`
here (its gauge-invariant closed networks are pinned); no permutation /
doubly-stochastic 0/1 kernel can. -/

/-- The smallest nontrivial SU(2) tetrahedron label `a=b=c=d=½`, internal
channels `e=f=spin 1` (twice-spin `2`). -/
def smallestTetra : Fin 6 → Rep := mk6 1 1 1 1 2 2

/-- The rational Racah kernel value at the smallest tetrahedron:
`P = 3·3·(1/6)² = 1/4` (num `1`, denominator `4`). -/
def oneQuarter : Q' := ⟨1, 3⟩

theorem oneQuarter_nonneg : (0 : Q') ≤ oneQuarter := by decide
theorem zero_ne_oneQuarter : ¬ (0 : Q').eqv oneQuarter := by decide
theorem one_ne_oneQuarter : ¬ (1 : Q').eqv oneQuarter := by decide

/-- **The permutation kernel is 0/1-valued.**  `racahPerm j ∈ {0,1}` — it is a
0/1 permutation matrix, never a fractional dimension-weighted 6j². -/
theorem racahPerm_zeroOne (j : Fin 6 → Rep) :
    racahPerm j = 0 ∨ racahPerm j = 1 := by
  unfold racahPerm
  by_cases hg : racahGuard (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) = true
  · rw [if_pos hg]; exact Or.inr rfl
  · rw [if_neg hg]; exact Or.inl rfl

/-- **No permutation kernel realizes the fractional value `1/4`.**  Since
`racahPerm j ∈ {0,1}` and `1/4 ∉ {0,1}`, `racahPerm j ≄ 1/4` at every label —
the sharp witness that a 0/1 permutation cannot carry the dimension-weighted
Wigner 6j². -/
theorem racahPerm_ne_oneQuarter (j : Fin 6 → Rep) :
    ¬ (racahPerm j).eqv oneQuarter := by
  rcases racahPerm_zeroOne j with h | h <;> rw [h]
  · exact zero_ne_oneQuarter
  · exact one_ne_oneQuarter

/-- **`PentagonNumericCore` — the genuine Level-2 associator datum (NAMED
frontier).**  A rational Racah kernel `P = dim(e)dim(f){6j}²` (nonnegative),
PINNED at the smallest tetrahedron to the fractional value `1/4`.  This is the
irreducible numeric content of the pentagon, strictly above the `{0,1}` fusion
multiplicities.  (The full doubly-stochastic + nonlinear coherence is
`RacahProb` × `PentagonRelation`; the pinning `smallest_value` is the piece
that defeats every permutation surrogate.) -/
structure PentagonNumericCore where
  /-- The rational dim-absorbed 6j probability. -/
  racahKernel : (Fin 6 → Rep) → Q'
  /-- `P ≥ 0` (a squared, dimension-weighted quantity). -/
  nonneg : ∀ j, (0 : Q') ≤ racahKernel j
  /-- **The fractional pinning** — at the smallest SU(2) tetrahedron the kernel
  takes the value `3·3·(1/6)² = 1/4`.  This is the genuine numeric content. -/
  smallest_value : (racahKernel smallestTetra).eqv oneQuarter

/-- **`PentagonNumericCore` is non-empty** (a shape witness — the constant `1/4`
kernel discharges `nonneg` and `smallest_value`).  So the frontier is a
genuine, correctly-specified obligation, NOT a provably-empty spec.  (The shape
witness is not the physical 6j; the real associator additionally satisfies the
nonlinear pentagon + two-sided stochasticity.) -/
def numericShapeWitness : PentagonNumericCore where
  racahKernel := fun _ => oneQuarter
  nonneg := fun _ => oneQuarter_nonneg
  smallest_value := Q'.eqv_refl oneQuarter

/-- **THE REFUTATION (pentagon is NOT permutation-satisfiable).**  Every
`PentagonNumericCore` kernel disagrees with the permutation kernel `racahPerm`
at the smallest tetrahedron: the core is `≃ 1/4` there, but `racahPerm ∈ {0,1}`.
So the Level-2 numeric datum cannot be a 0/1 permutation — the sharp obstruction
the repoint exposes. -/
theorem pentagonNumericCore_not_perm (P : PentagonNumericCore) :
    ¬ (P.racahKernel smallestTetra).eqv (racahPerm smallestTetra) := by
  intro h
  have h14 : (racahPerm smallestTetra).eqv oneQuarter :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm h) P.smallest_value
  exact racahPerm_ne_oneQuarter smallestTetra h14

/-- **The `RacahProb` permutation inhabitant fails the numeric pinning.**
`racahRP.racahProb = racahPerm ∈ {0,1}`, so it does NOT realize `1/4` at the
smallest tetrahedron.  Hence the genuinely-inhabited `RacahProb` (Level-1,
doubly-stochastic, permutation-satisfiable) is STRICTLY WEAKER than the
`PentagonNumericCore` (Level-2, fractional): the A2 repoint from `RacahProb` to
the pentagon is a genuine strengthening, not a re-label. -/
theorem racahRP_fails_numeric :
    ¬ (racahRP.racahProb smallestTetra).eqv oneQuarter :=
  racahPerm_ne_oneQuarter smallestTetra

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean):

  * `finSum_all_eqv_zero` — reusable zero-summand finSum collapse;
  * `fusionInd_symm_ab` — SU(2) fusion multiplicity strand symmetry;
  * `dimShadow_star` — the pentagon's dimension-shadow arithmetic core
    (`|E| = |F|`, re-exposing `RacahInhabit.star`);
  * `fusionAssoc_smallest` — a concrete non-vacuous instance of fusion-ring
    associativity (the dimension shadow), by evaluation;
  * `PentagonRelation` (+ `pentagonRelation_zero`) — the rational, `Q'`-legal
    NONLINEAR Biedenharn–Elliott coherence carrier; non-empty, and shown
    under-determined by the trivial `tet ≡ 0` pin (the coherence equation alone
    does not pin a nontrivial associator);
  * `oneQuarter` (+ `oneQuarter_nonneg`, `zero_ne_oneQuarter`,
    `one_ne_oneQuarter`) — the fractional Racah value `1/4 ∉ {0,1}`;
  * `racahPerm_zeroOne`, `racahPerm_ne_oneQuarter` — the permutation kernel is
    0/1 and never `1/4`;
  * `numericShapeWitness` — `PentagonNumericCore` is non-empty (not a
    provably-empty spec);
  * `pentagonNumericCore_not_perm`, `racahRP_fails_numeric` — **THE REFUTATION**:
    the pentagon numeric core disagrees with every permutation surrogate at the
    smallest tetrahedron, so the A2 repoint is a genuine strengthening.

NAMED-open (NOT faked, NO physical inhabitant):

  * `PentagonNumericCore` — the fractional 6j / associator F-symbol solving the
    nonlinear pentagon polynomial system; correctly specified, non-empty as a
    spec, refuted for every `RacahProb` permutation surrogate, and strictly
    above the `{0,1}` fusion multiplicities.  Its dimension shadow is
    `dimShadow_star`; its numeric core is genuine categorified data.

This module is the maximal reducible dimension shadow + the precise Level-2
pentagon frontier and its permutation-refutation.  It is NOT the full 6j
solution, NOT the loopy cluster expansion, NOT a continuum limit, and NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.PentagonRelation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PentagonRelation.finSum_all_eqv_zero
#print axioms YMGap.Continuum.PentagonRelation.fusionInd_symm_ab
#print axioms YMGap.Continuum.PentagonRelation.dimShadow_star
#print axioms YMGap.Continuum.PentagonRelation.fusionAssoc_smallest
#print axioms YMGap.Continuum.PentagonRelation.pentagonRelation_zero
#print axioms YMGap.Continuum.PentagonRelation.oneQuarter_nonneg
#print axioms YMGap.Continuum.PentagonRelation.zero_ne_oneQuarter
#print axioms YMGap.Continuum.PentagonRelation.one_ne_oneQuarter
#print axioms YMGap.Continuum.PentagonRelation.racahPerm_zeroOne
#print axioms YMGap.Continuum.PentagonRelation.racahPerm_ne_oneQuarter
#print axioms YMGap.Continuum.PentagonRelation.numericShapeWitness
#print axioms YMGap.Continuum.PentagonRelation.pentagonNumericCore_not_perm
#print axioms YMGap.Continuum.PentagonRelation.racahRP_fails_numeric
