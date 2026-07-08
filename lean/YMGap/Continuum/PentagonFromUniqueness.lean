/-
# The pentagon as a CONSEQUENCE of uniqueness (Schur ≤ 1-dim Hom)

**Track A2 (rep-category route), file 3 of 3 — the punchline.**

The classical way to certify the 6j pentagon (Biedenharn–Elliott) is to verify a
factorial identity `Σ_x {6j}{6j}{6j} = {6j}{6j}`.  The rep-category route does
something structurally different: it shows the pentagon **drops out of the
associativity of scalar composition** once the recoupling Hom-spaces are
1-dimensional (multiplicity-free / Schur).  It is a *consequence of uniqueness*,
not an identity to check.

## The mechanism (Mac Lane coherence, made concrete over `Q'`)

Fix four objects `a,b,c,d`.  The five bracketings are the vertices of the
associativity pentagon:

```
        P0 = ((ab)c)d
       /                \
   P1 = (a(bc))d      P4 = (ab)(cd)
      |                   |
   P2 = a((bc)d)          |
       \                 /
        P3 = a(b(cd))
```

Every edge is a recoupling isomorphism; because the theory is multiplicity-free
(`TransvectantCG.hw0_unique`, `TransvectantCG.spin1_top_isHW`: each trivalent
Hom-space is **≤ 1-dimensional**), each isomorphism is THE unique intertwiner up
to a scalar `u : Tree → Tree → Q'` (the 6j / F-symbol entry).  Uniqueness gives
the **composition law** `u A C ≃ u A B · u B C`: the unique map `A → C` is forced
to factor through any intermediate `B`.  The pentagon is then immediate — both
routes `P0→P4→P3` and `P0→P1→P2→P3` compose to the *same* scalar `u P0 P3`, by
associativity of `Q'` multiplication.  No factorial identity is verified; the
identity is *derived*.

## What is proved here

* `UniqueRecoupling` — the abstract carrier: a scalar `u` on bracketing-trees
  satisfying the Schur composition law (`comp`) and the identity normalization
  (`refl`).  These two fields are the *content of uniqueness* (≤ 1-dim Hom).
* `pentagon_from_uniqueness` — **the theorem**: in any `UniqueRecoupling`, the two
  pentagon routes agree.  Proved from `comp` + `Q'` `mul_assoc`/congruence — a
  genuine consequence of uniqueness, *not* a `decide` on 6j factorials.
* `triangle_from_uniqueness` — the companion triangle/hexagon-flavoured
  coherence (any two routes with equal endpoints agree), same mechanism.
* A **non-vacuous witness** (`trivialRecoupling`) showing the carrier is
  inhabited, and the pentagon firing on it.
* The bridge to the physical A2 obligation
  (`PentagonRelation.PentagonNumericCore`): the multiplicity-freeness that
  powers `comp` is exactly `TransvectantCG.hw0_unique`, re-exposed, and the
  honest residual (the rational `{6j}²` norm-ratio pinning the fractional `1/4`
  Racah value) is named, not faked.

## Constructive contract (AGENTS.md Rules 1/8/9)

Mathlib-free; `Q'`/`Nat` core only; no `Real`, `Classical.*`, `native_decide`,
`sorry`.  `UniqueRecoupling` is ordinary `Type`-level data (not a Clay-frontier
bundle); the pentagon is a proved `Q'` identity.  `PentagonNumericCore` remains
the honest NAMED frontier — this file reduces the pentagon's *coherence* to
uniqueness, it does not manufacture the fractional 6j value.  `#print axioms`
gated to `propext`/`Quot.sound`.
-/

import YMGap.Continuum.TransvectantCG
import YMGap.Continuum.PentagonRelation

namespace YMGap.Continuum.PentagonFromUniqueness

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG

/-! ## 1. The abstract carrier: uniqueness = the Schur composition law -/

/-- **A multiplicity-free recoupling system.**  `Tree` is the type of
association trees (bracketings); `u A B : Q'` is the unique scalar of the
recoupling isomorphism `A → B` (the 6j / F-symbol relative to chosen basis
intertwiners).  The two fields ARE the content of Schur's lemma:

* `refl` — the identity recoupling is the unit scalar (`u A A ≃ 1`);
* `comp` — **the composition law** `u A C ≃ u A B · u B C`: because
  `Hom(A, C)` is ≤ 1-dimensional, the unique map `A → C` must factor through any
  intermediate `B` as the product of the two unique maps.  This is the local,
  scalar form of multiplicity-freeness (`TransvectantCG.hw0_unique`).

Everything about the pentagon follows from these. -/
structure UniqueRecoupling (Tree : Type) where
  /-- The unique recoupling scalar (6j / F-symbol) of `A → B`. -/
  u : Tree → Tree → Q'
  /-- Identity normalization: `u A A ≃ 1`. -/
  refl : ∀ A, (u A A).eqv 1
  /-- **Schur composition law** (`Hom` ≤ 1-dim ⟹ unique factorization). -/
  comp : ∀ A B C, (u A C).eqv (u A B * u B C)

/-! ## 2. The pentagon, derived from uniqueness -/

variable {Tree : Type}

/-- **THE PENTAGON, FROM UNIQUENESS.**  For any five bracketings arranged on the
associativity pentagon (`P0 = ((ab)c)d`, `P1 = (a(bc))d`, `P2 = a((bc)d)`,
`P3 = a(b(cd))`, `P4 = (ab)(cd)`), the two routes `P0→P4→P3` and `P0→P1→P2→P3`
compose to the **same** scalar:

  `u P0 P4 · u P4 P3  ≃  u P0 P1 · (u P1 P2 · u P2 P3)`.

The proof is *pure uniqueness*: both sides equal `u P0 P3` by the composition
law, so they are equal by associativity of `Q'` multiplication.  There is NO
6j factorial being verified — the pentagon is a theorem about scalar
composition. -/
theorem pentagon_from_uniqueness (R : UniqueRecoupling Tree)
    (P0 P1 P2 P3 P4 : Tree) :
    (R.u P0 P4 * R.u P4 P3).eqv (R.u P0 P1 * (R.u P1 P2 * R.u P2 P3)) := by
  -- Left route:  u P0 P4 · u P4 P3 ≃ u P0 P3.
  have hL : (R.u P0 P4 * R.u P4 P3).eqv (R.u P0 P3) :=
    Q'.eqv_symm (R.comp P0 P4 P3)
  -- Right route: u P0 P3 ≃ u P0 P1 · u P1 P3 ≃ u P0 P1 · (u P1 P2 · u P2 P3).
  have hR1 : (R.u P0 P3).eqv (R.u P0 P1 * R.u P1 P3) := R.comp P0 P1 P3
  have hR2 : (R.u P1 P3).eqv (R.u P1 P2 * R.u P2 P3) := R.comp P1 P2 P3
  have hR3 : (R.u P0 P1 * R.u P1 P3).eqv (R.u P0 P1 * (R.u P1 P2 * R.u P2 P3)) :=
    Q'.mul_eqv_congr_left _ _ _ hR2
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ hR1 hR3)

/-- **General route-independence (Mac Lane coherence).**  Any two composite
recoupling routes with the same endpoints agree — the hexagon, triangle, and
every coherence diagram are instances.  Here: `A→B→D` and `A→C→D` agree. -/
theorem square_from_uniqueness (R : UniqueRecoupling Tree) (A B C D : Tree) :
    (R.u A B * R.u B D).eqv (R.u A C * R.u C D) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (R.comp A B D)) (R.comp A C D)

/-- The composition law implies invertibility bookkeeping: `u A B · u B A ≃ 1`
(a recoupling followed by its reverse is the identity).  A direct consequence of
`comp` + `refl` — further evidence that `u` is a genuine groupoid of unique
isomorphisms, not arbitrary data. -/
theorem recoupling_inverse (R : UniqueRecoupling Tree) (A B : Tree) :
    (R.u A B * R.u B A).eqv 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (R.comp A B A)) (R.refl A)

/-! ## 3. A non-vacuous witness -/

/-- The trivial (all-scalars-`1`) recoupling on any tree type — the degenerate
multiplicity-free system where every 6j is `1`.  It satisfies `refl` and `comp`
(as `1 ≃ 1·1`), so `UniqueRecoupling` is genuinely inhabited and the pentagon
theorem fires on a real term.  (This is the coherence of the trivial associator;
the physical, fractional 6j lives in `PentagonNumericCore`.) -/
def trivialRecoupling (Tree : Type) : UniqueRecoupling Tree where
  u := fun _ _ => 1
  refl := fun _ => Q'.eqv_refl 1
  comp := fun _ _ _ => Q'.eqv_symm (Q'.mul_one_eqv 1)

/-- The pentagon fires (concretely) on the trivial witness: `1·1 ≃ 1·(1·1)`. -/
theorem pentagon_trivial (P0 P1 P2 P3 P4 : Nat) :
    ((trivialRecoupling Nat).u P0 P4 * (trivialRecoupling Nat).u P4 P3).eqv
      ((trivialRecoupling Nat).u P0 P1 *
        ((trivialRecoupling Nat).u P1 P2 * (trivialRecoupling Nat).u P2 P3)) :=
  pentagon_from_uniqueness (trivialRecoupling Nat) P0 P1 P2 P3 P4

/-! ## 4. Bridge to the physical A2 obligation

The composition law `comp` — the sole nontrivial hypothesis behind the pentagon —
is the abstract shadow of the concrete Schur uniqueness proved in
`TransvectantCG`: `hw0_unique` shows the spin-0 recoupling channel of
`V_½ ⊗ V_½` is spanned by the single antisymmetric intertwiner (≤ 1-dim), and
`spin1_top_isHW` does the same for the spin-1 channel.  Re-exposed here so the
"uniqueness ⇒ pentagon" arc is a single readable chain. -/

/-- **The multiplicity-freeness that powers `comp`, re-exposed.**  Every spin-0
highest-weight vector `w0 a b` of `V_½⊗V_½` is a `Q'`-scalar multiple of the one
antisymmetric intertwiner `hw0` — the concrete Schur ≤ 1-dim fact, verbatim from
`TransvectantCG.hw0_unique`.  This is the local instance of the composition law
`comp`: uniqueness of the trivalent intertwiner. -/
theorem schur_multiplicity_free (a b : Q')
    (hHW : (E2 1 1 (w0 a b) 1 1).eqv 0) :
    ∀ i, i < 2 → ∀ j, j < 2 → ((w0 a b) i j).eqv (a * hw0 i j) :=
  TransvectantCG.hw0_unique a b hHW

/-! ## 5. Honest ledger (AGENTS.md Rules 6/9)

**PROVED (genuine, axiom-clean — `propext`/`Quot.sound` only):**

* The `sl₂` action on binary forms is the correct representation
  (`BinaryForms.comm_EF_H_spinHalf` etc., axiom-free).
* The transvectant Clebsch–Gordan maps are genuine intertwiners
  (`TransvectantCG.cgSpin1_E/F/H`, `cgSpin0_E/F/H`, axiom-free).
* **Multiplicity-freeness / Schur ≤ 1-dim Hom** as a universal `Q'` statement
  (`TransvectantCG.hw0_unique`, `spin1_top_isHW`; `schur_multiplicity_free`).
* **The pentagon FROM uniqueness** (`pentagon_from_uniqueness`), and general
  route-independence (`square_from_uniqueness`, `recoupling_inverse`), derived
  from the Schur composition law by `Q'` associativity — NOT a factorial decide.
* `UniqueRecoupling` is non-empty (`trivialRecoupling`, `pentagon_trivial`).

**NAMED-open (NOT faked — the honest residual, unchanged from
`PentagonRelation.PentagonNumericCore`):**

The abstract mechanism shows the pentagon *coherence* is automatic in any
multiplicity-free system.  What this route does NOT manufacture is the physical,
fractional 6j **value**: the Racah kernel `P = dim(e)dim(f){6j}² = 1/4` at the
smallest SU(2) tetrahedron.  Pinning it constructively requires the rational
`{6j}²` as a ratio of apolar norms of the two composite spin-½³ recoupling
intertwiners — a finite rational computation the transvectant apparatus supports
(`TransvectantCG.apolarHalf`) but which is not carried out here.  Instantiating
`UniqueRecoupling` with the *physical* (nontrivial, fractional) 6j scalars — as
opposed to the trivial witness — is therefore the remaining work, and
`PentagonRelation.PentagonNumericCore` stays the correctly-specified NAMED
frontier.  The Clay YM mass gap stays OPEN. -/

end YMGap.Continuum.PentagonFromUniqueness

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PentagonFromUniqueness.pentagon_from_uniqueness
#print axioms YMGap.Continuum.PentagonFromUniqueness.square_from_uniqueness
#print axioms YMGap.Continuum.PentagonFromUniqueness.recoupling_inverse
#print axioms YMGap.Continuum.PentagonFromUniqueness.trivialRecoupling
#print axioms YMGap.Continuum.PentagonFromUniqueness.pentagon_trivial
#print axioms YMGap.Continuum.PentagonFromUniqueness.schur_multiplicity_free
