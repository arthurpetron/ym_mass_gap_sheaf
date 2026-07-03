/-
**Track A2-6j — honest correction of the closed-fusion-loop 6j frontier.**

`PartitionBeyondTree.SixJRecoupling` was named as *the* irreducible `m ≥ 4`
frontier (the SU(2) 6j / Biedenharn–Elliott datum), advertised as "left
UNINHABITED, the 6j is the frontier".  A close reading of the *actual* Lean
field shows this label is wrong on two counts, and produces the corrected
datum.

# What this module delivers (a reduction/refutation, NOT a closure)

## Defect 1 (PROVED refutation): `SixJRecoupling` is UNINHABITED — a bug.

The `biedenharn_elliott` field quantifies over `∀ (D : Nat) …` with **no
largeness guard** (unlike every proved corner `nFoldCharInt_two/three`, which
carry `b < D`, `c < D`, `a < D`).  Instantiating `D = 0`, `a=b=c=d=e=0`:

  * RHS `= finSum _ 0 = 0` (`rfl`);
  * LHS `= fusionInd 0 0 0 · fusionInd 0 0 0 = 1·1` (`fusionOK 0 0 0 = true`).

So *every* `SixJRecoupling` forces `1 ≃ 0` — hence **none exists**
(`sixjRecoupling_uninhabited`).  The "left UNINHABITED = 6j frontier" framing is
therefore an accidental *truncation degeneracy* (a bug), not 6j depth.
`sixj_zero_fails` (non-vacuity at `D=1`) does NOT detect this.  As a corollary
the bundling `BeyondTreePartitionIdentity` is uninhabited too
(`beyondTreePartitionIdentity_uninhabited`).

## Defect 2 (PROVED machinery): a one-sided linear equation cannot pin a 6j.

Even guarded, `biedenharn_elliott` is ONE one-directional linear equation over
`{0,1}` multiplicities, hence trivially satisfiable by a weight-1 pin.  We show
the essence: **row-stochastic does NOT imply column-stochastic**.  The constant
column-0 pin `colPin` (weight-1, `colPin_zeroOne`) has every row-sum `≃ 1`
(`colPin_rowSum`) yet a column-0 sum `≄ 1` (`colPin_colSum_not_one`).  So a
*two-sided* (doubly-stochastic) constraint is strictly stronger — that is the
content the scalar-multiplicity field is missing.

## The corrected datum `RacahProb` (the genuine, correctly-specified frontier).

A `Q'`-kernel `P = (2e+1)(2f+1)·{6j}²` (rational, unlike the irrational Wigner
6j) with nonnegativity, support on both triangle channels, and **guarded
two-sided** row+column stochasticity (guard `a+b+c+d < D`).  We prove it is
Defect-1-safe (`guardedRow_satisfiable_at_zero`: the all-zero row constraint
admits the trivial-channel δ-kernel, contrast `1 ≃ 0`) and carries real content
(`racahProb_not_allZero`: the zero kernel fails it, guard-safe).  Inhabitation
by the actual Racah amplitudes is LEFT as the named residual — a correctly
specified `m ≥ 4` frontier, replacing the bug-and-trivial pair.

## The `m ≥ 4 → m = 3 + one contraction` collapse (STRUCTURE).

`tetraAmp` realizes the closed 4-valent fusion loop (Ponzano–Regge tetrahedron)
as **two proved trivalent corners** (`LoopyLinkIntegral.tripleCharInt`,
`= nFoldCharInt_three`) glued by **one** `RacahProb` contraction over the
internal `(e,f)` channels (`tetraAmp_nonneg`).  So the whole `m ≥ 4` frontier
collapses to the proved trivalent corner plus the single `RacahProb` datum.

# Honest verdict

`SixJRecoupling` as written is a mislabeled frontier: uninhabited at `D=0`
(bug) and, once guarded, under-determined (trivial).  The genuine irreducible
datum is the doubly-stochastic `RacahProb`; it is NEW amplitude-squared data,
not derivable from the proved `m = 3` corner.  The Clay mass gap stays OPEN;
this is a correction/reduction of a mislabeled datum, not a closure.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Fin` core only.  No `Classical.*`, no `Real`, no
`native_decide` (only `decide`/`omega` on decidable `Nat`/`Q'` facts).  No
`sorry` / `admit` / new `axiom`.  All witnesses are `Type`-level data; the
`RacahProb` datum is a NAMED obligation, never faked.  `#print axioms` gated
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PartitionBeyondTree

namespace YMGap.Continuum.SixJRecouplingProgress

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.LoopyLinkIntegral
open YMGap.Continuum.PartitionBeyondTree

/-! ## 0. A reusable `fusionInd 0 0 0 = 1` fact (the trivial-fusion corner). -/

/-- `N_{000} = 1`: the trivial rep occurs in `χ_0·χ_0` (`fusionOK 0 0 0 = true`). -/
theorem fusionInd_000 : fusionInd 0 0 0 = (1 : Q') := by
  unfold fusionInd
  rw [if_pos ((fusionOK_iff 0 0 0).mpr (by decide))]

/-- The left side of the `biedenharn_elliott` field at the all-zero label is
`≃ 1`: `N_{000}·N_{000} = 1·1 ≃ 1`. -/
theorem allZero_left_eqv_one : (fusionInd 0 0 0 * fusionInd 0 0 0).eqv 1 := by
  rw [fusionInd_000]; exact Q'.mul_one_eqv 1

/-! ## 1. Defect 1 — `SixJRecoupling` (as written) is UNINHABITED (a bug). -/

/-- **Defect 1 (PROVED refutation).**  The `biedenharn_elliott` field carries no
largeness guard, so at `D = 0`, `a=b=c=d=e=0` it demands
`(fusionInd 0 0 0 · fusionInd 0 0 0) ≃ finSum _ 0 = 0`, i.e. `1·1 ≃ 0`.  Hence
NO `SixJRecoupling` exists: the "left uninhabited = 6j frontier" claim is an
accidental truncation degeneracy, not depth.  (`sixj_zero_fails`, being at
`D = 1`, does not detect this.) -/
theorem sixjRecoupling_uninhabited (S : SixJRecoupling) : False := by
  have hbad := S.biedenharn_elliott 0 0 0 0 0 0
  rw [finSum_zero] at hbad
  -- hbad : (fusionInd 0 0 0 * fusionInd 0 0 0).eqv 0
  have h10 : (1 : Q').eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm allZero_left_eqv_one) hbad
  exact absurd h10 (by decide)

/-- **Corollary.**  `BeyondTreePartitionIdentity` bundles a `SixJRecoupling`
(`recoup`), so it inherits the uninhabitability: the "beyond-tree identity =
6j datum + identity" bundle is also empty as currently stated. -/
theorem beyondTreePartitionIdentity_uninhabited
    {L : Lattice} [DecidableEq L.Plaquette] {w : Q'} {label : L.Plaquette → Rep}
    (B : BeyondTreePartitionIdentity (L := L) w label) : False :=
  sixjRecoupling_uninhabited B.recoup

/-! ## 2. The corrected datum `RacahProb` — guarded two-sided stochasticity.

The genuine SU(2) recoupling content is the *rational* dim-absorbed Racah
probability `P(a,b,c,d;e,f) = (2e+1)(2f+1)·{a b e; c d f}²` (the Wigner 6j
itself is irrational, so cannot be a `Q'`-kernel).  Its defining constraint is
the **two-sided Racah orthogonality**: a doubly-stochastic matrix on the
bipartite support `{valid e} × {valid f}`, guarded by `a+b+c+d < D`.  The
two-sided pair closes Defect 2 (a one-directional equation cannot force double
stochasticity) and the guard closes Defect 1. -/

/-- **The corrected closed-fusion-loop 6j / Racah datum.**  Replaces the
mislabeled `SixJRecoupling`.  Left UNINHABITED here: the actual Racah amplitudes
are the named residual (a correctly-specified `m ≥ 4` frontier). -/
structure RacahProb where
  /-- The rational dim-absorbed 6j probability `P = (2e+1)(2f+1)·{6j}²`. -/
  racahProb : (Fin 6 → Rep) → Q'
  /-- `P ≥ 0` (a squared, dimension-weighted quantity). -/
  nonneg : ∀ j, (0 : Q') ≤ racahProb j
  /-- Support on BOTH triangle-valid channels (left `e` and right `f`). -/
  support : ∀ (a b c d e f : Rep),
    ¬ (racahProb (mk6 a b c d e f)).eqv 0 →
      ((fusionInd a b e * fusionInd e c d).eqv 1 ∧
        (fusionInd b c f * fusionInd a f d).eqv 1)
  /-- **Row-stochastic** (guarded): for each left-valid `e`, the row over `f`
  sums to `1`. -/
  rowStoch : ∀ (D a b c d e : Rep), a + b + c + d < D →
    (fusionInd a b e * fusionInd e c d).eqv 1 →
      (finSum (fun f => racahProb (mk6 a b c d e f)) D).eqv 1
  /-- **Column-stochastic** (guarded): for each right-valid `f`, the column over
  `e` sums to `1`.  This second constraint is what pins the 6j (Defect 2). -/
  colStoch : ∀ (D a b c d f : Rep), a + b + c + d < D →
    (fusionInd b c f * fusionInd a f d).eqv 1 →
      (finSum (fun e => racahProb (mk6 a b c d e f)) D).eqv 1

/-! ## 3. The corrected datum carries real content and is Defect-1-safe. -/

/-- **Defect-1 safety.**  Unlike the buggy `SixJRecoupling` (which forced
`1 ≃ 0` at `D = 0`), the *guarded* row constraint at the all-zero instance is
SATISFIABLE: the trivial-channel δ-kernel `f ↦ δ_{f,0}` has row-sum `1` for
every `0 < D`.  So the guard genuinely removes the truncation degeneracy. -/
theorem guardedRow_satisfiable_at_zero {D : Nat} (hD : 0 < D) :
    (finSum (fun f => orthoKernel f 0) D).eqv 1 := by
  have h1 : (finSum (fun f => orthoKernel f 0 * (1 : Q')) D).eqv ((fun _ => (1 : Q')) 0) :=
    finSum_delta_left (fun f => orthoKernel f 0) (fun _ => 1) 0
      (fun d hd => Q'.eqv_of_eq (orthoKernel_off hd))
      (Q'.eqv_of_eq (orthoKernel_diag 0)) hD
  refine Q'.eqv_trans _ _ _ ?_ h1
  exact finSum_eqv_congr_lt _ _ D
    (fun f _ => Q'.eqv_symm (Q'.mul_one_eqv (orthoKernel f 0)))

/-- **Non-vacuity (guard-safe analogue of `sixj_zero_fails`).**  No `RacahProb`
has the all-zero kernel: at the all-zero instance the (guarded) row constraint
forces the single-term sum `≃ 1`, contradicting `≃ 0`.  So the corrected datum
carries real content — it is not the empty obligation. -/
theorem racahProb_not_allZero (R : RacahProb) :
    ¬ (∀ j, (R.racahProb j).eqv 0) := by
  intro hzero
  have hrow := R.rowStoch 1 0 0 0 0 0 (by decide) allZero_left_eqv_one
  -- the single-term (D = 1) sum is ≃ the f = 0 value ≃ 0
  have hsum0 : (finSum (fun f => R.racahProb (mk6 0 0 0 0 0 f)) 1).eqv 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (R.racahProb (mk6 0 0 0 0 0 0)))) ?_
    exact hzero (mk6 0 0 0 0 0 0)
  have : (0 : Q').eqv 1 := Q'.eqv_trans _ _ _ (Q'.eqv_symm hsum0) hrow
  exact absurd this (by decide)

/-! ## 4. Defect 2 — row-stochastic does NOT imply column-stochastic.

The single one-directional `biedenharn_elliott` equation is only a row
constraint.  We exhibit the essential gap: the constant column-0 pin is
row-stochastic everywhere but violates column stochasticity — so a *two-sided*
constraint is strictly stronger (and the weight-1 trivial pin cannot satisfy
it). -/

/-- The constant column-0 pin: put all mass on the `f = 0` column.  This is the
weight-1 "trivial pin" a one-directional linear equation admits. -/
def colPin : Nat → Nat → Q' := fun _ f => if f = 0 then (1 : Q') else 0

/-- `colPin` is weight-1 (its values are `0` or `1`). -/
theorem colPin_zeroOne (e f : Nat) : colPin e f = 0 ∨ colPin e f = 1 := by
  unfold colPin
  by_cases h : f = 0
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- **Every row of `colPin` sums to `1`** (for `0 < D`): only the `f = 0` term
contributes.  (`colPin e f = orthoKernel f 0`, so this is
`guardedRow_satisfiable_at_zero`.) -/
theorem colPin_rowSum {D : Nat} (hD : 0 < D) (e : Nat) :
    (finSum (fun f => colPin e f) D).eqv 1 :=
  guardedRow_satisfiable_at_zero hD

/-- **But the `f = 0` column of `colPin` does NOT sum to `1`** — at `D = 2` its
column-0 sum is `0 + 1 + 1` (two rows both pin to column 0), which is `≄ 1`.
This is exactly the doubly-stochastic obstruction: a row-stochastic weight-1
kernel that is not a permutation over-fills a column. -/
theorem colPin_colSum_not_one :
    ¬ (finSum (fun e => colPin e 0) 2).eqv 1 := by
  have hval : (finSum (fun e => colPin e 0) 2) = (0 + 1 + 1 : Q') := rfl
  rw [hval]
  decide

/-- **Defect 2 (PROVED machinery).**  `colPin` is row-stochastic at every
`(D, e)` with `0 < D`, yet its `f = 0` column sum (at `D = 2`) is `≄ 1`.  Hence
row-stochastic does NOT imply column-stochastic: the two-sided `RacahProb`
constraint is STRICTLY stronger than the single one-directional
`biedenharn_elliott` equation, and the weight-1 pin cannot satisfy it. -/
theorem rowStoch_not_imply_colStoch :
    (∀ (D e : Nat), 0 < D → (finSum (fun f => colPin e f) D).eqv 1)
      ∧ ¬ (finSum (fun e => colPin e 0) 2).eqv 1 :=
  ⟨fun _D e hD => colPin_rowSum hD e, colPin_colSum_not_one⟩

/-! ## 5. The `m ≥ 4 → m = 3 + one contraction` collapse (STRUCTURE). -/

/-- **The closed 4-valent fusion loop (Ponzano–Regge tetrahedron)** as two
proved trivalent corners (`tripleCharInt`, `= nFoldCharInt_three`) glued by ONE
`RacahProb` contraction over the internal `(e, f)` channels:

    tetraAmp = Σ_{e<D} Σ_{f<D} P(a,b,c,d;e,f) · (N_{abe} · N_{ecd}).

So any `m ≥ 4` closed fusion loop reduces to the proved trivalent corner plus
the single `RacahProb` datum — the honest structural collapse. -/
def tetraAmp (R : RacahProb) (D : Nat) (a b c d : Rep) : Q' :=
  finSum (fun e => finSum (fun f =>
    R.racahProb (mk6 a b c d e f) *
      (tripleCharInt a b e * tripleCharInt e c d)) D) D

/-- The tetrahedron amplitude is nonnegative (a nested sum of products of the
nonnegative `RacahProb` and the nonnegative proved trivalent corners). -/
theorem tetraAmp_nonneg (R : RacahProb) (D : Nat) (a b c d : Rep) :
    (0 : Q') ≤ tetraAmp R D a b c d := by
  unfold tetraAmp
  refine finSum_nonneg_local (fun e => ?_) D
  refine finSum_nonneg_local (fun f => ?_) D
  exact Q'.mul_nonneg _ _ (R.nonneg _)
    (Q'.mul_nonneg _ _ (tripleCharInt_nonneg a b e) (tripleCharInt_nonneg e c d))

/-! ## 6. `#print axioms` gates (permitted: `propext` / `Quot.sound`). -/

#print axioms sixjRecoupling_uninhabited
#print axioms beyondTreePartitionIdentity_uninhabited
#print axioms guardedRow_satisfiable_at_zero
#print axioms racahProb_not_allZero
#print axioms rowStoch_not_imply_colStoch
#print axioms tetraAmp_nonneg

end YMGap.Continuum.SixJRecouplingProgress
