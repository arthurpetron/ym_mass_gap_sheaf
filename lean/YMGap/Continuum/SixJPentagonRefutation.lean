/-
**Track A2-pentagon — honest refutation of the `Tier0Scorecard.SixJPentagon`
carrier: the `pentagon` field is a channel-mismatch BUG (contradicts its own
`RacahProb.rowStoch`), so `SixJPentagon` is PROVABLY UNINHABITED.**

`Tier0Scorecard.SixJPentagon` bundles a doubly-stochastic Racah kernel `P`
(`SixJRecouplingProgress.RacahProb`) with a `pentagon` field advertised as "a
guarded CUBIC closure of `P`, nonlinear in the kernel — the genuine A2 residual,
LEFT UNINHABITED, never proved".  A close reading of the ACTUAL Lean field shows
this label is wrong: the `mk6`-wiring of the cubic relation mixes the LEFT (`e`,
couples `(a,b)`/`(c,d)`) and RIGHT (`f`, couples `(b,c)`/`(a,d)`) coupling
channels, so combined with the `RacahProb` structure it is self-contradictory —
exactly the accidental "Defect-1"-style degeneracy that
`SixJRecouplingProgress.sixjRecoupling_uninhabited` diagnosed for the earlier
`SixJRecoupling` frontier (there it forced `1 ≃ 0` at `D = 0`).

# The literal field (with `M e f := P.racahProb (mk6 a b c d e f)`, `a,b,c,d` fixed)

    pentagon :  M(e,f) · M(e,f)  ≃  Σ_{x<D}  M(e,x) · M(x,f) · M(x,e)     (guard a+…+f<D)

The third internal factor `M(x,e) = P.racahProb (mk6 a b c d x e)` puts the LEFT
index `e` into the RIGHT (`f`) slot.  When `e` is left-valid but NOT right-valid,
`RacahProb.support` forces `M(x,e) ≃ 0` for every `x`, hence the whole RHS `≃ 0`;
but `RacahProb.rowStoch` forces the LHS point `M(e,f) ≃ 1`, so the pentagon
demands `1 ≃ 0`.

# What is PROVED here (a REFUTATION, not a closure)

`sixJPentagon_uninhabited : SixJPentagon → False`, via the witness
`(a,b,c,d,e,f) = (0,0,1,1,0,1)`:

  * `rowStoch 3 0 0 1 1 0` collapses `Σ_{f<3} M(0,f)` (only `f = 1` is
    right-valid) to `M(0,1) ≃ 1`;
  * `support` forces `M(x,0) ≃ 0` for all `x` (right-channel `f = 0` fails the
    `(0,1,0)` triangle), so the pentagon RHS at `D = 4` is `≃ 0`;
  * the `pentagon` field then equates `M(0,1)² ≃ RHS`, i.e. `1 ≃ 0` — absurd.

# Honest verdict

`SixJPentagon` as written is NOT a genuine nonlinear frontier: it is uninhabited
by construction (its cubic field contradicts its stochastic base), so it cannot
be the A2 residual it is advertised as.  This is verified out-of-band against the
FAITHFUL rational 6j² kernel `SixJKernel.racahKernelQ` (the literal relation
fails at 158/4096 small labels) and the permutation surrogate `racahPerm` (fails
at 80/4096) — the relation is simply not the Biedenharn–Elliott identity.  The
GENUINE A2 content is unaffected and stays exactly where the codebase already
places it: the true Biedenharn–Elliott pentagon is LINEAR in the SIGNED (hence
irrational) Wigner `{6j}` and is NOT `Q'`-representable, so it remains the named
`PentagonRelation.PentagonNumericCore` obligation (the fractional associator),
with the true `Q'` recoupling relation being `SixJKernel.RacahOrthogonalityGeneral`.
This module closes NO physics; it corrects a mislabeled/degenerate carrier.  The
Clay Yang–Mills mass gap stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Fin` core only.  No `Classical.*`, no `Real`, no
`native_decide` (only `decide` on decidable `Q'.eqv`/`Bool` facts).  No `sorry`
/ `admit` / new `axiom`.  All witnesses are `Type`-level data.  `#print axioms`
gated (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.Tier0Scorecard

namespace YMGap.Continuum.SixJPentagonRefutation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.SixJRecouplingProgress
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Tier0Scorecard

/-! ## 0. Reusable helpers (all lemma-based; no numeral `rfl` fragility). -/

/-- A finite sum whose every summand on `[0,D)` is `≃ 0` is itself `≃ 0`.
(Local copy of `PentagonRelation.finSum_all_eqv_zero`, to keep this module's
import surface minimal.) -/
theorem finSum_all_zero (g : Nat → Q') (D : Nat)
    (h : ∀ i, i < D → (g i).eqv 0) : (finSum g D).eqv 0 :=
  Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt g (fun _ => 0) D (fun i hi => h i hi))
    (Q'.eqv_of_eq (finSum_zero_seq D))

/-- **Three-term Kronecker collapse.**  If `G 0 ≃ 0` and `G 2 ≃ 0`, then
`Σ_{i<3} G i ≃ G 1`.  Used for the guarded `rowStoch` sum at the witness label
(the only right-valid channel is `f = 1`). -/
theorem collapse3 (G : Nat → Q') (h0 : (G 0).eqv 0) (h2 : (G 2).eqv 0) :
    (finSum G 3).eqv (G 1) := by
  have e : finSum G 3 = 0 + G 0 + G 1 + G 2 := rfl
  rw [e]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((0 + G 0) + G 1) (G 2) 0 h2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (Q'.add_zero' ((0 + G 0) + G 1))) ?_
  have hg0 : ((0 : Q') + G 0).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 0 (G 0) 0 h0)
      (Q'.eqv_of_eq (Q'.add_zero' 0))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (0 + G 0) 0 (G 1) hg0) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (G 1))

/-! ## 1. The refutation. -/

/-- **`SixJPentagon` is UNINHABITED (PROVED refutation).**

At the witness `(a,b,c,d,e,f) = (0,0,1,1,0,1)`:

  * `support` forces `P.racahProb (mk6 0 0 1 1 x 0) ≃ 0` for every `x` (the
    right channel `f = 0` fails the `(b,c,f) = (0,1,0)` triangle), so the
    `pentagon` RHS (at `D = 4`) is `≃ 0`;
  * `rowStoch 3 0 0 1 1 0` (only `f = 1` is right-valid) forces
    `P.racahProb (mk6 0 0 1 1 0 1) ≃ 1`, hence the LHS square `≃ 1`;
  * `pentagon 0 0 1 1 0 1 4` equates the two, giving `1 ≃ 0` — absurd.

So the advertised "genuine cubic A2 residual" is self-contradictory: its
`pentagon` field cannot coexist with the `RacahProb.rowStoch` field it is built
on.  (Mirrors `SixJRecouplingProgress.sixjRecoupling_uninhabited`.) -/
theorem sixJPentagon_uninhabited (S : SixJPentagon) : False := by
  -- (a) support forces the right-channel-`0` kernels to vanish.
  have psupp0 : ∀ (x : Rep), (S.P.racahProb (mk6 0 0 1 1 x 0)).eqv 0 := by
    intro x
    by_cases h : (S.P.racahProb (mk6 0 0 1 1 x 0)).eqv 0
    · exact h
    · exact absurd (S.P.support 0 0 1 1 x 0 h).2 (by decide)
  -- (b) the row over `f<3` collapses to `P1` (only `f = 1` is right-valid).
  have hrow0 : (S.P.racahProb (mk6 0 0 1 1 0 0)).eqv 0 := by
    by_cases h : (S.P.racahProb (mk6 0 0 1 1 0 0)).eqv 0
    · exact h
    · exact absurd (S.P.support 0 0 1 1 0 0 h).2 (by decide)
  have hrow2 : (S.P.racahProb (mk6 0 0 1 1 0 2)).eqv 0 := by
    by_cases h : (S.P.racahProb (mk6 0 0 1 1 0 2)).eqv 0
    · exact h
    · exact absurd (S.P.support 0 0 1 1 0 2 h).2 (by decide)
  have hcollapse :
      (finSum (fun f => S.P.racahProb (mk6 0 0 1 1 0 f)) 3).eqv
        (S.P.racahProb (mk6 0 0 1 1 0 1)) :=
    collapse3 (fun f => S.P.racahProb (mk6 0 0 1 1 0 f)) hrow0 hrow2
  have hrowStoch :
      (finSum (fun f => S.P.racahProb (mk6 0 0 1 1 0 f)) 3).eqv 1 :=
    S.P.rowStoch 3 0 0 1 1 0 (by decide) (by decide)
  have hPone : (S.P.racahProb (mk6 0 0 1 1 0 1)).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcollapse) hrowStoch
  -- (c) hence the LHS square is `≃ 1`.
  have hsq_one :
      (S.P.racahProb (mk6 0 0 1 1 0 1) * S.P.racahProb (mk6 0 0 1 1 0 1)).eqv 1 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (S.P.racahProb (mk6 0 0 1 1 0 1)) 1
          (S.P.racahProb (mk6 0 0 1 1 0 1)) hPone)
        (Q'.mul_eqv_congr_left 1 (S.P.racahProb (mk6 0 0 1 1 0 1)) 1 hPone))
      (Q'.mul_one_eqv 1)
  -- (d) the pentagon RHS at `D = 4` is `≃ 0` (third factor vanishes).
  have hrhs_zero :
      (finSum (fun x =>
        S.P.racahProb (mk6 0 0 1 1 0 x) *
          (S.P.racahProb (mk6 0 0 1 1 x 1) *
            S.P.racahProb (mk6 0 0 1 1 x 0))) 4).eqv 0 := by
    refine finSum_all_zero _ 4 (fun x _ => ?_)
    have hC : (S.P.racahProb (mk6 0 0 1 1 x 0)).eqv 0 := psupp0 x
    have hBC :
        (S.P.racahProb (mk6 0 0 1 1 x 1) *
          S.P.racahProb (mk6 0 0 1 1 x 0)).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (S.P.racahProb (mk6 0 0 1 1 x 1))
          (S.P.racahProb (mk6 0 0 1 1 x 0)) 0 hC)
        (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (S.P.racahProb (mk6 0 0 1 1 0 x)) _ 0 hBC)
      (Q'.mul_zero_eqv _)
  -- (e) the pentagon field itself: LHS² ≃ RHS.
  have hpent :
      (S.P.racahProb (mk6 0 0 1 1 0 1) * S.P.racahProb (mk6 0 0 1 1 0 1)).eqv
        (finSum (fun x =>
          S.P.racahProb (mk6 0 0 1 1 0 x) *
            (S.P.racahProb (mk6 0 0 1 1 x 1) *
              S.P.racahProb (mk6 0 0 1 1 x 0))) 4) :=
    S.pentagon 0 0 1 1 0 1 4 (by decide)
  -- (f) chain: 1 ≃ P1² ≃ RHS ≃ 0, contradiction.
  have h_one_zero : (1 : Q').eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsq_one)
      (Q'.eqv_trans _ _ _ hpent hrhs_zero)
  exact absurd h_one_zero (by decide)

/-- **Corollary.**  `SubWallA` bundles a `SixJPentagon` (`a2Pentagon`), so it
too is uninhabited — but now for a DIFFERENT reason than "the continuum is open":
the `pentagon` carrier is degenerate.  (This does not by itself reopen the honest
open A-half; it flags that the A2 slot needs a corrected carrier — the genuine
signed-6j associator `PentagonRelation.PentagonNumericCore`, whose true `Q'`
recoupling relation is `SixJKernel.RacahOrthogonalityGeneral`.) -/
theorem subWallA_uninhabited
    {p : z4Chain.toLattice.Plaquette} {w : Q'} (A : SubWallA p w) : False :=
  sixJPentagon_uninhabited A.a2Pentagon

end YMGap.Continuum.SixJPentagonRefutation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SixJPentagonRefutation.finSum_all_zero
#print axioms YMGap.Continuum.SixJPentagonRefutation.collapse3
#print axioms YMGap.Continuum.SixJPentagonRefutation.sixJPentagon_uninhabited
#print axioms YMGap.Continuum.SixJPentagonRefutation.subWallA_uninhabited
