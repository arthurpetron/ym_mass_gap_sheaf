/-
**Track 11.4-ortho — the all-label Racah 6j orthogonality sum rule, cleaved into
its PROVED off-triangle half and its (sharpened) named diagonal-normalization
residual.**

The statement carrier `SixJKernel.RacahOrthogonalityGeneral` asserts the Wigner
sum rule for the faithful rational 6j² kernel at EVERY tetrahedron label and
every cutoff `D` past the physical support:

  `∀ a b c d f D, a+b+c+d+f < D →
     Σ_{x<D} P(mk6 a b c d x f)  ≃  fusionInd a d f · fusionInd c b f`,

i.e. `Σ_x (2x+1)(2f+1){a b x; c d f}² = δ(a,d,f)·δ(c,b,f)`.  Concrete instances
are already `decide`d in `SixJKernel` (`orthoSum_smallest = 1`,
`orthoSum_offTriangle = 0`, `orthoSum_pZero = 1`), but `Rep = Nat` is unbounded,
so the all-label statement is genuinely infinitary and cannot be `decide`d.

# The load-bearing structural split

`racahKernel6 a b c d x f` is guarded by
`valid6 a b c d x f = fusionOK a b x && fusionOK a d f && fusionOK c b f
   && fusionOK c d x`.  Two conjuncts — `fusionOK a d f` and `fusionOK c b f` —
are **x-independent** and coincide exactly with the two indicators on the RHS.
Hence the sum rule cleaves at those two guards:

## Half A — off-triangle (RHS = 0): PROVED here, unconditionally, axiom-clean.
If `¬ fusionOK a d f` OR `¬ fusionOK c b f`, then `valid6 a b c d x f = false`
for *every* `x` (the failing conjunct is x-independent), so
`racahKernel6 a b c d x f = 0` at every `x`, whence `orthoSum ≃ 0` via
`PentagonRelation.finSum_all_eqv_zero`; and the RHS product `≃ 0` because the
matching indicator is `0`.  The `D`-cutoff hypothesis is not even needed.
This is `orthoSum_offTriangle_gen` — a genuine all-label theorem, generalizing
the single `decide`d `orthoSum_offTriangle`.

## Half B — on-triangle (RHS = 1): the IRREDUCIBLE CORE, a NAMED residual.
When both `fusionOK a d f` and `fusionOK c b f` hold, the RHS is `1`, and the
claim reduces to the diagonal 6j orthonormality
`Σ_x (2x+1)(2f+1){a b x; c d f}² = 1` — a genuine *fractional* normalization
(`3/4 + 1/4 = 1` at the smallest tetrahedron, see `SixJKernel.orthoSum_smallest`;
NOT a δ-collapse, so `RacahInhabit.finSum_delta_left` does not apply).  Closing
it needs a 3j/Clebsch–Gordan orthogonality layer or the Schulten–Gordon
three-term 6j recursion — neither exists in this codebase — so it stays the
sharp named obligation `DiagonalSixJNormalization`.

# What this module delivers

  * `orthoSum_offTriangle_gen` — **Half A, PROVED for all labels/cutoffs.**
  * `DiagonalSixJNormalization` — **the sharpened Half-B residual** (a `def …
    : Prop`, inhabited nowhere; the honest strictly-smaller core).
  * `racahOrthogonalityGeneral_of_diagonal` — **the reduction**: the diagonal
    normalization core IMPLIES the full all-label sum rule
    `SixJKernel.RacahOrthogonalityGeneral`.  So the all-label statement is now
    (proved off-triangle half) + (one sharper still-open normalization core),
    an honest sharpening — NOT a closure.
  * `diagonalNormalization_smallest`, `diagonalNormalization_pZero` — `decide`d
    non-vacuity witnesses that the residual is genuinely TRUE at a cutoff
    satisfying the largeness bound (not a vacuous carrier).

# Honest verdict

`SixJKernel.RacahOrthogonalityGeneral` remains an uninhabited statement carrier.
Its off-triangle half is now a real theorem; its on-triangle half is reduced to
the strictly-smaller, still-open, `Q'`-expressible diagonal 6j normalization
`DiagonalSixJNormalization`, which we do NOT fake.  This is machinery + a sharp
reduction, not a physics closure.  The Clay YM mass gap stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Fin` core only.  No `Classical.*`, no `Real`, no
`native_decide` (only `decide` on decidable `Q'.eqv` instance facts and
`by_cases` on decidable `Bool` equalities).  No `sorry` / `admit` / new `axiom`.
All witnesses are `Type`-level data; the diagonal normalization is a NAMED
obligation, never faked.  `#print axioms` gated (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.SixJKernel

namespace YMGap.Continuum.RacahOrthogonalityGeneral

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.RacahInhabit
open YMGap.Continuum.SixJKernel

/-! ## 0. `mk6` evaluation of the faithful kernel. -/

/-- `racahKernelQ (mk6 a b c d e f) = racahKernel6 a b c d e f` (the internal
label `e` sits in slot 4). -/
theorem racahKernelQ_mk6 (a b c d e f : Rep) :
    racahKernelQ (mk6 a b c d e f) = racahKernel6 a b c d e f := rfl

/-! ## 1. The x-independent guard failure. -/

/-- If either x-independent face `(a,d,f)` or `(c,b,f)` fails the triangle guard,
then the tetrahedron guard `valid6 a b c d x f` fails for EVERY internal `x`. -/
theorem valid6_ne_true_of (a b c d x f : Rep)
    (h : ¬ fusionOK a d f = true ∨ ¬ fusionOK c b f = true) :
    ¬ (valid6 a b c d x f = true) := by
  intro hv
  unfold valid6 at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨_, hadf⟩, hcbf⟩, _⟩ := hv
  rcases h with h | h
  · exact h hadf
  · exact h hcbf

/-- With a failing x-independent face, the kernel vanishes at every internal
label. -/
theorem racahKernel6_eq_zero_of (a b c d x f : Rep)
    (h : ¬ fusionOK a d f = true ∨ ¬ fusionOK c b f = true) :
    racahKernel6 a b c d x f = 0 := by
  unfold racahKernel6
  rw [if_neg (valid6_ne_true_of a b c d x f h)]

/-! ## 2. Half A — the off-triangle sum rule, PROVED for all labels/cutoffs. -/

/-- **Half A (PROVED).**  If one of the two x-independent triangle faces
`(a,d,f)` / `(c,b,f)` fails, the orthogonality sum rule holds with both sides
`≃ 0`: `orthoSum a b c d f D ≃ fusionInd a d f · fusionInd c b f ≃ 0`.  No
cutoff hypothesis is needed.  This is the all-label generalization of the single
`decide`d `SixJKernel.orthoSum_offTriangle`. -/
theorem orthoSum_offTriangle_gen (a b c d f D : Rep)
    (h : ¬ fusionOK a d f = true ∨ ¬ fusionOK c b f = true) :
    (orthoSum a b c d f D).eqv (fusionInd a d f * fusionInd c b f) := by
  -- LHS ≃ 0: every summand vanishes.
  have hz : (orthoSum a b c d f D).eqv 0 := by
    unfold orthoSum
    apply finSum_all_eqv_zero
    intro x _
    have hk : racahKernelQ (mk6 a b c d x f) = 0 := by
      rw [racahKernelQ_mk6]; exact racahKernel6_eq_zero_of a b c d x f h
    rw [hk]; exact Q'.eqv_refl 0
  -- RHS ≃ 0: the matching indicator is 0.
  have hr : (fusionInd a d f * fusionInd c b f).eqv 0 := by
    rcases h with h | h
    · have h0 : fusionInd a d f = 0 := by unfold fusionInd; rw [if_neg h]
      rw [h0]; exact Q'.zero_mul_eqv _
    · have h0 : fusionInd c b f = 0 := by unfold fusionInd; rw [if_neg h]
      rw [h0]; exact Q'.mul_zero_eqv _
  exact Q'.eqv_trans _ _ _ hz (Q'.eqv_symm hr)

/-! ## 3. Half B — the sharpened named residual (uninhabited, NOT faked). -/

/-- **`DiagonalSixJNormalization` — the diagonal 6j orthonormality core (NAMED
RESIDUAL).**

When both x-independent faces `(a,d,f)`, `(c,b,f)` are triangle-valid and the
cutoff `D` clears the physical support, the orthogonality sum rule collapses to
the diagonal normalization

  `Σ_{x<D} (2x+1)(2f+1){a b x; c d f}²  ≃  1`.

This is the genuine Wigner 6j orthonormality — a *fractional* normalization
(`3/4 + 1/4 = 1` at the smallest tetrahedron), NOT a Kronecker δ-collapse.  It is
TRUE and fully `Q'`-expressible, but its all-label proof needs a 3j/CG
orthogonality layer or the Schulten–Gordon three-term recursion, neither present
in this codebase.  It is a faithful statement carrier; it is NOT inhabited
anywhere.  It is strictly smaller than the full sum rule (the off-triangle half
is discharged separately by `orthoSum_offTriangle_gen`). -/
def DiagonalSixJNormalization : Prop :=
  ∀ (a b c d f D : Rep), a + b + c + d + f < D →
    fusionOK a d f = true → fusionOK c b f = true →
    (orthoSum a b c d f D).eqv 1

/-! ## 4. The reduction: diagonal core ⇒ the full all-label sum rule. -/

/-- **The honest reduction.**  The sharpened diagonal-normalization core
`DiagonalSixJNormalization` (Half B) IMPLIES the full all-label Racah
orthogonality sum rule `SixJKernel.RacahOrthogonalityGeneral`.  Combined with the
unconditionally-proved off-triangle half `orthoSum_offTriangle_gen`, this
converts the all-label statement into (proved off-triangle) + (one strictly
smaller open normalization core) — a genuine sharpening, NOT a closure. -/
theorem racahOrthogonalityGeneral_of_diagonal
    (hdiag : DiagonalSixJNormalization) :
    SixJKernel.RacahOrthogonalityGeneral := by
  intro a b c d f D hlt
  by_cases hadf : fusionOK a d f = true
  · by_cases hcbf : fusionOK c b f = true
    · -- both faces valid: RHS = 1·1, use the diagonal core.
      have h1 := hdiag a b c d f D hlt hadf hcbf
      rw [fusionInd_val_one hadf, fusionInd_val_one hcbf]
      exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_symm (Q'.mul_one_eqv 1))
    · exact orthoSum_offTriangle_gen a b c d f D (Or.inr hcbf)
  · exact orthoSum_offTriangle_gen a b c d f D (Or.inl hadf)

/-! ## 5. Non-vacuity: the diagonal core holds at concrete cutoffs (`decide`). -/

/-- **Non-vacuity witness (`decide`).**  At the smallest tetrahedron
`a=b=c=d=½`, `f=spin 1` (twice-spin `2`) with a cutoff `D = 7 > a+b+c+d+f = 6`
clearing the physical support, the diagonal normalization holds:
`Σ_x (2x+1)·3·{½ ½ x; ½ ½ 1}² = 3/4 + 1/4 = 1`.  This shows
`DiagonalSixJNormalization` is a genuinely TRUE (non-vacuous) residual at a valid
largeness cutoff, not merely a statement carrier. -/
theorem diagonalNormalization_smallest : (orthoSum 1 1 1 1 2 7).eqv 1 := by decide

/-- **A second non-vacuity witness (`decide`), `f = spin 0`.**
`Σ_x dim(x)·{½ ½ x; ½ ½ 0}² = 1` at cutoff `D = 6 > a+b+c+d+f = 4`. -/
theorem diagonalNormalization_pZero : (orthoSum 1 1 1 1 0 6).eqv 1 := by decide

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean):

  * `orthoSum_offTriangle_gen` — Half A, the off-triangle Racah sum rule at ALL
    labels and cutoffs (both sides `≃ 0`);
  * `racahOrthogonalityGeneral_of_diagonal` — the reduction of the full
    all-label sum rule to the diagonal normalization core;
  * `diagonalNormalization_smallest`, `diagonalNormalization_pZero` — `decide`d
    non-vacuity of the residual at valid largeness cutoffs.

NAMED-open (NOT faked, NO inhabitant):

  * `DiagonalSixJNormalization` — the diagonal 6j orthonormality
    `Σ_x (2x+1)(2f+1){a b x; c d f}² = 1` (Half B), the sharpened,
    strictly-smaller core of `SixJKernel.RacahOrthogonalityGeneral`.

This module PROVES the off-triangle half of the Racah orthogonality sum rule and
SHARPENS the remaining obligation from the full all-label statement down to the
diagonal normalization core.  It is NOT the signed 6j associator, NOT the
Biedenharn–Elliott pentagon, NOT a continuum limit, and NOT a 4D Yang–Mills mass
gap.  The Clay problem stays OPEN. -/

end YMGap.Continuum.RacahOrthogonalityGeneral

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.racahKernelQ_mk6
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.valid6_ne_true_of
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.racahKernel6_eq_zero_of
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.orthoSum_offTriangle_gen
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.racahOrthogonalityGeneral_of_diagonal
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.diagonalNormalization_smallest
#print axioms YMGap.Continuum.RacahOrthogonalityGeneral.diagonalNormalization_pZero
