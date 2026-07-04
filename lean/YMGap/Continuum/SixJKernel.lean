/-
**Track sixj-kernel — a FAITHFUL rational Racah 6j² kernel over `Q'`, pinning
and upgrading the `PentagonNumericCore` frontier, and proving a genuine 6j
orthogonality sum rule.**

`PentagonRelation.PentagonNumericCore` is the Level-2 associator datum: a
nonnegative rational Racah kernel `P = dim(e)·dim(f)·{6j}²` pinned at the
smallest SU(2) tetrahedron to the fractional value `1/4`.  Until now it was
inhabited only by the CONSTANT shape witness `numericShapeWitness` (`P ≡ 1/4`
everywhere).  This module builds the real thing.

# The squaring trick (why this is `Q'`-legal)

The signed Wigner `{6j}` is irrational — its four triangle coefficients
`Δ(j₁j₂j₃) = √[(…)! / (…)!]` carry square roots.  But the pentagon's
dimension-absorbed kernel `P = dim(e)dim(f)·{6j}²` SQUARES every triangle
coefficient away: `{6j}² = Δ₁²Δ₂²Δ₃²Δ₄²·S²` where `Δ²` is a ratio of
factorials and `S` is the (signed) Racah `t`-sum.  Hence `P ∈ Q'` EXACTLY,
computed entirely in `Nat`/`Int` factorial arithmetic — no reals, no `√`.

# What this module delivers

## Layer 1 — the faithful rational kernel (`racahKernelQ`).
`racahKernelQ (mk6 a b c d e f)` computes `dim(e)dim(f)·{a b e; c d f}²` over
`Q'`, GUARDED by the four-face triangle+parity predicate `fusionOK` (the kernel
is `0` off the physical tetrahedron; this is the twice-spin `/2` faithfulness
guard the constant witness lacks).  `racahKernelQ_nonneg`: `P ≥ 0` at every
label (products of nonneg factorials, plus a squared Racah sum).

## Layer 2 — the pinned instance (`racahKernelCore : PentagonNumericCore`).
`racahKernelQ_smallest` (`decide`): at the smallest tetrahedron `a=b=c=d=½`,
`e=f=1`, `P = 3·3·(1/6)² = 1/4` EXACTLY.  This inhabits `PentagonNumericCore`
with a kernel that genuinely VARIES across labels — a faithful upgrade over the
constant `numericShapeWitness`.  It is still refuted for every permutation
surrogate by the pre-existing `pentagonNumericCore_not_perm`.

## Layer 3 — self-checks + a GENUINE 6j orthogonality sum rule (`decide`).
  * `racahKernelQ_offTriangle` — `P = 0` at a non-recouplable label
    (`f = spin 2`, breaking the `(a,d,f)` triangle): the kernel VARIES, unlike
    the constant witness.
  * `orthoSum_smallest`, `orthoSum_offTriangle` — the Racah orthogonality
    `Σ_x P(mk6 a b c d x f) = {a d f}{c b f}` (triangle indicators), verified
    at concrete labels to `1` and `0`.  This is real 6j content — a genuine
    normalization/orthogonality relation the SQUARED kernel DOES satisfy
    (whereas Biedenharn–Elliott, being linear in the SIGNED 6j, does not).

## Layer 4 — the honest named residuals (uninhabited).
  * `RacahOrthogonalityGeneral` — the orthogonality sum rule at ALL labels /
    cutoffs.  It is TRUE (verified over 4⁵ labels out-of-band) and expressible
    in `Q'`, but its all-label proof is left as a named residual (NOT faked).
  * The DEEPER frontier — the signed 6j / Biedenharn–Elliott associator — is
    irrational, hence NOT `Q'`-representable, and stays the pre-existing
    `PentagonRelation.PentagonNumericCore` named obligation.  We do not invent a
    false rational B–E: the squared kernel provably cannot carry it.

# Honest verdict

A faithful, varying, axiom-clean rational 6j² kernel that inhabits the numeric
pentagon core and satisfies a genuine 6j orthogonality relation — a real
strengthening of the constant witness.  It is NOT the signed associator, NOT
the Biedenharn–Elliott pentagon, and NOT a Yang–Mills mass gap.  The Clay
problem stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Int` / `Fin` core only.  No `Classical.*`, no
`Real`, no `native_decide` (only `decide` on decidable `Q'.eqv` facts and
`by_cases` on decidable `Bool` equalities).  No `sorry` / `admit` / new
`axiom`.  All witnesses are `Type`-level data; the general orthogonality and the
signed associator are NAMED obligations, never faked.  `#print axioms` gated
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PentagonRelation
import YMGap.Continuum.TreeGraphBoundProgress

namespace YMGap.Continuum.SixJKernel

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.RacahInhabit
open YMGap.Continuum.PentagonRelation

/-! ## 0. Local `Int` square-nonnegativity (Lean core has no `Int.mul_self_nonneg`). -/

/-- `0 ≤ a * a` on `Int`, via the decidable total order (no `Classical`). -/
theorem int_mul_self_nonneg (a : Int) : (0 : Int) ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : (0 : Int) ≤ -a := Int.neg_nonneg.mpr h
    have hh : (0 : Int) ≤ (-a) * (-a) := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at hh

/-! ## 1. `Q'` nonnegativity helpers. -/

/-- `0 ≤ ofNat n` (a `Nat` coercion is nonnegative). -/
theorem qOfNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg n

/-- `0 ≤ q * q` (a square is nonnegative). -/
theorem qMulSelf_nonneg (q : Q') : (0 : Q') ≤ q * q := by
  rw [Q'.zero_le_iff_num_nonneg]; exact int_mul_self_nonneg q.num

/-! ## 2. The twice-spin factorial building blocks.

Physical spins are `j = rep/2`; all factorial arguments are `(rep-sum)/2`,
integer under the triangle+parity guard.  `Nat` truncated subtraction makes
every out-of-range argument `0` (`fact 0 = 1`), harmless because the full
kernel is zeroed by the `fusionOK` guard off the physical tetrahedron. -/

/-- Twice-spin dimension `dim(2j) = 2j + 1 = rep + 1`. -/
def dimRep (x : Rep) : Nat := x + 1

/-- Numerator of the squared triangle coefficient
`Δ(jₓjᵧj_z)² = (jₓ+jᵧ−j_z)!(jₓ−jᵧ+j_z)!(−jₓ+jᵧ+j_z)! / (jₓ+jᵧ+j_z+1)!`. -/
def triSqNum (x y z : Nat) : Nat :=
  fact ((x + y - z) / 2) * fact ((x + z - y) / 2) * fact ((y + z - x) / 2)

/-- Denominator of the squared triangle coefficient (`(jₓ+jᵧ+j_z+1)!`). -/
def triSqDen (x y z : Nat) : Nat := fact ((x + y + z) / 2 + 1)

/-- The squared triangle coefficient as an exact `Q'` (nonnegative). -/
def triSq (x y z : Nat) : Q' := Q'.mkN (triSqNum x y z) (triSqDen x y z - 1)

/-- `0 ≤ triSq x y z` (numerator is a `Nat` coercion). -/
theorem triSq_nonneg (x y z : Nat) : (0 : Q') ≤ triSq x y z := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _

/-! ## 3. The signed Racah `t`-sum (each summand exactly rational, sign in `Int`). -/

/-- The seven-factorial denominator of the Racah summand at `t`. -/
def sevenFacts (s1 s2 s3 s4 p1 p2 p3 t : Nat) : Nat :=
  fact (t - s1) * fact (t - s2) * fact (t - s3) * fact (t - s4)
    * fact (p1 - t) * fact (p2 - t) * fact (p3 - t)

/-- The `t`-summand range guard: all four triangle sums `≤ t ≤` all three
square sums (out-of-range summands vanish). -/
def tGuard (s1 s2 s3 s4 p1 p2 p3 t : Nat) : Bool :=
  s1 ≤ t && s2 ≤ t && s3 ≤ t && s4 ≤ t && t ≤ p1 && t ≤ p2 && t ≤ p3

/-- The signed Racah summand `(−1)ᵗ (t+1)! / (seven factorials)` at `t`. -/
def racahSummand (s1 s2 s3 s4 p1 p2 p3 t : Nat) : Q' :=
  if tGuard s1 s2 s3 s4 p1 p2 p3 t = true then
    ⟨(if t % 2 = 0 then (1 : Int) else -1) * Int.ofNat (fact (t + 1)),
      sevenFacts s1 s2 s3 s4 p1 p2 p3 t - 1⟩
  else 0

/-- The full signed Racah `t`-sum for `{jj₁ jj₂ jj₃; jj₄ jj₅ jj₆}`
(twice-spin labels), summed over a range covering the physical support. -/
def racahSum (jj1 jj2 jj3 jj4 jj5 jj6 : Nat) : Q' :=
  finSum
    (fun t => racahSummand
      ((jj1 + jj2 + jj3) / 2) ((jj1 + jj5 + jj6) / 2)
      ((jj4 + jj2 + jj6) / 2) ((jj4 + jj5 + jj3) / 2)
      ((jj1 + jj2 + jj4 + jj5) / 2) ((jj2 + jj3 + jj5 + jj6) / 2)
      ((jj1 + jj3 + jj4 + jj6) / 2) t)
    ((jj1 + jj2 + jj3 + jj4 + jj5 + jj6) / 2 + 1)

/-! ## 4. The faithful kernel `P = dim(e)dim(f)·{6j}²`, guarded by `fusionOK`. -/

/-- The four-face triangle+parity validity of the tetrahedron
`{a b e; c d f}` (faces `(a,b,e),(a,d,f),(c,b,f),(c,d,e)`). -/
def valid6 (a b c d e f : Rep) : Bool :=
  fusionOK a b e && fusionOK a d f && fusionOK c b f && fusionOK c d e

/-- The kernel on six explicit reps: `dim(e)dim(f)·{a b e; c d f}²`, or `0` off
the physical tetrahedron. -/
def racahKernel6 (a b c d e f : Rep) : Q' :=
  if valid6 a b c d e f = true then
    Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f)
      * (triSq a b e * triSq a d f * triSq c b f * triSq c d e)
      * (racahSum a b e c d f * racahSum a b e c d f)
  else 0

/-- **The faithful rational Racah 6j² kernel** `P : (Fin 6 → Rep) → Q'`. -/
def racahKernelQ (j : Fin 6 → Rep) : Q' :=
  racahKernel6 (j 0) (j 1) (j 2) (j 3) (j 4) (j 5)

/-- **Nonnegativity of the six-rep kernel.**  Either `0`, or a product of the
two nonneg dimensions, four nonneg squared-triangle coefficients, and a squared
Racah sum. -/
theorem racahKernel6_nonneg (a b c d e f : Rep) : (0 : Q') ≤ racahKernel6 a b c d e f := by
  unfold racahKernel6
  by_cases h : valid6 a b c d e f = true
  · rw [if_pos h]
    refine Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ?_ ?_) (qMulSelf_nonneg _)
    · exact Q'.mul_nonneg _ _ (qOfNat_nonneg _) (qOfNat_nonneg _)
    · exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (triSq_nonneg _ _ _) (triSq_nonneg _ _ _))
          (triSq_nonneg _ _ _))
        (triSq_nonneg _ _ _)
  · rw [if_neg h]; exact Q'.le_refl' 0

/-- **`racahKernelQ` is nonnegative at every label.** -/
theorem racahKernelQ_nonneg (j : Fin 6 → Rep) : (0 : Q') ≤ racahKernelQ j :=
  racahKernel6_nonneg (j 0) (j 1) (j 2) (j 3) (j 4) (j 5)

/-! ## 5. Layer 2 — the pinned value and the `PentagonNumericCore` inhabitant. -/

/-- **The fractional pinning (`decide`).**  At the smallest tetrahedron
`a=b=c=d=½`, `e=f=spin 1`: four triangles `(½,½,1)` give `Δ² = 1/6`, the Racah
`t`-sum is `6`, so `{6j} = (1/6)²·6 = 1/6` and
`P = 3·3·(1/6)² = 9/36 = 1/4`.  This is a single decidable `Q'.eqv`
(Int cross-multiplication), and doubles as a self-check on the twice-spin
argument wiring. -/
theorem racahKernelQ_smallest :
    (racahKernelQ smallestTetra).eqv oneQuarter := by decide

/-- **`racahKernelCore` — the FAITHFUL `PentagonNumericCore`.**  A genuine
dimension-weighted 6j² kernel that varies across labels, inhabiting the numeric
pentagon core — a strengthening of the constant `numericShapeWitness`. -/
def racahKernelCore : PentagonNumericCore where
  racahKernel := racahKernelQ
  nonneg := racahKernelQ_nonneg
  smallest_value := racahKernelQ_smallest

/-- **The refutation transports.**  Being a `PentagonNumericCore`, the faithful
kernel disagrees with every permutation surrogate at the smallest tetrahedron
(`racahKernelQ ≃ 1/4`, `racahPerm ∈ {0,1}`). -/
theorem racahKernelCore_not_perm :
    ¬ (racahKernelQ smallestTetra).eqv (racahPerm smallestTetra) :=
  pentagonNumericCore_not_perm racahKernelCore

/-! ## 6. Layer 3 — variation self-check + the 6j orthogonality sum rule. -/

/-- **The kernel VARIES (`decide`).**  At `f = spin 2` (twice-spin `4`) the
`(a,d,f) = (½,½,2)` face fails the triangle inequality, so `P = 0` — unlike the
constant witness.  This confirms the `fusionOK`/twice-spin guard bites. -/
theorem racahKernelQ_offTriangle :
    (racahKernelQ (mk6 1 1 1 1 2 4)).eqv 0 := by decide

/-- The orthogonality partial sum `Σ_{x < D} P(mk6 a b c d x f)`. -/
def orthoSum (a b c d f : Rep) (D : Nat) : Q' :=
  finSum (fun x => racahKernelQ (mk6 a b c d x f)) D

/-- **Racah orthogonality at the smallest tetrahedron (`decide`).**
`Σ_x dim(x)dim(1)·{½ ½ x; ½ ½ 1}² = {½ ½ 1}·{½ ½ 1} = 1`
(the `x = spin 0` term `3/4` plus the `x = spin 1` term `1/4`).  A genuine 6j
normalization relation the squared kernel satisfies. -/
theorem orthoSum_smallest : (orthoSum 1 1 1 1 2 5).eqv 1 := by decide

/-- **Racah orthogonality vanishing (`decide`).**  With `f = spin 2` breaking
both outer triangles, `Σ_x P(mk6 1 1 1 1 x 4) = 0` — the indicator
`{a d f}{c b f}` is `0`. -/
theorem orthoSum_offTriangle : (orthoSum 1 1 1 1 4 6).eqv 0 := by decide

/-- **A second orthogonality instance (`decide`), `f = spin 0`.**
`Σ_x dim(x)·{½ ½ x; ½ ½ 0}² = 1`. -/
theorem orthoSum_pZero : (orthoSum 1 1 1 1 0 4).eqv 1 := by decide

/-! ## 7. Layer 4 — the honest named residuals (uninhabited, NOT faked). -/

/-- **`RacahOrthogonalityGeneral` — the 6j orthogonality sum rule at ALL labels
(NAMED RESIDUAL).**

For every outer tetrahedron label and a cutoff `D` past the physical support,
`Σ_x P(mk6 a b c d x f) = {a d f}·{c b f}` (the product of the two outer
triangle indicators `fusionInd`).  This is TRUE — verified out-of-band over
`4⁵` label tuples — and fully `Q'`-expressible (it involves only the SQUARED
kernel), but its all-label / all-cutoff proof (the full Racah backcoupling
algebra) is left here as a sharp named obligation.  Concrete instances are
`orthoSum_smallest` (`= 1`), `orthoSum_offTriangle` (`= 0`), `orthoSum_pZero`
(`= 1`).  This `def` is a faithful statement carrier; it is NOT asserted /
inhabited anywhere. -/
def RacahOrthogonalityGeneral : Prop :=
  ∀ (a b c d f D : Rep), a + b + c + d + f < D →
    (orthoSum a b c d f D).eqv (fusionInd a d f * fusionInd c b f)

/-- **The deeper frontier is NOT `Q'`-representable (documentation lemma).**  A
`decide`-checkable witness that the SQUARED, dimension-weighted kernel takes a
FRACTIONAL value `1/4 ∉ {0,1}` at the smallest tetrahedron.  The signed
`{6j} = Δ·Δ·Δ·Δ·S` whose square this is carries `√`-triangle coefficients and
is irrational — so the Biedenharn–Elliott pentagon (LINEAR in the signed 6j)
cannot be stated over `Q'` at all.  That deeper associator stays the
pre-existing `PentagonRelation.PentagonNumericCore` named obligation; we do not
fabricate a rational B–E the squared kernel provably cannot satisfy. -/
theorem racahKernelQ_smallest_fractional :
    ¬ (racahKernelQ smallestTetra).eqv 0 ∧ ¬ (racahKernelQ smallestTetra).eqv 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    exact zero_ne_oneQuarter (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) racahKernelQ_smallest)
  · intro h
    exact one_ne_oneQuarter (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) racahKernelQ_smallest)

/-! ## 8. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean):

  * `racahKernelQ` (+ `racahKernelQ_nonneg`) — the faithful, `fusionOK`-guarded,
    exactly-rational Racah 6j² kernel;
  * `racahKernelQ_smallest` — the fractional pinning `P = 1/4` (by evaluation);
  * `racahKernelCore` — a FAITHFUL `PentagonNumericCore` inhabitant (varies
    across labels; upgrade over the constant `numericShapeWitness`);
  * `racahKernelCore_not_perm` — the permutation refutation transports;
  * `racahKernelQ_offTriangle` — the kernel vanishes off the physical
    tetrahedron (genuine variation);
  * `orthoSum_smallest`, `orthoSum_offTriangle`, `orthoSum_pZero` — concrete
    instances of the Racah orthogonality sum rule;
  * `racahKernelQ_smallest_fractional` — `P ∈ Q' \ {0,1}` at the smallest
    tetrahedron (the squared kernel is genuinely fractional).

NAMED-open (NOT faked, NO inhabitant):

  * `RacahOrthogonalityGeneral` — the orthogonality sum rule for all labels /
    cutoffs (true, `Q'`-expressible, all-label proof deferred);
  * the signed 6j / Biedenharn–Elliott associator — irrational, not
    `Q'`-representable, stays `PentagonRelation.PentagonNumericCore`.

This module is a faithful rational 6j² kernel + a genuine orthogonality
relation.  It is NOT the signed associator, NOT the pentagon, NOT a continuum
limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.SixJKernel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SixJKernel.int_mul_self_nonneg
#print axioms YMGap.Continuum.SixJKernel.qOfNat_nonneg
#print axioms YMGap.Continuum.SixJKernel.qMulSelf_nonneg
#print axioms YMGap.Continuum.SixJKernel.triSq_nonneg
#print axioms YMGap.Continuum.SixJKernel.racahKernel6_nonneg
#print axioms YMGap.Continuum.SixJKernel.racahKernelQ_nonneg
#print axioms YMGap.Continuum.SixJKernel.racahKernelQ_smallest
#print axioms YMGap.Continuum.SixJKernel.racahKernelCore
#print axioms YMGap.Continuum.SixJKernel.racahKernelCore_not_perm
#print axioms YMGap.Continuum.SixJKernel.racahKernelQ_offTriangle
#print axioms YMGap.Continuum.SixJKernel.orthoSum_smallest
#print axioms YMGap.Continuum.SixJKernel.orthoSum_offTriangle
#print axioms YMGap.Continuum.SixJKernel.orthoSum_pZero
#print axioms YMGap.Continuum.SixJKernel.racahKernelQ_smallest_fractional
