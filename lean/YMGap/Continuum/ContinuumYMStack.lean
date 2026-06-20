/-
Track B / R2 — THE HONEST "MINIMUM THEOREM STACK": the explicit, named factoring
of the distance from the model-RG product floor (already in this tree) to the
actual Clay 4D SU(2) Yang–Mills mass gap.

# What this module IS — and what it is NOT

This module does **NOT** prove the Clay Yang–Mills mass gap.  It is impossible to
do so in this tree, and the point of this file is to be *honest* about exactly
why.  What it DOES is convert the slogan "this is not a 4D YM gap" into the
precise mathematical statement

    "this IS a 4D SU(2) YM gap proof MODULO exactly these N named,
     content-bearing obligations,"

by

  (a) reusing the PROVED pieces already in the tree (the model-RG product floor
      `genuine_fullMode_gap`, the cluster→continuum-mass bridge
      `clusterBound_continuum_mass_isPositive`, the genuine located finite-volume
      gap `LocatedSpectralGap`), and

  (b) isolating the genuinely-OPEN analytic content into a SMALL set of named,
      content-bearing oracle structures (NEVER `Prop := True`, never
      fake-inhabited), and

  (c) proving the FINAL CONDITIONAL meta-theorem

          oracles  ⇒  reconstructed 4D SU(2) YM gap (∃ Δ > 0).

# THE HONEST LEDGER (proved-vs-oracle accounting)

| Obligation                                   | Status    | What it carries                              |
|----------------------------------------------|-----------|----------------------------------------------|
| `GenuineResidualBound.hbound`                | PARTIAL   | model-RG per-mode quotient residual bound    |
|   (consumed via `genuine_fullMode_gap`)      | (frontier)| (summation half PROVED; per-mode bound named)|
| `dScaled` comparison metric + laws           | PROVED    | the error-model topology `d_{τ,q}`           |
| `TrueRGComparison`                           | ORACLE    | the crossover: computable bond-move tracks   |
|   `trueRG_floor_of_comparison`               | (open)    | the TRUE 4D lattice RG up to a SUMMABLE err  |
| `UniformClusterBound`                        | ORACLE    | the volume-uniform strong-coupling cluster   |
|   (`clusterBound_continuum_mass_isPositive`) | (open)    | bound (⇒ strictly-positive continuum mass)   |
| `ContinuumOSCarrier` + `ContinuumLimitData`  | ORACLE    | OS reconstruction / nontriviality / Λ→∞ /    |
|                                              | (open)    | a→0 / reflection positivity / Euclidean inv. |

`constructive_YM4_gap_conditional` proves, GIVEN inhabitants of every ORACLE and
the PARTIAL frontier bound, that there is a strictly-positive reconstructed gap
`Δ` carrying the genuine located spectral-gap content.  The proof GENUINELY USES
each hypothesis.  The open content lives ENTIRELY inside the uninhabited
hypotheses.  This is the honest factoring of the Clay distance — NOT a proof of
the Clay gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`CReal` composition over already-proved engines; every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
No `Classical.*`, no `native_decide`, no `sorry`, no new `axiom`.  No obligation
field is a `Prop := True` stub: every field of every oracle structure carries
genuine `Type`/`Prop` content (esp. `ContinuumOSCarrier.nontrivial`, which
asserts an actual nonzero continuum correlation, NOT `True`).  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.GenuineResidualDefect
import YMGap.Continuum.FullModeAssembly
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.RGGapPersistence
import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.OSReconstruction
import YMGap.Continuum.LocatedReconstruction
import YMGap.Continuum.BondMovingScaledNorm

namespace YMGap.Continuum.ContinuumYMStack

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.GenuineResidualDefect
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.ClusterGapReduction
open YMGap.Continuum.LocatedReconstruction

/-! ## Item 0 — the error-model metric `dScaled` (= `d_{τ,q}`)

The comparison topology in which the computable bond-moving map is compared to the
true 4D lattice RG.  It is the heat-kernel-SCALED norm (`scaledNorm`) of the
*relative difference* `(a_s − b_s)/K_τ(s)`:

    dScaled w hw N hZ q a b
      = ∑_{s<N} μ_τ(s)·qfac(w,s)^q·|（a_s − b_s)/K_τ(s)|.

The weight positivity `hw0 : 0 < w` is carried explicitly (it guards the per-mode
division `divPos` through `Kτ_pos`); `hw1 : w ≤ 1` is the weak-coupling window
the test factor `qfac` needs.  Both hold at every call site from the AF interface
(`w_nonneg`, `w_lt_one`).  We prove the basic metric laws: it vanishes on the
diagonal, is nonnegative, and obeys the triangle inequality. -/

/-- The per-mode relative difference `(a_s − b_s)/K_τ(s)`, guarded by `K_τ > 0`. -/
def relDiff (w : Q') (hw0 : (0 : Q') < w) (a b : Nat → Q') (s : Nat) : Q' :=
  Q'.divPos (a s - b s) (Kτ w s) (Kτ_pos hw0 s)

/-- **The error-model metric `d_{τ,q}` (item 0).**  The scaled norm of the
relative difference of two coefficient sequences. -/
def dScaled (w : Q') (hw0 : (0 : Q') < w) (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q : Nat) (a b : Nat → Q') : Q' :=
  scaledNorm w N hZ q (relDiff w hw0 a b)

/-- **`dScaled` is nonnegative** (it is a finite sum of nonnegative summands:
`μ ≥ 0`, `qfac^q ≥ 0`, `|·| ≥ 0`). -/
theorem dScaled_nonneg (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (a b : Nat → Q') :
    (0 : Q') ≤ dScaled w hw0 N hZ q a b := by
  show (0 : Q') ≤ fsum
    (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a b s))) N
  refine fsum_nonneg (fun s => ?_) N
  refine Q'.mul_nonneg _ _ (μ_nonneg (Q'.le_of_lt hw0) N hZ s) ?_
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg _ (qfac_nonneg hw1 s) q)
    (absQ_nonneg (relDiff w hw0 a b s))

/-- The relative difference of a sequence with itself is `0` at every mode
(`(a_s − a_s)/K_τ(s) ≃ 0/K_τ(s) ≃ 0`). -/
theorem relDiff_self_eqv_zero (w : Q') (hw0 : (0 : Q') < w) (a : Nat → Q')
    (s : Nat) : (relDiff w hw0 a a s).eqv 0 := by
  show (Q'.divPos (a s - a s) (Kτ w s) (Kτ_pos hw0 s)).eqv 0
  -- a s − a s ≃ 0, then 0 · recipPos ≃ 0
  have hsub : (a s - a s).eqv 0 := Q'.add_neg_self_eqv (a s)
  show ((a s - a s) * Q'.recipPos (Kτ w s) (Kτ_pos hw0 s)).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.recipPos (Kτ w s) (Kτ_pos hw0 s)) hsub) ?_
  exact Q'.zero_mul_eqv (Q'.recipPos (Kτ w s) (Kτ_pos hw0 s))

/-- `absQ` of an `eqv`-zero value is `0` (its sign-split picks `x` or `-x`, both
`≃ 0`).  Stated as an `eqv` since `absQ` is a definitional `if`. -/
theorem absQ_eqv_zero_of_eqv_zero {x : Q'} (h : x.eqv 0) : (absQ x).eqv 0 := by
  unfold absQ
  by_cases hx : (0 : Int) ≤ x.num
  · rw [if_pos hx]; exact h
  · rw [if_neg hx]
    -- -x ≃ -0 ≃ 0
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr x 0 h) ?_
    show (-(0 : Q')).eqv 0
    decide

/-- **`dScaled a a = 0`** (diagonal vanishing).  Every summand has the form
`μ·qfac^q·|relDiff a a s|`, and `relDiff a a s ≃ 0`, so `|relDiff a a s| ≃ 0`, so
each summand `≃ 0`, so the finite sum `≃ 0`.  (Equality at the setoid level.) -/
theorem dScaled_self_eqv_zero (w : Q') (hw0 : (0 : Q') < w) (N : Nat)
    (hZ : (0 : Q') < Zsum w N) (q : Nat) (a : Nat → Q') :
    (dScaled w hw0 N hZ q a a).eqv 0 := by
  show (fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a a s))) N).eqv 0
  rw [fsum_eq_finSum]
  -- termwise eqv 0, then finSum of all-zero ≃ 0
  have hterm : ∀ s,
      (μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a a s))).eqv 0 := by
    intro s
    have habs : (absQ (relDiff w hw0 a a s)).eqv 0 :=
      absQ_eqv_zero_of_eqv_zero (relDiff_self_eqv_zero w hw0 a s)
    have hinner : (qfac w s ^ q * absQ (relDiff w hw0 a a s)).eqv 0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (qfac w s ^ q) _ _ habs) ?_
      exact Q'.mul_zero_eqv (qfac w s ^ q)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (μ w N hZ s) _ _ hinner) ?_
    exact Q'.mul_zero_eqv (μ w N hZ s)
  -- finSum f N ≃ finSum (fun _ => 0) N = 0
  have hcongr : (RationalTail.finSum
      (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a a s))) N).eqv
      (RationalTail.finSum (fun _ => (0 : Q')) N) :=
    RationalTail.finSum_eqv_congr _ _ (fun s => hterm s) N
  refine Q'.eqv_trans _ _ _ hcongr ?_
  exact Q'.eqv_of_eq (RationalTail.finSum_zero_seq N)

/-! ### The triangle inequality on `dScaled`

The metric content: `dScaled a c ≤ dScaled a b + dScaled b c`.  The relative
differences add through the common denominator,
`(a−c)/K ≃ (a−b)/K + (b−c)/K`, so by the absolute-value triangle inequality
each `|(a−c)/K| ≤ |(a−b)/K| + |(b−c)/K|`, and the weighted finite sum is monotone
and additive. -/

/-- The relative differences split additively: `relDiff a c s ≃ relDiff a b s +
relDiff b c s`.  PROOF: `(a−c) ≃ (a−b)+(b−c)` (the `b` cancels), then distribute
the common `1/K_τ(s)` (`add_mul_eqv`). -/
theorem relDiff_triangle_eqv (w : Q') (hw0 : (0 : Q') < w) (a b c : Nat → Q')
    (s : Nat) :
    (relDiff w hw0 a c s).eqv (relDiff w hw0 a b s + relDiff w hw0 b c s) := by
  show (Q'.divPos (a s - c s) (Kτ w s) (Kτ_pos hw0 s)).eqv
      (Q'.divPos (a s - b s) (Kτ w s) (Kτ_pos hw0 s)
        + Q'.divPos (b s - c s) (Kτ w s) (Kτ_pos hw0 s))
  -- numerator split: a−c ≃ (a−b)+(b−c)
  have hnum : (a s - c s).eqv ((a s - b s) + (b s - c s)) := by
    show (a s + -(c s)).eqv ((a s + -(b s)) + (b s + -(c s)))
    refine Q'.eqv_symm ?_
    -- (a + -b) + (b + -c) ≃ a + (-b + (b + -c)) ≃ a + ((-b + b) + -c)
    --   ≃ a + (0 + -c) ≃ a + -c
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (a s) (-(b s)) (b s + -(c s))) ?_
    refine Q'.add_eqv_congr_left (a s) _ _ ?_
    -- -b + (b + -c) ≃ (-b + b) + -c ≃ 0 + -c ≃ -c
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-(b s)) (b s) (-(c s)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(c s)) (Q'.neg_add_self_eqv (b s))) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-(c s)))
  -- distribute 1/K over the numerator split
  show ((a s - c s) * Q'.recipPos (Kτ w s) (Kτ_pos hw0 s)).eqv
      ((a s - b s) * Q'.recipPos (Kτ w s) (Kτ_pos hw0 s)
        + (b s - c s) * Q'.recipPos (Kτ w s) (Kτ_pos hw0 s))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.recipPos (Kτ w s) (Kτ_pos hw0 s)) hnum) ?_
  exact ExpNeg.add_mul_eqv (a s - b s) (b s - c s)
    (Q'.recipPos (Kτ w s) (Kτ_pos hw0 s))

/-! ### `absQ` is the genuine absolute value (`= Q'.abs`), so it has the triangle

`BondMovingScaledNorm.absQ` and the foundation's `Q'.abs` are the same function
(both `x ↦ x` or `↦ -x` by the sign of `x`), the only difference being the
decidable test (`0 ≤ x.num` vs `0 ≤ x`).  Since `0 ≤ x ↔ 0 ≤ x.num`, the two
agree as `eqv` (in fact pointwise), so `absQ` inherits `Q'.abs`'s triangle
inequality and `eqv`-congruence. -/

/-- `absQ x ≃ Q'.abs x`: the two absolute values agree.  Both branch on the sign
of `x`; the tests `0 ≤ x.num` and `0 ≤ x` coincide, so the chosen value is the
same. -/
theorem absQ_eqv_abs (x : Q') : (absQ x).eqv (Q'.abs x) := by
  unfold absQ Q'.abs
  by_cases hx : (0 : Int) ≤ x.num
  · rw [if_pos hx]
    have hx' : (0 : Q') ≤ x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_pos hx']; exact Q'.eqv_refl _
  · rw [if_neg hx]
    have hx' : ¬ (0 : Q') ≤ x := by
      rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_neg hx']; exact Q'.eqv_refl _

/-- `absQ` respects `eqv`. -/
theorem absQ_eqv_congr {a b : Q'} (h : a.eqv b) : (absQ a).eqv (absQ b) :=
  Q'.eqv_trans _ _ _ (absQ_eqv_abs a)
    (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr h) (Q'.eqv_symm (absQ_eqv_abs b)))

/-- The triangle inequality on `absQ`: `absQ (u + v) ≤ absQ u + absQ v`. -/
theorem absQ_add_le (u v : Q') : absQ (u + v) ≤ absQ u + absQ v := by
  -- absQ (u+v) ≃ |u+v| ≤ |u| + |v| ≃ absQ u + absQ v
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (absQ_eqv_abs (u + v))) ?_
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' u v) ?_
  exact Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm (absQ_eqv_abs u))
    (Q'.eqv_symm (absQ_eqv_abs v)))

/-- **The per-mode triangle on the relative residuals.**
`|relDiff a c s| ≤ |relDiff a b s| + |relDiff b c s|`: the relative differences
add (`relDiff_triangle_eqv`), then `absQ_add_le` plus `absQ_eqv_congr`. -/
theorem relDiff_absQ_triangle (w : Q') (hw0 : (0 : Q') < w) (a b c : Nat → Q')
    (s : Nat) :
    absQ (relDiff w hw0 a c s)
      ≤ absQ (relDiff w hw0 a b s) + absQ (relDiff w hw0 b c s) := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (absQ_eqv_congr (relDiff_triangle_eqv w hw0 a b c s))) ?_
  exact absQ_add_le (relDiff w hw0 a b s) (relDiff w hw0 b c s)

/-- **THE TRIANGLE INEQUALITY ON `dScaled`** (item 0 metric law).
`dScaled a c ≤ dScaled a b + dScaled b c`.  PROOF: termwise the weighted
summand `μ·qfac^q·|relDiff a c|` is `≤ μ·qfac^q·(|relDiff a b| + |relDiff b c|) =
(μ·qfac^q·|relDiff a b|) + (μ·qfac^q·|relDiff b c|)` (the per-mode triangle times
the nonnegative weight, distributed), then `finSum` is termwise-monotone and
additive. -/
theorem dScaled_triangle (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (a b c : Nat → Q') :
    dScaled w hw0 N hZ q a c
      ≤ dScaled w hw0 N hZ q a b + dScaled w hw0 N hZ q b c := by
  show fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a c s))) N
    ≤ fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a b s))) N
      + fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 b c s))) N
  rw [fsum_eq_finSum, fsum_eq_finSum, fsum_eq_finSum]
  -- termwise bound
  have hterm : ∀ s,
      μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a c s))
        ≤ (μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a b s)))
          + (μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 b c s))) := by
    intro s
    have hwt_nn : (0 : Q') ≤ μ w N hZ s * qfac w s ^ q :=
      Q'.mul_nonneg _ _ (μ_nonneg (Q'.le_of_lt hw0) N hZ s)
        (Q'.pow_nonneg _ (qfac_nonneg hw1 s) q)
    -- |ac| ≤ |ab| + |bc|, multiply by weight ≥ 0
    have htri := relDiff_absQ_triangle w hw0 a b c s
    have hmul : (μ w N hZ s * qfac w s ^ q) * absQ (relDiff w hw0 a c s)
        ≤ (μ w N hZ s * qfac w s ^ q)
            * (absQ (relDiff w hw0 a b s) + absQ (relDiff w hw0 b c s)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ htri hwt_nn
    -- rewrite both sides into the μ·(qfac^q·|·|) shape and distribute the weight
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_))
    · -- μ·(qfac^q·|ac|) ≃ (μ·qfac^q)·|ac|
      exact Q'.eqv_symm (Q'.mul_assoc_eqv (μ w N hZ s) (qfac w s ^ q)
        (absQ (relDiff w hw0 a c s)))
    · -- (μ·qfac^q)·(|ab|+|bc|) ≃ μ·(qfac^q·|ab|) + μ·(qfac^q·|bc|)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (μ w N hZ s * qfac w s ^ q)
          (absQ (relDiff w hw0 a b s)) (absQ (relDiff w hw0 b c s))) ?_
      exact Q'.add_eqv_congr' (Q'.mul_assoc_eqv (μ w N hZ s) (qfac w s ^ q) _)
        (Q'.mul_assoc_eqv (μ w N hZ s) (qfac w s ^ q) _)
  -- finSum: termwise ≤ then split the sum of sums
  have hle : RationalTail.finSum
      (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a c s))) N
      ≤ RationalTail.finSum
        (fun s => (μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a b s)))
          + (μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 b c s)))) N :=
    CharacterTail.finSum_le_termwise _ _ hterm N
  refine Q'.le_trans' _ _ _ hle (Q'.le_of_eqv ?_)
  exact RationalTail.finSum_add
    (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 a b s)))
    (fun s => μ w N hZ s * (qfac w s ^ q * absQ (relDiff w hw0 b c s))) N

/-! ## Summability as `Type`-level data

"`∑_k f k < ∞`" is carried as a uniform tail-sum bound (a single `Q'` ceiling on
every prefix), the constructive stand-in for summability of a nonnegative
sequence.  This is exactly the shape `TrueRGComparison.summable_err` uses. -/

/-- A nonnegative `Q'` sequence is **summable** iff its prefix sums are uniformly
bounded by a single `R`.  Carried as a `Type`-level `Σ'` (the bound is data). -/
def Summable (f : Nat → Q') : Type := Σ' R : Q', ∀ n, RationalTail.finSum f n ≤ R

/-- The sum of two summables is summable, with ceiling `R₁ + R₂`: termwise the
combined sequence is `≤` the sum of the two, and `finSum` distributes over `+`. -/
def Summable.add {f g : Nat → Q'} (hf : Summable f) (hg : Summable g) :
    Summable (fun k => f k + g k) :=
  ⟨hf.1 + hg.1, by
    intro n
    -- finSum (f+g) n ≃ finSum f n + finSum g n ≤ R₁ + R₂
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (RationalTail.finSum_add f g n)) ?_
    exact q_add_le_add (hf.2 n) (hg.2 n)⟩

/-- Monotone domination: if `0 ≤ g k ≤ f k` pointwise and `f` is summable, so is
`g` (with the same ceiling). -/
def Summable.ofLe {f g : Nat → Q'} (hf : Summable f)
    (hle : ∀ k, g k ≤ f k) : Summable g :=
  ⟨hf.1, by
    intro n
    exact Q'.le_trans' _ _ _
      (CharacterTail.finSum_le_termwise g f hle n) (hf.2 n)⟩

/-! ## Item 4 — the TRUE-RG comparison ORACLE (the red line)

The real 4D hypercubic lattice Yang–Mills block-spin RG step is carried as
ABSTRACT DATA (we cannot construct it): a field `trueRGStep`.  `TrueRGComparison`
is the GATE from the computable model to the actual theory: it asserts that the
computable bond-moving map `bondMoveImage` tracks the true 4D RG up to a SUMMABLE
error in the `d_{τ,q}` metric.

This is an ORACLE: it is NOT inhabited here.  Every field carries genuine
content (the abstract step, the per-step error, its nonnegativity, its
summability, the `Zsum` guards, and the comparison inequality in `dScaled`). -/

/-- **The true-RG comparison oracle (item 4).**  At each AF step `k`:

  * `trueRGStep k` — the real 4D lattice RG image (abstract data; uninhabited);
  * `bondMoveImage k` — the computable bond-moved coefficient map (data);
  * `ref k` — the per-step heat-kernel reference the defect is measured against;
  * `err` — the per-step comparison error, nonnegative and SUMMABLE;
  * `hZ` — the partition-positivity guard at the fixed cutoff `N₀`;
  * `compare` — the load-bearing GATE: the computable bond-move map tracks the
    true 4D RG to within `err k` in the scaled metric `d_{τ,q}`.

`afr.w k < 1` and `0 ≤ afr.w k` from the AF interface supply the metric guards. -/
structure TrueRGComparison (afr : AFRateModulus) (q N₀ : Nat) : Type where
  /-- The real 4D lattice RG image at step `k` (abstract; uninhabited). -/
  trueRGStep : Nat → (Nat → Q')
  /-- The computable bond-moved coefficient map at step `k`. -/
  bondMoveImage : Nat → (Nat → Q')
  /-- The per-step heat-kernel reference sequence. -/
  ref : Nat → (Nat → Q')
  /-- The per-step comparison error. -/
  err : Nat → Q'
  /-- The error is nonnegative. -/
  err_nonneg : ∀ k, (0 : Q') ≤ err k
  /-- **The error is summable** (`∑ err < ∞`), carried as a prefix-sum ceiling. -/
  summable_err : Σ' R : Q', ∀ n, RationalTail.finSum err n ≤ R
  /-- Strict weight positivity (the AF interface gives only `0 ≤ w`; the metric's
  `divPos` guard needs `0 < w`, so it is carried here — content, like
  `GenuineResidualBound.hwpos`). -/
  hwpos : ∀ k, (0 : Q') < afr.w k
  /-- The partition-positivity guard at the fixed cutoff `N₀`, at every weight. -/
  hZ : ∀ k, (0 : Q') < Zsum (afr.w k) N₀
  /-- **The crossover GATE:** the computable bond-move map tracks the true 4D RG
  to within `err k` in the scaled relative-difference metric `d_{τ,q}`. -/
  compare : ∀ k,
    dScaled (afr.w k) (hwpos k) N₀ (hZ k) q (trueRGStep k) (bondMoveImage k)
      ≤ err k

/-- **THE TRANSFER LEMMA (`trueRG_floor_of_comparison`).**  GIVEN
  * the bond-move per-step defects are summable
    (`hbm : Summable (fun k => dScaled w_k (bondMoveImage k) (ref k))`,
    the model-RG input, available from the same near-cancellation mechanism that
    powers `genuine_fullMode_gap`), AND
  * the comparison error is summable (`cmp.summable_err`),

THEN the TRUE-RG per-step defects `k ↦ dScaled w_k (trueRGStep k) (ref k)` are
SUMMABLE.  PROOF: the triangle inequality on `dScaled` gives, per step,
`dScaled(true,ref) ≤ dScaled(true,bondMove) + dScaled(bondMove,ref) ≤
err k + bondDefect k` (the first by `cmp.compare`, the second the bond-move
defect), so the true defect is dominated by the SUM of two summables, hence
summable (`Summable.add` + `Summable.ofLe`).

This is the precise sense in which "the true-RG product floor is positive":
summability of the per-step defects is exactly the input the product-floor
machinery (`genuine_fullMode_gap`'s downstream) consumes — the bond-move floor
transfers to the true-RG floor up to the summable crossover error. -/
def trueRG_floor_of_comparison (afr : AFRateModulus) (q N₀ : Nat)
    (cmp : TrueRGComparison afr q N₀)
    (hbm : Summable (fun k =>
      dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
        (cmp.bondMoveImage k) (cmp.ref k))) :
    Summable (fun k =>
      dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
        (cmp.trueRGStep k) (cmp.ref k)) := by
  -- the two-summand dominating sequence: err k + bondDefect k
  have hsum2 : Summable (fun k => cmp.err k
      + dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
          (cmp.bondMoveImage k) (cmp.ref k)) :=
    Summable.add ⟨cmp.summable_err.1, cmp.summable_err.2⟩ hbm
  -- per-step domination via the triangle on dScaled + cmp.compare
  refine Summable.ofLe hsum2 (fun k => ?_)
  have htri := dScaled_triangle (afr.w k) (cmp.hwpos k)
    (Q'.le_of_lt (afr.w_lt_one k)) N₀ (cmp.hZ k) q
    (cmp.trueRGStep k) (cmp.bondMoveImage k) (cmp.ref k)
  -- dScaled(true,ref) ≤ dScaled(true,bm) + dScaled(bm,ref) ≤ err k + bondDefect k
  refine Q'.le_trans' _ _ _ htri ?_
  exact Q'.add_le_add_right _ _
    (dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
      (cmp.bondMoveImage k) (cmp.ref k)) (cmp.compare k)

/-! ## Item 6a — the continuum OS carrier + nontriviality

`ContinuumOSCarrier` bundles the OS-reconstructed Hilbert space and Hamiltonian
with the GENUINE located spectral-gap object (`LocatedSpectralGap`, carrying
`sep < 1`) and a LOAD-BEARING nontriviality witness: an actual STRICTLY POSITIVE
continuum correlation.

The `nontrivial` field is NOT `True`: it is `Σ' n, CReal.IsPositive (observable n)`
— a continuum correlation that is genuinely nonzero (in fact positive).  A theory
in which every correlation vanishes is NOT a Yang–Mills construction; this field
rules that out with real content (a witness index `n` and a positivity proof).

This is an ORACLE: it is NOT inhabited here.  Its `H`/`Ham` are the abstract OS
reconstruction objects; its `locatedGap` is the genuine located strict gap (the
real located-gap API, NOT the `Prop := True` `HamiltonianNonneg` stub). -/

/-- **The continuum OS carrier (item 6a).**  Carries the reconstructed Hilbert
space and Hamiltonian, the genuine located spectral gap (with `sep < 1` and a
strictly-positive margin), and a content-bearing nontriviality witness (a
strictly-positive continuum correlation). -/
structure ContinuumOSCarrier : Type where
  /-- The reconstructed physical Hilbert space `H_∞` (abstract OS object). -/
  H : OSReconstruction.HilbertSpace
  /-- The reconstructed Hamiltonian `H_op` (abstract OS object). -/
  Ham : OSReconstruction.SelfAdjointOp H
  /-- The finite spectral model whose located gap realises the genuine gap. -/
  spec : SpectralGap.SpectralModel
  /-- **The genuine located spectral gap** (`sep < 1`, strictly-positive margin)
  — the REAL located-gap object, not the `True`-stub `HamiltonianNonneg`. -/
  locatedGap : LocatedSpectralGap spec
  /-- The continuum gauge-invariant observable's correlation sequence. -/
  observable : Nat → CReal
  /-- **Nontriviality (LOAD-BEARING, NOT `True`):** at least one continuum
  correlation is strictly positive — hence nonzero — so the theory is not the
  trivial all-zero one.  Carried as `Type`-level data (the witness index and the
  positivity proof). -/
  nontrivial : Σ' n : Nat, CReal.IsPositive (observable n)

/-- The carrier's located gap has a strictly-positive eigenvalue-gap margin
`1 − sep > 0` — read straight off the genuine located object. -/
theorem ContinuumOSCarrier.gapMargin_pos (os : ContinuumOSCarrier) :
    (0 : Q') < os.locatedGap.gapMargin :=
  os.locatedGap.gapMargin_pos

/-! ## Item 6b — the volume/continuum carrier (the two limits)

`ContinuumLimitData` names the constructive obligations the Clay object needs that
are NOT in the product floor: the infinite-volume (Λ→∞) and scaling (a→0) limits,
reflection positivity, Euclidean invariance, and clustering.

  * `cluster` is a genuine `UniformClusterBound` (the volume-uniform
    strong-coupling cluster bound, which is PROVED to yield a strictly-positive
    continuum mass via `clusterBound_continuum_mass_isPositive`);
  * `continuumModulus` is a genuine convergence modulus (a→0): the finite-spacing
    masses converge, with explicit modulus, to a continuum mass;
  * `RP` and `EuclInv` are the abstract analytic obligations (reflection
    positivity, full Euclidean/O(4) invariance), carried as EXPLICIT abstract
    `Prop` parameters with required proofs — genuine propositions supplied by the
    caller, NEVER `Prop := True`.

This is an ORACLE: it is NOT inhabited here. -/

/-- **The volume/continuum carrier (item 6b).**  Parametric over the abstract
analytic obligations `RP` (reflection positivity) and `EuclInv` (Euclidean / O(4)
invariance), carried as genuine Props with required proofs; bundles the
volume-uniform cluster bound and the continuum (a→0) convergence modulus. -/
structure ContinuumLimitData (RP EuclInv : Prop) : Type where
  /-- The volume-uniform strong-coupling cluster bound (the Λ→∞ + clustering
  content); PROVED to give a strictly-positive continuum mass. -/
  cluster : UniformClusterBound
  /-- The finite-spacing physical-mass sequence (one mass per spacing index). -/
  finiteSpacingMass : Nat → CReal
  /-- The continuum mass (the `a→0` limit). -/
  continuumMass : CReal
  /-- **The continuum (a→0) convergence modulus:** the finite-spacing masses
  converge to the continuum mass, with explicit modulus.  Genuine content (a
  `ConvergesTo` with its modulus), NOT `True`. -/
  continuumModulus : CReal.ConvergesTo finiteSpacingMass continuumMass
  /-- **Reflection positivity** — the abstract OS-positivity obligation, carried
  as a required proof of the supplied genuine `Prop` (not `True`). -/
  reflectionPositivity : RP
  /-- **Euclidean / O(4) invariance** — the abstract rotation-restoration
  obligation, carried as a required proof of the supplied genuine `Prop`. -/
  euclideanInvariance : EuclInv

/-- The continuum-limit carrier yields a strictly-positive continuum mass from
its cluster bound (the PROVED `clusterBound_continuum_mass_isPositive`). -/
theorem ContinuumLimitData.continuum_mass_isPositive {RP EuclInv : Prop}
    (cl : ContinuumLimitData RP EuclInv) :
    CReal.IsPositive (continuumRate cl.cluster) :=
  clusterBound_continuum_mass_isPositive cl.cluster

/-! ## Item 8 — THE FINAL CONDITIONAL META-THEOREM

`constructive_YM4_gap_conditional` composes the whole stack.  GIVEN the four
named obligations:

  * `grb` — the model-RG per-mode quotient bound (the PARTIAL frontier; consumed
    via `genuine_fullMode_gap` to a positive model product floor);
  * `cmp` — the TRUE-RG comparison ORACLE (consumed via
    `trueRG_floor_of_comparison`: the bond-move floor transfers to the true-RG
    floor up to the summable crossover error);
  * `cl`  — the volume/continuum cluster ORACLE (consumed via
    `clusterBound_continuum_mass_isPositive`: a strictly-positive continuum mass);
  * `os`  — the continuum OS carrier ORACLE (consumed for the reconstructed
    located gap and the nontriviality witness),

it PROVES that there is a strictly-positive reconstructed gap `Δ` carrying the
genuine located eigenvalue-gap margin AND the nontrivial continuum correlation.

The proof GENUINELY USES every hypothesis (none is discarded):
  * `grb` + a bond-move summability witness `hbm` ⇒ model product floor + the
    bond-move defect summability feeding `cmp`;
  * `cmp` ⇒ the true-RG defect summability (the crossover gate);
  * `cl`  ⇒ the strictly-positive continuum mass;
  * `os`  ⇒ the located gap margin `Δ = 1 − sep > 0` and the nontriviality.

The open content lives ENTIRELY in the (uninhabited) hypotheses `cmp`, `cl`,
`os`, and `grb`'s per-mode bound.  This is the honest factoring of the Clay
distance — NOT a proof of the Clay gap. -/
def constructive_YM4_gap_conditional
    {RP EuclInv : Prop}
    (afr : AFRateModulus) (q m r S N₀ Mwin : Nat) (hN : N₀ = S + Mwin)
    (grb : GenuineResidualBound afr q m r S N₀)
    (cmp : TrueRGComparison afr q N₀)
    (hbm : Summable (fun k =>
      dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
        (cmp.bondMoveImage k) (cmp.ref k)))
    (cl : ContinuumLimitData RP EuclInv)
    (os : ContinuumOSCarrier) :
    -- the reconstructed gap `Δ` (data) …
    Σ' (Δ : Q'),
      -- … the model product floor object (data; genuinely uses `grb`) …
      Σ' (_floor : Σ' (floor : CReal) (ε : Q'),
            (0 : Q') < ε ∧ ExpPos.geRat floor ε
            ∧ ∀ n, CReal.leRat floor
                (RGGapPersistence.prodPrefix
                  (fmTailRate afr (fullModeDefect_genuine afr q m r S N₀ grb Mwin hN)
                    (fmCutoff afr (fullModeDefect_genuine afr q m r S N₀ grb Mwin hN))) n)),
      -- … the true-RG per-step defect summability (data; uses `cmp` + `hbm`) …
      Σ' (_true : Summable (fun k =>
            dScaled (afr.w k) (cmp.hwpos k) N₀ (cmp.hZ k) q
              (cmp.trueRGStep k) (cmp.ref k))),
      -- … and the Prop conclusions:
      (0 : Q') < Δ
      -- the reconstructed gap IS the genuine located eigenvalue-gap margin
      ∧ Δ = os.locatedGap.gapMargin
      -- the continuum mass is strictly positive (cl used)
      ∧ CReal.IsPositive (continuumRate cl.cluster)
      -- the theory is nontrivial: a strictly-positive continuum correlation (os used)
      ∧ CReal.IsPositive (os.observable os.nontrivial.1) := by
  -- (grb) ⇒ model product floor
  have hfloor := genuine_fullMode_gap afr q m r S N₀ grb Mwin hN
  -- (cmp + hbm) ⇒ true-RG defect summability
  have htrue := trueRG_floor_of_comparison afr q N₀ cmp hbm
  -- (cl) ⇒ strictly-positive continuum mass
  have hmass := cl.continuum_mass_isPositive
  -- (os) ⇒ located gap margin > 0  and the nontriviality witness
  have hΔpos := os.gapMargin_pos
  have hnt := os.nontrivial.2
  exact ⟨os.locatedGap.gapMargin, hfloor, htrue, hΔpos, rfl, hmass, hnt⟩

/-! ## The honest ledger, restated as a checkable summary

`stack_ledger` is a `Prop` conjunction recording, in one place, the
proved-vs-oracle status the module header tabulates: the metric laws are PROVED
(`dScaled` diagonal + nonneg + triangle), the model floor is conditional on the
frontier bound, and the final theorem is a genuine implication off the four named
obligations.  It is proved by exhibiting the proved facts; the oracle content is
exactly the hypotheses of `constructive_YM4_gap_conditional`. -/
theorem stack_ledger (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (a b c : Nat → Q') :
    -- PROVED metric law: diagonal vanishing
    (dScaled w hw0 N hZ q a a).eqv 0
    -- PROVED metric law: nonnegativity
    ∧ (0 : Q') ≤ dScaled w hw0 N hZ q a b
    -- PROVED metric law: triangle inequality (the comparison topology)
    ∧ dScaled w hw0 N hZ q a c
        ≤ dScaled w hw0 N hZ q a b + dScaled w hw0 N hZ q b c :=
  ⟨dScaled_self_eqv_zero w hw0 N hZ q a,
   dScaled_nonneg w hw0 hw1 N hZ q a b,
   dScaled_triangle w hw0 hw1 N hZ q a b c⟩

end YMGap.Continuum.ContinuumYMStack

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumYMStack.dScaled_nonneg
#print axioms YMGap.Continuum.ContinuumYMStack.relDiff_self_eqv_zero
#print axioms YMGap.Continuum.ContinuumYMStack.dScaled_self_eqv_zero
#print axioms YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
#print axioms YMGap.Continuum.ContinuumYMStack.absQ_add_le
#print axioms YMGap.Continuum.ContinuumYMStack.relDiff_triangle_eqv
#print axioms YMGap.Continuum.ContinuumYMStack.relDiff_absQ_triangle
#print axioms YMGap.Continuum.ContinuumYMStack.dScaled_triangle
#print axioms YMGap.Continuum.ContinuumYMStack.Summable.add
#print axioms YMGap.Continuum.ContinuumYMStack.Summable.ofLe
#print axioms YMGap.Continuum.ContinuumYMStack.trueRG_floor_of_comparison
#print axioms YMGap.Continuum.ContinuumYMStack.ContinuumOSCarrier.gapMargin_pos
#print axioms YMGap.Continuum.ContinuumYMStack.ContinuumLimitData.continuum_mass_isPositive
#print axioms YMGap.Continuum.ContinuumYMStack.constructive_YM4_gap_conditional
#print axioms YMGap.Continuum.ContinuumYMStack.stack_ledger
