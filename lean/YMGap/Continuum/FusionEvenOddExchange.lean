/-
`FusionEvenOddExchange` -- a constructive parity-state compiler for the
heat-weighted Clebsch-box interlacing residual.

# What this file proves

For a sequence `a`, write

    E r = a (2*r),       O r = a (2*r+1).

The two alternating exchange laws

    E r * E (r+1) <= O r * O r,
    O r * O (r+1) <= E (r+1) * E (r+1)

are exactly the even and odd states of the step-two log-concavity automaton.
This file packages those states, proves that they assemble constructively to
`a s * a (s+2) <= a (s+1)^2`, and specializes the compiler to the finite
Clebsch-box triangle `s+2 <= 2*N`.  The resulting theorem feeds the exact
`quadDiff` residual of `FusionWeightedBoxInterlacing`, hence the existing
`UniformBoxLogConcave` compiler.

# A stronger certificate interface

`FiniteAlternatingRatioFence` is a genuine sufficient certificate rather
than another spelling of the quadratic target.  At each parity state it
supplies a computable nonnegative scale `q` and two first-order inequalities

    A <= q*B,       q*C <= B.

Nonnegativity then composes them to `A*C <= B^2`.  This is the usual abstract-
interpretation pattern: the quadratic safety property is established from a
small inductive invariant whose witnesses are executable rational data.  It
allows later heat-kernel work to certify simpler ratio bounds instead of
expanding the Cauchy--Binet quadruple sum.

# Honest scope

The parity-state compiler by itself is a reindexing equivalence, not analytic
progress, and is labelled as such below.  No uniform heat-weight ratio fence
is inhabited in this file.  Supplying those scale witnesses on every finite
triangle remains the heat-kernel even/odd exchange problem.  Consequently no
continuum or Clay frontier bundle is inhabited here.

# Constructive contract

Mathlib-free; pure `Q'`/`Nat`.  No `Classical`, `native_decide`, `sorry`, new
axiom, or `noncomputable` definition.  Content-bearing ratio scales are fields
of a `Type`-level structure.  Load-bearing declarations are axiom-gated below.
-/

import YMGap.Continuum.FusionWeightedBoxInterlacing

namespace YMGap.Continuum.FusionEvenOddExchange

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionWeightedBoxInterlacing

/-! ## 1. The two-state parity automaton -/

/-- The even-indexed subsequence of `a`. -/
def evenSubsequence (a : Nat → Q') (r : Nat) : Q' := a (2 * r)

/-- The odd-indexed subsequence of `a`. -/
def oddSubsequence (a : Nat → Q') (r : Nat) : Q' := a (2 * r + 1)

/-- The coupled transition invariant for the even and odd states of a
step-two log-concavity scan. -/
structure CoupledEvenOddExchange (E O : Nat → Q') : Type where
  /-- Even state: the intervening odd value dominates its two even neighbors. -/
  evenToOdd : ∀ r, E r * E (r + 1) ≤ O r * O r
  /-- Odd state: the intervening even value dominates its two odd neighbors. -/
  oddToEven : ∀ r, O r * O (r + 1) ≤ E (r + 1) * E (r + 1)

/-- The exchange invariant induced by the canonical parity decomposition of
one sequence. -/
abbrev EvenOddExchange (a : Nat → Q') : Type :=
  CoupledEvenOddExchange (evenSubsequence a) (oddSubsequence a)

/-- **Parity-state assembly.**  The two exchange transitions yield step-two
log-concavity at every index.  The proof performs a constructive two-state
case split with `Nat.mod_two_eq_zero_or_one`; it does not use excluded middle.

HONEST CLASSIFICATION: for arbitrary `a` this is a parity reindexing compiler,
not a proof of the analytic exchange inequalities. -/
theorem all_logConcave_of_evenOddExchange {a : Nat → Q'}
    (exchange : EvenOddExchange a) :
    ∀ s, a s * a (s + 2) ≤ a (s + 1) * a (s + 1) := by
  intro s
  rcases Nat.mod_two_eq_zero_or_one s with hs | hs
  · have hs0 : s = 2 * (s / 2) := by omega
    have hs2 : s + 2 = 2 * (s / 2 + 1) := by omega
    have h := exchange.evenToOdd (s / 2)
    unfold evenSubsequence oddSubsequence at h
    rw [← hs0, ← hs2] at h
    exact h
  · have hs0 : s = 2 * (s / 2) + 1 := by omega
    have hs1 : s + 1 = 2 * (s / 2 + 1) := by omega
    have hs2 : s + 2 = 2 * (s / 2 + 1) + 1 := by omega
    have h := exchange.oddToEven (s / 2)
    unfold evenSubsequence oddSubsequence at h
    rw [← hs0, ← hs2, ← hs1] at h
    exact h

/-! ## 2. A bounded parity automaton for a finite support triangle -/

/-- The two exchange states restricted to windows whose right endpoint is at
most `limit`.  The guards are the exact even and odd forms of `s+2 <= limit`. -/
structure FiniteCoupledEvenOddExchange
    (E O : Nat → Q') (limit : Nat) : Type where
  evenToOdd : ∀ r, 2 * r + 2 ≤ limit → E r * E (r + 1) ≤ O r * O r
  oddToEven : ∀ r, 2 * r + 3 ≤ limit → O r * O (r + 1) ≤ E (r + 1) * E (r + 1)

/-- The finite exchange invariant induced by a sequence's canonical parity
decomposition. -/
abbrev FiniteEvenOddExchange (a : Nat → Q') (limit : Nat) : Type :=
  FiniteCoupledEvenOddExchange (evenSubsequence a) (oddSubsequence a) limit

/-- Bounded parity-state assembly on `s+2 <= limit`. -/
theorem finite_logConcave_of_finiteEvenOddExchange
    {a : Nat → Q'} {limit : Nat}
    (exchange : FiniteEvenOddExchange a limit) :
    ∀ s, s + 2 ≤ limit →
      a s * a (s + 2) ≤ a (s + 1) * a (s + 1) := by
  intro s hsLimit
  rcases Nat.mod_two_eq_zero_or_one s with hs | hs
  · have hs0 : s = 2 * (s / 2) := by omega
    have hs2 : s + 2 = 2 * (s / 2 + 1) := by omega
    have h := exchange.evenToOdd (s / 2) (by omega)
    unfold evenSubsequence oddSubsequence at h
    rw [← hs0, ← hs2] at h
    exact h
  · have hs0 : s = 2 * (s / 2) + 1 := by omega
    have hs1 : s + 1 = 2 * (s / 2 + 1) := by omega
    have hs2 : s + 2 = 2 * (s / 2 + 1) + 1 := by omega
    have h := exchange.oddToEven (s / 2) (by omega)
    unfold evenSubsequence oddSubsequence at h
    rw [← hs0, ← hs2, ← hs1] at h
    exact h

/-! ## 3. Ratio-fence certificates: first-order bounds imply exchange -/

/-- A finite abstract-interpretation certificate for the alternating scan.
The scale functions are computational witnesses in `Type`, not erased
existentials.  Each transition is certified by two first-order ratio bounds. -/
structure FiniteAlternatingRatioFence
    (E O : Nat → Q') (limit : Nat) : Type where
  /-- Scale used on an even-to-odd transition. -/
  evenScale : Nat → Q'
  /-- Scale used on an odd-to-even transition. -/
  oddScale : Nat → Q'
  evenScale_nonneg : ∀ r, (0 : Q') ≤ evenScale r
  oddScale_nonneg : ∀ r, (0 : Q') ≤ oddScale r
  evenLeft : ∀ r, 2 * r + 2 ≤ limit → E r ≤ evenScale r * O r
  evenRight : ∀ r, 2 * r + 2 ≤ limit → evenScale r * E (r + 1) ≤ O r
  oddLeft : ∀ r, 2 * r + 3 ≤ limit → O r ≤ oddScale r * E (r + 1)
  oddRight : ∀ r, 2 * r + 3 ≤ limit → oddScale r * O (r + 1) ≤ E (r + 1)

/-- The elementary ratio-fence composition:
`A <= q*B` and `q*C <= B` imply `A*C <= B^2` when `B,C` are nonnegative.
No division or cancellation is used. -/
theorem quadratic_exchange_of_ratio_fence {A B C q : Q'}
    (hB0 : (0 : Q') ≤ B) (hC0 : (0 : Q') ≤ C)
    (hLeft : A ≤ q * B) (hRight : q * C ≤ B) :
    A * C ≤ B * B := by
  have h1 : A * C ≤ (q * B) * C :=
    Q'.mul_le_mul_of_nonneg_right A (q * B) C hLeft hC0
  have h2 : B * (q * C) ≤ B * B :=
    Q'.mul_le_mul_of_nonneg_left (q * C) B B hRight hB0
  have hswap : ((q * B) * C).eqv (B * (q * C)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (q * B) (B * q) C (Q'.mul_comm_eqv q B))
      (Q'.mul_assoc_eqv B q C)
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap) h2)

/-- A finite ratio fence compiles to the two quadratic exchange transitions.
This implication is strict as an interface: callers provide explicit scale
witnesses and linear bounds, not either quadratic conclusion. -/
def finiteCoupledExchange_of_ratioFence
    {E O : Nat → Q'} {limit : Nat}
    (hE0 : ∀ r, (0 : Q') ≤ E r)
    (hO0 : ∀ r, (0 : Q') ≤ O r)
    (fence : FiniteAlternatingRatioFence E O limit) :
    FiniteCoupledEvenOddExchange E O limit where
  evenToOdd := fun r hr =>
    quadratic_exchange_of_ratio_fence (hO0 r) (hE0 (r + 1))
      (fence.evenLeft r hr) (fence.evenRight r hr)
  oddToEven := fun r hr =>
    quadratic_exchange_of_ratio_fence (hE0 (r + 1)) (hO0 (r + 1))
      (fence.oddLeft r hr) (fence.oddRight r hr)

/-! ## 4. Specialization to the heat-weighted Clebsch box -/

/-- Even Clebsch-box modes. -/
def boxEven (w : Q') (N r : Nat) : Q' := boxSum w N (2 * r)

/-- Odd Clebsch-box modes. -/
def boxOdd (w : Q') (N r : Nat) : Q' := boxSum w N (2 * r + 1)

/-- The finite exchange certificate for one Clebsch box. -/
abbrev FiniteBoxEvenOddExchange (w : Q') (N : Nat) : Type :=
  FiniteCoupledEvenOddExchange (boxEven w N) (boxOdd w N) (2 * N)

/-- A ratio fence for the box subsequences compiles to the finite box exchange
certificate.  Coefficient nonnegativity supplies the abstract interpreter's
state invariant. -/
def finiteBoxEvenOddExchange_of_ratioFence {w : Q'}
    (hw0 : (0 : Q') ≤ w) (N : Nat)
    (fence : FiniteAlternatingRatioFence
      (boxEven w N) (boxOdd w N) (2 * N)) :
    FiniteBoxEvenOddExchange w N :=
  finiteCoupledExchange_of_ratioFence
    (fun r => boxSum_nonneg hw0 N (2 * r))
    (fun r => boxSum_nonneg hw0 N (2 * r + 1)) fence

/-- The two finite box exchange states assemble to the exact finite
cross-parity box inequality. -/
theorem finite_box_logConcave_of_evenOddExchange {w : Q'} {N : Nat}
    (exchange : FiniteBoxEvenOddExchange w N) :
    ∀ s, s + 2 ≤ 2 * N →
      boxSum w N s * boxSum w N (s + 2) ≤
        boxSum w N (s + 1) * boxSum w N (s + 1) := by
  intro s hs
  exact finite_logConcave_of_finiteEvenOddExchange exchange s hs

/-- The finite even/odd exchange certificate supplies the exact `quadDiff`
nonnegativity required by `FusionWeightedBoxInterlacing`. -/
theorem quadDiff_nonneg_of_finiteBoxEvenOddExchange {w : Q'} {N : Nat}
    (exchange : FiniteBoxEvenOddExchange w N) :
    ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s := by
  intro s hs
  have hcross := finite_box_logConcave_of_evenOddExchange exchange s hs
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.sub_nonneg_of_le hcross
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-- **Parity compiler to the uniform box residual.**  A finite exchange
certificate at every cutoff yields `UniformBoxLogConcave` through the existing
finite-support compiler.  This is wiring, not an inhabitant of the exchange
family. -/
def uniformBoxLogConcave_of_evenOddExchange {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (exchange : ∀ N, FiniteBoxEvenOddExchange w N) :
    UniformBoxLogConcave w :=
  uniformBoxLogConcave_of_finite_interlacing hw0 hstrong
    (fun N => quadDiff_nonneg_of_finiteBoxEvenOddExchange (exchange N))

/-- **Ratio-fence route to the uniform box residual.**  Explicit rational
scale witnesses and first-order bounds at every finite parity state suffice
for `UniformBoxLogConcave`.  The heat-kernel-specific fence remains an honest
input. -/
def uniformBoxLogConcave_of_ratioFences {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (fences : ∀ N, FiniteAlternatingRatioFence
      (boxEven w N) (boxOdd w N) (2 * N)) :
    UniformBoxLogConcave w :=
  uniformBoxLogConcave_of_evenOddExchange hw0 hstrong
    (fun N => finiteBoxEvenOddExchange_of_ratioFence hw0 N (fences N))

/-! ## 5. The compiler is non-vacuous -/

/-- The rational `(2,1,1,0,...)` obstruction. -/
def parityObstructionQ : Nat → Q'
  | 0 => 2
  | 1 | 2 => 1
  | _ => 0

/-- The parity exchange interface rejects the known mixed-parity obstruction:
its first even transition would assert `2 <= 1`. -/
theorem parityObstructionQ_not_evenOddExchange :
    EvenOddExchange parityObstructionQ → False := by
  intro exchange
  have hbad := exchange.evenToOdd 0
  unfold evenSubsequence oddSubsequence parityObstructionQ at hbad
  exact (by decide : ¬ ((2 : Q') * 1 ≤ 1 * 1)) hbad

/-! ## 6. PROVED vs. remaining analytic input

PROVED (constructive, axiom-gated):

* `all_logConcave_of_evenOddExchange` and
  `finite_logConcave_of_finiteEvenOddExchange`: the two-state parity compiler;
* `quadratic_exchange_of_ratio_fence` and
  `finiteCoupledExchange_of_ratioFence`: the stronger explicit-scale ratio
  certificate, which derives rather than assumes each quadratic transition;
* `finiteBoxEvenOddExchange_of_ratioFence`: heat-box nonnegativity instantiates
  the ratio-certificate state invariant;
* `quadDiff_nonneg_of_finiteBoxEvenOddExchange`: finite parity exchange supplies
  the exact finite `quadDiff` obligation;
* `uniformBoxLogConcave_of_evenOddExchange` and
  `uniformBoxLogConcave_of_ratioFences`: the downstream uniform compilers;
* `parityObstructionQ_not_evenOddExchange`: the interface is non-vacuous.

REMAINING (explicit input, no inhabitant here):

* construct `FiniteAlternatingRatioFence (boxEven w N) (boxOdd w N) (2*N)`
  for every cutoff `N` in the heat-kernel regime.  This is now a family of
  explicit rational scales plus first-order even/odd bounds.  It remains the
  weighted local-CLT content and is not implied by unweighted ballot-row
  log-concavity.
-/

end YMGap.Continuum.FusionEvenOddExchange

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionEvenOddExchange.all_logConcave_of_evenOddExchange
#print axioms YMGap.Continuum.FusionEvenOddExchange.finite_logConcave_of_finiteEvenOddExchange
#print axioms YMGap.Continuum.FusionEvenOddExchange.quadratic_exchange_of_ratio_fence
#print axioms YMGap.Continuum.FusionEvenOddExchange.finiteCoupledExchange_of_ratioFence
#print axioms YMGap.Continuum.FusionEvenOddExchange.finiteBoxEvenOddExchange_of_ratioFence
#print axioms YMGap.Continuum.FusionEvenOddExchange.finite_box_logConcave_of_evenOddExchange
#print axioms YMGap.Continuum.FusionEvenOddExchange.quadDiff_nonneg_of_finiteBoxEvenOddExchange
#print axioms YMGap.Continuum.FusionEvenOddExchange.uniformBoxLogConcave_of_evenOddExchange
#print axioms YMGap.Continuum.FusionEvenOddExchange.uniformBoxLogConcave_of_ratioFences
#print axioms YMGap.Continuum.FusionEvenOddExchange.parityObstructionQ_not_evenOddExchange
