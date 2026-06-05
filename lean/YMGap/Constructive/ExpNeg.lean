/-
Level-2 sketch: the constructive `e^{−x}` for rational `x`, discharging
the `ExpUB` seed that `Constructive/ExpBound.lean` leaves abstract.

This is the **MVP/sketch** form (cf. `Reals.lean`, `Geometric.lean`,
which ship a compiling core plus a documented "Open work" section).  It
delivers the `Q'`-expressible series machinery and the structural facts
that are provable now; the convergence-modulus proof that upgrades
`partialSum` into a genuine `CReal` — and the bracket lemmas that
discharge the `ExpUB` fields — are derived in prose below and scoped as a
ledgered follow-on.  No theorem here is a `sorry`.

# The key observation: `e^{−x}` of a *rational* has *rational* partials

`e^{−x} = Σ_{k≥0} (−x)^k / k!`.  For `x : Q'` every term is rational, and
the term-to-term ratio is `(−x)/(k+1)` — a `Q'` multiplication by
`1/(k+1) = Q'.mkPos 1 (k+1)`.  So the partial sums are computable in `Q'`
with **no real arithmetic at all**.  This is why the constructive real
`expNeg x` can be built directly as the `CReal` whose `approx n` is the
`n`-term partial sum: the approximations live in `Q'`, only the *limit*
is a `CReal`.  Concretely (below): `term`, `partialSum`, and the rfl
recurrences are all here and compile.

# The modulus (sketch of the deferred `cauchy` proof)

To make `partialSum x` a `CReal` we owe the regular-Cauchy modulus:
`∀ ε > 0, ∃ N, ∀ m,n ≥ N, |Sₘ − Sₙ| ≤ ε`.  The clean route, valid for the
closure's use (`x = t·C₂ ≥ 0`):

  * **Restrict to a remainder regime `N₀ > x`.**  For `k ≥ N₀` the ratio
    `x/(k+1) ≤ x/(N₀+1) =: r < 1` (a `Q'` inequality), so the term
    magnitudes `|t_k| = x^k/k!` are dominated by a *geometric* sequence
    `|t_{N₀}|·r^{k−N₀}`.
  * **Geometric tail.**  `Σ_{k≥N} |t_k| ≤ |t_{N₀}|·r^{N−N₀}/(1−r)`, a
    `Q'` value — this is exactly the closed form deferred in
    `Geometric.lean` (`geometric_tail_closure_strong`).  Picking `N` with
    `r^{N−N₀} ≤ ε·(1−r)/|t_{N₀}|` (possible since `r^k → 0`, an
    `∃`-witness by induction on the rational `ε`) gives the modulus.
  * `|Sₘ − Sₙ| ≤ Σ_{k≥min(m,n)} |t_k|` since the partials differ by a
    block of terms; the geometric tail bounds it.

So `expNeg`'s modulus reduces to the **same geometric closed form** the
budget tail already needs — one piece of `Q'` arithmetic unlocks both.

# Discharging `ExpUB` (sketch)

With `expNeg x : CReal` in hand, the `ExpBound.ExpUB` fields become:

  * `E_pos`     — `e^{−x} ≥ 0`: every partial sum from an even cut is ≥ 0
                  for `x ∈ [0,1]`; in general use the dominated bracket.
  * `E_zero_le_one` — `e^{0} = 1`: `partialSum 0 n = 1` for `n ≥ 1`
                  (the `x = 0` series is `1 + 0 + …`), a rfl-level fact.
  * `E_antitone` — `x ≤ y ⇒ e^{−y} ≤ e^{−x}`: termwise on the dominated
                  series, lifted through `CReal.ofQ'_le_of_approx_ge`.
  * a usable *rational* `E`: the truncated lower bound `eₘ(x) = Σ_{k≤2m}
                  (−x)^k/k! ≤ e^{x}` (for `x ≥ 0`, even cut over-estimates)
                  gives `e^{−x} ≤ 1/eₘ(x)`; or, division-free, expose the
                  bound as `e^{−x}·eₘ(x) ≤ 1` — the form `ExpBound` can use
                  without `Q'.div`.

The bracket facts (`even cut ≥ limit ≥ odd cut` for `x ∈ [0,1]`) need the
alternating-decreasing argument, hence `Q'` term-magnitude monotonicity —
the same `mul_le_mul_of_nonneg_left` gap noted in `Geometric.lean`.

# Open work (ledgered, not `sorry`)

  * `expNeg (x : Q') : CReal` — needs the modulus above (⇒ geometric
    closed form).
  * `expNeg_le_one_of_nonneg`, `expNeg_antitone`, the `ExpUB` instance.
  * The `Q'` multiplicative lemmas (`mul_comm/assoc/add` at `eqv`,
    `mul_le_mul_of_nonneg_left`) shared with `Geometric.lean`'s
    extension — the single common dependency.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem below reports `[propext]` or empty.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import YMGap.Constructive.Reals

namespace YMGap.Constructive.ExpNeg

open YMGap.Constructive

/-! ## The series, in `Q'`

`term x k` is the `k`-th series term `(−x)^k / k!`, via the ratio
recurrence `t_{k+1} = t_k · (−x)/(k+1)`.  `partialSum x n = Σ_{k<n} t_k`.
Both are pure `Q'`; the division by `(k+1)` is `Q'.mkPos 1 (k+1)`. -/

/-- `k`-th term of the `e^{−x}` series.  `t_0 = 1`,
`t_{k+1} = t_k · ((−x) · 1/(k+1))`. -/
def term (x : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => term x k * ((-x) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))

/-- `n`-term partial sum `Σ_{k<n} term x k`. -/
def partialSum (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => partialSum x n + term x n

@[simp] theorem term_zero (x : Q') : term x 0 = 1 := rfl

@[simp] theorem term_succ (x : Q') (k : Nat) :
    term x (k + 1) = term x k * ((-x) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) := rfl

@[simp] theorem partialSum_zero (x : Q') : partialSum x 0 = 0 := rfl

@[simp] theorem partialSum_succ (x : Q') (n : Nat) :
    partialSum x (n + 1) = partialSum x n + term x n := rfl

/-- Sanity check that the recurrence is wired correctly: the 1-term
partial sum is `1` (the `k = 0` term), for every `x`. -/
theorem partialSum_one (x : Q') : partialSum x 1 = 1 := by
  simp only [partialSum_succ, partialSum_zero, term_zero, Q'.zero_add']

/-- The 2-term partial sum is `1 + t₁` (with `t₁ ≃ −x` the first-order
term).  Stated against the structural `1 + term x 1` rather than the
reduced `1 − x`, since `Q'` equality is structural, not semantic — the
`≃ 1 − x` form holds only up to `Q'.eqv` (cf. `Rationals.lean`). -/
theorem partialSum_two (x : Q') : partialSum x 2 = 1 + term x 1 := by
  show partialSum x 1 + term x 1 = 1 + term x 1
  rw [partialSum_one]

end YMGap.Constructive.ExpNeg

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.ExpNeg.term
#print axioms YMGap.Constructive.ExpNeg.partialSum
#print axioms YMGap.Constructive.ExpNeg.partialSum_one
#print axioms YMGap.Constructive.ExpNeg.partialSum_two
