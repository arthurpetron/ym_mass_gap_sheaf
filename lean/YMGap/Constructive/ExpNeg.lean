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

The shared dependencies are now **discharged**: the `Q'` semiring-`eqv`
layer (`RationalsMul.lean`: `mul_comm/assoc/add_eqv`,
`mul_le_mul_of_nonneg_left`, congruence) and the geometric tail closed
form (`GeometricTail.lean`: `geometric_tail_closure`) both exist and are
axiom-clean.  What remains for `expNeg`:

  * `expNeg (x : Q') : CReal` — the `cauchy` field.  Its analytic core
    (geometric tail past `N₀ > x`) is now `geometric_tail_closure`; the
    residual is the *term-magnitude* control: `|t_{k+1}| ≤ r·|t_k|` for
    `k ≥ N₀` (ratio `x/(k+1) ≤ r < 1`), the alternating two-sided block
    bound `|Sₘ − Sₙ| ≤` tail, and the `∃N` witness from `ε` (factorial
    growth).  No new shared lemmas — only series-specific `Q'` work.
  * `expNeg_le_one_of_nonneg`, `expNeg_antitone`, the `ExpUB` instance
    (and its `E_bounds` tie `expNeg x ≤ ofQ' (E x)`), then the SU(3)
    `Z_t` CReal upper bound feeding `ExpBound.Z_upper_su3`.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem below reports `[propext]` or empty.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import YMGap.Constructive.Reals
import YMGap.Constructive.RationalsMul

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

/-! ## The magnitude series `Σ xᵏ/k!` (all nonnegative)

`termAbs x k = xᵏ/k! = |term x k|` (for `x ≥ 0`), via the same recurrence
with `+x` in place of `−x`.  It dominates `term x k` two-sidedly
(`−termAbs ≤ term ≤ termAbs`), which is what turns the alternating series'
block differences into a (sign-free) magnitude tail — the first half of
the Cauchy modulus.  `Q'.mkPos 1 (k+1) (Nat.succ_pos _)` is `Q'.invSucc k`
definitionally, so `Q'.invSucc_nonneg` discharges the factor's sign. -/

/-- `k`-th magnitude term `xᵏ/k!`. -/
def termAbs (x : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))

@[simp] theorem termAbs_zero (x : Q') : termAbs x 0 = 1 := rfl

@[simp] theorem termAbs_succ (x : Q') (k : Nat) :
    termAbs x (k + 1) = termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) := rfl

/-- The magnitude partial sum `Σ_{k<n} termAbs x k`. -/
def partialSumAbs (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => partialSumAbs x n + termAbs x n

@[simp] theorem partialSumAbs_zero (x : Q') : partialSumAbs x 0 = 0 := rfl

@[simp] theorem partialSumAbs_succ (x : Q') (n : Nat) :
    partialSumAbs x (n + 1) = partialSumAbs x n + termAbs x n := rfl

/-- For `x ≥ 0`, every magnitude term is nonnegative. -/
theorem termAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ k, (0 : Q') ≤ termAbs x k
  | 0 => by show (0 : Q') ≤ 1; decide
  | k + 1 => by
    show (0 : Q') ≤ termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
    exact Q'.mul_nonneg _ _ (termAbs_nonneg x hx k)
      (Q'.mul_nonneg _ _ hx (Q'.invSucc_nonneg k))

/-! ## The alternating → magnitude two-sided bound

`−(termAbs x k) ≤ term x k ≤ termAbs x k` for `x ≥ 0`.  This is the
conceptual core that turns the *signed* alternating series into the
*nonnegative* magnitude series: it lets the block differences
`partialSum x m − partialSum x n` be bounded by the magnitude tail
`partialSumAbs x m − partialSumAbs x n`, which is the route to the Cauchy
modulus without any absolute-value construction on `Q'`.

Proved by induction: the step uses `term x (k+1) = term x k · (−x)·c`,
`termAbs x (k+1) = termAbs x k · (x·c)`, and the negation/congruence
`eqv` laws from `RationalsMul.lean`, chained through `≤` via
`le_of_eqv`/`ge_of_eqv` (the symmetric `±term ≤ termAbs` form keeps each
side using one induction hypothesis, with no double-negation). -/
theorem term_two_sided (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ k, term x k ≤ termAbs x k ∧ (-(term x k)) ≤ termAbs x k
  | 0 => by
    refine ⟨?_, ?_⟩
    · show (1 : Q') ≤ 1; exact Q'.le_refl' 1
    · show (-(1 : Q')) ≤ 1; decide
  | k + 1 => by
    obtain ⟨h1, h2⟩ := term_two_sided x hx k
    -- `Q'.invSucc k` is `Q'.mkPos 1 (k+1) (Nat.succ_pos _)` definitionally.
    have he : (0 : Q') ≤ x * Q'.invSucc k :=
      Q'.mul_nonneg _ _ hx (Q'.invSucc_nonneg k)
    refine ⟨?_, ?_⟩
    · -- term x (k+1) = term x k · ((−x)·c) ≤ termAbs x k · (x·c)
      show term x k * ((-x) * Q'.invSucc k) ≤ termAbs x k * (x * Q'.invSucc k)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left (term x k) ((-x) * Q'.invSucc k)
          (-(x * Q'.invSucc k)) (Q'.neg_mul_eqv x (Q'.invSucc k))))
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_neg_eqv (term x k) (x * Q'.invSucc k)))
          (Q'.le_trans' _ _ _
            (Q'.ge_of_eqv (Q'.neg_mul_eqv (term x k) (x * Q'.invSucc k)))
            (Q'.mul_le_mul_of_nonneg_right (-(term x k)) (termAbs x k)
              (x * Q'.invSucc k) h2 he)))
    · -- −(term x (k+1)) ≤ termAbs x k · (x·c)
      show (-(term x k * ((-x) * Q'.invSucc k))) ≤ termAbs x k * (x * Q'.invSucc k)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (term x k) ((-x) * Q'.invSucc k) (-(x * Q'.invSucc k))
            (Q'.neg_mul_eqv x (Q'.invSucc k)))))
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (term x k) (x * Q'.invSucc k))))
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.neg_neg_eqv (term x k * (x * Q'.invSucc k))))
            (Q'.mul_le_mul_of_nonneg_right (term x k) (termAbs x k)
              (x * Q'.invSucc k) h1 he)))

/-! ## Block bound: alternating partial-sum differences ≤ magnitude block

`blockAbs x n d = Σ_{j<d} termAbs x (n+j)` is the (nonnegative) magnitude
of the term block `[n, n+d)`.  The two-sided bound says the *signed*
partial-sum difference over that block is dominated by it — the bridge
from `term_two_sided` to the Cauchy modulus (a `Q'`, sign-free tail
two-sidedly bounding the alternating partials, no abs construction).

`block_upper` is the clean half (`add_assoc` only).  `block_lower` is the
standing follow-on: its step must commute a term past `blockAbs`, which
needs *additive* `eqv`-congruence (`a ≃ b → a+c ≃ b+c`), built like
`mul_eqv_congr_left` via a bespoke `Int` rearrangement — the AC-`simp`
route that sufficed for 3-term `add_assoc_eqv` times out on the 4-term
rearrangement. -/

/-- Magnitude of the term block `[n, n+d)`: `Σ_{j<d} termAbs x (n+j)`. -/
def blockAbs (x : Q') (n : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => blockAbs x n d + termAbs x (n + d)

@[simp] theorem blockAbs_zero (x : Q') (n : Nat) : blockAbs x n 0 = 0 := rfl

@[simp] theorem blockAbs_succ (x : Q') (n d : Nat) :
    blockAbs x n (d + 1) = blockAbs x n d + termAbs x (n + d) := rfl

/-- `0 ≤ term x k + termAbs x k` for `x ≥ 0` (from `term_two_sided.2`,
via `−(term) + term ≃ 0` and `add_comm`). -/
theorem term_add_termAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ term x k + termAbs x k :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_add_self_eqv (term x k)))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right (-(term x k)) (termAbs x k) (term x k)
        (term_two_sided x hx k).2)
      (Q'.le_of_eqv (Q'.add_comm_eqv (termAbs x k) (term x k))))

/-- **Block upper bound.**  `partialSum x (n+d) ≤ partialSum x n + blockAbs x n d`.
By induction on `d`: the step replaces `term` by `termAbs` in place
(`term ≤ termAbs`) and regroups with `add_assoc` — no commutation, so no
additive congruence is needed. -/
theorem block_upper (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    ∀ d, partialSum x (n + d) ≤ partialSum x n + blockAbs x n d
  | 0 => by
    show partialSum x n ≤ partialSum x n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_upper x hx n d
    show partialSum x (n + d) + term x (n + d)
          ≤ partialSum x n + (blockAbs x n d + termAbs x (n + d))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (partialSum x (n + d)) (term x (n + d)) (termAbs x (n + d))
        (term_two_sided x hx (n + d)).1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right (partialSum x (n + d)) (partialSum x n + blockAbs x n d)
          (termAbs x (n + d)) ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (partialSum x n) (blockAbs x n d)
          (termAbs x (n + d)))))

/-- **Block lower bound.**  `partialSum x n ≤ partialSum x (n+d) + blockAbs x n d`.
By induction on `d`: the step injects the nonnegative `term + termAbs`
(`term_add_termAbs_nonneg`) and re-sorts the four summands with
`add_swap_inner` — this is the half that needs additive `eqv`-congruence. -/
theorem block_lower (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    ∀ d, partialSum x n ≤ partialSum x (n + d) + blockAbs x n d
  | 0 => by
    show partialSum x n ≤ partialSum x n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_lower x hx n d
    show partialSum x n
          ≤ (partialSum x (n + d) + term x (n + d))
            + (blockAbs x n d + termAbs x (n + d))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (partialSum x (n + d) + blockAbs x n d)
        (term x (n + d) + termAbs x (n + d)) (term_add_termAbs_nonneg x hx (n + d)))
      (Q'.le_of_eqv (Q'.add_swap_inner (partialSum x (n + d)) (blockAbs x n d)
        (term x (n + d)) (termAbs x (n + d))))

end YMGap.Constructive.ExpNeg

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.ExpNeg.term
#print axioms YMGap.Constructive.ExpNeg.partialSum
#print axioms YMGap.Constructive.ExpNeg.partialSum_one
#print axioms YMGap.Constructive.ExpNeg.partialSum_two
#print axioms YMGap.Constructive.ExpNeg.termAbs
#print axioms YMGap.Constructive.ExpNeg.partialSumAbs
#print axioms YMGap.Constructive.ExpNeg.termAbs_nonneg
#print axioms YMGap.Constructive.ExpNeg.term_two_sided
#print axioms YMGap.Constructive.ExpNeg.blockAbs
#print axioms YMGap.Constructive.ExpNeg.term_add_termAbs_nonneg
#print axioms YMGap.Constructive.ExpNeg.block_upper
#print axioms YMGap.Constructive.ExpNeg.block_lower
