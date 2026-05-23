/-
Constructive rationals — a minimal axiom-clean ℚ for Phase 3 of the
constructive Yang–Mills mass gap program.  Milestone 3.0.

# Why this module exists

`lean/AGENTS.md` Rule 3 forbids Mathlib's `ℝ` (which uses
`Classical.choice` for completeness) and demands that every limit,
bound, and rate carry an explicit modulus.  The Phase-3 kickoff
analysis (Decision 1) determined that for the per-step budgets
ε_sf, ε_lf, Δ_∩, η — each of which is naturally bounded above by
an explicit rational expression in `(b, g_k)` — **a rational upper
bound IS an explicit modulus**.  Full constructive reals are not
required for stating per-step bounds; exact rationals suffice and
are Rule-3-compliant.

Lean 4 core's built-in `Rat` cannot be used here: the P1.1 SU(2)
work empirically established that even the reflexive equality
`(3 : Rat) / 4 = (3 : Rat) / 4` proved by `rfl` reports
`depends on axioms: [propext, Classical.choice, Quot.sound]` via
`Rat.decEq`.  AGENTS.md Rule 1 forbids `Classical.choice` in
load-bearing theorems.  We therefore reconstruct ℚ from scratch
here, atop `Int` and `Nat` (both axiom-clean in Lean core).

# Representation

`Q'` carries a numerator `num : Int` and the *predecessor* of its
denominator `denPred : Nat`; the actual denominator
`den := denPred + 1` is therefore positive structurally.  We do
**not** enforce normalization (no `gcd(num, den) = 1` field).  Two
`Q'` values can represent the same rational but differ
structurally — e.g.\ `mk 1 2 = ⟨1, 1⟩` and `mk 2 4 = ⟨2, 3⟩` both
represent `1/2`.  For Phase-3 use (constructing explicit constants
with simple denominators, then performing limited arithmetic),
this is acceptable; semantic equality and order are decidable
via cross-product comparison on `Int`.

Trade-off: unnormalized terms can grow.  Phase 3 does not chain
deeply enough for this to matter.  If a later phase needs
normalization, a `Q'.reduce` operation can be added without
breaking the interface.

# Boundary — what this module does NOT cover

**The ℚ-only representation handles per-step bounds, not infinite
sums.**  A statement like "ε_sf(b, g_k) ≤ q for some q : Q'" at a
fixed scale `k` is a complete Rule-3 modulus.  But the global
budget closures that Phase 3 must eventually establish —

  `Σ_k Δ_∩(b, g_k) < ∞`        (work_plan.md §10.3)
  `Σ_k η(b, g_k) < σ̂_0`        (work_plan.md §10.4)
  `inf_k σ̂_k > 0`               (the uniform σ-3 survival)

— are statements about an infinite-sum's convergence (or an
infinite-infimum's positivity).  Per-term rational bounds do
**not** automatically yield these limit facts.  The convergence
of `Σ_k η_k` to a value `< σ̂_0` is a constructive-limit
statement that may require either:

  (a) A separate constructive-limit / Cauchy-style argument
      built on Q' (a small additional module, much smaller than
      full `Constructive/Reals.lean`); or
  (b) A direct rational majorization showing each tail
      `Σ_{k ≥ K} η_k ≤ q` for some `q : Q'` parametrized by `K`,
      where the tail bound itself is rational; or
  (c) Full `Constructive/Reals.lean` if (a) and (b) prove
      insufficient.

This boundary is named here, in the very docstring of the module
the Phase-3 framework rests on, so that whichever later milestone
needs the global closure (Milestone 3.4, σ̂ 2-cell budget) does
not silently assume `Q'` is sufficient.  When 3.4 arrives,
re-examine: what does the actual analytic derivation of η need?
Decision recorded in the Phase-3 kickoff ratification (Decision 1
record-now item).
-/

namespace YMGap.Constructive

/-! ## The `Q'` representation -/

/-- A rational number.  `num` is the integer numerator; `denPred + 1`
is the (positive) denominator.  See module docstring for the design
rationale (unnormalized; not Lean-core `Rat`). -/
structure Q' where
  num     : Int
  denPred : Nat
deriving DecidableEq, Repr

namespace Q'

/-- The denominator of `q`, always positive. -/
@[inline] def den (q : Q') : Nat := q.denPred + 1

theorem den_pos (q : Q') : 0 < q.den := Nat.succ_pos _

/-- Construct `n/d` for `n : Int`, `d : Nat`, `0 < d`.

The positivity hypothesis `_h` is required of the caller (so users
cannot construct nonsensical `mkPos n 0 _`) but is not used in the
body: by Nat structure, `d ≥ 1` implies `d = d.pred + 1`, so storing
`d.pred` recovers `d` as `den`.  See `mkPos_den` below for the proof. -/
@[inline] def mkPos (n : Int) (d : Nat) (_h : 0 < d) : Q' :=
  ⟨n, d.pred⟩

/-- `mkPos` produces a `Q'` with the requested denominator. -/
theorem mkPos_den (n : Int) (d : Nat) (h : 0 < d) :
    (mkPos n d h).den = d := by
  unfold mkPos den
  exact Nat.succ_pred_eq_of_pos h

/-- `mkPos` produces a `Q'` with the requested numerator. -/
theorem mkPos_num (n : Int) (d : Nat) (h : 0 < d) :
    (mkPos n d h).num = n := rfl

/-- Construct from a `Nat` numerator over denominator `d.pred + 1`. -/
@[inline] def mkN (n : Nat) (denPred : Nat) : Q' :=
  ⟨Int.ofNat n, denPred⟩

/-- Coerce an integer to `Q'` (denominator 1). -/
@[inline] def ofInt (n : Int) : Q' := ⟨n, 0⟩

/-- Coerce a natural to `Q'` (denominator 1). -/
@[inline] def ofNat (n : Nat) : Q' := ⟨Int.ofNat n, 0⟩

/-! ### Numeric literals -/

instance : Zero Q' := ⟨ofInt 0⟩
instance : One Q' := ⟨ofInt 1⟩
instance (n : Nat) : OfNat Q' n := ⟨ofNat n⟩

/-! ### Arithmetic — unnormalized, exact at the value level -/

/-- Negation: `-(n/d) = (-n)/d`. -/
@[inline] def neg (q : Q') : Q' := ⟨-q.num, q.denPred⟩

instance : Neg Q' := ⟨neg⟩

/-- Addition: `a/b + c/d = (ad + cb) / (bd)`.  Denominator is `b*d`,
both positive, so the predecessor is `b*d - 1` (Nat truncating
subtraction is well-defined here since `b*d ≥ 1`). -/
@[inline] def add (p q : Q') : Q' :=
  ⟨p.num * (q.den : Int) + q.num * (p.den : Int),
   p.den * q.den - 1⟩

instance : Add Q' := ⟨add⟩

/-- Subtraction: `p - q = p + (-q)`. -/
@[inline] def sub (p q : Q') : Q' := p + (-q)

instance : Sub Q' := ⟨sub⟩

/-- Multiplication: `(a/b) * (c/d) = (ac)/(bd)`. -/
@[inline] def mul (p q : Q') : Q' :=
  ⟨p.num * q.num, p.den * q.den - 1⟩

instance : Mul Q' := ⟨mul⟩

/-! ### Semantic equivalence and ordering

Structural equality on `Q'` is decidable (auto-derived) but
distinguishes representations of the same rational
(`mk 1 2 ≠ mk 2 4` structurally).  We additionally provide
*semantic* equivalence and order, via cross-product comparison on
`Int`.  Both are decidable because `Int` has decidable equality
and order. -/

/-- Semantic equivalence: `a/b ≃ c/d` iff `a*d = c*b`. -/
@[inline] def eqv (p q : Q') : Prop :=
  p.num * (q.den : Int) = q.num * (p.den : Int)

instance : DecidableRel Q'.eqv := fun p q =>
  decEq (p.num * (q.den : Int)) (q.num * (p.den : Int))

/-- Semantic ≤: `a/b ≤ c/d` iff `a*d ≤ c*b`  (assuming `b, d > 0`,
which is structural here). -/
@[inline] def le (p q : Q') : Prop :=
  p.num * (q.den : Int) ≤ q.num * (p.den : Int)

instance : LE Q' := ⟨le⟩

instance : DecidableRel ((· ≤ ·) : Q' → Q' → Prop) := fun p q =>
  inferInstanceAs (Decidable (p.num * (q.den : Int) ≤ q.num * (p.den : Int)))

/-- Semantic <. -/
@[inline] def lt (p q : Q') : Prop :=
  p.num * (q.den : Int) < q.num * (p.den : Int)

instance : LT Q' := ⟨lt⟩

instance : DecidableRel ((· < ·) : Q' → Q' → Prop) := fun p q =>
  inferInstanceAs (Decidable (p.num * (q.den : Int) < q.num * (p.den : Int)))

/-! ### Min and Max -/

/-- Semantic min via the decidable ≤. -/
@[inline] def min' (p q : Q') : Q' := if p ≤ q then p else q

/-- Semantic max via the decidable ≤. -/
@[inline] def max' (p q : Q') : Q' := if p ≤ q then q else p

instance : Min Q' := ⟨min'⟩
instance : Max Q' := ⟨max'⟩

/-! ## Spec-quoted SU(2) Casimir constants (P1.1 mirror, ℚ form)

The Casimirs that `lean/YMGap/RepTheory/SU2.lean` exposes as
`4 · C_2(j) ∈ ℕ` can now be exposed at their natural rational form
`C_2(j) ∈ Q'`.  These are the constants Phase-3 milestones consume
via `Q'`.  All are `rfl`-equal in their canonical `Q'.mk`
representation. -/

/-- `C_2(0) = 0`. -/
def C2_zero : Q' := 0

/-- `C_2(1/2) = 3/4` — the smallest nonzero Casimir, the κ_{SU(2)}
input to the buffer-overlap measure of `outline.md` §18.1. -/
def C2_oneHalf : Q' := mkPos 3 4 (by decide)

/-- `C_2(1) = 2`. -/
def C2_one : Q' := ofNat 2

/-- `C_2(3/2) = 15/4`. -/
def C2_threeHalves : Q' := mkPos 15 4 (by decide)

/-- `C_2(2) = 6`. -/
def C2_two : Q' := ofNat 6

/-! ## Spec values, verified by computation -/

theorem C2_oneHalf_num : C2_oneHalf.num = 3 := rfl
theorem C2_oneHalf_den : C2_oneHalf.den = 4 := rfl
theorem C2_one_num : C2_one.num = 2 := rfl
theorem C2_one_den : C2_one.den = 1 := rfl
theorem C2_threeHalves_num : C2_threeHalves.num = 15 := rfl
theorem C2_threeHalves_den : C2_threeHalves.den = 4 := rfl

/-- `C_2(1/2) = 3/4` as a semantic equivalence to the canonical
representation `mkPos 3 4 _`.  Holds by `rfl` since both sides have
identical numerator and denominator. -/
theorem C2_oneHalf_eqv : C2_oneHalf.eqv (mkPos 3 4 (by decide)) := by
  unfold Q'.eqv
  rfl

/-- `C_2(1/2) ≤ C_2(1)` — the spectrum is monotone. -/
theorem C2_oneHalf_le_one : C2_oneHalf ≤ C2_one := by
  show (3 : Int) * (1 : Int) ≤ (2 : Int) * (4 : Int)
  decide

/-- `0 < C_2(1/2)` — the smallest *nonzero* Casimir is positive. -/
theorem C2_oneHalf_pos : (0 : Q') < C2_oneHalf := by
  show (0 : Int) * (4 : Int) < (3 : Int) * (1 : Int)
  decide

end Q'

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.den_pos
#print axioms YMGap.Constructive.Q'.mkPos_den
#print axioms YMGap.Constructive.Q'.mkPos_num
#print axioms YMGap.Constructive.Q'.C2_oneHalf_num
#print axioms YMGap.Constructive.Q'.C2_oneHalf_den
#print axioms YMGap.Constructive.Q'.C2_one_num
#print axioms YMGap.Constructive.Q'.C2_threeHalves_num
#print axioms YMGap.Constructive.Q'.C2_oneHalf_eqv
#print axioms YMGap.Constructive.Q'.C2_oneHalf_le_one
#print axioms YMGap.Constructive.Q'.C2_oneHalf_pos
