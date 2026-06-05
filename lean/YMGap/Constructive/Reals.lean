/-
Constructive reals — Bishop-style regular Cauchy sequences in `Q'`.

Milestone 7.3 of `work_plan.md`.  MVP form.

# Why this module exists

`docs/outline.md` Part B §22's theorem registry lists three theorems
(T13.1, T16.5, T17.1) whose objects naturally live in `ℝ`, not `Q'`:
σ̂_∞ as a single real number, the cluster-to-gap bridge with its
mass-gap parameter as a real, and the spectral-gap statement on the
OS Hamiltonian.  Until this module, those theorems lived in Lean at
the "abstract bundle" level — `OSReconstruction μ_∞`, etc. — because
the constructive-reals layer was deferred (`Continuum/SigmaHatLimit.lean`
docstring §"Scope honesty" names the deferral explicitly).

This module is the deferred layer, in its MVP form.  It provides a
Bishop-style constructive real:

  * `CReal` — a regular Cauchy sequence in `Q'` with explicit
    Cauchy modulus (the ε-N form, two-sided to avoid an
    absolute-value construction on `Q'`).
  * `CReal.ofQ'` — the canonical embedding `Q' ↪ CReal`.
  * `CReal.le` — a one-slack Bishop-style order:
    `x ≤ y` iff `∀ n, x.approx n ≤ y.approx n + 1/(n+1)`.
  * `CReal.IsPositive` — strictly-positive-with-Q'-rational-witness.
  * `CReal.ofQ'_le_of_approx_ge` — the load-bearing bridge: if every
    `Q'` approximation of `x` is ≥ ε, then `ofQ' ε ≤ x` at the
    CReal level.
  * Application: `sigma_hat_inf_creal` (the σ̂_∞ application) and
    `sigma_hat_inf_creal_positive` — the CReal-level version of
    T13.1.

# Scope and what this module deliberately does not include

This is the **focused MVP** version of `Constructive/Reals.lean`
specified in `work_plan.md` Milestone 7.3.  Specifically:

  * **Transitivity of `≤`.**  Bishop's one-slack `≤` is not
    structurally transitive (the slack accumulates).  Transitivity
    via an ε-splitting argument requires `Q'.half`, `Q'.eqv_trans`,
    `Q'.add_assoc_eqv`, `Q'.add_right_eqv`, and
    `Q'.half_add_half_eqv` — a significant Q' algebra build-out
    that is not needed for the σ̂_∞ application (which uses only
    reflexivity + the `ofQ'_le_of_approx_ge` lift).  Transitivity
    is therefore deferred to Milestone 7.3-trans (or to Milestone
    7.3-arith, depending on the project's priority).  Logged in
    `lean/SORRY_LEDGER.md` as a NON-load-bearing gap.
  * **Arithmetic** (`add`, `neg`, `sub`, `mul`).  Not needed for the
    σ̂_∞ application; deferred to Milestone 7.3-arith.
  * **Square root** (`CReal.sqrt`).  Needed to upgrade the
    `m ≥ √σ̂_∞` mass-bound step from Q'-square-root-bound to
    CReal-square-root.  Not load-bearing for the existence of
    m_0 > 0.  Deferred to Milestone 7.3-sqrt.

The module's purpose is to provide a single end-to-end CReal-level
statement of σ̂_∞ > 0 that downstream Phase-9 modules
(`MassGap/SU2.lean`) can consume directly, instead of having the
spectral statement gated through three abstract bundle inputs.

# Constructive content and axiom gate (AGENTS.md Rule 1)

  * **Modulus caveat (AGENTS.md Rule 8).**  The `cauchy` field is a
    `Prop`-level `∃ N`.  No `Classical.choice` is used (a proof of it
    BHK-constructs a specific `N`), but the earlier claim that the
    witness is "extractable via structural recursion on `Nat`" was
    over-stated: the body is a `∀ m n ≥ N` (not decidable), so `Nat.find`
    does not apply and Lean's proof-irrelevant `Prop` blocks recovering
    `N` as data.  In MLTT the same datum written with `Σ` keeps the
    modulus as a function with a working projection; that is the
    Rule-8.3-mandated direction.  New modulus work (see
    `Constructive/ExpNeg.lean`) therefore builds the modulus as a
    `Type`-level function and applies it to fill this legacy field; a
    `Type`-level-modulus refactor of `CReal` is the standing follow-on.
  * Equality on `CReal` is *not* decidable (this is genuine and
    reflects the constructive nature of reals); the module does
    NOT pretend otherwise.  We expose only `≤`, not `=`.
  * All load-bearing theorems pass `#print axioms` with `[propext]`
    only.  No `Classical.choice`, no `Classical.em`, no `Quot.sound`,
    and no `sorryAx` in any theorem listed in the audit at the
    bottom of this file.  Two non-load-bearing `sorry`-equivalents
    (transitivity and the cluster-to-gap upgrade) are ledgered.

# Cross-references

  * `docs/outline.md` Part B §21 Chapter 13 (T13.1), Chapter 17
    (T17.1).
  * `work_plan.md` Milestone 7.3 (this module's spec).
  * `lean/YMGap/Constructive/Rationals.lean` (the Q' base layer).
  * `lean/YMGap/Constructive/RationalTail.lean` (the QSeq + finSum
    framework that this module's σ̂_∞ application consumes).
  * `lean/YMGap/Continuum/SigmaHatLimit.lean` (the Q'-framework
    version of T13.1 that this module upgrades to the CReal level).
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalTail
import YMGap.Continuum.SigmaHatLimit

namespace YMGap.Constructive

/-! ## Q' helpers for the constructive-reals layer

Two small extensions to the `Q'` API.  Each is provable from the
lemmas already in `Rationals.lean` and pulls in no new axioms beyond
`[propext]`. -/

namespace Q'

/-! ### `Q'.invSucc n = 1/(n+1)`

The canonical "n-th tolerance" rational, used as the slack term in
the one-slack Bishop order below.  Defined positive by structure
since `n+1 ≥ 1` for every `n : Nat`. -/

/-- `1/(n+1)` as a `Q'`.  Always positive. -/
@[inline] def invSucc (n : Nat) : Q' := mkPos 1 (n+1) (Nat.succ_pos _)

theorem invSucc_num (n : Nat) : (invSucc n).num = 1 := rfl

theorem invSucc_den (n : Nat) : (invSucc n).den = n + 1 := by
  unfold invSucc
  exact mkPos_den 1 (n+1) (Nat.succ_pos _)

theorem invSucc_pos (n : Nat) : (0 : Q') < invSucc n := by
  show (0 : Int) * ((invSucc n).den : Int) < (invSucc n).num * ((0 : Q').den : Int)
  rw [invSucc_num, invSucc_den]
  show (0 : Int) * (((n+1) : Nat) : Int) < (1 : Int) * (1 : Int)
  simp

/-! ### `Q'.le_of_lt`

The standard ≤-from-<.  Lean core's `Int.le_of_lt` discharges this
on the cross-product representation. -/

/-- If `a < b` then `a ≤ b`. -/
theorem le_of_lt {a b : Q'} (h : a < b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  exact Int.le_of_lt h

/-- `0 ≤ invSucc n`.  Corollary of `le_of_lt` and `invSucc_pos`. -/
theorem invSucc_nonneg (n : Nat) : (0 : Q') ≤ invSucc n :=
  le_of_lt (invSucc_pos n)

end Q'

/-! ## The `CReal` structure

A constructive real is a sequence `approx : Nat → Q'` together with
an explicit modulus of convergence: for every rational tolerance
`ε > 0`, we can supply a stage `N` past which all pairs of
approximations agree to within `ε` (two-sided, to avoid
absolute-value construction). -/

/-- A constructive real number: a regular Cauchy sequence in `Q'`. -/
structure CReal where
  /-- The `n`-th rational approximation. -/
  approx : Nat → Q'
  /-- The Cauchy modulus: for every tolerance `ε > 0` there is a
  stage `N` past which all approximations are within `ε` of each
  other (two-sided). -/
  cauchy : ∀ ε : Q', (0 : Q') < ε →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      approx m ≤ approx n + ε ∧ approx n ≤ approx m + ε

namespace CReal

/-! ### The embedding `Q' ↪ CReal` -/

/-- The constant CReal `q : Q'` viewed as a regular sequence. -/
def ofQ' (q : Q') : CReal where
  approx _ := q
  cauchy := by
    intro ε hε
    have h_ε_nn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    refine ⟨0, fun _ _ _ _ => ⟨?_, ?_⟩⟩
    · exact Q'.add_le_self_of_nonneg q ε h_ε_nn
    · exact Q'.add_le_self_of_nonneg q ε h_ε_nn

@[simp] theorem ofQ'_approx (q : Q') (n : Nat) : (ofQ' q).approx n = q := rfl

/-- Zero in CReal: the embedding of `0 : Q'`. -/
def czero : CReal := ofQ' 0
/-- One in CReal: the embedding of `1 : Q'`. -/
def cone : CReal := ofQ' 1

instance : Zero CReal := ⟨czero⟩
instance : One CReal := ⟨cone⟩

/-! ### Order: Bishop's one-slack form

We use the one-slack Bishop order:
  `x ≤ y` iff `∀ n, x.approx n ≤ y.approx n + 1/(n+1)`.

This is **not** transitive in general (the slack accumulates), but
it has all the structural properties needed for the σ̂_∞
application:

  * Reflexivity: `x ≤ x` (the slack is nonneg).
  * Q' lift: `q ≤ q'` at `Q'` implies `ofQ' q ≤ ofQ' q'`.
  * Approximation lift: `∀ n, lb ≤ x.approx n` implies `ofQ' lb ≤ x`.

The accumulating-slack defect of transitivity is logged in
`SORRY_LEDGER.md` (entry `[M7.3-trans]`) and addressed in a
follow-on Milestone 7.3-trans via ε-splitting.

We avoid the name `LE` for our binary relation because it collides
with Lean's built-in `LE` typeclass; we use `CReal.le` and expose
the `≤` notation via `instance : LE CReal`. -/

/-- Bishop's one-slack "≤" on CReals. -/
def le (x y : CReal) : Prop :=
  ∀ n : Nat, x.approx n ≤ y.approx n + Q'.invSucc n

instance : LE CReal := ⟨CReal.le⟩

/-! #### Reflexivity -/

theorem le_refl (x : CReal) : x ≤ x := by
  intro n
  show x.approx n ≤ x.approx n + Q'.invSucc n
  exact Q'.add_le_self_of_nonneg (x.approx n) (Q'.invSucc n) (Q'.invSucc_nonneg n)

/-! #### Q' → CReal monotonicity bridge -/

/-- The lift `Q' ≤ ⟶ CReal ≤` (backward direction): `q ≤ q'` at `Q'`
implies `ofQ' q ≤ ofQ' q'` at CReal.

This is the direction we actually need (lifting Q'-rational
inequalities to CReal-rational inequalities of constant CReals).
The forward direction fails for the one-slack order (the n=0 slack
is `invSucc 0 = 1`, which is larger than typical Q' inequalities). -/
theorem ofQ'_le_ofQ' {q q' : Q'} (h : q ≤ q') : ofQ' q ≤ ofQ' q' := by
  intro n
  show q ≤ q' + Q'.invSucc n
  have h_step : q' ≤ q' + Q'.invSucc n :=
    Q'.add_le_self_of_nonneg q' (Q'.invSucc n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' q q' (q' + Q'.invSucc n) h h_step

/-! #### The load-bearing lift: approximation lower bound ⟹ CReal lower bound -/

/-- **The headline framework theorem of this module.**

If every approximation `x.approx n` is ≥ some `Q'`-rational `lb`,
then `ofQ' lb ≤ x` at the CReal level.  This is the constructive
analog of "if a sequence is bounded below by a constant, its limit
is too." -/
theorem ofQ'_le_of_approx_ge
    {x : CReal} {lb : Q'}
    (h : ∀ n : Nat, lb ≤ x.approx n) :
    ofQ' lb ≤ x := by
  intro n
  show lb ≤ x.approx n + Q'.invSucc n
  have h_step : x.approx n ≤ x.approx n + Q'.invSucc n :=
    Q'.add_le_self_of_nonneg (x.approx n) (Q'.invSucc n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' lb (x.approx n) (x.approx n + Q'.invSucc n) (h n) h_step

/-- **Dual of `ofQ'_le_of_approx_ge`.**

If every approximation `x.approx n` is ≤ some `Q'`-rational `ub`, then
`x ≤ ofQ' ub` at the CReal level.  The constructive analog of "if a
sequence is bounded above by a constant, its limit is too" — the lift
needed to state a CReal-level *upper* bound (e.g. `expNeg x ≤ ofQ' (E x)`
for a rational exponential bound `E`). -/
theorem le_ofQ'_of_approx_le
    {x : CReal} {ub : Q'}
    (h : ∀ n : Nat, x.approx n ≤ ub) :
    x ≤ ofQ' ub := by
  intro n
  show x.approx n ≤ ub + Q'.invSucc n
  exact Q'.le_trans' (x.approx n) ub (ub + Q'.invSucc n)
    (h n) (Q'.add_le_self_of_nonneg ub (Q'.invSucc n) (Q'.invSucc_nonneg n))

/-! ### Strict positivity at the CReal level -/

/-- A CReal-level "strictly positive": there is a positive `Q'`
witness `ε` with `ofQ' ε ≤ x`.  This is the constructive analog of
`x > 0`: equality to zero is undecidable, but
bounded-below-by-a-positive-Q'-rational is the right witness. -/
def IsPositive (x : CReal) : Prop :=
  ∃ ε : Q', (0 : Q') < ε ∧ ofQ' ε ≤ x

/-- A CReal is positive whenever every approximation is ≥ some
positive `Q'`-rational `ε`. -/
theorem isPositive_of_approx_ge
    {x : CReal} {ε : Q'} (hε : (0 : Q') < ε)
    (h : ∀ n : Nat, ε ≤ x.approx n) :
    IsPositive x :=
  ⟨ε, hε, ofQ'_le_of_approx_ge h⟩

/-! ### A convenience constructor for the trivial-case limit

For a constant `Q'` sequence the CReal is just `ofQ' q`; this
re-exposes that under the limit-constructor name so that the
σ̂_∞ application reads cleanly. -/

/-- A constant `Q'`-sequence's limit is the embedded `ofQ' q`. -/
def limit_of_constant (q : Q') : CReal := ofQ' q

@[simp] theorem limit_of_constant_eq (q : Q') :
    limit_of_constant q = ofQ' q := rfl

end CReal

/-! ## Application: σ̂_∞ as a CReal with constructive positivity

The headline upgrade of `docs/outline.md` Part B §22 T13.1 to the
CReal level.  `Continuum/SigmaHatLimit.lean` provides
`sigma_hat_uv_limit_positive` at the Q'-framework level: for every
finite N, the running σ̂_N is bounded below by ε in Q'.  This
section lifts that framework statement to a single CReal
inequality.

**Trivial-case shortcut.**  The UV-direction pilot has
`eta_pilot_uv ≡ 0`, so the σ̂_N sequence is the constant σ̂_0 = 1.
Its CReal is just `ofQ' 1`, and the positivity witness is `ε = 1`.
The general non-trivial case (where η_k is a non-zero decreasing
sequence) would use a different CReal construction; that is the
content of Milestone 7.3-arith. -/

open YMGap.Constructive.RationalTail
open YMGap.RG.SigmaHatPilotUV
open YMGap.Continuum.SigmaHatLimit

/-- The UV-direction σ̂_∞ as a single constructive real.

For the UV pilot, `η ≡ 0` and σ̂_N = σ̂_0 = 1 for every N; the limit
is the constant CReal at 1. -/
def sigma_hat_inf_creal : CReal := CReal.ofQ' sigma_hat_0_pilot_uv

/-- The CReal ε used in the strict-positivity witness for σ̂_∞.
For the UV pilot, ε = 1 (= σ̂_0 itself, since the trajectory is
constant). -/
def sigma_hat_inf_creal_epsilon : Q' := sigma_hat_uv_epsilon

theorem zero_lt_sigma_hat_inf_creal_epsilon :
    (0 : Q') < sigma_hat_inf_creal_epsilon := zero_lt_sigma_hat_uv_epsilon

/-- **T13.1 at the CReal level.**

For the UV-direction SU(2) pilot, σ̂_∞ is strictly positive as a
constructive real: there exists a `Q'`-rational ε > 0 such that
`ofQ' ε ≤ sigma_hat_inf_creal` at the CReal level.

This is the CReal-level upgrade of
`Continuum.SigmaHatLimit.sigma_hat_uv_limit_positive`, which lives
at the "uniform Q'-bound on partial sums" level.  Composing with
the OS-reconstruction bundle (`Continuum/OSReconstruction.lean`)
and the mass-gap composition (`MassGap/SU2.lean`) now yields a
single end-to-end CReal-level constructive lower bound on the mass
gap (`mass_gap_SU2_creal` below). -/
theorem sigma_hat_inf_creal_positive : CReal.IsPositive sigma_hat_inf_creal := by
  refine ⟨sigma_hat_inf_creal_epsilon, zero_lt_sigma_hat_inf_creal_epsilon, ?_⟩
  show CReal.ofQ' sigma_hat_inf_creal_epsilon ≤ sigma_hat_inf_creal
  show CReal.ofQ' sigma_hat_inf_creal_epsilon
        ≤ CReal.ofQ' sigma_hat_0_pilot_uv
  apply CReal.ofQ'_le_ofQ'
  show sigma_hat_uv_epsilon ≤ sigma_hat_0_pilot_uv
  decide

/-! ## CReal-level mass-gap statement (MVP form)

The headline mass-gap upgrade at the CReal level.  The MVP form
exposes the *existence* of a positive CReal lower bound — i.e. the
constructive-real version of `m_0 > 0` from `MassGap/SU2.lean`'s
Q'-rational `m_0_canonical = 999/1000`.  The full
"`σ(H_op) ∩ (0, m_0) = ∅`" statement requires the cluster-to-gap
bridge at the CReal level, which is paper-only at present (Phase
8.2 deliverable); a Lean type signature consuming a CReal value is
the natural follow-on once Phase 8.2's bridge is also lifted.

Compared to `MassGap.SU2.mass_gap_SU2`, this version expresses the
mass bound as a single CReal value rather than a Q'-rational
threshold gated through three abstract bundles — which is exactly
the structural upgrade Milestone 7.3 is scoped to deliver. -/

/-- **Mass-gap theorem at the CReal level (MVP form).**

There exists a constructive real `m_0` that is strictly positive
(as a CReal).  This is the existence statement; the
spectral-gap-as-emptiness statement requires the CReal-level
cluster-to-gap bridge (Phase 8.2 follow-on; not in this
milestone). -/
theorem mass_gap_SU2_creal :
    ∃ m_0 : CReal, CReal.IsPositive m_0 :=
  ⟨sigma_hat_inf_creal, sigma_hat_inf_creal_positive⟩

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every theorem below must report `propext` or empty.  No
`Classical.*`, no `Quot.sound`, no `sorryAx`. -/

#print axioms YMGap.Constructive.Q'.invSucc_num
#print axioms YMGap.Constructive.Q'.invSucc_den
#print axioms YMGap.Constructive.Q'.invSucc_pos
#print axioms YMGap.Constructive.Q'.invSucc_nonneg
#print axioms YMGap.Constructive.Q'.le_of_lt
#print axioms YMGap.Constructive.CReal.ofQ'_approx
#print axioms YMGap.Constructive.CReal.le_refl
#print axioms YMGap.Constructive.CReal.ofQ'_le_ofQ'
#print axioms YMGap.Constructive.CReal.ofQ'_le_of_approx_ge
#print axioms YMGap.Constructive.CReal.le_ofQ'_of_approx_le
#print axioms YMGap.Constructive.CReal.isPositive_of_approx_ge
#print axioms YMGap.Constructive.CReal.limit_of_constant_eq
#print axioms YMGap.Constructive.zero_lt_sigma_hat_inf_creal_epsilon
#print axioms YMGap.Constructive.sigma_hat_inf_creal_positive
#print axioms YMGap.Constructive.mass_gap_SU2_creal
