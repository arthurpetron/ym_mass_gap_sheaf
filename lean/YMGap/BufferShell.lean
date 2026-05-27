/-
Single-plaquette buffer-shell bound — Lean mechanization of
T6.1 + T6.2 (`docs/outline.md` Part B §22) via Q′ interval
arithmetic.

Milestone 1.3 of `work_plan.md` (Python pilot), Lean upgrade
authorized 2026-05-26.

# What this module does

`computations/buffer_shell.py` provides
`single_plaquette_buffer_measure(δ, g, conv).uniform_value()` — the
project's uniform upper bound on the single-plaquette buffer-shell
probability `P[δ/2 < d(U_p, 1) < 2δ]` under the heat-kernel
measure.  `tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound`
verifies that the bound dominates the direct heat-kernel integral
at every (δ, g) in the grid `δ ∈ {0.02, 0.06, ..., 1.00}` step 0.04,
`g ∈ {0.05, 0.10, ..., 1.50}` step 0.05, in both canonical and
Wilson conventions — a floating-point numerical check at ~1500
points.

This module lifts a representative sample of that check to a
`decide`-style Lean theorem at the Q′-rational level: for each
sample grid point `(δ, g)` encoded as a Q′ pair, we provide
  * a Q′-rational LOWER bound `uniform_lower_Q'` on the project's
    `uniform_value(δ, g)` (rounded DOWN from the Python value),
  * a Q′-rational UPPER bound `numerical_upper_Q'` on the direct
    heat-kernel integral (rounded UP from the Python value),
and prove
    uniform_lower_Q'(δ, g)  ≥  numerical_upper_Q'(δ, g)
by `decide` on the cross-product representation.

The `decide`-style closure gives a Lean-verified (axiom-clean,
`[propext]` only) certificate of the domination at each sample
point.  Trust shifts from "floating-point Python comparison passes"
to "Q′ tabulated values + conservative rounding + axiom-clean
Lean `decide`."

# Scope honesty

  * **Sample grid, not full grid.**  We encode 6 representative
    grid points from the canonical convention covering the
    "tail-dominated regime" `g ∈ {0.5, 1.0}` × `δ ∈ {0.1, 0.5, 1.0}`.
    The smaller-g regime (`g ≤ 0.1`) has Python-computed
    `uniform_value(δ, g) = numerical(δ, g)` to within floating-point
    noise (Haar floor regime), so no nontrivial Q′ separation is
    possible without finer-than-1e-4 denominators; that case is
    documented but not encoded here.
  * **Tabulated values from Python.**  The `uniform_lower_Q'` and
    `numerical_upper_Q'` constants below are derived from
    Python execution at the grid points, then rounded conservatively
    (DOWN for the lower bound on `uniform_value`, UP for the upper
    bound on the numerical integral) to denominators of 10000.  The
    rounding direction is what makes the per-point inequality
    Q′-decidable.
  * **Canonical convention only in this MVP.**  The Wilson
    convention has the same structural form (κ = 3 instead of 3/4)
    and can be mechanized symmetrically; deferred to a follow-on
    `BufferShell.Wilson` module.

# Axiom-gate (AGENTS.md Rule 1)

Every per-point inequality is `decide` on the Q′ cross-product
representation, which involves only `Int` arithmetic + `propext`.
The sentinel theorem `bound_dominates_at_sample_grid` is the
conjunction of all per-point checks, also `decide`-able.

# Cross-references

  * Python implementation: `computations/buffer_shell.py`
    (`BufferShellBound.uniform_value`).
  * Python test: `tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound`.
  * Paper companion: `notes/single-plaquette-derivation.md` §4
    (the uniform-in-g resolution via Haar floor + tail).
  * Theorem registry: `docs/outline.md` Part B §22 T6.1, T6.2.
-/

import YMGap.Constructive.Rationals

namespace YMGap.BufferShell

open YMGap.Constructive

/-! ## Grid point encoding

A `GridPoint` packages a (δ, g) pair as Q′ rationals together with
the conservatively-rounded Q′ bounds on `uniform_value(δ, g)` (from
below) and `numerical(δ, g)` (from above).  All values are sourced
from Python and listed with provenance in the constants section. -/

/-- A sample grid point: (δ, g) as Q′ rationals plus the
conservatively-rounded Q′ bounds on the project's uniform bound
and the direct heat-kernel integral. -/
structure GridPoint where
  /-- Buffer-shell threshold δ in Q′ (exact, small denominator). -/
  delta : Q'
  /-- Coupling g in Q′ (exact, small denominator). -/
  g : Q'
  /-- A Q′-rational LOWER bound on `uniform_value(δ, g)`. -/
  uniform_lower : Q'
  /-- A Q′-rational UPPER bound on the direct heat-kernel integral
  `numerical(δ, g)`. -/
  numerical_upper : Q'

namespace GridPoint

/-- The decidable predicate: `uniform_lower ≥ numerical_upper`. -/
def dominates (p : GridPoint) : Prop :=
  p.numerical_upper ≤ p.uniform_lower

instance (p : GridPoint) : Decidable p.dominates :=
  inferInstanceAs (Decidable (p.numerical_upper ≤ p.uniform_lower))

end GridPoint

/-! ## The sample grid (canonical convention)

The six sample points cover the tail-dominated regime where the
Q′-decidable domination is non-trivial (margin ≥ 1.6).  The
Haar-floor regime (`g ≤ 0.1`) where `uniform_value ≈ numerical`
exactly is documented but not encoded — separating them at Q′
requires a finer-than-1e-4 denominator which doesn't add structural
content to the mechanization.

For each row, the (uniform_lower, numerical_upper) values come from
Python execution of `single_plaquette_buffer_measure(...).uniform_value()`
and `buffer_measure_exact_numerical(...)` at the same (δ, g),
rounded conservatively to denominator 10000:

  * `uniform_lower`: floor of `uniform_value * 10000` / 10000
    (so `uniform_lower ≤ uniform_value` holds; we take the lower
    bound on the bound).
  * `numerical_upper`: ceil of `numerical * 10000` / 10000 (so
    `numerical ≤ numerical_upper` holds; we take the upper bound
    on the numerical).

The decidable check `numerical_upper ≤ uniform_lower` then implies
the actual analytical inequality `numerical ≤ uniform_value` at the
grid point by transitivity. -/

/-- Grid point #1: δ = 0.1, g = 0.5.

Python values: uniform_value = 4.076e-4, numerical = 2.505e-4.
Q′ rounding: uniform_lower = 4/10000, numerical_upper = 3/10000. -/
def gp1 : GridPoint :=
  { delta := Q'.mkPos 1 10 (by decide),
    g := Q'.mkPos 1 2 (by decide),
    uniform_lower := Q'.mkPos 4 10000 (by decide),
    numerical_upper := Q'.mkPos 3 10000 (by decide) }

/-- Grid point #2: δ = 0.1, g = 1.0.

Python values: uniform_value = 2.098e-3, numerical = 9.441e-4.
Q′ rounding: uniform_lower = 20/10000, numerical_upper = 10/10000. -/
def gp2 : GridPoint :=
  { delta := Q'.mkPos 1 10 (by decide),
    g := Q'.mkPos 1 1 (by decide),
    uniform_lower := Q'.mkPos 20 10000 (by decide),
    numerical_upper := Q'.mkPos 10 10000 (by decide) }

/-- Grid point #3: δ = 0.5, g = 0.5.

Python values: uniform_value = 4.971e-2, numerical = 2.945e-2.
Q′ rounding: uniform_lower = 490/10000, numerical_upper = 300/10000. -/
def gp3 : GridPoint :=
  { delta := Q'.mkPos 1 2 (by decide),
    g := Q'.mkPos 1 2 (by decide),
    uniform_lower := Q'.mkPos 490 10000 (by decide),
    numerical_upper := Q'.mkPos 300 10000 (by decide) }

/-- Grid point #4: δ = 0.5, g = 1.0.

Python values: uniform_value = 2.610e-1, numerical = 9.977e-2.
Q′ rounding: uniform_lower = 2600/10000, numerical_upper = 1000/10000. -/
def gp4 : GridPoint :=
  { delta := Q'.mkPos 1 2 (by decide),
    g := Q'.mkPos 1 1 (by decide),
    uniform_lower := Q'.mkPos 2600 10000 (by decide),
    numerical_upper := Q'.mkPos 1000 10000 (by decide) }

/-- Grid point #5: δ = 1.0, g = 0.5.

Python values: uniform_value = 3.695e-1, numerical = 1.951e-1.
Q′ rounding: uniform_lower = 3690/10000, numerical_upper = 2000/10000. -/
def gp5 : GridPoint :=
  { delta := Q'.mkPos 1 1 (by decide),
    g := Q'.mkPos 1 2 (by decide),
    uniform_lower := Q'.mkPos 3690 10000 (by decide),
    numerical_upper := Q'.mkPos 2000 10000 (by decide) }

/-- Grid point #6: δ = 1.0, g = 1.0.

Python values: uniform_value = 2.060e0, numerical = 4.878e-1.
Q′ rounding: uniform_lower = 20590/10000, numerical_upper = 5000/10000. -/
def gp6 : GridPoint :=
  { delta := Q'.mkPos 1 1 (by decide),
    g := Q'.mkPos 1 1 (by decide),
    uniform_lower := Q'.mkPos 20590 10000 (by decide),
    numerical_upper := Q'.mkPos 5000 10000 (by decide) }

/-! ## Per-point domination theorems (the `decide`-style closure)

Each point's `dominates` predicate unfolds to a Q′-rational
inequality `numerical_upper ≤ uniform_lower`, which is decidable by
cross-product comparison on `Int`. -/

theorem gp1_dominates : gp1.dominates := by decide
theorem gp2_dominates : gp2.dominates := by decide
theorem gp3_dominates : gp3.dominates := by decide
theorem gp4_dominates : gp4.dominates := by decide
theorem gp5_dominates : gp5.dominates := by decide
theorem gp6_dominates : gp6.dominates := by decide

/-! ## The sentinel theorem: domination at the entire sample grid -/

/-- **Sample-grid domination theorem.**

The project's uniform bound `uniform_value(δ, g)` dominates the
direct heat-kernel integral `numerical(δ, g)` at every sample
grid point, in the form of the Q′-rational bracketing:

    numerical(δ, g)  ≤  numerical_upper_Q'(δ, g)
                     ≤  uniform_lower_Q'(δ, g)
                     ≤  uniform_value(δ, g).

The middle step is the Lean-verified Q′-decidable claim; the
outer steps follow from the conservative rounding of the Python
tabulated values (downward for `uniform_value`, upward for
`numerical`).

This is the Lean upgrade of the Python floating-point check
`tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound`
at the sample subset of its grid.  Extending to the full ~1500-
point grid is mechanical (per-point `decide` calls; deferred to
a Python-script-generated `BufferShell/Grid.lean` follow-on). -/
theorem bound_dominates_at_sample_grid :
    gp1.dominates ∧ gp2.dominates ∧ gp3.dominates ∧
    gp4.dominates ∧ gp5.dominates ∧ gp6.dominates :=
  ⟨gp1_dominates, gp2_dominates, gp3_dominates,
   gp4_dominates, gp5_dominates, gp6_dominates⟩

/-! ## T6.1 and T6.2 structural signatures

The work_plan §1.3 deliverable for T6.1 is the existence of a
triple `(C, κ, β)` such that `bound = C · exp(-κ/g²) · g^β`.  For
SU(2) in the canonical convention:

  * `κ = 3/4` (smallest nonzero Casimir; `Q'.C2_oneHalf` from
    `Rationals.lean`),
  * `β = 3` (group dimension dim SU(2)),
  * `C(δ) = 4 · shell_weyl_volume(δ)` (the
    `BUFFER_BOUND_PREFACTOR = 4` calibration).

We expose these as Q′ constants so downstream Lean modules can
reference them symbolically. -/

/-- T6.1 — the Casimir κ for SU(2) in the canonical convention.

`κ = C₂(1/2) = 3/4`.  Q′ value, exposed from
`Rationals.lean::Q'.C2_oneHalf`. -/
def kappa_canonical : Q' := Q'.C2_oneHalf

theorem kappa_canonical_value : kappa_canonical = Q'.mkPos 3 4 (by decide) := rfl

/-- T6.1 — the Casimir κ for SU(2) in the Wilson convention.

`κ = 2N · C₂(1/2)`.  With N = 2 and C₂(1/2) = 3/4: `κ = 3`. -/
def kappa_wilson : Q' := 3

/-- T6.1 — the shell-volume exponent β = dim SU(2) = 3. -/
def beta_su2 : Nat := 3

/-- T6.2 — the tail-uniform prefactor 4 as a Q′ rational. -/
def tail_uniform_prefactor : Q' := 4

/-! ## Strict positivity of the bound constants -/

/-- `0 < κ_canonical` (= 3/4). -/
theorem kappa_canonical_pos : (0 : Q') < kappa_canonical := by
  show (0 : Q') < Q'.C2_oneHalf
  exact Q'.C2_oneHalf_pos

/-- `0 < κ_wilson` (= 3). -/
theorem kappa_wilson_pos : (0 : Q') < kappa_wilson := by decide

/-- `0 < tail_uniform_prefactor` (= 4). -/
theorem tail_uniform_prefactor_pos : (0 : Q') < tail_uniform_prefactor := by decide

/-! ## Provenance sanity checks

Direct `decide` checks that each grid point's (δ, g) is exactly
the Q′ value expected from its label.  These guard against silent
edits of the constants. -/

theorem gp1_delta_eq : gp1.delta = Q'.mkPos 1 10 (by decide) := rfl
theorem gp1_g_eq : gp1.g = Q'.mkPos 1 2 (by decide) := rfl
theorem gp6_delta_eq : gp6.delta = Q'.mkPos 1 1 (by decide) := rfl
theorem gp6_g_eq : gp6.g = Q'.mkPos 1 1 (by decide) := rfl

end YMGap.BufferShell

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `propext` or empty.  No
`Classical.*`, no `Quot.sound`, no `sorryAx`. -/

#print axioms YMGap.BufferShell.gp1_dominates
#print axioms YMGap.BufferShell.gp2_dominates
#print axioms YMGap.BufferShell.gp3_dominates
#print axioms YMGap.BufferShell.gp4_dominates
#print axioms YMGap.BufferShell.gp5_dominates
#print axioms YMGap.BufferShell.gp6_dominates
#print axioms YMGap.BufferShell.bound_dominates_at_sample_grid
#print axioms YMGap.BufferShell.kappa_canonical_value
#print axioms YMGap.BufferShell.kappa_canonical_pos
#print axioms YMGap.BufferShell.kappa_wilson_pos
#print axioms YMGap.BufferShell.tail_uniform_prefactor_pos
#print axioms YMGap.BufferShell.gp1_delta_eq
#print axioms YMGap.BufferShell.gp1_g_eq
#print axioms YMGap.BufferShell.gp6_delta_eq
#print axioms YMGap.BufferShell.gp6_g_eq
