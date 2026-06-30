/-
Track B / R2 — **THE SHARPEST STATEMENT of the single open continuum input.**

# Why this module exists (read first — and the HONEST scope)

The whole development bottoms out, on the continuum frontier, at exactly ONE open
analytic input.  The sibling unification module collapses the several
independent continuum walls into a single polymorphic interface
`UniformSpacingFloor` (a strictly-positive rational floor lying below a per-scale
gap quantity, uniformly in the scale).  That interface is the right *shape*, but
it is unit-agnostic and abstract.  This module states the SAME open input in its
most transparent, most directly-citable physical form and proves it discharges
the unified interface:

    `ContinuumGapTheorem  →  UniformSpacingFloor`.

So the program's entire remaining continuum obligation is the ONE statement
`ContinuumGapTheorem`: *the physical (dimensionful) mass gap*

    Δ(a)  =  m_lat(a) / a   =  (1 − sep(a)) / a

*stays bounded below by a single positive constant `c` as the lattice spacing
`a → 0`* — a spacing-uniform physical gap.

# The physics, and WHY this is exactly the open core

At FIXED lattice spacing the gap is PROVEN in this development (strong coupling):
the dimensionless lattice gap `m_lat = 1 − sep` is strictly positive with rate
`sep = ρ = 2 w³ < 1` for `0 < w ≤ 1/2` (the tree / single-line geometry;
see the proven fixed-spacing gap of this Continuum development, whose separator
is the proved real-correlator decay rate).  But the continuum limit forces the
coupling to run to the asymptotically-free fixed point `w → 1`, where the
LATTICE-unit gap `m_lat(a) → 0`.  Dimensional transmutation is the statement that
`m_lat(a)` vanishes *at exactly the rate of the spacing* `a`, so that the
PHYSICAL gap `Δ(a) = m_lat(a)/a` tends to a positive constant.  In the
asymptotic-freedom dictionary this is the logarithmic relation

    a · Λ_phys  =  exp( − 1 / (2 b₀ g²) )            (dimensional transmutation),

with `g²` the running coupling, `b₀ > 0` the one-loop β-function coefficient, and
`Λ_phys > 0` the dynamically-generated mass scale.  Reading `m_lat ≍ a·Λ_phys`
along the flow gives `Δ = m_lat/a → Λ_phys > 0`.

The HONEST obstruction (why this is still OPEN, not merely unproven plumbing): in
the constructive substrate the exponential / logarithm controlling the
transmutation limit — concretely `b^k · (1 − sep₀^{1/b^k}) → −ln sep₀` — is not
yet a constructive object on `CReal` (no constructive `b`-th root / `log` of the
required generality), AND, more deeply, the spacing-uniform lower bound
`c · a_k ≤ m_lat(a_k)` is genuine 4-D dynamical content that no fixed-spacing
strong-coupling theorem supplies.  Nothing here inhabits `ContinuumGapTheorem`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`ContinuumGapTheorem` and `AFDimensionalTransmutation` are `Type`-level records
whose load-bearing fields are `Pi`-types of the order relation (never `Prop`-∃
witnesses).  Each reduction is a structural repackaging plus one rational
division lemma (`Q'.le_divPos_of_mul_le`).  Every declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  This is a SHARPENING of the open statement, not a
closure: `ContinuumGapTheorem` is UNINHABITED for genuine 4-D Yang–Mills.
-/

import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.SharpContinuumObligation

open YMGap.Constructive
open YMGap.Continuum.UnifiedContinuumFloor

/-! ## 1. `ContinuumGapTheorem` — the single sharp open input

A spacing schedule `a_k → 0`, the fixed-spacing dimensionless lattice gap
`latMargin_k = m_lat(a_k) = 1 − sep_k` (PROVEN strictly positive at each fixed
spacing in this development), and the genuinely-open spacing-uniform datum: a
single positive physical floor `c` with `c · a_k ≤ latMargin_k` at EVERY scale —
equivalently the dimensionful gap `Δ(a_k) = latMargin_k / a_k ≥ c`, uniformly as
`a_k → 0`.  All fields are `Type`-level data (Rule 8); `rate_matched` is a `Pi`
of `≤`, never a `Prop`-∃. -/

/-- **THE SINGLE OPEN CONTINUUM INPUT, in its sharpest physical form.**

The spacing-uniform physical mass gap: a positive constant `c` lies below the
dimensionful gap `Δ(a_k) = (1 − sep_k)/a_k` at every scale of a spacing schedule
`a_k → 0`.  UNINHABITED for genuine 4-D Yang–Mills — it IS the open
dimensional-transmutation / continuum spectral-gap physics. -/
structure ContinuumGapTheorem : Type where
  /-- The lattice-spacing schedule `a_k` along the continuum limit. -/
  a : Nat → Q'
  /-- Each spacing is strictly positive. -/
  a_pos : ∀ k, (0 : Q') < a k
  /-- The dimensionless lattice gap `m_lat(a_k) = 1 − sep_k` at scale `k`.
  PROVEN strictly positive at each FIXED spacing (strong coupling) elsewhere in
  this development; carried here as the per-scale gap data. -/
  latMargin : Nat → Q'
  /-- The fixed-spacing lattice gap is strictly positive at every scale. -/
  latMargin_pos : ∀ k, (0 : Q') < latMargin k
  /-- The spacing-uniform PHYSICAL gap floor `c`. -/
  c : Q'
  /-- The floor is strictly positive. -/
  c_pos : (0 : Q') < c
  /-- **THE OPEN DIMENSIONAL-TRANSMUTATION CONTENT.**  At every scale,
  `c · a_k ≤ latMargin_k`, i.e. the dimensionful gap `Δ(a_k) = latMargin_k/a_k`
  stays `≥ c` as `a_k → 0`.  This is the genuine 4-D input. -/
  rate_matched : ∀ k, c * a k ≤ latMargin k

namespace ContinuumGapTheorem

/-- The **dimensionful physical gap** `Δ(a_k) = m_lat(a_k) / a_k = latMargin_k / a_k`
as a rational, via division by the positive spacing. -/
def physGap (G : ContinuumGapTheorem) (k : Nat) : Q' :=
  Q'.divPos (G.latMargin k) (G.a k) (G.a_pos k)

/-- The physical gap is bounded below by the uniform floor: `c ≤ Δ(a_k)`.
Immediate from `rate_matched` (`c · a_k ≤ latMargin_k`) and `le_divPos_of_mul_le`. -/
theorem c_le_physGap (G : ContinuumGapTheorem) (k : Nat) :
    G.c ≤ G.physGap k :=
  Q'.le_divPos_of_mul_le (G.latMargin k) (G.a k) (G.a_pos k) (G.rate_matched k)

/-- The physical gap is strictly positive at every scale. -/
theorem physGap_pos (G : ContinuumGapTheorem) (k : Nat) :
    (0 : Q') < G.physGap k :=
  Q'.divPos_pos (G.latMargin k) (G.a k) (G.a_pos k) (G.latMargin_pos k)

end ContinuumGapTheorem

/-! ## 2. THE REDUCTION — `ContinuumGapTheorem → UniformSpacingFloor`

Two faithful presentations of the discharge, both genuine inhabitants of the
canonical `UniformSpacingFloor` interface that the unification module proves
every continuum wall coincides with.  Producing either shows the program's whole
remaining continuum obligation reduces to the single citable `ContinuumGapTheorem`. -/

/-- **(headline) `ContinuumGapTheorem` ⇒ canonical floor, on the PHYSICAL gap.**
The uniform floor `c` lies below the dimensionful gap `Δ(a_k) = physGap_k` under
the plain rational order — a `QFloor` (hence a `UniformSpacingFloor`) on the
physical mass gap. -/
def toQFloor (G : ContinuumGapTheorem) : QFloor G.physGap where
  floor := G.c
  floor_pos := G.c_pos
  bound := G.c_le_physGap

/-- **(headline, restated) THE REMAINING OBLIGATION IS ONE STATEMENT.**  A
citable `ContinuumGapTheorem` discharges the unified continuum input
`UniformSpacingFloor` (here on the physical gap `Δ(a)`).  This is the single
analytic theorem the entire program still needs. -/
def continuumGapTheorem_discharges_uniformSpacingFloor
    (G : ContinuumGapTheorem) :
    UniformSpacingFloor (fun (q x : Q') => q ≤ x) G.physGap :=
  toQFloor G

/-- **`ContinuumGapTheorem` ⇒ canonical floor, in the SPACING-MATCHED shape.**
This is the exact order relation `q · a ≤ rhs` and `(spacing, gap)` carrier used
by the dimensional-transmutation extraction `ofDimensionalTransmutation` of the
unification module, so `ContinuumGapTheorem` discharges that wall in its own
units, with no division. -/
def toSpacingMatchedFloor (G : ContinuumGapTheorem) :
    UniformSpacingFloor (fun (q : Q') (p : Q' × Q') => q * p.1 ≤ p.2)
      (fun k => (G.a k, G.latMargin k)) where
  floor := G.c
  floor_pos := G.c_pos
  bound := G.rate_matched

/-! ## 3. THE ASYMPTOTIC-FREEDOM / DIMENSIONAL-TRANSMUTATION BRIDGE

The bridge that *explains* `ContinuumGapTheorem`: the dimensional-transmutation
law `a · Λ_phys = exp(−1/(2 b₀ g²))` says the lattice gap vanishes at the spacing
rate with positive physical proportionality `Λ_phys`.  Combined with the PROVEN
fixed-spacing positivity of `m_lat`, it yields `ContinuumGapTheorem` with
`c = Λ_phys`.

`AFDimensionalTransmutation` packages this as `Type`-level data:

  * the spacing schedule `a_k` with the PROVEN-shaped continuum modulus
    `a_to_zero` (this development proves the AF schedule tends to zero —
    `afSchedule_to_zero`);
  * the fixed-spacing lattice gap `latMargin_k = 1 − sep_k` with its PROVEN
    positivity;
  * the dynamically-generated scale `Λ_phys > 0` and the transmutation lower
    bound `Λ_phys · a_k ≤ latMargin_k` (`= m_lat(a_k) ≥ a_k · Λ_phys`).

The `transmutation` field is the constructive *shadow* of
`a·Λ_phys = exp(−1/(2 b₀ g²))`: the genuine exponential limit
`b^k(1 − sep₀^{1/b^k}) → −ln sep₀ = a₀·Λ_phys` is the open core (no constructive
`log`).  This interface is therefore **NOT inhabited** here. -/

/-- **THE AF / DIMENSIONAL-TRANSMUTATION BRIDGE (Type-level interface).**

A spacing schedule `a_k → 0`, a fixed-spacing-positive lattice gap
`latMargin_k`, and the transmutation relation `Λ_phys · a_k ≤ latMargin_k` with a
positive dynamically-generated scale `Λ_phys`.  Encodes the asymptotic-freedom
law `a·Λ_phys = exp(−1/(2 b₀ g²))` in its lower-bound (gap-floor) consequence.
UNINHABITED for genuine 4-D Yang–Mills (the exponential transmutation limit is
the open core). -/
structure AFDimensionalTransmutation : Type where
  /-- The lattice-spacing schedule `a_k`. -/
  a : Nat → Q'
  /-- Each spacing is strictly positive. -/
  a_pos : ∀ k, (0 : Q') < a k
  /-- **The continuum direction (PROVEN-shaped):** the spacing tends to zero with
  an explicit modulus — `∀ ε > 0, ∃ N, ∀ k ≥ N, a_k ≤ ε`.  This development proves
  exactly this for the AF schedule (`afSchedule_to_zero`). -/
  a_to_zero : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ k : Nat, N ≤ k → a k ≤ ε
  /-- The fixed-spacing dimensionless lattice gap `m_lat(a_k) = 1 − sep_k`. -/
  latMargin : Nat → Q'
  /-- The fixed-spacing lattice gap is strictly positive (PROVEN strong-coupling). -/
  latMargin_pos : ∀ k, (0 : Q') < latMargin k
  /-- The dynamically-generated physical scale `Λ_phys` (the
  `exp(−1/(2 b₀ g²))` constant). -/
  Lambda : Q'
  /-- `Λ_phys > 0`. -/
  Lambda_pos : (0 : Q') < Lambda
  /-- **THE TRANSMUTATION LAW (lower-bound form).**  `Λ_phys · a_k ≤ latMargin_k`:
  the lattice gap vanishes no faster than `a_k·Λ_phys`, so `Δ(a_k) ≥ Λ_phys`.
  The constructive shadow of `a·Λ_phys = exp(−1/(2 b₀ g²))`; the open core. -/
  transmutation : ∀ k, Lambda * a k ≤ latMargin k

/-- **THE BRIDGE THEOREM.**  The AF / dimensional-transmutation interface yields
`ContinuumGapTheorem` with physical floor `c = Λ_phys`: the fixed-spacing gap
positivity plus the transmutation lower bound are exactly the spacing-uniform
physical gap.  (Honest: this CONSTRUCTS the reduction; it does NOT inhabit
`AFDimensionalTransmutation`, which is open.) -/
def AFDimensionalTransmutation.toContinuumGapTheorem
    (D : AFDimensionalTransmutation) : ContinuumGapTheorem where
  a := D.a
  a_pos := D.a_pos
  latMargin := D.latMargin
  latMargin_pos := D.latMargin_pos
  c := D.Lambda
  c_pos := D.Lambda_pos
  rate_matched := D.transmutation

/-- **AF bridge ⇒ unified continuum input (end-to-end).**  Composing the bridge
with the headline reduction: the dimensional-transmutation interface discharges
the canonical `UniformSpacingFloor` on the physical gap. -/
def afTransmutation_discharges_uniformSpacingFloor
    (D : AFDimensionalTransmutation) :
    UniformSpacingFloor (fun (q x : Q') => q ≤ x)
      (D.toContinuumGapTheorem).physGap :=
  continuumGapTheorem_discharges_uniformSpacingFloor D.toContinuumGapTheorem

/-! ## 4. THE OBLIGATION LEDGER — exactly one open analytic theorem

`continuum_program_remaining_obligation` restates, as one green declaration with
the literature citations, the single statement the program still needs.

**The one open theorem.**  `ContinuumGapTheorem`: there exist a positive physical
constant `c`, a spacing schedule `a_k → 0`, and the fixed-spacing lattice gaps
`m_lat(a_k) > 0`, such that `c · a_k ≤ m_lat(a_k)` for all `k` — i.e. the
dimensionful gap `Δ(a) = m_lat(a)/a ≥ c` uniformly as `a → 0`.

**Closest known results, and why they do NOT yet close 4-D.**

  * **Osterwalder–Seiler (strong coupling)** and **Shen–Zhu–Zhu** prove a mass
    gap at FIXED lattice spacing in the strong-coupling region.  These give
    `m_lat(a) > 0` for fixed `a` (the `latMargin_pos` field) — but the bound is in
    lattice units and DEGRADES to `0` as the coupling runs toward the continuum
    (`w → 1`).  They do not control the RATIO `m_lat(a)/a`, i.e. they do not
    supply `rate_matched`.

  * **Bałaban's renormalization-group** construction controls the continuum limit
    of the partition function / effective actions through the AF flow, the
    natural source of the spacing-uniform estimate `c·a ≤ m_lat(a)`.  It is the
    closest machinery to `rate_matched`, but a complete, spacing-uniform LOWER
    bound on the 4-D mass gap (a constructive dimensional-transmutation statement)
    has not been assembled from it.

  * **Asymptotic freedom / β-function** (`a·Λ = exp(−1/(2 b₀ g²))`) gives the
    EXPECTED rate, and this development carries its running-coupling and
    spacing-to-zero pieces as PROVEN data (the AF reciprocal rate, `a_to_zero`).
    But turning the rate into the constructive uniform inequality `c·a ≤ m_lat(a)`
    requires the exponential transmutation limit `b^k(1−sep₀^{1/b^k}) → −ln sep₀`,
    which is the open constructive core (no `log`/`b`-th root of the needed
    generality) and, more deeply, genuine 4-D dynamics. -/
def continuum_program_remaining_obligation
    (G : ContinuumGapTheorem) :
    UniformSpacingFloor (fun (q x : Q') => q ≤ x) G.physGap :=
  continuumGapTheorem_discharges_uniformSpacingFloor G

end YMGap.Continuum.SharpContinuumObligation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SharpContinuumObligation.ContinuumGapTheorem.c_le_physGap
#print axioms YMGap.Continuum.SharpContinuumObligation.ContinuumGapTheorem.physGap_pos
#print axioms YMGap.Continuum.SharpContinuumObligation.toQFloor
#print axioms YMGap.Continuum.SharpContinuumObligation.continuumGapTheorem_discharges_uniformSpacingFloor
#print axioms YMGap.Continuum.SharpContinuumObligation.toSpacingMatchedFloor
#print axioms YMGap.Continuum.SharpContinuumObligation.AFDimensionalTransmutation.toContinuumGapTheorem
#print axioms YMGap.Continuum.SharpContinuumObligation.afTransmutation_discharges_uniformSpacingFloor
#print axioms YMGap.Continuum.SharpContinuumObligation.continuum_program_remaining_obligation
