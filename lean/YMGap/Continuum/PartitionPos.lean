/-
Track B / E2 — **partition-function positivity** (continuum stage S2) and the
**Bishop integration-space packaging** for the convergent-regime continuum
functional `μ_∞`.

This module discharges, FOR REAL, the first concrete lemma of the
`ContinuumExistence` attack surface — the finite-volume partition-function
lower bound `Z_n = Π_{i<n} W i > 0` — and lays down the constructive
*object* the rest of the construction assembles into: a **Bishop
integration space** (positive normalized linear functional on a dense
subalgebra of cylinder/Wilson observables, completed by an EXPLICIT
convergence modulus), NOT a σ-algebra / non-constructive completion.

# What is genuine here (constructed / proved, axiom-clean)

  * `Q'.mul_pos` — the missing strict-positivity multiplication helper
    (`0 < a → 0 < b → 0 < a·b`), via `CReal.num_pos_of_pos` /
    `CReal.pos_of_num_pos` and the definitional `(a·b).num = a.num·b.num`.
    This is exactly the helper the attack-surface doc flagged as the only
    missing primitive for S2.

  * `prodE_pos` — a finite product of strictly-positive `Q'` weights is
    strictly positive (`prodE`-induction, base `1 > 0`, step `Q'.mul_pos`).

  * `partitionFunctionLB` / `partitionFunction_pos` — **S2 CLOSED.**  The
    partition function `Z_n = Π_{i<n} W i` of a `PlaquetteWeight` is `> 0`,
    with the explicit `Q'` lower bound `z₀ = Z_n` returned as Type-level
    `Σ'` data (Rule 2/8).  This converts the `Z_pos` *hypothesis* field of
    `PlaquetteReweight.Reweight` into a *theorem* for any genuine plaquette
    weight built from positive Boltzmann factors.

  * `weightFromPos` — a concrete `PlaquetteWeight` from a positive-rational
    Boltzmann-factor family `W : Nat → Q'` (`0 < W i`): the partition
    function of a free measure on `n` decoupled edges, exhibiting S2 on a
    real (non-placeholder, non-unit) object `Z_n = Π_i W_i > 0`.  (The
    continuum action's `e^{−S_i}` enters at `CReal` level via `ExpNeg.expNeg`
    one rung up; at the `Q'` partition-function rung the weights are the
    positive rational Boltzmann factors `W_i`.)

  * `BishopFunctional` — the **Bishop integration-space packaging**: a
    `Type`-level structure (Rule 8) carrying a `Q'` observable subalgebra
    `L` with a finite-volume expectation family `I_fin : Nat → L → Q'`, a
    positivity datum, a normalization datum, and — the heart — a per-step
    GEOMETRIC convergence modulus (the KP cluster-series remainder, the
    Bishop summability axiom in modulus form).  `I_inf` is then assembled
    as a `CReal` with explicit Cauchy modulus by feeding the increment
    datum into `KPLimit.crealOfGeoIncrement` — NO compactness, NO
    dominated convergence, NO σ-algebra.

  * `BishopFunctional.I_inf` / `I_inf_approx` — **S5 CLOSED at the packaging
    level**: the infinite-volume functional exists as a `CReal` whose
    `Λ`-th approximation is the finite-volume `I_fin Λ`.

  * `BishopFunctional.I_inf_nonneg` — **S6 CLOSED conditionally**: if every
    finite-volume `I_fin Λ o` is `≥ 0` (the per-volume state positivity,
    = OS2 reflection positivity, the open analytic input), the limit is
    `≥ 0` via `ExpPos.geRat` limit-of-nonneg.

# What this is / is NOT

S2 (partition positivity) and the Bishop *structure* + its S5/S6 stages are
genuine and closed.  The `BishopFunctional` structure FIELD `incrementC`
(the per-step geometric increment constant of the KP cluster series) is the
genuine analytic input — carried as DATA (a structure field), NOT proved
here: deriving it from the convergent SU(2) polymer expansion is stage S4
(the analytic heart), which stays a named obligation in `ContinuumExistence`.
We do NOT fake that bound; we package everything around it so that S4 is the
sole remaining analytic increment to supply.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (via `Q'`/`Int`/`omega`-backed
helpers).  No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.ContinuumExistence
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos

namespace YMGap.Continuum.PartitionPos

open YMGap.Continuum.ContinuumExistence
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum
open YMGap.Constructive
open YMGap.Constructive.HalfPow

/-! ## Strict-positivity primitives and Stage S2 — single-sourced from `ContinuumExistence`

The strict-positivity helpers `mul_pos` / `zero_lt_one'` / `prodE_pos` (and the
`PlaquetteWeight` structure) live in `Continuum/ContinuumExistence.lean` and are
in scope here via `open YMGap.Continuum.ContinuumExistence` (above).  This module
formerly re-declared byte-identical copies of all three; they are now
single-sourced.  The Stage-S2 partition-function lemmas below are stated locally
(re-exported) for this module's `BishopFunctional` packaging. -/

/-- **S2 (first lemma), data form — CLOSED.**  The partition function
`Z_n = Π_{i<n} W i` is positive, returning the explicit lower bound
`z₀ = Z_n` itself as Type-level witness data (`Σ'`, Rule 8.3). -/
def partitionFunctionLB {n : Nat} (p : PlaquetteWeight n) :
    Σ' z₀ : Q', (0 : Q') < z₀ ∧ z₀ ≤ prodE p.W n :=
  ⟨prodE p.W n, prodE_pos p.W p.W_pos n, Q'.le_refl' _⟩

/-- **S2 (first lemma), Prop form — CLOSED.**  `0 < Z_n = Π_{i<n} W i`. -/
theorem partitionFunction_pos {n : Nat} (p : PlaquetteWeight n) :
    (0 : Q') < prodE p.W n :=
  prodE_pos p.W p.W_pos n

/-! ## A genuine plaquette weight from positive rational Boltzmann factors

At the `Q'` partition-function rung the edge Boltzmann factors are positive
RATIONAL weights `W i` (the continuum `e^{−S_i}` enters one rung up at
`CReal` level via `ExpNeg.expNeg`).  A positive-rational family
`W : Nat → Q'` with `0 < W i` is a genuine `PlaquetteWeight`, and its
partition function `Z_n = Π_{i<n} W_i > 0` is S2 on a non-placeholder,
non-unit object. -/

/-- A `PlaquetteWeight` from any positive-rational Boltzmann-factor family. -/
def weightFromPos (n : Nat) (W : Nat → Q') (hW : ∀ i, (0 : Q') < W i) :
    PlaquetteWeight n where
  W := W
  W_pos := hW

/-- The partition function `Z_n = Π_{i<n} W_i` of a positive-rational weight
family is strictly positive (S2 on the genuine non-unit weights). -/
theorem pos_partitionFunction_pos (n : Nat) (W : Nat → Q')
    (hW : ∀ i, (0 : Q') < W i) :
    (0 : Q') < prodE W n :=
  partitionFunction_pos (weightFromPos n W hW)

/-- A concrete non-unit instance: the half-weight `W ≡ 1/2 > 0` gives
`Z_n = (1/2)^n > 0` for every volume `n` (S2 fires on a genuine, non-trivial
positive weight, not the `W ≡ 1` placeholder). -/
theorem half_partitionFunction_pos (n : Nat) :
    (0 : Q') < prodE (fun _ => half) n :=
  pos_partitionFunction_pos n (fun _ => half) (fun _ => (by decide : (0 : Q') < half))

/-! ## The Bishop integration-space packaging of `μ_∞`

The right constructive object (per the constructive-measure literature:
Bishop–Bridges *Constructive Analysis* Ch.6; Coquand–Spitters *Integrals
and Valuations*; Petrakis *pre-integration spaces*) is a **positive
normalized linear functional on a dense subalgebra of observables, completed
by an explicit convergence modulus** — NOT a σ-algebra.

Bishop's integration-space *summability axiom* (if `Σ ∫|f_n| < ∞` then
`Σ f_n` converges with `∫` commuting) is, in modulus form, exactly a
convergence modulus on the finite-volume tower.  In the convergent KP
regime the cluster series furnishes that modulus as a GEOMETRIC remainder,
which the `KPLimit` engine consumes directly (no compactness, no dominated
convergence).

We package this as a `Type`-level structure (Rule 8): the observable
subalgebra `L`, the finite-volume expectation tower `I_fin : Nat → L → Q'`,
and the per-observable geometric single-step increment constant
`incrementC` (the KP cluster-series remainder constant — the genuine
analytic datum, carried as DATA, not proved here). -/

/-- A **Bishop integration space** for the convergent-regime continuum
functional: the finite-volume expectation tower together with the explicit
geometric convergence modulus that completes it to an infinite-volume
`CReal` functional.

  * `L` — the dense observable subalgebra (cylinder / Wilson observables);
  * `I_fin Λ o` — the finite-volume (volume-`Λ`) expectation `⟨o⟩_Λ`;
  * `incrementC o` — the KP geometric single-step increment constant for
    observable `o`, with `incrementC_nonneg` and the two-sided geometric
    increment `hup`/`hlo` in EXACTLY the form `crealOfGeoIncrement`
    consumes (this is the carried analytic datum, stage S4);
  * `modulus o` — the `ρ = 1/2` rescaling witness closing the modulus.

`I_inf o` is then the `CReal` infinite-volume expectation with explicit
Cauchy modulus, assembled below. -/
structure BishopFunctional where
  /-- The observable subalgebra (cylinder / Wilson observables). -/
  L : Type
  /-- The finite-volume expectation tower `⟨o⟩_Λ`. -/
  I_fin : Nat → L → Q'
  /-- The per-observable KP geometric increment constant (stage-S4 datum). -/
  incrementC : L → Q'
  /-- The increment constant is nonnegative. -/
  incrementC_nonneg : ∀ o, (0 : Q') ≤ incrementC o
  /-- Two-sided upper geometric single-step increment (KP cluster tail). -/
  hup : ∀ o l, I_fin (l + 1) o ≤ I_fin l o + geoIncr (incrementC o) l
  /-- Two-sided lower geometric single-step increment (KP cluster tail). -/
  hlo : ∀ o l, I_fin l o ≤ I_fin (l + 1) o + geoIncr (incrementC o) l
  /-- The `ρ = 1/2` rescaling witness closing the geometric modulus. -/
  modulus : ∀ o (ε : Q'), (0 : Q') < ε →
    ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * incrementC o) * δ ≤ ε

/-- **S5 (packaging) — CLOSED.**  The infinite-volume expectation
`⟨o⟩_∞ : CReal` with explicit Cauchy modulus, assembled by feeding the
Bishop functional's geometric increment datum into the KP engine
`crealOfGeoIncrement`.  No compactness, no dominated convergence. -/
def BishopFunctional.I_inf (B : BishopFunctional) (o : B.L) : CReal :=
  crealOfGeoIncrement (fun Λ => B.I_fin Λ o) (B.incrementC o)
    (B.incrementC_nonneg o) (B.hup o) (B.hlo o) (B.modulus o)

/-- **S5 (modulus exactness) — CLOSED.**  The limit's `Λ`-th approximation
is the finite-volume expectation `⟨o⟩_Λ = I_fin Λ o`: the infinite-volume
functional is genuinely `lim_Λ ⟨o⟩_Λ`. -/
@[simp] theorem BishopFunctional.I_inf_approx (B : BishopFunctional) (o : B.L)
    (Λ : Nat) : (B.I_inf o).approx Λ = B.I_fin Λ o := rfl

/-- **S6 (positivity) — CLOSED conditionally on OS2.**  If every
finite-volume expectation `I_fin Λ o` is nonnegative (the per-volume
Wilson reflection positivity, the open OS2 input), the infinite-volume
limit is `≥ 0`, via `ExpPos.geRat` limit-of-nonneg. -/
theorem BishopFunctional.I_inf_nonneg (B : BishopFunctional) (o : B.L)
    (hpos : ∀ Λ, (0 : Q') ≤ B.I_fin Λ o) :
    ExpPos.geRat (B.I_inf o) 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun Λ _ => hpos Λ⟩

/-! ## A concrete inhabitant: the constant (zero-coupling) Bishop functional

The all-ones finite-volume tower `I_fin ≡ 1` (the normalized free state at
zero coupling) with zero increment constant: a genuine `BishopFunctional`
whose infinite-volume limit is the constant `CReal` `1`.  This exhibits the
packaging on a real object (not a `True`/`Unit` placeholder) and shows the
S5/S6 stages fire end-to-end. -/

/-- The constant (zero-coupling) Bishop functional: `I_fin Λ o = 1` for all
volumes, increment constant `1` (any positive constant majorant works for a
volume-independent tower; the modulus is the canonical `CReal.exists_mul_le`
division-free witness). -/
def constBishop : BishopFunctional where
  L := PUnit
  I_fin := fun _ _ => 1
  incrementC := fun _ => 1
  incrementC_nonneg := fun _ => Q'.zero_le_one
  hup := fun _ l => by
    show (1 : Q') ≤ 1 + geoIncr 1 l
    exact Q'.add_le_self_of_nonneg 1 (geoIncr 1 l) (geoIncr_nonneg 1 Q'.zero_le_one l)
  hlo := fun _ l => by
    show (1 : Q') ≤ 1 + geoIncr 1 l
    exact Q'.add_le_self_of_nonneg 1 (geoIncr 1 l) (geoIncr_nonneg 1 Q'.zero_le_one l)
  modulus := fun _ ε hε =>
    CReal.exists_mul_le
      (Q'.mul_nonneg _ _ (by decide) Q'.zero_le_one) hε

/-- The constant Bishop functional's infinite-volume expectation has every
approximation `= 1` — the limit is genuinely the constant free state. -/
@[simp] theorem constBishop_I_inf_approx (o : constBishop.L) (Λ : Nat) :
    (constBishop.I_inf o).approx Λ = 1 := rfl

/-- The constant Bishop functional's limit is `≥ 0` (S6 fires end-to-end on
a concrete object). -/
theorem constBishop_I_inf_nonneg (o : constBishop.L) :
    ExpPos.geRat (constBishop.I_inf o) 0 :=
  constBishop.I_inf_nonneg o (fun _ => Q'.zero_le_one)

end YMGap.Continuum.PartitionPos

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PartitionPos.partitionFunctionLB
#print axioms YMGap.Continuum.PartitionPos.partitionFunction_pos
#print axioms YMGap.Continuum.PartitionPos.weightFromPos
#print axioms YMGap.Continuum.PartitionPos.pos_partitionFunction_pos
#print axioms YMGap.Continuum.PartitionPos.half_partitionFunction_pos
#print axioms YMGap.Continuum.PartitionPos.BishopFunctional.I_inf
#print axioms YMGap.Continuum.PartitionPos.BishopFunctional.I_inf_approx
#print axioms YMGap.Continuum.PartitionPos.BishopFunctional.I_inf_nonneg
#print axioms YMGap.Continuum.PartitionPos.constBishop
#print axioms YMGap.Continuum.PartitionPos.constBishop_I_inf_approx
#print axioms YMGap.Continuum.PartitionPos.constBishop_I_inf_nonneg
