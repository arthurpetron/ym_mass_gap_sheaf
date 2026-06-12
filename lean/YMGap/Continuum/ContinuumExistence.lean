/-
Track B — continuum measure μ_∞ EXISTENCE: statements-only attack-surface
skeleton.

This module is the Lean entry point for the staged construction of the
continuum SU(2) Wilson state μ_∞ that does NOT yet exist in the repo (the
existing `ContinuumMeasure`/`OSReconstruction` carry the existence content
as input hypotheses / abstract `Prop`/`Type` fields — see §1 of
`docs/continuum-measure-attack-surface.md`).

It states the staged obligations S1–S6 of that attack surface as honest
`sorry`s (Rule 6), with the FIRST concrete formalizable lemma — the
finite-volume partition-function lower bound (stage S2,
`partitionFunction_pos` / `partitionFunctionLB`) — written as a Type-level
witness (Rule 2/8). The chosen construction route is the convergent
Kotecký–Preiss route (ii): reuse the `KPLimit` engine
(`crealOfGeoIncrement`) and the `PlaquetteReweight` reweighting state-law,
both already present and axiom-clean.

# Honesty (per AGENTS.md)

  * Every `sorry` here stands for a tier-(S) "standard but unformalized"
    obligation in the convergent regime, EXCEPT where it is conditional on
    the open full-Wilson-PSD positivity (OS2) — flagged inline.
  * The 4D existence + O(4) restoration (the Clay problem) and Conjecture
    7.4 (RG transport) are NOT stated here; they are the genuinely-open
    residue flagged in the attack-surface doc, not formalizable obligations.
  * This file is NOT imported by `YMGap.lean`; build it directly with
    `lake build YMGap.Continuum.ContinuumExistence`.

# Axiom-gate (AGENTS.md Rule 1)

The one non-`sorry` declaration here is the data structure
`PlaquetteWeight`; the lemmas carry `sorry` and are logged.
-/

import YMGap.Continuum.PlaquetteReweight
import YMGap.Continuum.KPLimit
import YMGap.Constructive.ExpPos

namespace YMGap.Continuum.ContinuumExistence

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.PlaquetteReweight
open YMGap.Continuum
open YMGap.Constructive

/-! ## Stage S1 data — a positive plaquette Boltzmann weight on `n` edges

`W i = e^{−S_plaq i}` with `S_plaq i ≥ 0`, so `0 < W i (≤ 1)`.  The genuine
construction (S1) builds `W` from `ExpNeg.expNeg`; here the positivity of
the weights is the carried datum that drives the partition-function bound. -/

/-- A finite-volume plaquette Boltzmann weight: one positive `Q'` weight
per edge.  (In the full S1 construction `W i = e^{−S i}` via `expNeg`; the
positivity `W_pos` is then `expNeg_pos`.) -/
structure PlaquetteWeight (n : Nat) where
  /-- The per-edge Boltzmann weight `W i = e^{−S i}`. -/
  W : Nat → Q'
  /-- Each weight is strictly positive (`e^{−S} > 0`). -/
  W_pos : ∀ i, (0 : Q') < W i

/-! ## Stage S2 — THE FIRST CONCRETE LEMMA: partition-function positivity

`Z_n = E_⊗(W) = Π_{i<n} W i > 0`, with an explicit `Q'` lower bound carried
as DATA (Rule 2/8).  This discharges the currently-hypothesised `Z_pos`
field of `PlaquetteReweight.Reweight`, turning the reweighting state-law
from conditional into constructed.  Proof is `prodE`-induction on a product
of positives — pure tier-(S), no PSD / no increment bound / no conjecture. -/

/-- **S2 (first lemma), data form.**  The partition function
`Z_n = Π_{i<n} W i` is positive, returning the explicit lower bound
`z₀ = Z_n` itself as Type-level witness data (`Σ'`, Rule 8.3). -/
def partitionFunctionLB {n : Nat} (p : PlaquetteWeight n) :
    Σ' z₀ : Q', (0 : Q') < z₀ ∧ z₀ ≤ prodE p.W n :=
  -- SORRY[continuum]: S2 — induct on n; `prodE W 0 = 1 > 0`, step is a
  -- product of two positives (`W_pos`); take z₀ = prodE p.W n with the
  -- bound `≤` by reflexivity.  Needs a `Q'.mul_pos` (positive·positive)
  -- helper not yet in `Constructive/Rationals*.lean` — derivable from
  -- `mul_nonneg` + a strictness lemma.
  sorry

/-- **S2 (first lemma), Prop form.**  `0 < Z_n = Π_{i<n} W i`.  The first
projection of `partitionFunctionLB`. -/
theorem partitionFunction_pos {n : Nat} (p : PlaquetteWeight n) :
    (0 : Q') < prodE p.W n :=
  -- SORRY[continuum]: S2 — `(partitionFunctionLB p).2.1` transported along
  -- the bound; or direct `prodE`-induction.
  sorry

/-! ## Stage S3 — the finite-volume reweighted expectation sequence

`S Λ = ⟨o⟩_Λ = Ew_Λ(o) · recip(Z_Λ)`, a `Q'` sequence in the volume Λ,
built from the reweighting datum at each finite volume (reusing `recip` and
`Reweight.Eβ`).  This is the sequence the KP engine will consume. -/

/-- **S3.**  A volume-indexed family of reweighting data for a fixed
observable yields the finite-volume expectation sequence `S Λ = ⟨o⟩_Λ`.
(Signature placeholder: the genuine family carries the plaquette-coupled
`E_Λ` of stage S1.) -/
def finiteVolumeExpectation
    (Efam : ∀ Λ : Nat, Σ' A : ObsAlg, Reweight A × A.carrier) : Nat → Q' :=
  fun Λ =>
    -- SORRY[continuum]: S3 — `(Efam Λ).2.1.Eβ (Efam Λ).2.2`, i.e.
    -- `Ew_Λ(o) · recip(Z_Λ)`.  Mechanical once S1's `E_Λ` is constructed.
    sorry

/-! ## Stage S4 — the Kotecký–Preiss per-step increment bound (the heart)

THE genuine unformalized analysis: the convergent polymer/cluster expansion
of the reweighted expectation gives a two-sided geometric single-step
increment `|S (Λ+1) − S Λ| ≤ C·(1/2)^Λ` from the certified activity
smallness (`Sheaf/SU2KP.lean` `ρ < 1`, `q < 1`; `SU3CharFactor` `Z_t<1/16`).
We state it in EXACTLY the shape `KPLimit.crealOfGeoIncrement` consumes
(`geoIncr C l = C · (1/2)^l`), with `(C)` returned as data. -/

/-- **S4 (the analytic heart).**  The finite-volume expectation sequence
`S` has a two-sided geometric single-step increment bound with explicit
constant `C ≥ 0`, in the form the KP engine consumes.  Derived from the
convergent cluster expansion + the certified activity smallness. -/
def kpIncrementBound (S : Nat → Q') :
    Σ' C : Q', (0 : Q') ≤ C ∧
      (∀ l, S (l + 1) ≤ S l + geoIncr C l) ∧
      (∀ l, S l ≤ S (l + 1) + geoIncr C l) :=
  -- SORRY[continuum]: S4 — the convergent SU(2) polymer/cluster expansion
  -- bounds the volume increment by the geometric polymer-activity tail
  -- `C·ρ^Λ`, `ρ ≤ 1/2` after domination; the constants come from the Sheaf
  -- KP certificates.  This is the one genuinely-novel-to-formalize step on
  -- route (ii); everything around it is mechanical.
  sorry

/-! ## Stage S5 — the infinite-volume limit as a `CReal` with modulus

Feed S4 into `KPLimit.crealOfGeoIncrement`: the limit exists as a `CReal`
with explicit Cauchy modulus, `approx Λ = S Λ`.  This stage is mostly
mechanical GIVEN S4 — the engine is present and axiom-clean. -/

/-- **S5.**  The infinite-volume expectation `⟨o⟩_∞` exists as a `CReal`
with explicit modulus, built by feeding the S4 increment bound into the KP
engine `crealOfGeoIncrement`. -/
def infiniteVolumeExpectation (S : Nat → Q') : CReal :=
  -- SORRY[continuum]: S5 — `crealOfGeoIncrement S C hC hup hlo modulus`
  -- with `(C, hC, hup, hlo)` from `kpIncrementBound S` and `modulus` the
  -- `ρ=1/2` instance (`δ = ε/2`, cf. `geoPolymerLimit`).  Mechanical.
  sorry

/-- **S5 (modulus exactness).**  The limit's `Λ`-th approximation is the
finite-volume expectation `S Λ` — the limit is genuinely `lim_Λ ⟨o⟩_Λ`. -/
theorem infiniteVolumeExpectation_approx (S : Nat → Q') (Λ : Nat) :
    (infiniteVolumeExpectation S).approx Λ = S Λ :=
  -- SORRY[continuum]: S5 — `rfl` once `infiniteVolumeExpectation` is the
  -- `crealOfGeoIncrement` (whose `approx` is `S` by `crealOfGeoIncrement_approx`).
  sorry

/-! ## Stage S6 — positivity + normalization of the limit functional

`0 ≤ ⟨a*·a⟩_∞` and `⟨1⟩_∞ = 1` from each finite-volume `E_Λ` being a state,
via `CReal` limit-of-nonneg (`ExpPos.geRat` / `ofQ'_le_of_approx_ge`).

NOTE (honesty): the positivity INPUT is the FULL single-edge Wilson PSD
positivity (= OS2), which is 🟡 (cone-only, `coneExp_nonneg`; all-N `P_N`
OPEN).  Until that closes, S6 is CONDITIONAL on the per-volume `Ew_pos`. -/

/-- **S6 (positivity, conditional on OS2).**  If every finite-volume
expectation `S Λ` is nonnegative, the infinite-volume limit is `≥ 0`. -/
theorem infiniteVolumeExpectation_nonneg (S : Nat → Q')
    (hS : ∀ Λ, (0 : Q') ≤ S Λ) :
    ExpPos.geRat (infiniteVolumeExpectation S) 0 :=
  -- SORRY[continuum]: S6 — limit-of-nonneg: `ofQ'_le_of_approx_ge` /
  -- `geRat_of_approx` on `approx Λ = S Λ ≥ 0`.  The hypothesis `hS` is, on
  -- `a*·a`, the per-volume Wilson reflection positivity (OS2) — 🟡 open at
  -- full PSD; tier-(S) given PSD.
  sorry

end YMGap.Continuum.ContinuumExistence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

The only `sorry`-free declaration is the `PlaquetteWeight` data structure.
The staged lemmas carry `sorry` (logged above and in `SORRY_LEDGER.md`);
once closed, each gets a `#print axioms` gate here. -/
