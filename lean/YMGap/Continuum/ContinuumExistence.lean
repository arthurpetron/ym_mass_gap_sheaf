/-
Track B — continuum measure μ_∞ EXISTENCE: statements-only attack-surface
skeleton.

This module is the Lean entry point for the staged construction of the
continuum SU(2) Wilson state μ_∞ that does NOT yet exist in the repo (the
existing `ContinuumMeasure`/`OSReconstruction` carry the existence content
as input hypotheses / abstract `Prop`/`Type` fields — see §1 of
`docs/continuum-measure-attack-surface.md`).

It stages the obligations S2–S6 of that attack surface.  Stages **S2**
(partition-function positivity, `partitionFunction_pos` / `partitionFunctionLB`),
**S5** (the `CReal` infinite-volume limit with modulus,
`infiniteVolumeExpectation` / `_approx`), and **S6** (limit positivity,
`infiniteVolumeExpectation_nonneg`, conditional on the per-volume OS2 input)
are CLOSED as theorems carrying Type-level witnesses (Rule 2/8).  The
remaining two `sorry`s (Rule 6) are the genuinely-open analytic stages **S3**
(`finiteVolumeExpectation`, needs the constructed interacting `E_Λ`) and
**S4** (`kpIncrementBound`, the convergent-cluster-expansion increment bound
— the analytic heart, NOT faked).  The chosen route is the convergent
Kotecký–Preiss route (ii): reuse the `KPLimit` engine
(`crealOfGeoIncrement`) and the `PlaquetteReweight` reweighting state-law,
both already present and axiom-clean.  The companion module
`Continuum/PartitionPos.lean` carries the S2 positivity again plus the
**Bishop integration-space packaging** of the limit functional.

# Honesty (per AGENTS.md)

  * The two remaining `sorry`s (S3, S4) stand for tier-(S) "standard but
    unformalized" obligations in the convergent regime; S4 is the
    genuinely-novel-to-formalize cluster-expansion increment bound and is
    NOT faked.  S6's positivity is conditional on the open full-Wilson-PSD
    positivity (OS2) — flagged inline.
  * The 4D existence + O(4) restoration (the Clay problem) and Conjecture
    7.4 (RG transport) are NOT stated here; they are the genuinely-open
    residue flagged in the attack-surface doc, not formalizable obligations.
  * This file is NOT imported by `YMGap.lean`; build it directly with
    `lake build YMGap.Continuum.ContinuumExistence`.

# Axiom-gate (AGENTS.md Rule 1)

The CLOSED stages (S2/S5/S6) are `#print axioms`-gated at the foot of the
file (`propext` / `Quot.sound` only).  The two open lemmas carry logged
`sorry`s (S3, S4).
-/

import YMGap.Continuum.PlaquetteReweight
import YMGap.Continuum.KPLimit
import YMGap.Constructive.ExpPos
import YMGap.Constructive.CRealMul

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

/-- **Product of two strictly-positive `Q'` is strictly positive.**
`(a·b).num = a.num·b.num > 0` (both numerators positive). -/
theorem mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  apply CReal.pos_of_num_pos
  show (0 : Int) < a.num * b.num
  exact Int.mul_pos (CReal.num_pos_of_pos ha) (CReal.num_pos_of_pos hb)

/-- `0 < 1` on `Q'` (closed-form, no free variables — used inside the
`prodE_pos` match arm). -/
theorem zero_lt_one' : (0 : Q') < 1 := by decide

/-- **Product of strictly-positive weights is strictly positive.** -/
theorem prodE_pos (f : Nat → Q') (h : ∀ i, (0 : Q') < f i) :
    ∀ n, (0 : Q') < prodE f n
  | 0 => zero_lt_one'
  | n + 1 => by
    show (0 : Q') < prodE f n * f n
    exact mul_pos (prodE_pos f h n) (h n)

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

/-- **S5 — CLOSED (given the S4 increment datum).**  The infinite-volume
expectation `⟨o⟩_∞` exists as a `CReal` with explicit modulus, built by
feeding the S4 geometric increment bound `(C, hC, hup, hlo, modulus)` into
the KP engine `crealOfGeoIncrement`.  S4 (`kpIncrementBound`) is the genuine
analytic obligation that produces this datum for the real Wilson sequence;
GIVEN it, the limit assembly is exactly the engine call — no compactness,
no dominated convergence. -/
def infiniteVolumeExpectation (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncr C l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncr C l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * C) * δ ≤ ε) :
    CReal :=
  crealOfGeoIncrement S C hC hup hlo modulus

/-- **S5 (modulus exactness) — CLOSED.**  The limit's `Λ`-th approximation
is the finite-volume expectation `S Λ` — the limit is genuinely
`lim_Λ ⟨o⟩_Λ`. -/
theorem infiniteVolumeExpectation_approx (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncr C l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncr C l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * C) * δ ≤ ε)
    (Λ : Nat) :
    (infiniteVolumeExpectation S C hC hup hlo modulus).approx Λ = S Λ := rfl

/-! ## Stage S6 — positivity + normalization of the limit functional

`0 ≤ ⟨a*·a⟩_∞` and `⟨1⟩_∞ = 1` from each finite-volume `E_Λ` being a state,
via `CReal` limit-of-nonneg (`ExpPos.geRat` / `ofQ'_le_of_approx_ge`).

NOTE (honesty): the positivity INPUT is the FULL single-edge Wilson PSD
positivity (= OS2), which is 🟡 (cone-only, `coneExp_nonneg`; all-N `P_N`
OPEN).  Until that closes, S6 is CONDITIONAL on the per-volume `Ew_pos`. -/

/-- **S6 (positivity) — CLOSED, conditional on OS2.**  If every
finite-volume expectation `S Λ` is nonnegative, the infinite-volume limit
is `≥ 0`, via `ExpPos.geRat` limit-of-nonneg (the limit's `Λ`-th
approximation is `S Λ`).  The hypothesis `hS` is, on `a*·a`, the per-volume
Wilson reflection positivity (OS2) — 🟡 open at full PSD; tier-(S) given
PSD. -/
theorem infiniteVolumeExpectation_nonneg (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncr C l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncr C l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * C) * δ ≤ ε)
    (hS : ∀ Λ, (0 : Q') ≤ S Λ) :
    ExpPos.geRat (infiniteVolumeExpectation S C hC hup hlo modulus) 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun Λ _ => hS Λ⟩

end YMGap.Continuum.ContinuumExistence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

The CLOSED stages — S2 (`partitionFunctionLB`/`partitionFunction_pos`),
S5 (`infiniteVolumeExpectation`/`_approx`), S6
(`infiniteVolumeExpectation_nonneg`) — are gated below (`propext` /
`Quot.sound` only).  The genuinely-open analytic stages remain logged
`sorry`s: S3 `finiteVolumeExpectation` (needs the constructed interacting
`E_Λ`) and S4 `kpIncrementBound` (THE analytic heart: the convergent
cluster-expansion increment bound). -/

#print axioms YMGap.Continuum.ContinuumExistence.mul_pos
#print axioms YMGap.Continuum.ContinuumExistence.prodE_pos
#print axioms YMGap.Continuum.ContinuumExistence.partitionFunctionLB
#print axioms YMGap.Continuum.ContinuumExistence.partitionFunction_pos
#print axioms YMGap.Continuum.ContinuumExistence.infiniteVolumeExpectation
#print axioms YMGap.Continuum.ContinuumExistence.infiniteVolumeExpectation_approx
#print axioms YMGap.Continuum.ContinuumExistence.infiniteVolumeExpectation_nonneg
