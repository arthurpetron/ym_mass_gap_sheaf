/-
Track B / R2 — collapsing the TWO open thermodynamic-limit obligations of the
continuum gap-persistence interface to a SINGLE literature-backed input, and
CONSTRUCTING both from it.

# What this module is

The continuum gap-persistence interface carries the proven finite-volume located
gaps together with TWO honest open fields: the thermodynamic Λ→∞ CONVERGENCE of
the per-volume gap-margin sequence to a continuum rate, and the PERSISTENCE of a
uniform positive floor to that limit.

Deep research into the strong-coupling cluster expansion (Osterwalder–Seiler
1978; Seiler LNP 159 1982; Shen–Zhu–Zhu CMP 2023) establishes that at FIXED
lattice spacing BOTH of those fields are theorem-consequences of ONE fact: a
VOLUME-UNIFORM cluster-expansion convergence bound.  There exist explicit
rationals (a sum-of-activities bound `eps < 1` and a clustering floor
`floorRate > 0`) depending only on (β, d, group) and NOT on the volume, giving
exponential clustering uniformly in Λ AND a DIRECT geometric Cauchy modulus for
the finite-volume gap margins — no subsequence / Prokhorov extraction.

This module isolates exactly that one fact as a single `Type`-level structure,
`UniformClusterBound`, and from it CONSTRUCTS the full gap-persistence datum:

  * `converges` is CONSTRUCTED — the geometric single-step increment bound is fed
    through the project's `crealOfGeoIncrement` engine to define the continuum
    rate as a genuine `CReal` whose approximations ARE the margin sequence, so
    that `ConvergesTo` is the engine's own self-convergence (the geometric
    modulus IS the Cauchy modulus);
  * `floor_persists` is CONSTRUCTED — the uniform per-volume floor passes to the
    limit by the "approximations bounded below ⟹ limit bounded below" lift.

The two formerly-open fields are therefore both PROVED from the single input.
The continuum (spacing→0) tightness — the Prokhorov extraction of a continuum
measure as the lattice spacing tends to zero — remains the separate,
genuinely-open interface; it is NOT addressed here.

# Axiom-gate

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.KPLimit
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ClusterGapReduction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuumGapLimit

/-! ## The single open interface: a volume-uniform cluster bound

`UniformClusterBound` is the ONE honest hypothesis to which the entire
thermodynamic limit is reduced.  It is the constructive stand-in for the
Osterwalder–Seiler / Seiler / Shen–Zhu–Zhu volume-uniform cluster-expansion
convergence bound.  It packages, all as `Type`-level data (Rule 8):

  * the finite-volume spectral models with their PROVED located gaps
    (`gaps`, `located`) — exactly the proven finite-volume mass-gap data;
  * a uniform positive rational floor `δ` below every per-volume gap margin
    (`floorRate`, `floorRate_pos`, `uniform_floor`) — the no-collapse content;
  * the cluster activity-sum bound represented by a geometric rate: a
    nonnegative `Q'` constant `tailConst` and the two-sided SINGLE-STEP
    geometric increment bounds (`incr_up`, `incr_lo`) saying consecutive gap
    margins differ by at most `tailConst·(1/2)^Λ` — the DIRECT geometric tail
    of the cluster expansion;
  * the rescaling witness (`modulus`) certifying that the project's `HalfPow`
    modulus closes any target tolerance, so the geometric tail genuinely defines
    a `CReal` limit with an explicit Cauchy modulus.

From this ONE structure the continuum rate and BOTH formerly-open persistence
fields are constructed below. -/

/-- **The volume-uniform cluster bound** — the single open input of the
thermodynamic limit.  An inhabitant asserts the strong-coupling cluster
expansion's volume-uniform convergence: a uniform clustering floor `δ > 0` and a
geometric single-step tail `tailConst·(1/2)^Λ` controlling the gap-margin
sequence.  Everything downstream — the continuum rate, its convergence, and the
floor persistence — is PROVED from this. -/
structure UniformClusterBound : Type where
  /-- A finite-volume spectral model at each volume `Λ`. -/
  gaps : Nat → SpectralModel
  /-- The PROVED located gap (`sep < 1`) at each volume. -/
  located : (Λ : Nat) → LocatedSpectralGap (gaps Λ)
  /-- A uniform positive rational clustering floor below every per-volume gap
  margin. -/
  floorRate : Q'
  /-- The floor is strictly positive. -/
  floorRate_pos : (0 : Q') < floorRate
  /-- **Uniform floor:** every finite-volume gap margin `1 − sep` stays at or
  above `δ` — the volume-uniform clustering content. -/
  uniform_floor : ∀ Λ : Nat, floorRate ≤ (located Λ).gapMargin
  /-- The geometric tail constant of the cluster expansion (nonnegative). -/
  tailConst : Q'
  /-- The tail constant is nonnegative. -/
  tailConst_nonneg : (0 : Q') ≤ tailConst
  /-- **Geometric single-step bound (up):** consecutive gap margins differ by at
  most `tailConst·(1/2)^Λ` — the connected-correlator geometric tail. -/
  incr_up : ∀ Λ : Nat,
    (located (Λ + 1)).gapMargin ≤ (located Λ).gapMargin + geoIncr tailConst Λ
  /-- **Geometric single-step bound (lo):** the reverse single-step geometric
  bound. -/
  incr_lo : ∀ Λ : Nat,
    (located Λ).gapMargin ≤ (located (Λ + 1)).gapMargin + geoIncr tailConst Λ
  /-- The rescaling witness: the `HalfPow` modulus closes any target tolerance
  against the tail constant.  At concrete data this is discharged by `decide`. -/
  modulus : ∀ ε : Q', (0 : Q') < ε →
    ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * tailConst) * δ ≤ ε

/-! ## The constructed continuum rate

The gap-margin sequence `Λ ↦ (located Λ).gapMargin`, equipped with the two-sided
geometric single-step bound, is fed straight into the project's
`crealOfGeoIncrement` engine.  The result is a genuine `CReal` whose `approx Λ`
is the margin at volume `Λ` — the thermodynamic limit, with the geometric tail
as its explicit Cauchy modulus. -/

/-- The continuum gap rate `m_∞` CONSTRUCTED from the geometric cluster tail: the
`CReal` limit of the per-volume gap-margin sequence, with modulus inherited from
the geometric tail.  Its `approx Λ` is exactly `(located Λ).gapMargin`. -/
def continuumRate (B : UniformClusterBound) : CReal :=
  crealOfGeoIncrement
    (fun Λ => (B.located Λ).gapMargin)
    B.tailConst B.tailConst_nonneg
    B.incr_up B.incr_lo B.modulus

/-- The constructed continuum rate's `Λ`-th approximation is the gap margin at
volume `Λ` — the limit is fed by the genuine finite-volume located gaps. -/
@[simp] theorem continuumRate_approx (B : UniformClusterBound) (Λ : Nat) :
    (continuumRate B).approx Λ = (B.located Λ).gapMargin := rfl

/-! ## `converges` — CONSTRUCTED from the geometric tail

Because the continuum rate's approximations ARE the margin sequence, the
convergence of the margin sequence to it is the engine's own self-convergence
(`convergesTo_self`): the geometric modulus is the Cauchy modulus.  No
subsequence, no Prokhorov. -/

/-- **Convergence, CONSTRUCTED.**  The per-volume gap-margin sequence
`Λ ↦ ofQ' (1 − sep_Λ)` converges to the constructed continuum rate, with the
explicit geometric modulus.  Proof: the continuum rate's own approximations are
the margins, so this is `convergesTo_self`. -/
theorem converges (B : UniformClusterBound) :
    CReal.ConvergesTo
      (fun Λ => CReal.ofQ' (B.located Λ).gapMargin) (continuumRate B) :=
  CReal.convergesTo_self (continuumRate B)

/-! ## `floor_persists` — CONSTRUCTED from the uniform floor

The uniform per-volume floor `δ ≤ margin_Λ` is exactly "every approximation of
the continuum rate is `≥ δ`", so the limit is `≥ δ` by the standard
approximation-lower-bound lift. -/

/-- **Floor persistence, CONSTRUCTED.**  The uniform positive floor `δ` survives
to the constructed limit, `ofQ' δ ≤ m_∞`.  Proof: every approximation of the
continuum rate is a gap margin, hence `≥ δ` by `uniform_floor`, so the limit is
`≥ δ` by `ofQ'_le_of_approx_ge` — no tightness/Prokhorov input needed. -/
theorem floor_persists (B : UniformClusterBound) :
    CReal.ofQ' B.floorRate ≤ continuumRate B :=
  CReal.ofQ'_le_of_approx_ge (fun Λ => B.uniform_floor Λ)

/-! ## The constructor: cluster bound ⟹ gap persistence

Both formerly-open fields now built, the cluster bound populates the entire
`ContinuumGapPersistence` interface that the rest of the continuum theory
consumes. -/

/-- **The reduction.**  A volume-uniform cluster bound CONSTRUCTS the full
continuum gap-persistence datum: the located gaps and uniform floor are carried
verbatim, while the two formerly-open fields — `converges` and `floor_persists`
— are PROVED from the geometric tail and the uniform floor respectively.  This
collapses the two thermodynamic-limit obligations to the single cluster input. -/
def continuumGapPersistence_of_clusterBound (B : UniformClusterBound) :
    ContinuumGapPersistence where
  gaps := B.gaps
  located := B.located
  floorRate := B.floorRate
  floorRate_pos := B.floorRate_pos
  uniform_floor := B.uniform_floor
  continuumRate := continuumRate B
  converges := converges B
  floor_persists := floor_persists B

/-- The reduced persistence datum's continuum rate is the constructed limit. -/
theorem reduction_continuumRate (B : UniformClusterBound) :
    (continuumGapPersistence_of_clusterBound B).continuumRate = continuumRate B :=
  rfl

/-! ## Capstone: the strictly-positive continuum mass off the single bound

Composing the constructor with the proven `continuum_mass_isPositive` shows the
end-to-end chain — finite-volume located gaps ⟹ uniform cluster bound ⟹
strictly-positive continuum mass — now hangs off the single input. -/

/-- **Capstone (positivity).**  A volume-uniform cluster bound yields a
strictly-positive continuum mass: compose the reduction with the proven
positivity of the persistence continuum rate. -/
theorem clusterBound_continuum_mass_isPositive (B : UniformClusterBound) :
    CReal.IsPositive (continuumRate B) :=
  continuum_mass_isPositive (continuumGapPersistence_of_clusterBound B)

/-- **Capstone (packaged).**  The continuum mass as `Type`-level data with its
positivity proof, fed end-to-end by the single cluster bound. -/
def clusterBound_continuum_gap_bridge (B : UniformClusterBound) :
    Σ' m : CReal, CReal.IsPositive m :=
  ⟨continuumRate B, clusterBound_continuum_mass_isPositive B⟩

/-- The packaged mass is exactly the constructed continuum rate. -/
theorem clusterBound_bridge_fst (B : UniformClusterBound) :
    (clusterBound_continuum_gap_bridge B).1 = continuumRate B := rfl

end YMGap.Continuum.ClusterGapReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ClusterGapReduction.continuumRate
#print axioms YMGap.Continuum.ClusterGapReduction.continuumRate_approx
#print axioms YMGap.Continuum.ClusterGapReduction.converges
#print axioms YMGap.Continuum.ClusterGapReduction.floor_persists
#print axioms YMGap.Continuum.ClusterGapReduction.continuumGapPersistence_of_clusterBound
#print axioms YMGap.Continuum.ClusterGapReduction.reduction_continuumRate
#print axioms YMGap.Continuum.ClusterGapReduction.clusterBound_continuum_mass_isPositive
#print axioms YMGap.Continuum.ClusterGapReduction.clusterBound_continuum_gap_bridge
#print axioms YMGap.Continuum.ClusterGapReduction.clusterBound_bridge_fst
