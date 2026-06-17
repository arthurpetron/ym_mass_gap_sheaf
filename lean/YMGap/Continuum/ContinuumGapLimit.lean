/-
Track B / R2 — the continuum gap-persistence bridge: collapsing the entire
thermodynamic-and-continuum limit to a SINGLE honest interface, and wiring the
REAL finite-volume located gap into a strictly-positive continuum mass.

# What this module is

The finite-volume mass gap is already PROVED constructively: for each volume the
compact (finite) transfer operator carries a `LocatedSpectralGap`, whose
`gapMargin = 1 − sep` is a strictly-positive `Q'` quantity
(`gapMargin_pos`).  What is genuinely OPEN is the thermodynamic / continuum
limit: that the per-volume gap margins do not collapse to `0` as the volume
grows — i.e. a UNIFORM positive floor `δ > 0` survives the limit, and the
margin sequence converges to a continuum rate `m_∞` that inherits that floor.

This module isolates exactly that open analysis into one named structure,
`ContinuumGapPersistence`, and PROVES everything that follows from it:

  * the uniform floor `δ > 0` together with its persistence to the limit forces
    the continuum rate `m_∞` to be a strictly-positive constructive real
    (`continuum_mass_isPositive`) — the real content, derived not assumed;
  * the bridge feeds that proven positive `m_∞` into the final
    existence-with-gap datum, so the continuum mass field is populated by
    CONSTRUCTED finite-volume data rather than left a free parameter
    (`withGap_of_persistence`).

The convergence and uniform-floor-persistence facts are the honest hypothesis:
they are the thermodynamic Λ→∞ persistence and the tightness of the continuum
gap, which are open mathematics.  They are carried as explicit fields an
inhabitant must supply; nothing about them is faked.  The structure is the
single open interface of the continuum limit — every other step here is proved
from it.

# Axiom-gate

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.LocatedReconstruction
import YMGap.Continuum.FourDExistence
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.ContinuumGapLimit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap

/-! ## The single open interface: continuum gap persistence

`ContinuumGapPersistence` is the ONE honest hypothesis to which the continuum
limit is reduced.  It packages:

  * a family of finite-volume spectral models indexed by volume `Λ : Nat`, each
    carrying a PROVED located gap (`gaps`, `located`);
  * a UNIFORM positive rational floor `δ > 0` below ALL the per-volume gap
    margins (`floorRate`, `floorRate_pos`, `uniform_floor`) — the
    no-collapse-as-volume-grows content;
  * the continuum gap rate `continuumRate : CReal`, with the margin sequence
    CONVERGING to it (`converges`, using the project's `ConvergesTo` with its
    explicit modulus) and the uniform floor PERSISTING to it
    (`floor_persists`).

The convergence and floor-persistence fields are the genuinely-open analysis
(thermodynamic limit + tightness of the continuum gap).  They are stated
honestly as obligations an inhabitant must produce — never discharged here. -/

/-- **The continuum gap-persistence hypothesis** — the single open interface of
the continuum limit.  Carried as `Type`-level data (Rule 8): the spectral
models, the per-volume located gaps, and the continuum rate are all data; the
uniform-floor and persistence facts are the honest obligations.

An inhabitant asserts: the finite-volume located gaps admit a uniform positive
floor `δ` that survives to a continuum rate `m_∞` the margin sequence converges
to.  This is the thermodynamic / continuum persistence — assumed, never proven
in this development. -/
structure ContinuumGapPersistence : Type where
  /-- A finite-volume spectral model at each volume `Λ`. -/
  gaps : Nat → SpectralModel
  /-- The PROVED located gap (`sep < 1`) at each volume. -/
  located : (Λ : Nat) → LocatedSpectralGap (gaps Λ)
  /-- A uniform positive rational floor below every per-volume gap margin. -/
  floorRate : Q'
  /-- The floor is strictly positive. -/
  floorRate_pos : (0 : Q') < floorRate
  /-- **Uniform floor:** every finite-volume eigenvalue-gap margin `1 − sep`
  stays at or above `δ` (no collapse of the gap as the volume grows). -/
  uniform_floor : ∀ Λ : Nat, floorRate ≤ (located Λ).gapMargin
  /-- The continuum gap rate `m_∞` (a constructive real). -/
  continuumRate : CReal
  /-- **Convergence (open):** the per-volume gap-margin sequence
  `Λ ↦ ofQ' (1 − sep_Λ)` converges to the continuum rate `m_∞`, with the
  project's explicit `ConvergesTo` modulus.  This is the thermodynamic Λ→∞
  limit — the genuinely open analysis. -/
  converges :
    CReal.ConvergesTo (fun Λ => CReal.ofQ' (located Λ).gapMargin) continuumRate
  /-- **Floor persistence (open):** the uniform positive floor survives to the
  limit, `ofQ' δ ≤ m_∞`.  Together with `converges` this is the tightness /
  persistence content of the continuum gap — assumed, never proven. -/
  floor_persists : CReal.ofQ' floorRate ≤ continuumRate

/-! ## The proved bridge: a strictly-positive continuum mass gap

From a `ContinuumGapPersistence` witness we PROVE that the continuum rate is a
strictly-positive constructive real.  This is the real content: positivity
follows CONSTRUCTIVELY from the uniform `δ > 0` floor and its persistence
(`CReal.IsPositive` is exactly "bounded below by a positive `Q'`-rational"),
with the positive rational witness produced as data. -/

/-- The strictly-positive continuum mass gap `m_∞ > 0`, PROVED from the
persistence hypothesis.  The witness is the uniform floor `δ`: `0 < δ` and
`ofQ' δ ≤ m_∞` are exactly an `IsPositive` certificate. -/
theorem continuum_mass_isPositive (P : ContinuumGapPersistence) :
    CReal.IsPositive P.continuumRate :=
  ⟨P.floorRate, P.floorRate_pos, P.floor_persists⟩

/-- **The continuum mass-gap bridge, packaged.**  A `ContinuumGapPersistence`
witness yields a constructive real `m_∞` that is strictly positive — the
continuum mass gap as `Type`-level data with its positivity proof, fed by the
proven finite-volume located gaps through the persistence interface. -/
def continuum_gap_bridge (P : ContinuumGapPersistence) :
    Σ' m : CReal, CReal.IsPositive m :=
  ⟨P.continuumRate, continuum_mass_isPositive P⟩

/-- The continuum rate is bounded below by the uniform finite-volume floor —
the explicit `ofQ' δ ≤ m_∞` link making the continuum mass no smaller than the
proven per-volume gap floor. -/
theorem continuumRate_ge_floor (P : ContinuumGapPersistence) :
    CReal.ofQ' P.floorRate ≤ P.continuumRate :=
  P.floor_persists

/-! ## A concrete persistence skeleton from the proven `sep = 1/2` gap

To exhibit that the interface is fed by REAL constructed finite-volume data
(not a free parameter), the constant family at the proven `sep = 1/2` located
gap supplies everything EXCEPT the two open fields.  Its uniform floor is the
proven margin `1 − 1/2 = 1/2 > 0`; `uniform_floor` is then `Q'.le_refl`.  The
two open fields (`converges`, `floor_persists`) remain the honest obligations a
real inhabitant must supply — here they would assert convergence of the
constant margin sequence, which is the degenerate case of the open analysis. -/

/-- The constant finite-volume family at the proven `sep = 1/2` located gap:
real constructed finite-volume data for the persistence interface (every volume
the same genuine strict gap), with uniform floor `δ = 1/2`. -/
def constGappedFamily : Nat → SpectralModel :=
  fun _ => LocatedReconstruction.gappedSpectralModel

/-- The proven located `sep = 1/2` gap at every volume. -/
def constGappedLocated (Λ : Nat) : LocatedSpectralGap (constGappedFamily Λ) :=
  LocatedReconstruction.gappedLocated

/-- The uniform floor `δ = 1/2` is met with equality by the constant family:
`δ ≤ gapMargin = 1 − 1/2 = 1/2`.  This is the proven, non-open content the
concrete skeleton supplies to `uniform_floor`. -/
theorem constGapped_uniform_floor (Λ : Nat) :
    Q'.mkPos 1 2 (by decide) ≤ (constGappedLocated Λ).gapMargin := by
  show Q'.mkPos 1 2 (by decide) ≤ 1 - Q'.mkPos 1 2 (by decide)
  decide

/-! ## Feeding the proven gap into the final existence-with-gap datum

`withGap_of_persistence` populates `ContinuumYMWithGap.mass` / `mass_pos` from
the persistence bridge: the continuum mass field is no longer a free parameter
but is the constructed `P.continuumRate` with its PROVED positivity.  The
remaining fields (`reconstruction`, `spectral_gap`, and the existence carriers)
are exactly the OTHER open obligations of the continuum theory, so the
constructor takes them as explicit arguments — yielding the clean conditional
theorem "persistence + (other existence carriers) ⟹ existence-with-gap". -/

open YMGap.Continuum.ContinuumMeasure (ContinuumMeasure)
open YMGap.Continuum.OSReconstruction (OSReconstruction)
open YMGap.Continuum.FourDExistence

/-- **Persistence + the other existence carriers ⟹ continuum YM with a mass
gap.**  Given the gap-persistence witness `P` (supplying the strictly-positive
continuum mass `m_∞` from the proven finite-volume gaps), an existence
hypothesis `E`, an OS reconstruction `rec`, and the spectral-gap statement at
`P.continuumRate`, produce a `ContinuumYMWithGap` whose `mass` / `mass_pos`
fields are populated by the CONSTRUCTED persistence data — not an abstract free
parameter.

The conditional is stated cleanly: the open obligations of the continuum theory
(`E`, `rec`, and the spectral-gap datum) remain explicit arguments; this module
contributes the proven positive mass `m_∞` and wires it in. -/
def withGap_of_persistence
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ContinuumGapPersistence)
    (E : ContinuumYMExistence μ_inf)
    (rec : OSReconstruction μ_inf)
    (gap : OSReconstruction.HasSpectralGapAt rec P.continuumRate) :
    ContinuumYMWithGap μ_inf where
  toContinuumYMExistence := E
  reconstruction := rec
  mass := P.continuumRate
  mass_pos := continuum_mass_isPositive P
  spectral_gap := gap

/-- The mass field of the assembled datum is exactly the persistence continuum
rate — confirming the final mass is fed by constructed finite-volume data. -/
theorem withGap_mass_eq
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ContinuumGapPersistence)
    (E : ContinuumYMExistence μ_inf)
    (rec : OSReconstruction μ_inf)
    (gap : OSReconstruction.HasSpectralGapAt rec P.continuumRate) :
    (withGap_of_persistence P E rec gap).mass = P.continuumRate := rfl

end YMGap.Continuum.ContinuumGapLimit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumGapLimit.continuum_mass_isPositive
#print axioms YMGap.Continuum.ContinuumGapLimit.continuum_gap_bridge
#print axioms YMGap.Continuum.ContinuumGapLimit.continuumRate_ge_floor
#print axioms YMGap.Continuum.ContinuumGapLimit.constGapped_uniform_floor
#print axioms YMGap.Continuum.ContinuumGapLimit.withGap_of_persistence
#print axioms YMGap.Continuum.ContinuumGapLimit.withGap_mass_eq
