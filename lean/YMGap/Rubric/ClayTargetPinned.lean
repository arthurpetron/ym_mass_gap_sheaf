/-
The **pinned Clay target** — `ClayTarget` with every clause tied to ONE shared
physical stack, closing the "surrogate hole" of the 4-field `ClayScorecard.ClayTarget`.

# The hole this closes (read first)

`ClayScorecard.ClayTarget` bundles four clauses — `fixedSpacing`,
`continuumExistence`, `o4Restoration`, `uniformInCoupling` — but pins **no**
shared continuum object: nothing forces the mass gap read off the spectral data
to be the mass of the SAME Hilbert space whose OS reconstruction, GNS
completion, and continuum limits the other clauses talk about.  A term of
`ClayTarget` could, in principle, discharge each clause with an UNRELATED object.
That is the surrogate hole.

`ClayTargetPinned` removes it.  It carries ONE OS-axiom bundle `bundle`
(fixing the observable algebra `A` and probability functional `E`), ONE OS
reconstruction `recon` over the SAME `μ_∞` (fixing the Hilbert space and
Hamiltonian), ONE GNS datum + completed GNS Hilbert space, and then a set of
**pin fields** — genuine equalities into load-bearing carrier fields — that
force these objects to be the same one:

  * `ePinned`  : the GNS form's expectation IS the OS bundle's functional `E`
                 (the genuinely NEW interface — `GNSData` / `WilsonGNSData` is
                 NOT `μ_∞`-indexed, so nothing otherwise ties the GNS algebra to
                 the OS bundle's algebra);
  * `gnsPinned`: the GNS datum IS the one built from the bundle's algebra;
  * `specPinned`: the reconstruction's OS4 spectral model IS the bundle's;
  * `massGapPinned`: the mass gap `Δ` IS the reconstruction's own eigenvalue-gap
                 margin (not a free positive real);
  * `massPinned`: the continuum-limit mass IS that same `Δ`.

# PROVED vs OPEN (AGENTS.md Rule 6)

PROVED (real terms in this module):
  * `clay_fixed_spacing_met` (transported verbatim into the `fixedSpacing` slot);
  * `reconGapCReal_isPositive` — the reconstruction's margin `1 − sep` is a
    strictly-positive `CReal` (so the mass-gap clause is non-vacuous);
  * `toClayTarget` — the coarsening `ClayTargetPinned ⇒ ClayScorecard.ClayTarget`,
    projecting the shared limit data onto the coarse `o4Restoration` slot and
    transporting the other three clauses verbatim.

OPEN (carried as fields with NO inhabitant — the honest continuum frontier):
  * `continuumExistence : ClayScorecard.ClayContinuumExistence`;
  * `limitData`'s `cluster` / `continuumModulus` / reflection-positivity /
    Euclidean-invariance obligations;
  * `uniformInCoupling : ClayScorecard.RubricUniformInCoupling`.

# DELIBERATELY UNINHABITED

`ClayTargetPinned` is a bare `structure … : Type _` with **no term**.  Producing
one WITHOUT `sorry` / `axiom` / `Prop := True` — genuinely inhabiting the shared
stack AND every open continuum obligation, all pinned to that one stack — is
strictly HARDER than inhabiting `ClayTarget` (it additionally forbids the
surrogate).  `toClayTarget` therefore produces no `ClayTarget` term either; the
Clay problem stays OPEN, and this module only records "pinned ⇒ coarse rubric".

# Axiom-gate (AGENTS.md Rule 1)

Pure structural / `CReal` composition over already-proved engines.  Every
load-bearing declaration is `#print axioms`-gated (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `sorry`, no new `axiom`.  No field is a
`Prop := True` stub; every pin is a genuine identity into a real carrier field.
-/

import YMGap.Rubric.ClayScorecard
import YMGap.Continuum.OSAxioms
import YMGap.Continuum.OSReconstruction
import YMGap.Continuum.ContinuumMeasure
import YMGap.Continuum.WilsonGNS
import YMGap.Continuum.GNSComplete
import YMGap.Continuum.ContinuumYMStack
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Rubric.ClayTargetPinned

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.ContinuumYMStack

/-! ## Two small helper defs the pins reference -/

/-- **`GNSDataOfBundle` — forge the GNS datum from the OS bundle's algebra.**
`GNSData` is a standalone algebraic structure, NOT `μ_∞`-indexed, so on its own
it floats free of the OS bundle.  Given the extra module structure `W` living
over the bundle's OWN observable algebra `b.A` (a `WilsonGNSData b.A`, whose GNS
form is `E(star a · b)`), this packages it into the `GNSData` shape.  This is the
one place the identity of the GNS carrier with the OS-bundle algebra is made
explicit: the returned datum's carrier is `b.A.carrier`. -/
def GNSDataOfBundle {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (b : OSAxiomBundle μ_inf) (W : WilsonGNSData b.A) : GNSData :=
  W.toGNSData

/-- **`reconGapCReal` — the reconstruction's own mass gap as a `CReal`.**  The
eigenvalue-gap MARGIN `1 − sep` (`sep = rec.gapBound`) embedded into `CReal` —
the margin currency the located-gap pipeline uses (the physical mass is
`−log sep`, kept as the margin to avoid `exp`/`log` on `CReal`, exactly as in
`OSReconstruction.HasSpectralGapAt`).  So a mass-gap clause pinned to this is
genuinely THIS reconstruction's gap, not a free positive real. -/
def reconGapCReal {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) : CReal :=
  CReal.ofQ' (1 - rec.gapBound)

/-- **The reconstruction's margin gap is a strictly-positive `CReal`.**  From the
STRUCTURAL field `rec.gapBound_lt_one` (`sep < 1`), the margin `1 − sep > 0`
(`one_sub_pos_of_lt_one`), and a constant-sequence `CReal` bounded below by a
positive rational is `IsPositive`.  This makes the mass-gap clause of
`ClayTargetPinned` non-vacuous. -/
theorem reconGapCReal_isPositive {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) :
    CReal.IsPositive (reconGapCReal rec) :=
  CReal.isPositive_of_approx_ge
    (YMGap.Continuum.one_sub_pos_of_lt_one rec.gapBound_lt_one)
    (fun _ => Q'.le_refl' (1 - rec.gapBound))

/-! ## The pinned Clay target (DELIBERATELY UNINHABITED) -/

/-- **`ClayTargetPinned` — the Clay target with ALL clauses pinned to ONE shared
physical stack.**

Deliberately UNINHABITED: a bare `structure`, no term is provided (only the
coarsening `toClayTarget`).  See the module header for the PROVED/OPEN ledger and
the surrogate hole this closes.  Every pin field is a genuine identity into a
load-bearing carrier field (never `Prop := True`, never an `∃` for the gap). -/
structure ClayTargetPinned {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 2 where
  -- === SHARED PHYSICAL OBJECTS (the pin root) =========================
  /-- ONE OS-axiom bundle over `μ_∞`: fixes the observable algebra `A`, the
  probability functional `E`, and the OS4 spectral model `S`. -/
  bundle : OSAxiomBundle μ_inf
  /-- ONE OS reconstruction over the SAME `μ_∞`: fixes `H_∞`, the Hamiltonian,
  the finite spectral model and the located gap. -/
  recon : OSReconstruction μ_inf
  /-- The extra module structure (add/neg/smul + the GNS form `E(star a · b)`)
  living over the bundle's OWN observable algebra `bundle.A`. -/
  wilson : WilsonGNSData bundle.A
  /-- The GNS datum for the completed Hilbert space. -/
  gnsData : GNSData
  /-- ONE completed GNS Hilbert space over that datum. -/
  gns : CompleteGNSHilbert gnsData

  -- === PROVED (fixed spacing) =========================================
  /-- PROVED: transported verbatim from `clay_fixed_spacing_met`. -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet

  -- === PIN / IDENTITY FIELDS (force the objects to be the same one) ===
  /-- **PIN (the genuinely NEW interface):** the GNS form's expectation IS the
  OS bundle's probability functional `E`.  Since `WilsonGNSData` / `GNSData`
  carry their own `E : carrier → Q'` and are NOT `μ_∞`-indexed, this is the one
  identity that ties the GNS algebra to the OS bundle. -/
  ePinned : wilson.E = bundle.E.E
  /-- **PIN:** the reconstruction's OS4 spectral model IS the bundle's OS4 model,
  so the gap is read off the SAME finite spectral data that feeds clustering. -/
  specPinned : recon.spec = bundle.S
  /-- **PIN:** the GNS datum IS the one forged from the bundle's algebra. -/
  gnsPinned : GNSDataOfBundle bundle wilson = gnsData

  -- === MASS-GAP CLAUSE as Σ-data (mirrors `ContinuumOSCarrier.nontrivial`) ==
  /-- `Δ` = the mass gap, carried WITH a positivity witness (Type-level `Σ'`,
  NOT a bare `∃`). -/
  massGap : Σ' Δ : CReal, CReal.IsPositive Δ
  /-- **PIN:** that `Δ` is the gap of THIS reconstruction (its margin `1 − sep`),
  not a free positive real. -/
  massGapPinned : massGap.1 = reconGapCReal recon
  /-- The genuine spectral gap of the shared reconstruction. -/
  hasGap : HasSpectralGap recon

  -- === OPEN continuum obligations, now over the SHARED stack ===========
  /-- OPEN: continuum measure existence + tightness. -/
  continuumExistence : ClayScorecard.ClayContinuumExistence
  /-- OPEN: the Λ→∞ / a→0 limits + reflection positivity + O(4) invariance,
  carried on the shared masses as genuine `ContinuumLimitData` whose reflection
  positivity is the bundle's OS2 predicate and whose Euclidean-invariance Prop is
  the coarse rubric `RubricO4Restoration`. -/
  limitData : ContinuumLimitData
    (IsOS2ReflectionPositivity bundle.t bundle.ht) ClayScorecard.RubricO4Restoration
  /-- **PIN:** the continuum-limit mass IS the same `Δ` as the mass-gap clause. -/
  massPinned : limitData.continuumMass = massGap.1
  /-- OPEN: the gap uniform across coupling / the continuum. -/
  uniformInCoupling : ClayScorecard.RubricUniformInCoupling

/-! ## The coarsening `ClayTargetPinned ⇒ ClayScorecard.ClayTarget`

Mirrors `Tier0Scorecard.toFrontierC`: transport the clauses the coarse
enumeration keeps verbatim, and project the finer pinned data onto the one coarse
slot the finer stack hands back for free.  Here `limitData` is instantiated at
`EuclInv := RubricO4Restoration`, so its `euclideanInvariance` field IS a proof
of the coarse `o4Restoration` slot. -/

/-- **`toClayTarget` — the supersession coarsening (TOTAL in `P`).**  A pinned
target forgets the shared-object identities and projects onto the 4-field
`ClayScorecard.ClayTarget`:

  * `fixedSpacing` / `continuumExistence` / `uniformInCoupling` transport verbatim;
  * `o4Restoration` is the pinned limit data's `euclideanInvariance` (which is a
    proof of `RubricO4Restoration`, since `limitData` is instantiated there).

Because `ClayTargetPinned` is uninhabited, this produces NO `ClayTarget` term:
Clay stays OPEN, and the coarsening only records "pinned ⇒ coarse rubric" — i.e.
the pinned target is strictly stronger (it additionally forbids the surrogate). -/
def toClayTarget {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ClayTargetPinned μ_inf) : ClayScorecard.ClayTarget where
  fixedSpacing := P.fixedSpacing
  continuumExistence := P.continuumExistence
  o4Restoration := P.limitData.euclideanInvariance
  uniformInCoupling := P.uniformInCoupling

/-- The fixed-spacing half of any pinned target is the PROVED rubric line. -/
theorem pinned_fixedSpacing_proved {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ClayTargetPinned μ_inf) : ClayScorecard.ClayFixedSpacingMet :=
  P.fixedSpacing

/-- The coarsening preserves the fixed-spacing line (a `rfl`-level sanity check
that `toClayTarget` transports `fixedSpacing` verbatim). -/
theorem toClayTarget_fixedSpacing {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ClayTargetPinned μ_inf) :
    (toClayTarget P).fixedSpacing = P.fixedSpacing := rfl

/-- The coarsening's `o4Restoration` slot is exactly the pinned limit data's
Euclidean-invariance proof — the one coarse atom the finer stack hands back. -/
theorem toClayTarget_o4_eq {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (P : ClayTargetPinned μ_inf) :
    (toClayTarget P).o4Restoration = P.limitData.euclideanInvariance := rfl

/-! ## Documentation: PROVED vs OPEN (AGENTS.md Rule 6)

PROVED here (axiom-clean):
  * `reconGapCReal_isPositive` — the reconstruction's margin gap is a positive
    `CReal` (mass-gap clause non-vacuous);
  * `toClayTarget` — the coarsening onto `ClayScorecard.ClayTarget`;
  * `pinned_fixedSpacing_proved` / `toClayTarget_fixedSpacing` / `toClayTarget_o4_eq`.

OPEN (NAMED fields with NO inhabitant):
  * the shared stack `bundle` / `recon` / `wilson` / `gns` together with every
    pin identity, AND the continuum obligations `continuumExistence`,
    `limitData` (cluster / modulus / RP / O(4)), `uniformInCoupling`.

  ⟹ `ClayTargetPinned`  [DELIBERATELY UNINHABITED — the open Clay problem, with
     the surrogate hole additionally closed].

This module records a genuine REFINEMENT (a pinned, surrogate-free target that
coarsens to the rubric `ClayTarget`), NOT a closure.  The Clay Yang–Mills mass
gap remains OPEN. -/

end YMGap.Rubric.ClayTargetPinned

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ClayTargetPinned.reconGapCReal_isPositive
#print axioms YMGap.Rubric.ClayTargetPinned.toClayTarget
#print axioms YMGap.Rubric.ClayTargetPinned.pinned_fixedSpacing_proved
#print axioms YMGap.Rubric.ClayTargetPinned.toClayTarget_fixedSpacing
#print axioms YMGap.Rubric.ClayTargetPinned.toClayTarget_o4_eq
