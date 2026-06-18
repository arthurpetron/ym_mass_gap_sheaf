/-
Track B / R2 — the PHYSICAL gauge-invariant continuum mass separator as a
distinct object, and the genuine residual against the BARE heat-kernel separator.

# Why this module exists — bare ≠ physical

The continuum-gap bridge isolates the open content as a uniform lower bound on a
per-spacing eigenvalue-gap margin divided by the spacing.  When that margin is
taken to be the CLOSED-FORM heat-kernel value `1 − w³` (the spin-`1`
single-plaquette transfer eigenvalue ratio), one obtains the BARE separator

    sep_HK(w) = w³

— a single-plaquette, single-mode TRANSFER coordinate.  It is tempting, and
WRONG, to identify `sep_HK` with the PHYSICAL gauge-invariant continuum mass
separator.  They are NOT the same object:

  * `sep_HK = w³` is a BARE model coordinate: the ratio of the first-excited to
    the vacuum eigenvalue of the *single-plaquette* heat-kernel transfer
    operator, before any 4D renormalization-group resummation.
  * `sep_phys j` is the PHYSICAL gauge-invariant transfer separator at spacing
    index `j`: the actual decay rate of CONNECTED GAUGE-INVARIANT correlators in
    the interacting 4D theory.

The difference is a genuine 4D RG DEVIATION `δ`, the residual the program must
control.  This module introduces `sep_phys` as a NAMED distinct object, states
the real obligation on it (`PhysicalGapFloor`, with BOTH a positive floor and a
finiteness ceiling — the two-sided dimensional-transmutation requirement), and
states the comparison to the bare separator (`HKPhysicalComparison`, carrying the
per-spacing deviation `δ` and the residual bound `δ(a) ≤ C·a·Λ` as NAMED OPEN
content).

# What is genuine — and what remains OPEN (honest)

PROVED here: that a `PhysicalSeparator` whose `sep_phys` satisfies
`PhysicalGapFloor` yields a `RGGapPersistence`, hence `physGapMin > 0` (the
continuum gap).  This re-anchors the open content cleanly on `sep_phys` (NOT on
bare `w`), exactly mirroring the bare-separator bridge.

NOT inhabited (the genuine residual): the floor `PhysicalGapFloor` itself, and
the comparison `HKPhysicalComparison` — specifically its deviation field `δ` and
the residual bound `δ j ≤ C·(a j)·Λ` (the 4D near-fixed-point deviation between
the bare single-plaquette coordinate and the physical gauge-invariant
separator).  These are the open frontier; no inhabitant is provided.  The point
is to STOP conflating the bare coordinate with the physical separator.

The bare trajectory `sep_phys := sep_HK` VIOLATES the finiteness ceiling of
`PhysicalGapFloor`: as `a → 0` the bare physical mass `(1 − w(a)³)/a → ∞` unless
the 4D RG deviation `δ` reshapes it.  That violation is precisely why the
PHYSICAL separator, not the bare one, carries the real content.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural assembly over the reused located-gap,
cluster-bound, and `divPos` data.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  Every witness is `Type`-level
data; the abstract correlator interface, the floor, and the comparison residual
are NAMED Props/structures, never faked.
-/

import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.RGGapPersistence
import YMGap.Continuum.RegularContinuumPipeline
import YMGap.Continuum.SpectralGap
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.PhysicalSeparator

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RGGapPersistence

/-! ## 0. The abstract gauge-invariant correlator interface

The physical separator is DEFINED by what it controls: the decay of connected
gauge-invariant correlators.  The project's analytic core does not (yet) carry a
4D gauge-invariant observable algebra with connected correlators, so we declare
the interface here HONESTLY as named abstract data — NOT faked content.  An
inhabitant of `PhysicalSeparator` must supply these (`Obs`, `GaugeInvariantLocal`,
`connectedCorr`) as the genuine objects whose decay `sep_phys` governs.

  * `Obs` — the type of (continuum) observables;
  * `GaugeInvariantLocal O` — the predicate that `O` is a gauge-invariant local
    observable (the class whose correlators a physical mass gap controls);
  * `connectedCorr j O n` — the connected correlator of `O` at spacing index `j`
    and time separation `n` (a `Q'` bound on its magnitude).

These are the interface to be SUPPLIED; this module states the control relation
abstractly and honestly, and does not pretend to define the 4D measure. -/

/-- The abstract gauge-invariant correlator interface a `PhysicalSeparator`
carries.  Bundled as `Type`-level data: the observable type, the
gauge-invariant-local predicate, and the connected-correlator magnitude
function.  This is the INTERFACE TO BE SUPPLIED — the genuine 4D gauge-invariant
content lives in an inhabitant, never faked here. -/
structure CorrInterface : Type 1 where
  /-- The type of (continuum) observables. -/
  Obs : Type
  /-- `O` is a gauge-invariant LOCAL observable — the class a physical mass gap
  controls. -/
  GaugeInvariantLocal : Obs → Prop
  /-- The connected correlator magnitude of `O` at spacing index `j`, time
  separation `n` (a `Q'` bound). -/
  connectedCorr : Nat → Obs → Nat → Q'
  /-- Connected correlators are nonnegative magnitudes. -/
  connectedCorr_nonneg : ∀ j O n, (0 : Q') ≤ connectedCorr j O n

/-! ## 1. The physical gauge-invariant separator `sep_phys`

`PhysicalSeparator` carries the physical gauge-invariant transfer separator
`sep j` at spacing index `j`, with `0 < sep j < 1` (a genuine sub-unit decay
rate), together with the abstract correlator interface and the CONTENT field
`controlsGaugeInvariantCorr` stating that `sep` governs the decay of connected
gauge-invariant correlators:

    ∀ O, GaugeInvariantLocal O → ∃ C, 0 < C ∧
        ∀ j n, connectedCorr j O n ≤ C · (sep j)^n.

This is the DEFINING physical property — the physical separator is exactly the
geometric rate controlling gauge-invariant clustering.  It is stated honestly
against the supplied interface; no inhabitant is claimed. -/

/-- **The physical gauge-invariant continuum mass separator.**  Carries:

  * `corrIface` — the abstract gauge-invariant correlator interface (§0);
  * `sep j` — the physical gauge-invariant transfer separator at spacing index
    `j`, with `0 < sep j < 1` (`sep_pos`, `sep_lt_one`);
  * `controlsGaugeInvariantCorr` — the DEFINING content: `sep` governs the
    geometric decay of every connected gauge-invariant-local correlator.

This is a DISTINCT object from the bare heat-kernel separator `heatKernelSep w =
w³`; the comparison between them is `HKPhysicalComparison` (§4).  No inhabitant is
claimed — the physical separator with a positive surviving floor is the open
content. -/
structure PhysicalSeparator : Type 1 where
  /-- The abstract gauge-invariant correlator interface this separator controls. -/
  corrIface : CorrInterface
  /-- The physical gauge-invariant transfer separator at spacing index `j`. -/
  sep : Nat → Q'
  /-- The separator is strictly positive (a genuine decay rate, not collapse). -/
  sep_pos : ∀ j : Nat, (0 : Q') < sep j
  /-- The separator is strictly sub-unit (so the margin `1 − sep j > 0`). -/
  sep_lt_one : ∀ j : Nat, sep j < (1 : Q')
  /-- **The defining content:** `sep` governs the geometric decay of every
  connected gauge-invariant-local correlator.  For each gauge-invariant local
  observable `O` there is a positive constant `C` with
  `connectedCorr j O n ≤ C · (sep j)^n` for all spacing index `j` and separation
  `n` — i.e. `sep j` is the gauge-invariant clustering rate at spacing `j`. -/
  controlsGaugeInvariantCorr : ∀ O : corrIface.Obs,
    corrIface.GaugeInvariantLocal O →
      Σ' C : Q', (0 : Q') < C ∧
        ∀ j n : Nat, corrIface.connectedCorr j O n ≤ C * (sep j) ^ n

/-- The separator is nonnegative (from `sep_pos`). -/
theorem PhysicalSeparator.sep_nonneg (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') ≤ P.sep j :=
  Q'.le_of_lt (P.sep_pos j)

/-- **The physical eigenvalue-gap margin** `physMargin j = 1 − sep_phys j`, the
gauge-invariant transfer-gap margin at spacing index `j` (constructive proxy for
`physMass = −log sep_phys`, avoiding `log` per the project convention). -/
def PhysicalSeparator.physMargin (P : PhysicalSeparator) (j : Nat) : Q' :=
  (1 : Q') - P.sep j

@[simp] theorem PhysicalSeparator.physMargin_eq (P : PhysicalSeparator) (j : Nat) :
    P.physMargin j = (1 : Q') - P.sep j := rfl

/-- The physical margin is strictly positive (`1 − sep_phys j > 0`), the
gauge-invariant "there is a gap at spacing `j`" witness. -/
theorem PhysicalSeparator.physMargin_pos (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') < P.physMargin j :=
  one_sub_pos_of_lt_one (P.sep_lt_one j)

/-! ## 2. The genuine physical-gap floor obligation — `PhysicalGapFloor`

The Clay-relevant obligation is on `sep_phys`, NOT on bare `w`.  With `physMass j`
proxied by the margin `physMargin j = 1 − sep_phys j` (per the project's
`log`-free convention), and `a j` the lattice spacing at index `j`, the PHYSICAL
gap is the genuine quotient

    Δ_phys(a_j) = (1 − sep_phys j) / a_j     (= physMass / a, dimension one).

`PhysicalGapFloor` is the TWO-SIDED dimensional-transmutation requirement:

  * a positive FLOOR `c > 0` with `c ≤ (1 − sep_phys j)/a_j` for all `j` (the
    genuine mass-gap survival as `a → 0`);
  * a finiteness CEILING `C` with `(1 − sep_phys j)/a_j ≤ C` for all `j` (the
    physical mass does not blow up — dimensional transmutation, not a trivial
    infinite-mass "continuum").

The BARE trajectory violates the CEILING — that is the whole point of separating
bare from physical.  NO inhabitant is provided. -/

/-- **The genuine physical-gap floor obligation (two-sided).**  Given a physical
separator `P` and a spacing sequence `a_j > 0`, `PhysicalGapFloor` carries:

  * `c`, `c_pos` — a positive uniform PHYSICAL gap floor;
  * `floor` — **open content:** `c ≤ (1 − sep_phys j)/a_j` for all `j` (the gap
    survives `a → 0`);
  * `ceil` — a uniform PHYSICAL gap ceiling;
  * `finiteness` — `(1 − sep_phys j)/a_j ≤ ceil` for all `j` (the two-sided /
    dimensional-transmutation requirement; the BARE trajectory VIOLATES this).

NO inhabitant for 4D Yang–Mills — the positive floor SURVIVING `a → 0` together
with the finiteness ceiling on the PHYSICAL separator is the open content. -/
structure PhysicalGapFloor
    (P : PhysicalSeparator)
    (a : Nat → Q')
    (ha : ∀ j : Nat, (0 : Q') < a j) : Type where
  /-- The uniform physical-gap floor `c`. -/
  c : Q'
  /-- The floor is strictly positive — the dimensional-transmutation witness. -/
  c_pos : (0 : Q') < c
  /-- **The OPEN floor:** `c ≤ (1 − sep_phys j)/a_j` for all `j`. -/
  floor : ∀ j : Nat, c ≤ Q'.divPos (P.physMargin j) (a j) (ha j)
  /-- The uniform physical-gap finiteness ceiling `C`. -/
  ceil : Q'
  /-- **The finiteness requirement:** `(1 − sep_phys j)/a_j ≤ C` for all `j`.
  The two-sided dimensional-transmutation bound; the bare trajectory FAILS it. -/
  finiteness : ∀ j : Nat,
    Q'.divPos (P.physMargin j) (a j) (ha j) ≤ ceil

/-! ## 3. The per-scale physical cluster bound — `floorRate = 1 − sep_phys j`

To feed the existing `RGGapPersistence` bridge, the physical margin `1 −
sep_phys j` must appear as the `floorRate` of a genuine `RegUniformClusterBound`.
We build a one-mode (single-plaquette-shaped, but with the PHYSICAL eigenvalue
`sep_phys j`) finite spectral model and its located gap, constant in the volume
`Λ`, exactly as the bare bridge does — but with the physical separator in place
of the bare `w³`. -/

/-- The one-excited-mode physical spectral model at spacing index `j`: a single
mode with weight `1` and eigenvalue `sep_phys j`. -/
def physSpectralModel (P : PhysicalSeparator) (j : Nat) : SpectralModel where
  k := 1
  w := fun _ => (1 : Q')
  lam := fun _ => P.sep j
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => P.sep_nonneg j

/-- The located gap of the physical spectral model: separator `sep_phys j < 1`,
every eigenvalue `≤ sep_phys j`. -/
def physLocatedGap (P : PhysicalSeparator) (j : Nat) :
    LocatedSpectralGap (physSpectralModel P j) where
  sep := P.sep j
  sep_lt_one := P.sep_lt_one j
  bound := fun _ => Q'.le_refl' (P.sep j)

/-- The physical located gap's margin is the physical margin `1 − sep_phys j`. -/
@[simp] theorem physLocatedGap_gapMargin (P : PhysicalSeparator) (j : Nat) :
    (physLocatedGap P j).gapMargin = P.physMargin j := rfl

/-- **The per-scale physical cluster bound.**  A `RegUniformClusterBound` whose
finite-volume located gaps are the physical located gap `physLocatedGap P j`
(constant in the volume `Λ`) and whose uniform clustering floor is EXACTLY the
physical margin `floorRate = physMargin j = 1 − sep_phys j`.  The outer Cauchy
modulus is trivial (`M ε = 0`) because the gap-margin sequence is constant. -/
def physClusterBound (P : PhysicalSeparator) (j : Nat) : RegUniformClusterBound where
  gaps := fun _ => physSpectralModel P j
  located := fun _ => physLocatedGap P j
  floorRate := P.physMargin j
  floorRate_pos := P.physMargin_pos j
  uniform_floor := fun _ => Q'.le_refl' (P.physMargin j)
  M := fun _ => 0
  Mmono := fun _ _ _ _ => Nat.le_refl 0
  bound := by
    intro ε hε i j' _ _
    exact ⟨Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε),
           Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)⟩

/-- The per-scale physical cluster bound's clustering floor is the physical
margin `1 − sep_phys j`. -/
@[simp] theorem physClusterBound_floorRate (P : PhysicalSeparator) (j : Nat) :
    (physClusterBound P j).floorRate = P.physMargin j := rfl

/-! ## 4. The bridge — `PhysicalGapFloor ⇒ RGGapPersistence ⇒ physGapMin > 0`

This is the headline re-anchoring.  A `PhysicalGapFloor` on `sep_phys` supplies
precisely the data a `RGGapPersistence` needs, with the per-spacing cluster bound
taken to be `physClusterBound P j` (so each `(atSpacing j).floorRate = 1 −
sep_phys j` definitionally).  Hence the open inequality, the band's
`physGapMin > 0`, and the continuum survival theorem all transfer — but now keyed
to the PHYSICAL separator, not the bare `w³`. -/

/-- **The bridge (band construction) from the physical floor.**  From a
`PhysicalGapFloor` on `sep_phys` CONSTRUCT a `RGGapPersistence` whose per-spacing
cluster bounds are `physClusterBound P j` (so each `(atSpacing j).floorRate = 1 −
sep_phys j` definitionally) and whose floor / ceiling estimates are carried
verbatim.  Mirrors the bare-separator bridge, but anchored on `sep_phys`. -/
def toRGGapPersistence
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) : RGGapPersistence where
  spacing := a
  spacing_pos := ha
  atSpacing := fun j => physClusterBound P j
  floorConst := F.c
  floorConst_pos := F.c_pos
  ceilConst := F.ceil
  -- `(atSpacing j).floorRate = physMargin j` definitionally, so `physFloor` /
  -- `physCeil` ARE the physical-separator floor / finiteness estimates.
  physFloor := F.floor
  physCeil := F.finiteness

/-- The reduced obligation's per-spacing lattice floor is the physical margin
`1 − sep_phys j`. -/
@[simp] theorem toRGGapPersistence_floorRate
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) (j : Nat) :
    ((toRGGapPersistence F).atSpacing j).floorRate = P.physMargin j := rfl

/-- The reduced obligation's physical floor constant is the floor `c`. -/
@[simp] theorem toRGGapPersistence_floorConst
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) :
    (toRGGapPersistence F).floorConst = F.c := rfl

/-- **The headline: physical-gap floor ⇒ continuum gap positive.**  From a
`PhysicalGapFloor` on `sep_phys` the constructed band's continuum physical-gap
floor is strictly positive.  So the continuum mass-gap positivity is a PROVED
CONSEQUENCE of the floor obligation on the PHYSICAL separator — NOT on the bare
`w³`. -/
theorem physGapMin_pos_of_physicalGapFloor
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) :
    (0 : Q') < (toScalingBand (toRGGapPersistence F)).physGapMin :=
  physGapMin_pos_of_persistence (toRGGapPersistence F)

/-- **The continuum gap SURVIVES `a → 0`, from the physical floor.**  Every
physical gap of the constructed band, as a regular real, dominates the single
positive constant `ofQ' c`, uniformly in `j` — built entirely from the physical
separator's floor obligation. -/
theorem continuum_gap_of_physicalGapFloor
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) (j : Nat) :
    ofQ' (toScalingBand (toRGGapPersistence F)).physGapMin
      ≤ ofQ' ((toScalingBand (toRGGapPersistence F)).physGap j) :=
  continuum_gap_of_RGGapPersistence (toRGGapPersistence F) j

/-- The bridge also delivers the uniform finiteness half: every physical gap is
bounded above by `ofQ' ceil` as a regular real (the two-sided dimensional
transmutation, on the physical separator). -/
theorem continuum_gap_le_ceiling_of_physicalGapFloor
    {P : PhysicalSeparator} {a : Nat → Q'} {ha : ∀ j : Nat, (0 : Q') < a j}
    (F : PhysicalGapFloor P a ha) (j : Nat) :
    ofQ' ((toScalingBand (toRGGapPersistence F)).physGap j)
      ≤ ofQ' (toScalingBand (toRGGapPersistence F)).physGapMax :=
  continuum_gap_le_ceiling_of_RGGapPersistence (toRGGapPersistence F) j

/-! ## 5. The comparison to the BARE heat-kernel separator — `HKPhysicalComparison`

This is the genuine residual.  The bare separator `heatKernelSep (w j) = w_j³` is
the single-plaquette transfer coordinate; `sep_phys j` is the physical
gauge-invariant separator.  Their difference is a 4D RG deviation `δ j ≥ 0`, and
the comparison is controlled by it BOTH ways:

  * `physMargin_le` : `1 − sep_phys j ≤ (1 − w_j³) + δ j`;
  * `physMargin_ge` : `(1 − w_j³) ≤ (1 − sep_phys j) + δ j`,

i.e. `|sep_phys j − w_j³| ≤ δ j` in margin form.  The RESIDUAL BOUND is the named
OPEN content:

  * `residual` : `δ j ≤ resC · (a j) · Λ`,

the 4D near-fixed-point deviation between the bare single-plaquette coordinate
and the physical separator — vanishing linearly in the spacing `a_j` (with a
scale `Λ`).  NO inhabitant is provided: this residual is exactly the open 4D RG
content the program owes. -/

/-- **The bare↔physical separator comparison (the genuine residual).**  Relates
the bare heat-kernel separator `heatKernelSep (w j) = w_j³` to the physical
separator `sep_phys j` via a per-spacing deviation `δ j`, with BOTH-sided margin
control and the residual bound `δ j ≤ resC · a_j · Λ` as NAMED OPEN content.

Fields:

  * `w`, `w_nonneg`, `w_lt_one` — the bare heat-kernel weights `w_j` (so
    `heatKernelSep (w j) = w_j³` is the bare separator);
  * `δ`, `δ_nonneg` — the per-spacing deviation between bare and physical;
  * `physMargin_le`, `physMargin_ge` — the two-sided comparison `|sep_phys j −
    w_j³| ≤ δ j` in margin form;
  * `Λ`, `resC` — the RG scale and residual constant;
  * `residual` — **the OPEN content:** `δ j ≤ resC · a_j · Λ`, the 4D
    near-fixed-point deviation, vanishing linearly in the spacing.

NO inhabitant is provided — the deviation `δ` and its residual bound are the open
4D RG frontier.  This record exists to NAME the bare↔physical gap, not to close
it. -/
structure HKPhysicalComparison
    (P : PhysicalSeparator) (a : Nat → Q') : Type where
  /-- The bare heat-kernel weights `w_j`. -/
  w : Nat → Q'
  /-- Each weight is nonnegative. -/
  w_nonneg : ∀ j : Nat, (0 : Q') ≤ w j
  /-- Each weight is strictly sub-unit (so `1 − w_j³ > 0`). -/
  w_lt_one : ∀ j : Nat, w j < (1 : Q')
  /-- The per-spacing bare↔physical deviation `δ j`. -/
  δ : Nat → Q'
  /-- The deviation is nonnegative. -/
  δ_nonneg : ∀ j : Nat, (0 : Q') ≤ δ j
  /-- **Forward comparison:** `1 − sep_phys j ≤ (1 − w_j³) + δ j`. -/
  physMargin_le : ∀ j : Nat,
    P.physMargin j ≤ heatKernelMargin (w j) + δ j
  /-- **Reverse comparison:** `(1 − w_j³) ≤ (1 − sep_phys j) + δ j`. -/
  physMargin_ge : ∀ j : Nat,
    heatKernelMargin (w j) ≤ P.physMargin j + δ j
  /-- The RG scale `Λ` controlling the residual. -/
  Λ : Q'
  /-- The residual constant `resC`. -/
  resC : Q'
  /-- **The OPEN content — the residual bound:** `δ j ≤ resC · a_j · Λ`, the 4D
  near-fixed-point deviation between the bare single-plaquette coordinate and the
  physical gauge-invariant separator, vanishing linearly in the spacing `a_j`. -/
  residual : ∀ j : Nat, δ j ≤ (resC * a j) * Λ

/-- **The bare separator is recovered as the `δ = 0` degenerate comparison.**
For convenience, the margin-form two-sided comparison collapses to equality when
the deviation vanishes: with `δ j = 0` the forward bound reads `1 − sep_phys j ≤
1 − w_j³` and the reverse `1 − w_j³ ≤ 1 − sep_phys j`.  This records that the
COMPARISON object genuinely measures the bare↔physical gap (it is tight exactly
when bare = physical), without asserting `δ = 0` holds. -/
theorem HKPhysicalComparison.degenerate_is_bare
    {P : PhysicalSeparator} {a : Nat → Q'}
    (H : HKPhysicalComparison P a) (j : Nat) (hδ : H.δ j = (0 : Q')) :
    P.physMargin j ≤ heatKernelMargin (H.w j) + (0 : Q') ∧
      heatKernelMargin (H.w j) ≤ P.physMargin j + (0 : Q') := by
  refine ⟨?_, ?_⟩
  · have := H.physMargin_le j; rw [hδ] at this; exact this
  · have := H.physMargin_ge j; rw [hδ] at this; exact this

/-! ## 6. Doc-section — the reframing, precisely (HONEST)

The structures above re-anchor the open content correctly.

**The bare separator is a model coordinate.**  `heatKernelSep w = w³` is the
single-plaquette, single-mode heat-kernel TRANSFER coordinate — a bare,
pre-renormalization quantity.  It is fully PROVED data (`HeatKernelGap`), and it
is useful as the explicit object the bare bridge consumes.  But it is NOT the
physical gauge-invariant mass separator.

**The Clay obligation lives on the PHYSICAL separator.**  The genuine obligation
is `PhysicalGapFloor` on `sep_phys` (§2):

    ∃ c > 0, ∀ j,  c ≤ (1 − sep_phys j)/a_j      (the gap SURVIVES a → 0)

TOGETHER WITH the finiteness ceiling

    ∃ C, ∀ j,  (1 − sep_phys j)/a_j ≤ C          (dimensional transmutation),

PLUS the comparison residual `HKPhysicalComparison` (§5):

    δ j ≤ resC · a_j · Λ                          (the 4D RG deviation),

with the two-sided margin control `|sep_phys j − w_j³| ≤ δ j` tying `sep_phys`
back to the bare coordinate.

**Why the BARE trajectory fails — and why the physical separator carries the
content.**  Identifying `sep_phys := sep_HK = w³` would make the physical mass
`(1 − w(a)³)/a` blow up as `a → 0` along asymptotic freedom (the dimensionless
bare margin vanishes only like `a`-or-slower depending on the bare running),
VIOLATING the finiteness ceiling of `PhysicalGapFloor`: an infinite-mass,
trivial "continuum", not Yang–Mills.  The physical separator `sep_phys`, differing
from the bare one by the 4D RG deviation `δ`, is precisely what can satisfy BOTH
the positive floor AND the finiteness ceiling.  That is why the physical
separator, not the bare one, carries the real content — and why `δ` (with its
residual bound) is the genuine open frontier.

**Underclaim.**  This module introduces `sep_phys` as a NAMED distinct object,
states the real two-sided obligation `PhysicalGapFloor` on it, proves the bridge
`PhysicalGapFloor ⇒ physGapMin > 0`, and NAMES the comparison residual
`HKPhysicalComparison` (deviation `δ` + bound `δ ≤ C·a·Λ`).  It does NOT inhabit
`PhysicalGapFloor` or `HKPhysicalComparison` — the floor and the deviation are
the open content.  The deliverable is the clean SEPARATION of the bare coordinate
from the physical separator, and the honest naming of the residual between
them. -/

end YMGap.Continuum.PhysicalSeparator

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PhysicalSeparator.PhysicalSeparator.sep_nonneg
#print axioms YMGap.Continuum.PhysicalSeparator.PhysicalSeparator.physMargin_pos
#print axioms YMGap.Continuum.PhysicalSeparator.physSpectralModel
#print axioms YMGap.Continuum.PhysicalSeparator.physLocatedGap
#print axioms YMGap.Continuum.PhysicalSeparator.physLocatedGap_gapMargin
#print axioms YMGap.Continuum.PhysicalSeparator.physClusterBound
#print axioms YMGap.Continuum.PhysicalSeparator.physClusterBound_floorRate
#print axioms YMGap.Continuum.PhysicalSeparator.toRGGapPersistence
#print axioms YMGap.Continuum.PhysicalSeparator.toRGGapPersistence_floorRate
#print axioms YMGap.Continuum.PhysicalSeparator.toRGGapPersistence_floorConst
#print axioms YMGap.Continuum.PhysicalSeparator.physGapMin_pos_of_physicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparator.continuum_gap_of_physicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparator.continuum_gap_le_ceiling_of_physicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparator.HKPhysicalComparison.degenerate_is_bare
