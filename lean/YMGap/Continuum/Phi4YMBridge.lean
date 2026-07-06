/-
Track B / R2 — THE φ⁴ → YM BRIDGE (deliverable P2).

# What this module is — the honest boundary, stated up front

This file is the GLUE that connects the Yang–Mills *additive-erosion* carrier
(`TrueMarginRecursionPhysical`, the honest dimensionless-margin residual) to the
*same* `RegScalingBand` continuum pipeline that the φ⁴ validation model
(`Phi4ScalingBand`) already exercised end-to-end.  It proves, as a Lean theorem,
that φ⁴ and YM share the IDENTICAL final assembly: given the YM carrier, the
continuum physical-gap floor `physGapMin` is strictly positive, over the very
same `RGGapPersistence ⇒ RegScalingBand` reduction φ⁴ ran — with the additive
`ε_k` step (`TrueMarginRecursionPhysical.step` + `lowerBound`, the
anchor-dominates-budget conclusion) as the SOLE isolated open core.

**This is CONDITIONAL and inhabits NOTHING.**  Every theorem below takes a
`TrueMarginRecursionPhysical` (and a small pipeline envelope, see §2) as an
explicit HYPOTHESIS.  `TrueMarginRecursionPhysical` is the deliberately
UNINHABITED Clay-core residual: producing an inhabitant (the non-abelian 4D
block-spin `step` law together with anchor-dominates-budget) is exactly the open
dimensional-transmutation problem.  Nothing here inhabits it, nor any guarded
frontier bundle; `YMGapGuard` still reports all five frontiers uninhabited.

# The chain, exactly as built

  1. `TrueMarginRecursionPhysical` carries the TRUE margin
     `margin k = m_lat(a_k)/a_k` (`margin_def`, via `Q'.divPos`), the positive
     continuum limit `Δ : CReal`, its rational lower witness `floorWitness > 0`
     with `ofQ' floorWitness ≤ Δ`, and the uniform lower bound
     `Δ ≤ ofQ' (margin k)` at every scale (`lowerBound`).

  2. `Δ`'s positive rational witness is `floorWitness` itself
     (`delta_isPositive` unfolds to `⟨floorWitness, floorWitness_pos,
     floorWitness_le⟩` — the codebase carries `c := floorWitness` as `Type`-level
     DATA rather than eliminating the `Prop`-∃ `CReal.IsPositive`, which is the
     MLTT-clean way to "extract the rational below `Δ`", Rule 8).

  3. `physFloor_of_trueMarginPhysical` — THE CORE c-BOUND (unconditional on the
     §2 envelope): for every `k`,
        `floorWitness ≤ m_lat(a_k)/a_k`   (`Q'.divPos`),
     the collapse of `ofQ' floorWitness ≤ Δ ≤ ofQ' (margin k)` to the plain
     rational order (`le_of_leEv_ofQ'`), i.e. the exact `RGGapPersistence.physFloor`
     shape with `floorConst := floorWitness`.  This IS the shared uniform floor.

  4. `rgGapPersistence_of_trueMarginPhysical` — assembles a genuine
     `RGGapPersistence` (hence, via `toScalingBand`, a genuine `RegScalingBand`)
     whose per-scale physical gap `physGap k = (atSpacing k).floorRate / a_k`
     equals the true margin `margin k`, and whose floor is `floorWitness`.

  5. `physGapMin_pos_of_trueMarginPhysical` — THE BRIDGE: the YM continuum
     physical-gap floor is strictly positive, GIVEN the additive-erosion carrier,
     over the same `RegScalingBand` pipeline φ⁴ validated.

# The pipeline envelope (§2) — the honestly-named, non-Clay pieces T lacks

`RGGapPersistence`/`RegScalingBand` express the per-scale numerator as a
`RegUniformClusterBound.floorRate`, which is structurally a located gap-margin
`1 − sep ∈ (0,1]` (a compact-transfer-operator finite-volume gap).  The abstract
`TrueMarginRecursionPhysical.massLat` carries no such range, and T carries no
uniform CEILING (its content is a LOWER bound on the margin).  So entering the
pipeline needs two inputs T does not supply:

  * `massLat_lt_one` — the lattice gap margin is `< 1` (a located separator
    exists), and
  * `ceilConst`/`physCeil` — a uniform upper bound `margin k ≤ C` (the
    finiteness half of the band).

Both are genuine but NON-Clay facts: a lattice gap margin lies in `(0,1)`, and
the physical gap is finite.  They are carried as an explicit named envelope
(`MarginBandEnvelope`, Rule 6a), NOT smuggled and NOT the open content.  The
positivity `massLat_pos` is DERIVED from T (not assumed).  The cluster bound is
built with the SAME generic constructor `phi4ClusterBoundOf` the φ⁴ band uses —
literally the same plumbing.

# What the bridge establishes vs. what stays open

  * ESTABLISHED (this file, a Lean implication): YM `physGapMin > 0`
    ⇐ `TrueMarginRecursionPhysical` (+ the non-Clay `MarginBandEnvelope`), via the
    identical `RGGapPersistence ⇒ RegScalingBand` assembly φ⁴ validated with a
    dialed-in floor.  The floor `physGapMin = floorWitness` is the REAL rational
    witness of the true margin's continuum limit `Δ`, not a fake.

  * OPEN (untouched): `TrueMarginRecursionPhysical` itself — the additive-`ε_k`
    block-spin `step` law and the anchor-dominates-budget positive limit.  That
    is the YM-specific delta; φ⁴ replaces exactly this engine with a bare mass.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Every modulus / constant is `Type`-level data.
-/
import YMGap.Continuum.TrueMarginRecursionPhysical
import YMGap.Continuum.RGGapPersistence
import YMGap.Continuum.Phi4ScalingBand

namespace YMGap.Continuum.Phi4YMBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.RegularContinuumPipeline

/-! ## 1. The core c-bound — the shared uniform floor (unconditional on §2)

`floorWitness` is precisely the positive rational witness under `Δ.IsPositive`
(`delta_isPositive T = ⟨floorWitness, floorWitness_pos, floorWitness_le⟩`), carried
as `Type`-level data.  Below it sits the true margin at every scale, by collapsing
`ofQ' floorWitness ≤ Δ ≤ ofQ' (margin k)` to the plain rational order. -/

/-- `Δ`'s positive-rational-witness narrative, re-exported: the carried
`floorWitness` IS a rational strictly below the positive continuum limit `Δ`.
This is the "`c` extracted from `Δ.IsPositive`" step — but as data (Rule 8). -/
theorem delta_isPositive_witness (T : TrueMarginRecursionPhysical) :
    CReal.IsPositive T.Δ :=
  delta_isPositive T

/-- The carried rational floor `floorWitness` lies below the true margin at every
scale (the `QFloor` bound, phrased on `margin`). -/
theorem floorWitness_le_margin (T : TrueMarginRecursionPhysical) (k : Nat) :
    T.floorWitness ≤ T.margin k :=
  (uniformSpacingFloor_of_trueMarginPhysical T).bound k

/-- **THE CORE c-BOUND.**  For every scale `k`, the positive rational witness
`floorWitness` of the continuum limit `Δ` lies below the TRUE dimensionless
physical margin `m_lat(a_k)/a_k` (`Q'.divPos`).  This is exactly the
`RGGapPersistence.physFloor` shape with `floorConst := floorWitness`, obtained by
collapsing `ofQ' floorWitness ≤ Δ ≤ ofQ' (margin k)` to the rational order.  NO
`MarginBandEnvelope` is needed for this — it is the shared uniform floor itself. -/
theorem physFloor_of_trueMarginPhysical (T : TrueMarginRecursionPhysical) (k : Nat) :
    T.floorWitness ≤ Q'.divPos (T.massLat k) (T.spacing k) (T.spacing_pos k) := by
  have h : T.floorWitness ≤ T.margin k := floorWitness_le_margin T k
  rw [T.margin_def k] at h
  exact h

/-- The lattice mass `m_lat(a_k)` is strictly positive — DERIVED from T (not
assumed): `0 < floorWitness ≤ margin k` gives `0 < margin k`, and
`margin k · a_k ≃ m_lat(a_k)` (`divPos_mul_eqv`) with `a_k > 0` forces the
numerator positive.  Needed only to build the cluster bound's positive floor. -/
theorem massLat_pos (T : TrueMarginRecursionPhysical) (k : Nat) :
    (0 : Q') < T.massLat k := by
  have hmpos : (0 : Q') < T.margin k :=
    AFExpLift.lt_of_lt_of_le T.floorWitness_pos (floorWitness_le_margin T k)
  have hprod : (0 : Q') < T.margin k * T.spacing k :=
    Q'.mul_pos hmpos (T.spacing_pos k)
  have he : (T.margin k * T.spacing k).eqv (T.massLat k) := by
    rw [T.margin_def k]
    exact Q'.divPos_mul_eqv (T.massLat k) (T.spacing k) (T.spacing_pos k)
  exact AFExpLift.lt_of_lt_of_le hprod (Q'.le_of_eqv he)

/-! ## 2. The pipeline envelope — the honestly-named, non-Clay carrier pieces

`RGGapPersistence` needs the numerator as a located gap margin `∈ (0,1]` and a
uniform ceiling.  `MarginBandEnvelope` carries exactly those two non-Clay inputs
(positivity `massLat_pos` is derived above, not carried).  Discharging it is NOT
the open problem: a lattice gap margin lies in `(0,1)` and the physical gap is
finite; the open content stays the additive-`ε_k` `step`/`lowerBound` of T. -/

/-- **The non-Clay pipeline envelope for the YM carrier.**  Two genuine but
non-open facts that the abstract `TrueMarginRecursionPhysical` does not carry,
needed to enter the located-gap `RGGapPersistence` shape:

  * `massLat_lt_one` — the lattice gap margin `m_lat(a_k)` is `< 1` (a genuine
    located separator `sep = 1 − m_lat ∈ (0,1)` exists at every scale);
  * `ceilConst`/`physCeil` — a uniform CEILING on the physical gap (the
    finiteness half; T carries only a LOWER bound).

This is the φ⁴-shaped plumbing the carrier plugs into — NOT the Clay core. -/
structure MarginBandEnvelope (T : TrueMarginRecursionPhysical) : Type where
  /-- The lattice gap margin is `< 1` at every scale (located separator exists). -/
  massLat_lt_one : ∀ k, T.massLat k < (1 : Q')
  /-- A uniform physical ceiling `C` (the finiteness half). -/
  ceilConst : Q'
  /-- The physical gap `m_lat(a_k)/a_k` is bounded above by `C`, uniformly. -/
  physCeil : ∀ k,
    Q'.divPos (T.massLat k) (T.spacing k) (T.spacing_pos k) ≤ ceilConst

/-! ## 3. The assembly — `TrueMarginRecursionPhysical (+ envelope) ⇒ RGGapPersistence`

The per-scale cluster bound is built with the SAME generic constructor the φ⁴
band uses, `Phi4ScalingBand.phi4ClusterBoundOf`, at floor `m_lat(a_k)` — so its
`floorRate` is `m_lat(a_k)` definitionally and the derived physical gap
`physGap k = (atSpacing k).floorRate / a_k` is exactly the true margin
`margin k`.  The band's `physFloor`/`physCeil` are then the core c-bound (§1) and
the envelope ceiling; positivity of `physGapMin` is `floorWitness_pos`. -/

/-- **The assembly.**  From the YM carrier `T` and the non-Clay envelope `E`,
CONSTRUCT a genuine `RGGapPersistence` whose per-scale numerator is `m_lat(a_k)`
(via the φ⁴ generic cluster bound), floor `floorWitness > 0`, ceiling
`E.ceilConst`.  Its physical gap equals the TRUE margin `margin k`. -/
def rgGapPersistence_of_trueMarginPhysical
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) :
    RGGapPersistence where
  spacing := T.spacing
  spacing_pos := T.spacing_pos
  atSpacing := fun k =>
    Phi4ScalingBand.phi4ClusterBoundOf (T.massLat k) (massLat_pos T k) (E.massLat_lt_one k)
  floorConst := T.floorWitness
  floorConst_pos := T.floorWitness_pos
  ceilConst := E.ceilConst
  physFloor := fun k => physFloor_of_trueMarginPhysical T k
  physCeil := fun k => E.physCeil k

/-- The assembled persistence carries `floorConst = floorWitness` — the REAL
rational witness of the continuum-limit margin `Δ`, not a fabricated constant. -/
@[simp] theorem rgGapPersistence_floorConst
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) :
    (rgGapPersistence_of_trueMarginPhysical T E).floorConst = T.floorWitness := rfl

/-- The assembled band's per-scale numerator is exactly `m_lat(a_k)` — so its
physical gap `physGap k` is the TRUE margin `margin k` (non-vacuity: the pipeline
runs on the real carrier quantity, not a surrogate). -/
@[simp] theorem rgGapPersistence_floorRate
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) (k : Nat) :
    ((rgGapPersistence_of_trueMarginPhysical T E).atSpacing k).floorRate = T.massLat k := rfl

/-! ## 4. THE BRIDGE — YM `physGapMin > 0` ⇐ the additive-erosion carrier

The headline: routing the assembled persistence through the SAME
`toScalingBand` / `physGapMin_pos_of_persistence` reduction φ⁴ validated, the YM
continuum physical-gap floor is strictly positive — conditional ONLY on the
uninhabited carrier `T` (plus the non-Clay envelope). -/

/-- The `RegScalingBand` for the YM carrier, over the φ⁴-validated pipeline. -/
def scalingBand_of_trueMarginPhysical
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) : RegScalingBand :=
  toScalingBand (rgGapPersistence_of_trueMarginPhysical T E)

/-- **THE φ⁴ → YM BRIDGE.**  The YM continuum physical-gap floor `physGapMin` is
strictly positive, GIVEN the additive-erosion carrier `TrueMarginRecursionPhysical`
(and the non-Clay `MarginBandEnvelope`), over the SAME `RegScalingBand` pipeline
φ⁴ validated.  This is `floorWitness_pos` transported through the identical
`toScalingBand` reduction — the sole YM delta is the (uninhabited) carrier. -/
theorem physGapMin_pos_of_trueMarginPhysical
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) :
    (0 : Q') < (scalingBand_of_trueMarginPhysical T E).physGapMin :=
  physGapMin_pos_of_persistence (rgGapPersistence_of_trueMarginPhysical T E)

/-- The bridge's positive floor is `floorWitness` — the genuine rational witness
of the continuum-limit margin `Δ` (`delta_isPositive_witness`).  Non-vacuity:
`physGapMin` is the real margin floor, not a dialed-in placeholder. -/
@[simp] theorem scalingBand_physGapMin
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) :
    (scalingBand_of_trueMarginPhysical T E).physGapMin = T.floorWitness := rfl

/-- **The YM continuum gap SURVIVES `a → 0`, from the carrier.**  Every physical
gap dominates the positive floor `ofQ' floorWitness`, uniformly in the spacing —
the Clay-relevant `liminf physGap ≥ floorWitness > 0`, over the φ⁴-validated
`band_gap_survives`, conditional on the carrier. -/
theorem gap_survives_of_trueMarginPhysical
    (T : TrueMarginRecursionPhysical) (E : MarginBandEnvelope T) (j : Nat) :
    RegularCReal.ofQ' (scalingBand_of_trueMarginPhysical T E).physGapMin
      ≤ RegularCReal.ofQ' ((scalingBand_of_trueMarginPhysical T E).physGap j) :=
  (scalingBand_of_trueMarginPhysical T E).band_gap_survives j

end YMGap.Continuum.Phi4YMBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Phi4YMBridge.delta_isPositive_witness
#print axioms YMGap.Continuum.Phi4YMBridge.floorWitness_le_margin
#print axioms YMGap.Continuum.Phi4YMBridge.physFloor_of_trueMarginPhysical
#print axioms YMGap.Continuum.Phi4YMBridge.massLat_pos
#print axioms YMGap.Continuum.Phi4YMBridge.rgGapPersistence_of_trueMarginPhysical
#print axioms YMGap.Continuum.Phi4YMBridge.rgGapPersistence_floorConst
#print axioms YMGap.Continuum.Phi4YMBridge.rgGapPersistence_floorRate
#print axioms YMGap.Continuum.Phi4YMBridge.scalingBand_of_trueMarginPhysical
#print axioms YMGap.Continuum.Phi4YMBridge.physGapMin_pos_of_trueMarginPhysical
#print axioms YMGap.Continuum.Phi4YMBridge.scalingBand_physGapMin
#print axioms YMGap.Continuum.Phi4YMBridge.gap_survives_of_trueMarginPhysical
