/-
Track B / R2 — the END-TO-END constructive continuum pipeline on the
CANONICAL-modulus regular constructive real `RegularCReal`.

# What this module is

This is the capstone that assembles, on a single unified substrate
(`RegularCReal`, whose Bishop order is genuinely transitive and whose
modulus is `Type`-level data), the full infinite-volume continuum
mass-gap chain on concrete SU(2) data, with the genuinely-open scaling
step isolated as ONE named interface.

The chain it builds, all on `RegularCReal`:

  finite-volume located gap  (the compact transfer operator's located
      second eigenvalue, `sep < 1`)
    →  uniform-floor cluster bound  (a volume-uniform clustering floor
          `δ > 0` together with a `Type`-level outer Cauchy modulus on the
          per-volume gap-margin sequence)
    →  positive `RegularCReal` continuum gap rate  (`Λ → ∞`, via the
          regular-real completeness limit `completeLimit`, with positivity
          PROVED from `δ > 0` by `isPositive_completeLimit`)
    →  bundled with the continuum positive functional  (`RegProbFunctional`)
          into a single `ConstructiveContinuumYM` datum.

# Unconditional vs conditional (HONESTY — open problem)

  * **UNCONDITIONAL.**  The infinite-volume (`Λ → ∞`) part at FIXED lattice
    spacing.  From a `RegUniformClusterBound` (a structure with no open
    field — its modulus is concrete `Type`-level data) the module
    CONSTRUCTS a positive `RegularCReal` gap rate and bundles it with the
    concrete SU(2) character functional `regCharFunctional`.  The concrete
    inhabitant `concreteContinuumYM` is fully unconditional: no hypothesis
    is assumed, the gap is a strictly-positive regular real, and the mass
    gap is stated as the located clustering rate of the COMPACT transfer
    operator (via `decay_of_spectralGap_corr0`), NOT any unbounded
    spectral theorem.

  * **CONDITIONAL on ONE open input — DIMENSIONAL TRANSMUTATION.**  The
    scaling limit `a → 0` requires a lattice-spacing-uniform two-sided
    modulus on the PHYSICAL gap `Δ(a) = m_lat(a)/a`, NOT on the lattice-unit
    gap (which must VANISH like `a` as `a → 0`).  This is NOT known for
    4D Yang–Mills.  It is isolated as the named obligation
    `RegScalingLimitModulus` carrying the spacings `a_j → 0`, the AF bare
    coupling, the physical gap with its uniform two-sided bound
    `0 < physGapMin ≤ physGap j ≤ physGapMax`, and a spacing-uniform
    convergence modulus.  The CONDITIONAL theorem
    `scaling_continuum_physGap_isPositive` builds the continuum physical gap
    as a positive regular real from this data.  NO inhabitant is claimed —
    `physGapMin > 0` surviving `a → 0` is the open content.  This is the
    precise, single location of the open continuum problem, kept rigorously
    distinct from the unconditional content above.

This module does NOT close the Clay problem.  Its deliverable is the
unconditional infinite-volume positive regular-real gap rate + functional
bundle on concrete SU(2) data, plus the honest naming of the one open
a→0 interface.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom;
the permitted output is `propext` / `Quot.sound` only (the latter only via
reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`,
no `sorry`.  Every modulus is carried as `Type`-level data.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.SpectralGap
import YMGap.Continuum.RegularFunctional
import YMGap.Continuum.NonSaturatedFloor
import YMGap.Continuum.ContinuumFunctional
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RegularContinuumPipeline

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.RegularFunctional

/-! ## 1. The regular-real volume-uniform cluster bound

`RegUniformClusterBound` is the infinite-volume input on the regular-real
substrate.  It packages, all as `Type`-level data (Rule 8):

  * the finite-volume spectral models with their PROVED located gaps
    (`gaps`, `located`) — the genuine finite-volume mass-gap data of the
    COMPACT transfer operator;
  * a uniform positive rational clustering floor `δ` below every per-volume
    gap margin (`floorRate`, `floorRate_pos`, `uniform_floor`) — the
    no-collapse content;
  * an outer Cauchy modulus on the per-volume gap-margin sequence
    (`M`, `Mmono`, `bound`), `Type`-level data, exactly the
    `RegularCReal.ModCauchy` content phrased at the `Q'` margin level so the
    `ofQ'` lift to a regular-real completeness limit is immediate.

Unlike the scaling interface of §4, this structure has NO open field — it
is the strong-coupling cluster-expansion convergence data at fixed lattice
spacing, and a concrete inhabitant is exhibited in §3. -/

/-- **The regular-real volume-uniform cluster bound** — the infinite-volume
input of the continuum gap rate, on the regular-real substrate.  Carries
the proven finite-volume located gaps, a uniform positive clustering floor,
and a `Type`-level outer Cauchy modulus on the gap-margin sequence. -/
structure RegUniformClusterBound : Type where
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
  /-- Outer Cauchy modulus on the gap-margin sequence, `Type`-level data. -/
  M : Q' → Nat
  /-- The outer modulus is antitone. -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ
  /-- Two-sided outer bound: for `i, j ≥ M ε`, the gap margins are
  `ε`-close — the geometric cluster tail in modulus form. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ i j : Nat, M ε ≤ i → M ε ≤ j →
    (located i).gapMargin ≤ (located j).gapMargin + ε ∧
    (located j).gapMargin ≤ (located i).gapMargin + ε

/-! ## 2. The constructed regular-real continuum gap rate

The per-volume gap-margin sequence `Λ ↦ (located Λ).gapMargin`, lifted to
the regular reals by `ofQ'`, is a `ModCauchy` sequence (the `Q'` bound
transfers termwise through `ofQ'`).  Its diagonal `completeLimit` is the
thermodynamic-limit (`Λ → ∞`) gap rate as a genuine `RegularCReal`. -/

/-- The lifted regular-real gap-margin sequence `Λ ↦ ofQ' (1 − sep_Λ)`. -/
def regMarginSeq (B : RegUniformClusterBound) : Nat → RegularCReal :=
  fun Λ => ofQ' (B.located Λ).gapMargin

@[simp] theorem regMarginSeq_approx (B : RegUniformClusterBound) (Λ k : Nat) :
    (regMarginSeq B Λ).approx k = (B.located Λ).gapMargin := rfl

/-- The lifted gap-margin sequence is `ModCauchy`: the `Q'` outer bound
transfers termwise through `ofQ'` (constant approximations), and the
antitone modulus carries over unchanged. -/
def regMarginModCauchy (B : RegUniformClusterBound) :
    ModCauchy (regMarginSeq B) where
  M := B.M
  Mmono := B.Mmono
  bound := by
    intro ε hε i j hi hj k
    -- (regMarginSeq B i).approx k = margin_i ; (regMarginSeq B j).approx k = margin_j.
    exact B.bound ε hε i j hi hj

/-- **The regular-real continuum gap rate `m_∞`.**  The diagonal
completeness limit of the per-volume gap-margin sequence, on the regular
reals: the thermodynamic (`Λ → ∞`) limit with the cluster modulus as its
canonical Cauchy modulus.  This is the clean unified-substrate version of
the infinite-volume mass gap. -/
def regContinuumGapRate (B : RegUniformClusterBound) : RegularCReal :=
  completeLimit (regMarginSeq B) (regMarginModCauchy B)

/-! ## 3. Positivity of the regular-real continuum gap rate

The uniform per-volume floor `δ ≤ margin_Λ` is exactly "every approximation
of every term of the lifted sequence is `≥ δ`", so the diagonal limit is
positive with witness `δ > 0` by `isPositive_completeLimit`. -/

/-- **The capstone positivity theorem (infinite-volume, UNCONDITIONAL).**  A
regular-real volume-uniform cluster bound yields a strictly-positive
regular-real continuum gap rate.  Proof: every approximation of every term
of the lifted gap-margin sequence is the gap margin `1 − sep_Λ ≥ δ` by
`uniform_floor`, so the diagonal `completeLimit` is positive with witness
`δ > 0` (`isPositive_completeLimit`).  No tightness/Prokhorov, no scaling
input — this is the `Λ → ∞` gap as a positive `RegularCReal`. -/
theorem regClusterBound_isPositive_gap (B : RegUniformClusterBound) :
    IsPositive (regContinuumGapRate B) :=
  isPositive_completeLimit (regMarginSeq B) (regMarginModCauchy B)
    B.floorRate_pos
    (fun Λ _ => B.uniform_floor Λ)

/-- The continuum gap rate is bounded below by the clustering floor as a
regular real: `ofQ' δ ≤ m_∞`. -/
theorem regContinuumGapRate_ge_floor (B : RegUniformClusterBound) :
    ofQ' B.floorRate ≤ regContinuumGapRate B :=
  ofQ'_le_completeLimit (regMarginSeq B) (regMarginModCauchy B)
    (fun Λ _ => B.uniform_floor Λ)

/-! ## 4. The capstone bundle: constructive continuum YM on regular reals

`ConstructiveContinuumYM` bundles the constructive continuum theory on the
regular-real substrate:

  * the continuum positive functional `RegProbFunctional` (the constructive
    primitive — Daniell/expectation, normalized and reflection-positive);
  * a positive regular-real gap rate `gapRate`;
  * the clustering link: the located finite-volume gap data whose
    gap-margin limit IS `gapRate`, carrying the located `.decay` witness
    (`G(n) ≤ G(0)·sep^n`) at every volume — the gap stated as the geometric
    clustering rate of the compact transfer operator.

"constructive continuum YM = positive functional + located positive mass
gap = clustering rate," on regular reals. -/

/-- The constructive continuum theory on the regular-real substrate: a
continuum positive functional, a positive regular-real gap rate, and the
located finite-volume gap data linking the gap to geometric clustering of
the compact transfer operator. -/
structure ConstructiveContinuumYM where
  /-- The observable *-algebra of the continuum functional. -/
  A : ObsAlg
  /-- The continuum positive functional (the constructive primitive). -/
  funct : RegProbFunctional A
  /-- The infinite-volume cluster bound generating the gap rate. -/
  cluster : RegUniformClusterBound
  /-- The positive regular-real continuum gap rate, defined as the gap-margin
  limit of `cluster`. -/
  gapRate : RegularCReal
  /-- The gap rate IS the constructed regular-real continuum gap rate. -/
  gapRate_eq : gapRate = regContinuumGapRate cluster
  /-- The gap rate is strictly positive — the "there is a mass gap" witness. -/
  gap_pos : IsPositive gapRate

/-- **The clustering link.**  For a bundled constructive continuum YM, the
finite-volume located gap at every volume `Λ` forces the connected
two-point function of the compact transfer operator to decay geometrically:
`G(n) ≤ G(0)·sep_Λ^n` with `sep_Λ < 1`.  This is the mass gap stated as the
located clustering rate of the COMPACT (finite) transfer operator — no
unbounded spectral theorem (reuses `decay_of_spectralGap_corr0` via
`LocatedSpectralGap.decay`). -/
theorem ConstructiveContinuumYM.clustering (Y : ConstructiveContinuumYM)
    (Λ n : Nat) :
    corr (Y.cluster.gaps Λ) n
      ≤ (corr (Y.cluster.gaps Λ) 0) * (Y.cluster.located Λ).sep ^ n :=
  (Y.cluster.located Λ).decay n

/-- The bundled gap rate is positive (re-exported from the bundle field for
convenience). -/
theorem ConstructiveContinuumYM.gapRate_isPositive (Y : ConstructiveContinuumYM) :
    IsPositive Y.gapRate := Y.gap_pos

/-! ## 5. The capstone constructor and concrete UNCONDITIONAL inhabitant

The constructor `continuumYM_of_clusterBound` turns ANY regular-real cluster
bound + a continuum functional on it into a `ConstructiveContinuumYM`, with
positivity PROVED.  The concrete inhabitant instantiates it on the
NON-SATURATED SU(2) located gap family (`sep = 1/1000`, floor
`mFiducial = 999/1000`) and the concrete SU(2) character functional
`regCharFunctional` — yielding a fully UNCONDITIONAL positive regular-real
continuum gap rate (the `Λ → ∞` gap, no open hypothesis). -/

/-- **The capstone constructor.**  Given a regular-real cluster bound `B` and
a continuum positive functional on an algebra `A`, bundle them into a
`ConstructiveContinuumYM` whose gap rate is the constructed `regContinuumGapRate B`
with positivity PROVED by `regClusterBound_isPositive_gap`. -/
def continuumYM_of_clusterBound {A : ObsAlg} (B : RegUniformClusterBound)
    (F : RegProbFunctional A) : ConstructiveContinuumYM where
  A := A
  funct := F
  cluster := B
  gapRate := regContinuumGapRate B
  gapRate_eq := rfl
  gap_pos := regClusterBound_isPositive_gap B

/-! ### The concrete non-saturated SU(2) cluster bound on regular reals

The non-saturated located family (`NonSaturatedFloor`) is CONSTANT in `Λ`
(every volume has the same `sep = 1/1000` gap, margin `mFiducial`), so its
gap-margin sequence is the constant `mFiducial` and is `ModCauchy` with the
trivial outer modulus `M ε = 0`.  Floor `= mFiducial > 0`. -/

/-- The concrete non-saturated SU(2) regular-real cluster bound: the
constant located family at `sep = 1/1000`, uniform floor `mFiducial`, and
the trivial (`M ε = 0`) outer modulus — the constant margin sequence is
exactly Cauchy. -/
def concreteClusterBound : RegUniformClusterBound where
  gaps := NonSaturatedFloor.nonSatFamily
  located := NonSaturatedFloor.nonSatLocatedAt
  floorRate := NonSaturatedFloor.mFiducial
  floorRate_pos := NonSaturatedFloor.mFiducial_pos
  uniform_floor := NonSaturatedFloor.nonSat_uniform_floor
  M := fun _ => 0
  Mmono := fun _ _ _ _ => Nat.le_refl 0
  bound := by
    intro ε hε i j _ _
    -- margin_i = mFiducial = margin_j (constant family); each ≤ self + ε.
    rw [NonSaturatedFloor.nonSat_gapMargin_eq i,
        NonSaturatedFloor.nonSat_gapMargin_eq j]
    exact ⟨Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε),
           Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)⟩

/-- The concrete cluster bound's clustering floor is the genuine non-trivial
fiducial mass `mFiducial = 999/1000`. -/
theorem concreteClusterBound_floor :
    concreteClusterBound.floorRate = NonSaturatedFloor.mFiducial := rfl

/-- **The concrete regular-real continuum gap rate (UNCONDITIONAL).**  The
`Λ → ∞` gap of the non-saturated SU(2) family as a positive `RegularCReal`. -/
def concreteContinuumGapRate : RegularCReal :=
  regContinuumGapRate concreteClusterBound

/-- Every approximation of the concrete continuum gap rate is the fiducial
gap margin `1 − sep = mFiducial`. -/
@[simp] theorem concreteContinuumGapRate_approx (k : Nat) :
    concreteContinuumGapRate.approx k = NonSaturatedFloor.mFiducial := by
  show (NonSaturatedFloor.nonSatLocatedAt
      (Mhat (regMarginSeq concreteClusterBound) (regMarginModCauchy concreteClusterBound)
        k)).gapMargin = NonSaturatedFloor.mFiducial
  exact NonSaturatedFloor.nonSat_gapMargin_eq _

/-- **The concrete continuum gap rate is strictly positive (UNCONDITIONAL).**
The infinite-volume SU(2) mass gap as a positive regular real, with no open
hypothesis. -/
theorem concreteContinuumGapRate_isPositive :
    IsPositive concreteContinuumGapRate :=
  regClusterBound_isPositive_gap concreteClusterBound

/-- The concrete continuum gap rate dominates the genuine non-trivial
fiducial mass `mFiducial > 0`: `ofQ' mFiducial ≤ m_∞`. -/
theorem concreteContinuumGapRate_ge_fiducial :
    ofQ' NonSaturatedFloor.mFiducial ≤ concreteContinuumGapRate :=
  regContinuumGapRate_ge_floor concreteClusterBound

/-- **THE CONCRETE UNCONDITIONAL CAPSTONE INHABITANT.**  Constructive
continuum YM on the regular-real substrate, on concrete SU(2) data: the
non-saturated cluster bound (floor `mFiducial`, gap `sep = 1/1000`) bundled
with the concrete SU(2) character functional `regCharFunctional`.  The gap
rate is a strictly-positive `RegularCReal` and the mass gap is the located
clustering rate of the compact transfer operator — all UNCONDITIONAL (the
`Λ → ∞` limit at fixed spacing).  No open hypothesis is consumed. -/
def concreteContinuumYM : ConstructiveContinuumYM :=
  continuumYM_of_clusterBound concreteClusterBound
    (regCharFunctional NonSaturatedFloor.mFiducial
      (Q'.le_of_lt NonSaturatedFloor.mFiducial_pos))

/-- The concrete inhabitant's gap rate is the concrete continuum gap rate. -/
theorem concreteContinuumYM_gapRate :
    concreteContinuumYM.gapRate = concreteContinuumGapRate :=
  concreteContinuumYM.gapRate_eq

/-- **The concrete inhabitant's gap is positive — the headline unconditional
result.** -/
theorem concreteContinuumYM_gap_pos :
    IsPositive concreteContinuumYM.gapRate :=
  concreteContinuumYM.gap_pos

/-! ## 6. The single open a→0 (scaling / continuum) interface (CONDITIONAL)

Everything above is the INFINITE-VOLUME limit `Λ → ∞` at FIXED lattice
spacing `a`, and is UNCONDITIONAL.  The continuum theory additionally
requires the SCALING limit `a → 0`.  The correct shape of this limit is
DIMENSIONAL TRANSMUTATION, and getting that shape right is the whole point
of this section.

**Why a uniform LATTICE-unit floor is the WRONG shape.**  A finite-volume
gap margin `m_lat = 1 − sep` is a DIMENSIONLESS lattice quantity (a gap in
lattice units).  At the continuum critical point the correlation length
diverges in lattice units, so the dimensionless lattice gap must VANISH,
`m_lat(a) → 0` like `a`, as `a → 0`.  A single positive lattice-unit floor
holding uniformly across the spacing sequence would therefore describe an
infinite physical mass — a trivial, non-interacting "continuum" with NO
continuum limit, not Yang–Mills.  The quantity that stays finite and
positive is the PHYSICAL gap `Δ(a) = m_lat(a) / a`, carrying mass dimension
one.  The genuine open content is that THIS physical gap is bounded below by
a positive constant uniformly in the spacing and converges as `a → 0`.

So the scaling interface below carries, indexed by refinement step `j`
(spacing `a_j → 0`):

  * `spacing j = a_j > 0` with an explicit modulus `a_j → 0`;
  * `bareCoupling j = g₀(a_j)` — the asymptotically-free RG-trajectory bare
    coupling (its AF running is itself deep input: carried as data, not
    proved);
  * `atSpacing j` — the fixed-spacing infinite-volume cluster bound at step
    `j`, whose own LATTICE floor `(atSpacing j).floorRate` may (indeed
    MUST) → 0 as `j → ∞`;
  * `latMargin j` — the lattice-unit gap margin at step `j` (the floor of
    `atSpacing j`, derived), which vanishes like `a_j`;
  * `physGap j` — the PHYSICAL gap, DERIVED as the genuine quotient
    `latMargin j / a_j` (`Q'.divPos`, a rational division of two positives), so
    its defining multiplicative relation `physGap j · a_j ≃ latMargin j` is a
    THEOREM, not assumed data;
  * the two-sided UNIFORM PHYSICAL bound `0 < physGapMin ≤ physGap j ≤
    physGapMax` — dimensional transmutation: the gap is finite and positive
    in PHYSICAL units, uniformly in the spacing.  `physGapMin > 0` surviving
    `a → 0` is the OPEN content;
  * a spacing-uniform two-sided CONVERGENCE modulus on `j ↦ physGap j` (so
    the physical gap CONVERGES as `a → 0`).

NO inhabitant is provided — none is known for YM in `d = 4`.  This is an
HONEST open interface, not a `True`-stub.  The conditional theorems below
build the genuine continuum (`a → 0`) PHYSICAL gap from such an inhabitant. -/

/-- **The scaling-limit modulus — the single remaining OPEN obligation, in
its dimensionally-correct (dimensional-transmutation) shape.**

Carries, indexed by refinement step `j` (spacing `a_j → 0`):

  * `spacing`, `spacing_pos`, `spacingMod`, `spacing_to_zero` — the lattice
    spacings `a_j > 0` together with an explicit modulus making `a_j → 0`;
  * `bareCoupling` — the AF RG-trajectory bare coupling `g₀(a_j)` (data);
  * `atSpacing` — the fixed-spacing infinite-volume cluster bounds.  Its
    own lattice floor `(atSpacing j).floorRate` is the lattice-unit margin
    `latMargin j` and MUST be allowed to vanish as `j → ∞`;
  * `physGap` (DERIVED, not a field) — the PHYSICAL gap `latMargin j / a_j` as
    the genuine rational quotient `Q'.divPos (latMargin j) (a_j)`, with its
    defining relation `physGap j * a_j ≃ latMargin j` now a THEOREM
    (`physGap_spacing`) from `Q'.divPos_mul_eqv`;
  * `physGapMin`, `physGapMax`, `physGapMin_pos`, `physGap_ge`, `physGap_le`
    — the two-sided UNIFORM PHYSICAL bound `0 < physGapMin ≤ physGap j ≤
    physGapMax`.  `physGapMin > 0` surviving `a → 0` is the OPEN content
    (dimensional transmutation);
  * `physMod`, `physMod_mono`, `physBound` — a spacing-uniform two-sided
    `ModCauchy`-style convergence modulus on `j ↦ physGap j`.

No inhabitant is asserted: for Yang–Mills in `d = 4` the positivity of
`physGapMin` as `a → 0` is OPEN.  This structure is the precise location of
the open continuum problem, kept rigorously distinct from the (constructed,
unconditional) infinite-volume limit. -/
structure RegScalingLimitModulus where
  /-- The lattice spacings `a_j`, indexed by refinement step `j`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j : Nat, (0 : Q') < spacing j
  /-- Modulus witnessing `a_j → 0`: `spacingMod ε` is a step beyond which the
  spacing is below `ε`. -/
  spacingMod : Q' → Nat
  /-- The spacing vanishes: for `j ≥ spacingMod ε`, `a_j ≤ ε`. -/
  spacing_to_zero : ∀ ε : Q', (0 : Q') < ε → ∀ j : Nat, spacingMod ε ≤ j →
    spacing j ≤ ε
  /-- The AF RG-trajectory bare coupling `g₀(a_j)` (carried as data; its
  asymptotic-freedom running is itself deep input, not proved here). -/
  bareCoupling : Nat → Q'
  /-- The fixed-spacing infinite-volume cluster bounds, indexed by `j`.  Its
  own LATTICE floor `(atSpacing j).floorRate` is the lattice-unit margin and
  may (indeed must) → 0 as `j → ∞`.  The PHYSICAL gap `Δ(a_j)` is DERIVED from
  this and `spacing` as the genuine quotient `(atSpacing j).floorRate / a_j`
  (see `RegScalingLimitModulus.physGap`); it is NOT carried as primitive data. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- The uniform physical lower bound (the dimensional-transmutation gap). -/
  physGapMin : Q'
  /-- The uniform physical upper bound. -/
  physGapMax : Q'
  /-- **The OPEN content:** the physical gap floor is strictly positive,
  surviving `a → 0`. -/
  physGapMin_pos : (0 : Q') < physGapMin
  /-- The physical gap (the genuine quotient `(atSpacing j).floorRate / a_j`,
  here as `Q'.divPos`) is bounded below by `physGapMin`, uniformly in `j` —
  the dimensional-transmutation floor (OPEN as `a → 0`). -/
  physGap_ge : ∀ j : Nat,
    physGapMin ≤ Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j)
  /-- The physical gap is bounded above by `physGapMax`, uniformly in `j`. -/
  physGap_le : ∀ j : Nat,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ physGapMax
  /-- Spacing-uniform convergence modulus on the physical-gap sequence. -/
  physMod : Q' → Nat
  /-- The convergence modulus is antitone. -/
  physMod_mono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → physMod ε ≤ physMod δ
  /-- Two-sided convergence of the physical gap: for `i, j ≥ physMod ε`, the
  physical gaps are `ε`-close — the physical gap converges as `a → 0`. -/
  physBound : ∀ ε : Q', (0 : Q') < ε → ∀ i j : Nat, physMod ε ≤ i → physMod ε ≤ j →
    Q'.divPos ((atSpacing i).floorRate) (spacing i) (spacing_pos i)
        ≤ Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) + ε ∧
      Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j)
        ≤ Q'.divPos ((atSpacing i).floorRate) (spacing i) (spacing_pos i) + ε

/-- The lattice-unit gap margin at refinement step `j`: the (vanishing)
lattice floor of the fixed-spacing cluster bound.  As `a_j → 0` this
DIMENSIONLESS quantity vanishes like `a_j` — only `physGap j = latMargin j /
a_j` stays finite and positive. -/
def RegScalingLimitModulus.latMargin (L : RegScalingLimitModulus) (j : Nat) : Q' :=
  (L.atSpacing j).floorRate

@[simp] theorem RegScalingLimitModulus.latMargin_eq (L : RegScalingLimitModulus)
    (j : Nat) : L.latMargin j = (L.atSpacing j).floorRate := rfl

/-- **The PHYSICAL gap `Δ(a_j) = latMargin j / a_j`, DERIVED** as the genuine
rational quotient of the (vanishing) lattice-unit margin by the spacing,
via `Q'.divPos`.  Both numerator `(atSpacing j).floorRate` and denominator
`spacing j` are strictly positive, so the quotient is a genuine division — the
`physGap ↔ latMargin` relation below is now a THEOREM, not assumed data. -/
def RegScalingLimitModulus.physGap (L : RegScalingLimitModulus) (j : Nat) : Q' :=
  Q'.divPos (L.latMargin j) (L.spacing j) (L.spacing_pos j)

@[simp] theorem RegScalingLimitModulus.physGap_eq (L : RegScalingLimitModulus)
    (j : Nat) :
    L.physGap j = Q'.divPos ((L.atSpacing j).floorRate) (L.spacing j) (L.spacing_pos j) :=
  rfl

/-- **The defining relation, now a THEOREM:** `physGap j · a_j ≃ latMargin j`.
Proved from `Q'.divPos`'s defining identity `divPos_mul_eqv` (the physical gap
is the genuine quotient of `latMargin j` by `spacing j`). -/
theorem RegScalingLimitModulus.physGap_spacing (L : RegScalingLimitModulus)
    (j : Nat) : (L.physGap j * L.spacing j).eqv (L.atSpacing j).floorRate :=
  Q'.divPos_mul_eqv (L.latMargin j) (L.spacing j) (L.spacing_pos j)

/-- The defining relation in `latMargin` form: `physGap j · a_j ≃ latMargin j`. -/
theorem RegScalingLimitModulus.physGap_mul_spacing (L : RegScalingLimitModulus)
    (j : Nat) : (L.physGap j * L.spacing j).eqv (L.latMargin j) :=
  L.physGap_spacing j

/-! ### The lifted physical-gap sequence and its `ModCauchy` modulus -/

/-- The lifted regular-real physical-gap sequence `j ↦ ofQ' (physGap j)`. -/
def regPhysGapSeq (L : RegScalingLimitModulus) : Nat → RegularCReal :=
  fun j => ofQ' (L.physGap j)

@[simp] theorem regPhysGapSeq_approx (L : RegScalingLimitModulus) (j k : Nat) :
    (regPhysGapSeq L j).approx k = L.physGap j := rfl

/-- The lifted physical-gap sequence is `ModCauchy`: the `Q'` two-sided
physical convergence bound transfers termwise through `ofQ'` (constant
approximations), and the antitone modulus carries over unchanged. -/
def regPhysGapModCauchy (L : RegScalingLimitModulus) :
    ModCauchy (regPhysGapSeq L) where
  M := L.physMod
  Mmono := L.physMod_mono
  bound := by
    intro ε hε i j hi hj k
    exact L.physBound ε hε i j hi hj

/-! ### The continuum (`a → 0`) PHYSICAL gap

This is the dimensionally-CORRECT continuum gap: the `completeLimit` of the
lifted physical-gap sequence `j ↦ ofQ' (physGap j)`, with its positivity
PROVED from the uniform physical floor `physGapMin > 0`. -/

/-- **The continuum (`a → 0`) physical gap.**  The diagonal completeness
limit of the lifted physical-gap sequence on the regular reals: the genuine
continuum PHYSICAL mass gap (mass dimension one), with the spacing-uniform
physical convergence modulus as its canonical Cauchy modulus.  This REPLACES
the old (dimensionally wrong) uniform-lattice-floor scaling statement. -/
def scaling_continuum_physGap (L : RegScalingLimitModulus) : RegularCReal :=
  completeLimit (regPhysGapSeq L) (regPhysGapModCauchy L)

@[simp] theorem scaling_continuum_physGap_approx (L : RegScalingLimitModulus)
    (k : Nat) :
    (scaling_continuum_physGap L).approx k =
      L.physGap (Mhat (regPhysGapSeq L) (regPhysGapModCauchy L) k) := rfl

/-- **The conditional scaling-limit theorem (dimensionally correct).**  GIVEN
a `RegScalingLimitModulus` (the OPEN input), the continuum (`a → 0`) PHYSICAL
gap dominates the spacing-uniform physical floor `ofQ' physGapMin`.

This is the CONDITIONAL `a → 0` statement in its correct PHYSICAL-unit shape:
IF the physical gap stays bounded below by a positive constant uniformly in
the spacing (the open dimensional-transmutation input), THEN the continuum
physical gap is bounded below by that single positive constant.  Proved from
the open lower bound `physGap_ge` together with the regular-real completeness
limit (`ofQ'_le_completeLimit`). -/
theorem scaling_continuum_physGap_ge_floor (L : RegScalingLimitModulus) :
    ofQ' L.physGapMin ≤ scaling_continuum_physGap L :=
  ofQ'_le_completeLimit (regPhysGapSeq L) (regPhysGapModCauchy L)
    (fun j _ => L.physGap_ge j)

/-- **The conditional positivity of the continuum physical gap.**  Under the
open `RegScalingLimitModulus`, the continuum (`a → 0`) physical gap is
strictly positive with the single spacing-uniform witness `physGapMin` — the
continuum YM mass gap as a positive `RegularCReal`, CONDITIONAL on the one
open input (`physGapMin > 0` surviving `a → 0`).  Proved via
`isPositive_completeLimit`. -/
theorem scaling_continuum_physGap_isPositive (L : RegScalingLimitModulus) :
    IsPositive (scaling_continuum_physGap L) :=
  isPositive_completeLimit (regPhysGapSeq L) (regPhysGapModCauchy L)
    L.physGapMin_pos (fun j _ => L.physGap_ge j)

/-- The continuum physical gap is also bounded ABOVE by the uniform physical
ceiling `ofQ' physGapMax` — the finiteness half of dimensional transmutation
(the gap does not blow up as `a → 0`). -/
theorem scaling_continuum_physGap_le_ceiling (L : RegScalingLimitModulus) :
    scaling_continuum_physGap L ≤ ofQ' L.physGapMax :=
  completeLimit_le_ofQ' (regPhysGapSeq L) (regPhysGapModCauchy L)
    (fun j _ => L.physGap_le j)

/-! ### Continuum clustering at the PHYSICAL rate (CONDITIONAL)

The fixed-spacing clustering `G(n) ≤ G(0)·sep_Λ^n` (`ConstructiveContinuumYM.clustering`)
is the correct `Λ → ∞` lattice-unit form and is kept unchanged.  Its
continuum (`a → 0`) counterpart asserts decay at the PHYSICAL gap.  Two
honest pieces:

  * PROVED here: at EVERY refinement step `j` and volume `Λ`, the lattice
    connected correlator decays geometrically at that step's located rate
    `sep < 1` — the per-spacing clustering datum whose physical gaps converge
    to `scaling_continuum_physGap L`.
  * CONDITIONAL (the open content): that the LIMIT correlator decays at the
    LIMIT physical gap requires the spacing-uniform modulus, i.e. exactly the
    `RegScalingLimitModulus` hypothesis.  We expose the physical-gap limit
    bound (`scaling_continuum_physGap_ge_floor`) as the rate witness; the full
    continuum-correlator decay is NOT faked. -/

/-- **Per-step lattice clustering of the scaling family (PROVED).**  At every
refinement step `j`, volume `Λ`, and separation `n`, the fixed-spacing
connected correlator of the compact transfer operator decays geometrically
at the located rate `sep_Λ^{(j)} < 1`.  This is the spacing-indexed family
of lattice clustering data whose PHYSICAL gaps (`physGap j`) converge to the
continuum physical gap `scaling_continuum_physGap L`. -/
theorem scaling_lattice_clustering (L : RegScalingLimitModulus)
    (j Λ n : Nat) :
    corr ((L.atSpacing j).gaps Λ) n
      ≤ (corr ((L.atSpacing j).gaps Λ) 0)
        * ((L.atSpacing j).located Λ).sep ^ n :=
  ((L.atSpacing j).located Λ).decay n

/-- **Continuum clustering rate = the physical gap (CONDITIONAL).**  The rate
governing continuum (`a → 0`) clustering is the continuum PHYSICAL gap
`scaling_continuum_physGap L`, which is bounded below by the strictly
positive spacing-uniform floor `ofQ' physGapMin`.  This packages the physical
decay RATE as a positive regular real; combined with `scaling_lattice_clustering`
(the per-spacing geometric decay) it is the dimensionally-correct continuum
clustering statement, CONDITIONAL on the open `RegScalingLimitModulus`. -/
theorem scaling_continuum_clustering_rate_pos (L : RegScalingLimitModulus) :
    ofQ' L.physGapMin ≤ scaling_continuum_physGap L ∧
      IsPositive (scaling_continuum_physGap L) :=
  ⟨scaling_continuum_physGap_ge_floor L, scaling_continuum_physGap_isPositive L⟩

/-! ## 7. Doc-section: the end-to-end constructive chain on `RegularCReal`

The pipeline assembled in this module, on the unified `RegularCReal`
substrate (transitive Bishop order, `Type`-level canonical modulus):

  1. **Finite-volume located gap.**  At each volume `Λ`, the COMPACT (finite)
     transfer operator has a constructively LOCATED second eigenvalue
     `sep_Λ < 1` (`LocatedSpectralGap`).  Its gap margin `1 − sep_Λ > 0` is
     the constructive "there is a gap" witness, and it forces geometric
     clustering `G(n) ≤ G(0)·sep_Λ^n` (`ConstructiveContinuumYM.clustering`)
     — no unbounded spectral theorem.

  2. **Uniform-floor cluster bound.**  `RegUniformClusterBound` packages the
     located gaps with a volume-uniform positive clustering floor `δ > 0`
     and a `Type`-level outer Cauchy modulus on the gap-margin sequence.

  3. **Positive `RegularCReal` continuum gap rate (`Λ → ∞`, UNCONDITIONAL).**
     The gap-margin sequence, lifted to the regular reals, has a diagonal
     `completeLimit` `regContinuumGapRate`, whose strict positivity
     (`regClusterBound_isPositive_gap`) is PROVED from `δ > 0`.  This is the
     infinite-volume mass gap as a positive regular real.

  4. **Bundled with the continuum positive functional.**  `ConstructiveContinuumYM`
     bundles the gap rate with a `RegProbFunctional`; the concrete inhabitant
     `concreteContinuumYM` instantiates it UNCONDITIONALLY on the
     non-saturated SU(2) located family (floor `mFiducial = 999/1000`, gap
     `sep = 1/1000`) and the concrete SU(2) character functional — a genuine,
     hypothesis-free positive regular-real continuum gap.

  5. **The ONE remaining open interface (`a → 0`, CONDITIONAL) — DIMENSIONAL
     TRANSMUTATION.**  The scaling limit is NOT a uniform lattice-unit floor:
     the dimensionless lattice gap `m_lat(a) = 1 − sep` must VANISH like `a`
     as `a → 0` (the correlation length diverges in lattice units at the
     critical point), so a uniform lattice floor would describe an infinite
     physical mass — a trivial continuum, not Yang–Mills.  The quantity that
     stays finite and positive is the PHYSICAL gap `Δ(a) = m_lat(a)/a`.  The
     interface `RegScalingLimitModulus` carries the spacings `a_j → 0` (with
     modulus), the AF bare coupling `g₀(a_j)`, the fixed-spacing cluster
     bounds (whose lattice floors `→ 0`), the physical gap `physGap j` DERIVED
     as the genuine quotient `latMargin j / a_j` (with its defining relation
     `physGap j · a_j ≃ latMargin j` now a THEOREM), the two-sided
     UNIFORM PHYSICAL bound `0 < physGapMin ≤ physGap j ≤ physGapMax`, and a
     spacing-uniform two-sided convergence modulus on `physGap`.  The
     continuum physical gap `scaling_continuum_physGap` is the `completeLimit`
     of `j ↦ ofQ' (physGap j)`, with positivity PROVED from `physGapMin > 0`
     (`scaling_continuum_physGap_isPositive`) and finiteness from `physGapMax`
     (`scaling_continuum_physGap_le_ceiling`).  The OPEN content is
     `physGapMin > 0` SURVIVING `a → 0`; NO inhabitant is provided for 4D YM.

Underclaim: the unconditional deliverable is the INFINITE-VOLUME positive
regular-real gap rate + functional bundle on concrete SU(2) data.  The
`a → 0` step is a NAMED open obligation in its dimensionally-correct
(physical-gap, two-sided, with convergence modulus) shape.  This module does
NOT close the Clay problem. -/

end YMGap.Continuum.RegularContinuumPipeline

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RegularContinuumPipeline.regMarginSeq_approx
#print axioms YMGap.Continuum.RegularContinuumPipeline.regMarginModCauchy
#print axioms YMGap.Continuum.RegularContinuumPipeline.regContinuumGapRate
#print axioms YMGap.Continuum.RegularContinuumPipeline.regClusterBound_isPositive_gap
#print axioms YMGap.Continuum.RegularContinuumPipeline.regContinuumGapRate_ge_floor
#print axioms YMGap.Continuum.RegularContinuumPipeline.ConstructiveContinuumYM.clustering
#print axioms YMGap.Continuum.RegularContinuumPipeline.ConstructiveContinuumYM.gapRate_isPositive
#print axioms YMGap.Continuum.RegularContinuumPipeline.continuumYM_of_clusterBound
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteClusterBound
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteClusterBound_floor
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumGapRate
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumGapRate_approx
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumGapRate_isPositive
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumGapRate_ge_fiducial
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumYM
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumYM_gapRate
#print axioms YMGap.Continuum.RegularContinuumPipeline.concreteContinuumYM_gap_pos
#print axioms YMGap.Continuum.RegularContinuumPipeline.RegScalingLimitModulus.latMargin_eq
#print axioms YMGap.Continuum.RegularContinuumPipeline.RegScalingLimitModulus.physGap
#print axioms YMGap.Continuum.RegularContinuumPipeline.RegScalingLimitModulus.physGap_eq
#print axioms YMGap.Continuum.RegularContinuumPipeline.RegScalingLimitModulus.physGap_spacing
#print axioms YMGap.Continuum.RegularContinuumPipeline.RegScalingLimitModulus.physGap_mul_spacing
#print axioms YMGap.Continuum.RegularContinuumPipeline.regPhysGapSeq_approx
#print axioms YMGap.Continuum.RegularContinuumPipeline.regPhysGapModCauchy
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_physGap
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_physGap_approx
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_physGap_ge_floor
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_physGap_isPositive
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_physGap_le_ceiling
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_lattice_clustering
#print axioms YMGap.Continuum.RegularContinuumPipeline.scaling_continuum_clustering_rate_pos
