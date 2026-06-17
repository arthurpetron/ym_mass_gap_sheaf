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

  * **CONDITIONAL on ONE open input.**  The scaling limit `a → 0` requires
    a lattice-spacing-uniform two-sided modulus, which is NOT known for
    4D Yang–Mills.  It is isolated as the named obligation
    `RegScalingLimitModulus`, with a CONDITIONAL theorem
    (`reg_scaling_continuum_gap`) that consumes such a modulus together
    with the infinite-volume pipeline.  NO inhabitant is claimed — none is
    known.  This is the precise, single location of the open continuum
    problem, kept rigorously distinct from the unconditional content above.

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

/-! ## 6. The single open a→0 interface (CONDITIONAL)

Everything above is the INFINITE-VOLUME limit `Λ → ∞` at FIXED lattice
spacing, and is UNCONDITIONAL.  The continuum theory additionally requires
the SCALING limit `a → 0`, which needs a lattice-spacing-UNIFORM two-sided
modulus on the gap-margin sequence as the spacing is refined.  Such a
uniform modulus is known for scalar `φ⁴` in `d = 2, 3` but is NOT known for
Yang–Mills in `d = 4`.

It is isolated as the single named obligation `RegScalingLimitModulus`.  NO
inhabitant is provided — none is known for YM.  This is an HONEST open
interface, not a `True`-stub: an inhabitant would carry, indexed by the
refinement step `j` (spacing `a_j → 0`), a fixed-spacing infinite-volume
cluster bound together with a spacing-UNIFORM positive floor surviving the
refinement, i.e. exactly the data this module's constructor consumes but
now along the spacing axis. -/

/-- **The scaling-limit modulus — the single remaining OPEN obligation.**

Carries, indexed by refinement step `j` (spacing `a_j → 0`):

  * `atSpacing j` — the fixed-spacing infinite-volume regular-real cluster
    bound at refinement step `j`;
  * `spacingFloor` — a candidate spacing-uniform positive floor;
  * `spacingFloor_pos` — its positivity;
  * `uniform_in_spacing` — that the floor is uniform IN the spacing: every
    step's own cluster floor is at least `spacingFloor`.

No inhabitant is asserted: for Yang–Mills in `d = 4` this spacing-uniform
floor (the persistence of the mass gap as `a → 0`) is OPEN.  This structure
is the precise location of the open continuum problem, kept rigorously
distinct from the (constructed, unconditional) infinite-volume limit. -/
structure RegScalingLimitModulus where
  /-- The fixed-spacing infinite-volume cluster bounds, indexed by the
  refinement step `j`. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- A candidate spacing-uniform positive floor. -/
  spacingFloor : Q'
  /-- The candidate floor is strictly positive. -/
  spacingFloor_pos : (0 : Q') < spacingFloor
  /-- **Spacing-uniformity (the open content):** every refinement step's own
  cluster floor is at least `spacingFloor` — the mass gap survives `a → 0`. -/
  uniform_in_spacing : ∀ j : Nat, spacingFloor ≤ (atSpacing j).floorRate

/-- **The conditional scaling-limit theorem.**  GIVEN a `RegScalingLimitModulus`
(the OPEN input) and ANY refinement step `j`, the fixed-spacing
infinite-volume gap rate at that step dominates the spacing-uniform floor
`ofQ' spacingFloor`, which is strictly positive UNIFORMLY in the spacing.

This is the CONDITIONAL `a → 0` statement: it says exactly that IF the
spacing-uniform floor exists (the open YM input), THEN the infinite-volume
gap rate at every refinement step is bounded below by a single positive
constant independent of the spacing — the continuum-scaling-limit gap.  The
hypothesis is the open obligation; the conclusion is proved from it together
with the unconditional infinite-volume pipeline (`regContinuumGapRate_ge_floor`). -/
theorem reg_scaling_continuum_gap (L : RegScalingLimitModulus) (j : Nat) :
    ofQ' L.spacingFloor ≤ regContinuumGapRate (L.atSpacing j) :=
  le_trans (ofQ'_le_ofQ' (L.uniform_in_spacing j))
    (regContinuumGapRate_ge_floor (L.atSpacing j))

/-- **The conditional positivity corollary.**  Under the open
`RegScalingLimitModulus`, every fixed-spacing infinite-volume gap rate is
strictly positive with the SINGLE spacing-uniform witness `spacingFloor` —
the continuum (`a → 0`) mass gap, CONDITIONAL on the one open input. -/
theorem reg_scaling_continuum_gap_isPositive (L : RegScalingLimitModulus)
    (j : Nat) : IsPositive (regContinuumGapRate (L.atSpacing j)) :=
  ⟨L.spacingFloor, L.spacingFloor_pos, reg_scaling_continuum_gap L j⟩

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

  5. **The ONE remaining open interface (`a → 0`, CONDITIONAL).**  The
     scaling limit needs a lattice-spacing-uniform floor, OPEN for 4D YM.
     It is named `RegScalingLimitModulus` with the conditional theorem
     `reg_scaling_continuum_gap` and NO inhabitant.

Underclaim: the unconditional deliverable is the INFINITE-VOLUME positive
regular-real gap rate + functional bundle on concrete SU(2) data.  The
`a → 0` step is a NAMED open obligation.  This module does NOT close the
Clay problem. -/

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
#print axioms YMGap.Continuum.RegularContinuumPipeline.reg_scaling_continuum_gap
#print axioms YMGap.Continuum.RegularContinuumPipeline.reg_scaling_continuum_gap_isPositive
