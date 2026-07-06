/-
Track B1 — the FIRST concrete inhabitant of the a→0 continuum band
(`RegularContinuumPipeline.RegScalingBand`) that genuinely VARIES with the
lattice spacing: a lattice φ⁴ (d = 2,3) validation model.

# What this module is — and, sharply, what it is NOT

`RegScalingBand` is the modulus-free two-sided a→0 obligation of the continuum
pipeline: spacings `a_j → 0`, per-spacing fixed-spacing cluster bounds, the
DERIVED physical gap `Δ(a_j) = latMargin j / a_j` (`Q'.divPos`), and the
uniform two-sided band `0 < physGapMin ≤ physGap j ≤ physGapMax`.  Until now the
ONLY concrete `RegUniformClusterBound` inhabitant in the project
(`concreteContinuumYM` / `concreteClusterBound`) is CONSTANT in volume
(`M ε = 0`) and has NO scaling structure at all — nothing concrete ever
exercised the `divPos` physical-gap derivation across a spacing sequence, nor
the two-sided band.

This module supplies that missing concrete inhabitant on a MODEL problem —
lattice φ⁴ in d = 2,3 with a FIXED PHYSICAL MASS — validating the
spacing-uniform continuum PLUMBING before the YM-specific attack.  Concretely:

  * spacings `a_j = 1/(j+2) → 0`  (`Q'.invSucc (j+1)`);
  * at each `j`, a fixed-spacing cluster bound whose LATTICE floor
    `latMargin j = c_j · a_j` VANISHES like `a_j` (near-critical lattice:
    `sep_j = 1 − latMargin j → 1`), with `c_j = 1 + 1/(j+2)` the tuned physical
    gap;
  * the DERIVED physical gap `physGap j = latMargin j / a_j ≃ c_j` sits in the
    band `[physGapMin, physGapMax] = [1, 3/2]`, `physGapMin = 1 > 0`.

The φ⁴ transfer data is supplied as RATIONAL cluster-expansion envelopes — the
same honesty convention as the SU(2) fiducial `NonSaturatedFloor` (which posts
`mFiducial = 999/1000` rather than computing SU(2) integrals).  We do NOT build
φ⁴ path integrals; deriving these rationals from the φ⁴ action would need the
from-scratch constructive-integral layer, which is the deliberate boundary of
this validation (Glimm–Jaffe–Spencer / Feldman–Osterwalder / Bauerschmidt–
Dagallier arXiv:2202.02295 supply the spacing-uniform floor + explicit rate the
rationals stand for).

# HONESTY — this is NOT the Yang–Mills continuum gap

  * **`physGapMin > 0` here is a DIALED-IN BARE MASS, a rational fact.**  φ⁴₂,₃
    is super-renormalizable with a relevant bare mass `m₀²`; one tunes it to
    hold the physical correlation length fixed as `a → 0`.  YM has NO mass
    parameter to dial: its `physGapMin > 0` must come from DIMENSIONAL
    TRANSMUTATION (`Λ_YM = a⁻¹exp(−1/(2β₀g²))`, an open non-perturbative fact).
    This module puts the fixed physical mass in BY HAND.

  * **This validates the PLUMBING, not the physics.**  It does NOT validate
    dimensional transmutation / asymptotic-freedom running: it discharges the
    band through the PLAIN-FLOOR shape, NOT `ofDimensionalTransmutation`
    (`physFloor·aScaling ≤ (1−sep)·∏ρ_dec`) and NOT `DefectGapRecursion`.  It
    exercises NO `∏ρ_dec` decimation product.

  * **It inhabits NO guarded YM Clay-frontier type.**  `RegScalingBand` is a
    generic pipeline structure, not a frontier bundle.  This module deliberately
    does NOT wire the φ⁴ band into `UniformSpacingFloor`, `ClayTarget`,
    `Tier0Scorecard`, `ClayTargetPinned`, or `FrontierDAG`; those stay
    UNINHABITED (`YMGapGuard` reports all five).  A φ⁴ success leaves the YM
    engine — non-perturbative generation of `physGapMin > 0` — exactly as open
    as before, because φ⁴ replaces that engine with a bare mass.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Every quantity is `Q'`/`Type`-level data.
-/

import YMGap.Continuum.RegularContinuumPipeline
import YMGap.Continuum.AFRateCalibration
import YMGap.Constructive.ExpNeg
import YMGap.Continuum.SemicircleConvClosed
import YMGap.Continuum.BernsteinStageData
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.AFExpLift

namespace YMGap.Continuum.Phi4ScalingBand

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RegularContinuumPipeline

/-! ## 0. A small arithmetic helper: `1 − v < 1` for `v > 0`

Self-contained (mirrors `LocatedSpectralGap.one_sub_pos_of_lt_one`), so this
file needs no extra `Continuum` import for the located separator. -/

/-- `0 < v ⟹ 1 − v < 1` (the located separator `sep = 1 − latMargin < 1`). -/
theorem one_sub_lt_one {v : Q'} (h : (0 : Q') < v) : (1 : Q') - v < (1 : Q') := by
  show ((1 : Q') - v).num * ((1 : Q').den : Int) < (1 : Q').num * (((1 : Q') - v).den : Int)
  have hnum : ((1 : Q') - v).num = (1 : Int) * (v.den : Int) + (-v.num) * (1 : Int) := rfl
  have hden : (((1 : Q') - v).den : Int) = (1 : Int) * (v.den : Int) := by
    show (((1 : Q') + (-v)).den : Int) = (1 : Int) * (v.den : Int)
    rw [Q'.add_den_cast (1 : Q') (-v)]; rfl
  rw [hnum, hden]
  have hvn : 0 < v.num := Q'.num_pos_of_pos h
  have hd : (0 : Int) < (v.den : Int) := by exact_mod_cast v.den_pos
  show ((1 : Int) * (v.den : Int) + (-v.num) * (1 : Int)) * ((1 : Q').den : Int)
      < (1 : Q').num * ((1 : Int) * (v.den : Int))
  have hon : (1 : Q').num = 1 := rfl
  have hod : ((1 : Q').den : Int) = 1 := rfl
  rw [hon, hod, Int.one_mul, Int.one_mul, Int.mul_one]
  omega

/-! ## 1. The φ⁴ spacing / physical-mass / lattice-margin sequences

All three are explicit `Q'` sequences (fiducial cluster-expansion envelopes,
NOT computed integrals).  The physical gap `c_j` is TUNED to hold a fixed
physical mass; the lattice margin `latMargin j = c_j · a_j` VANISHES like the
spacing, as the a→0 physics demands. -/

/-- The lattice spacings `a_j = 1/(j+2) → 0` (`Q'.invSucc (j+1)`). -/
def aSeq (j : Nat) : Q' := Q'.invSucc (j + 1)

/-- Each spacing is strictly positive. -/
theorem aSeq_pos (j : Nat) : (0 : Q') < aSeq j := Q'.invSucc_pos (j + 1)

/-- Each spacing is `≤ 1/2` (monotone-decreasing, `a_0 = 1/2`). -/
theorem aSeq_le_half (j : Nat) : aSeq j ≤ Q'.mkPos 1 2 (by decide) :=
  ExpNeg.invSucc_le_of_le (Nat.succ_le_succ (Nat.zero_le j))

/-- **The tuned physical gap** `c_j = 1 + 1/(j+2)`.  Decreasing from `3/2`
towards `1`; the dialed-in bare mass keeps this in a fixed physical band. -/
def cSeq (j : Nat) : Q' := 1 + Q'.invSucc (j + 1)

/-- `c_j > 0`. -/
theorem cSeq_pos (j : Nat) : (0 : Q') < cSeq j :=
  Q'.add_pos (by decide) (Q'.invSucc_pos (j + 1))

/-- `physGapMin = 1 ≤ c_j` (the band floor is met from above). -/
theorem cSeq_ge_one (j : Nat) : (1 : Q') ≤ cSeq j :=
  Q'.add_le_self_of_nonneg 1 (Q'.invSucc (j + 1)) (Q'.le_of_lt (Q'.invSucc_pos (j + 1)))

/-- `c_j ≤ 3/2 = physGapMax` (the band ceiling). -/
theorem cSeq_le_max (j : Nat) : cSeq j ≤ Q'.mkPos 3 2 (by decide) := by
  have h1 : Q'.invSucc (j + 1) ≤ Q'.invSucc 1 :=
    ExpNeg.invSucc_le_of_le (Nat.succ_le_succ (Nat.zero_le j))
  have h2 : (1 : Q') + Q'.invSucc (j + 1) ≤ (1 : Q') + Q'.invSucc 1 :=
    Q'.add_le_add_left 1 _ _ h1
  exact Q'.le_trans' _ _ _ h2 (by decide)

/-- **The lattice-unit gap margin** `latMargin j = c_j · a_j` — the fixed-spacing
cluster floor.  It VANISHES like `a_j` as `j → ∞` (near-critical lattice); only
`physGap j = latMargin j / a_j ≃ c_j` stays finite and positive. -/
def vSeq (j : Nat) : Q' := cSeq j * aSeq j

/-- `latMargin j > 0`. -/
theorem vSeq_pos (j : Nat) : (0 : Q') < vSeq j := Q'.mul_pos (cSeq_pos j) (aSeq_pos j)

/-- `latMargin j ≤ 3/4 < 1` — so `sep_j = 1 − latMargin j ∈ (0,1)` is a genuine
located separator (`c_j ≤ 3/2`, `a_j ≤ 1/2`). -/
theorem vSeq_lt_one (j : Nat) : vSeq j < (1 : Q') := by
  have s1 : cSeq j * aSeq j ≤ Q'.mkPos 3 2 (by decide) * aSeq j :=
    Q'.mul_le_mul_of_nonneg_right (cSeq j) _ (aSeq j) (cSeq_le_max j) (Q'.le_of_lt (aSeq_pos j))
  have s2 : Q'.mkPos 3 2 (by decide) * aSeq j
      ≤ Q'.mkPos 3 2 (by decide) * Q'.mkPos 1 2 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left (aSeq j) _ (Q'.mkPos 3 2 (by decide)) (aSeq_le_half j) (by decide)
  have s3 : Q'.mkPos 3 2 (by decide) * Q'.mkPos 1 2 (by decide) ≤ Q'.mkPos 3 4 (by decide) := by
    decide
  have hle : vSeq j ≤ Q'.mkPos 3 4 (by decide) :=
    Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 s3)
  exact Q'.lt_of_le_of_lt hle (by decide)

/-! ## 2. The per-spacing φ⁴ cluster bound

A generic `RegUniformClusterBound` at floor `v ∈ (0,1)`: one excited mode at
transfer eigenvalue `sep = 1 − v`, constant in volume, floor `v` met with
equality by the gap margin `1 − sep`, trivial outer modulus `M ε = 0` (the
constant-in-volume Cauchy datum at FIXED spacing — the a→0 variation lives in
the band of §3, not here). -/

/-- One excited mode at `sep = 1 − v`, weight `1`. -/
def phi4Model (v : Q') (hlt1 : v < (1 : Q')) : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 1 - v
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => Q'.le_of_lt (one_sub_pos_of_lt_one hlt1)

/-- The located gap at `sep = 1 − v < 1` (genuine, non-degenerate for `v > 0`);
gap margin `1 − sep = 1 − (1 − v) ≃ v`. -/
def phi4Located (v : Q') (hpos : (0 : Q') < v) (hlt1 : v < (1 : Q')) :
    LocatedSpectralGap (phi4Model v hlt1) where
  sep := 1 - v
  sep_lt_one := one_sub_lt_one hpos
  bound := fun _ => Q'.le_refl' (1 - v)

/-- **The per-spacing φ⁴ cluster bound at lattice floor `v`.**  Constant in
volume, floor `v` (met with equality by `gapMargin = 1 − (1 − v) ≃ v`), trivial
outer modulus.  This is the fixed-spacing infinite-volume (`Λ → ∞`) datum. -/
def phi4ClusterBoundOf (v : Q') (hpos : (0 : Q') < v) (hlt1 : v < (1 : Q')) :
    RegUniformClusterBound where
  gaps := fun _ => phi4Model v hlt1
  located := fun _ => phi4Located v hpos hlt1
  floorRate := v
  floorRate_pos := hpos
  uniform_floor := fun _ => Q'.ge_of_eqv (AFRateCalibration.one_sub_one_sub_eqv v)
  M := fun _ => 0
  Mmono := fun _ _ _ _ => Nat.le_refl 0
  bound := fun ε hε _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)⟩

/-- The per-spacing cluster bound's floor is exactly the lattice margin `v`. -/
@[simp] theorem phi4ClusterBoundOf_floor (v : Q') (hpos : (0 : Q') < v) (hlt1 : v < (1 : Q')) :
    (phi4ClusterBoundOf v hpos hlt1).floorRate = v := rfl

/-! ## 3. The headline: the φ⁴ scaling band `Phi4ScalingBand : RegScalingBand`

The first concrete inhabitant of the a→0 band that VARIES with the spacing:
`atSpacing j` has floor `latMargin j = c_j · a_j → 0`, and the derived physical
gap `physGap j = divPos (latMargin j) a_j ≃ c_j ∈ [1, 3/2]` sits in the band
`[physGapMin, physGapMax] = [1, 3/2]` with `physGapMin = 1 > 0`. -/

/-- **THE φ⁴ SCALING BAND.**  A concrete `RegScalingBand` whose lattice floors
`latMargin j = c_j · a_j` vanish like the spacing `a_j → 0`, while the derived
physical gap `physGap j = latMargin j / a_j` stays in the fixed physical band
`[1, 3/2]`.  The band floor `physGapMin = 1 > 0` is a DIALED-IN BARE MASS
(rational fact), discharged through the PLAIN-FLOOR route — NOT dimensional
transmutation.  This inhabits the generic pipeline structure, NOT any guarded
YM frontier type. -/
def phi4ScalingBand : RegScalingBand where
  spacing := aSeq
  spacing_pos := aSeq_pos
  atSpacing := fun j => phi4ClusterBoundOf (vSeq j) (vSeq_pos j) (vSeq_lt_one j)
  physGapMin := 1
  physGapMax := Q'.mkPos 3 2 (by decide)
  physGapMin_pos := by decide
  physGap_ge := fun j =>
    Q'.le_divPos_of_mul_le (vSeq j) (aSeq j) (aSeq_pos j)
      (Q'.mul_le_mul_of_nonneg_right 1 (cSeq j) (aSeq j) (cSeq_ge_one j) (Q'.le_of_lt (aSeq_pos j)))
  physGap_le := fun j =>
    Q'.divPos_le_of_le_mul (vSeq j) (aSeq j) (aSeq_pos j)
      (Q'.mul_le_mul_of_nonneg_right (cSeq j) (Q'.mkPos 3 2 (by decide)) (aSeq j)
        (cSeq_le_max j) (Q'.le_of_lt (aSeq_pos j)))

/-! ### 3.1 The Clay-relevant headlines, FIRED on the φ⁴ band

These are the pipeline's own modulus-free a→0 headlines, now discharged on a
concrete non-degenerate inhabitant (validating that the interface is
downstream-LIVE, not a stub). -/

/-- The physical band floor is strictly positive — FIRED on φ⁴. -/
theorem phi4_band_physGapMin_pos : (0 : Q') < phi4ScalingBand.physGapMin :=
  phi4ScalingBand.band_physGapMin_pos

/-- **"The mass gap survives `a → 0`" — FIRED on the φ⁴ band.**  Every physical
gap dominates `ofQ' 1 > 0`, uniformly in the spacing.  (φ⁴ model: the survival
is a dialed-in bare mass, NOT YM dimensional transmutation.) -/
theorem phi4_band_gap_survives (j : Nat) :
    RegularCReal.ofQ' phi4ScalingBand.physGapMin
      ≤ RegularCReal.ofQ' (phi4ScalingBand.physGap j) :=
  phi4ScalingBand.band_gap_survives j

/-- The physical gap is uniformly bounded above by `ofQ' (3/2)` — the finiteness
half of the band, FIRED on φ⁴. -/
theorem phi4_band_physGap_le (j : Nat) :
    RegularCReal.ofQ' (phi4ScalingBand.physGap j)
      ≤ RegularCReal.ofQ' phi4ScalingBand.physGapMax :=
  phi4ScalingBand.band_physGap_le j

/-! ### 3.2 NON-VACUITY: the physical gap genuinely VARIES with the spacing

The whole point of a φ⁴ inhabitant is that it is not the degenerate
constant-in-volume family.  Here `physGap j ≃ c_j = 1 + 1/(j+2)`, which really
changes with `j` — exhibited at `j = 0` (`physGap ≃ 3/2`) and `j = 1`
(`physGap ≃ 4/3`), two DISTINCT rationals inside the band. -/

/-- **The physical gap equals the tuned physical mass:** `physGap j ≃ c_j`.
Both `divPos`-bounds collapse to `c_j · a_j ≤ c_j · a_j` (`= latMargin j`), so
the quotient is `c_j` up to `Q'` equivalence. -/
theorem phi4_physGap_eqv_c (j : Nat) : (phi4ScalingBand.physGap j).eqv (cSeq j) := by
  show (Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j)).eqv (cSeq j)
  have h1 : Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j) ≤ cSeq j :=
    Q'.divPos_le_of_le_mul (vSeq j) (aSeq j) (aSeq_pos j) (Q'.le_refl' (vSeq j))
  have h2 : cSeq j ≤ Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j) :=
    Q'.le_divPos_of_mul_le (vSeq j) (aSeq j) (aSeq_pos j) (Q'.le_refl' (vSeq j))
  exact Int.le_antisymm h1 h2

/-- `physGap 0 ≃ 3/2` (the physical gap at spacing `a_0 = 1/2`). -/
theorem phi4_physGap_zero : (phi4ScalingBand.physGap 0).eqv (Q'.mkPos 3 2 (by decide)) :=
  Q'.eqv_trans _ _ _ (phi4_physGap_eqv_c 0) (by decide)

/-- `physGap 1 ≃ 4/3` (the physical gap at spacing `a_1 = 1/3`). -/
theorem phi4_physGap_one : (phi4ScalingBand.physGap 1).eqv (Q'.mkPos 4 3 (by decide)) :=
  Q'.eqv_trans _ _ _ (phi4_physGap_eqv_c 1) (by decide)

/-- **Genuine spacing-variation (non-vacuity).**  `physGap 0` is NOT equivalent
to `physGap 1`: the physical gap really changes with the lattice spacing
(`3/2 ≠ 4/3`).  This distinguishes the φ⁴ inhabitant from the existing
degenerate constant-in-volume `concreteClusterBound` (`physGap` would be a single
value there); it is the concrete witness that the a→0 band is exercised. -/
theorem phi4_physGap_varies :
    ¬ (phi4ScalingBand.physGap 0).eqv (phi4ScalingBand.physGap 1) := by
  intro h
  have hc : (cSeq 0).eqv (cSeq 1) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (phi4_physGap_eqv_c 0))
      (Q'.eqv_trans _ _ _ h (phi4_physGap_eqv_c 1))
  exact absurd hc (by decide)

/-- **The lattice margin VANISHES with the spacing** (the a→0 physics): the
per-spacing floor `latMargin j = c_j · a_j` is genuinely spacing-dependent and
tends to `0`, exhibited by `latMargin 0 = 3/4 > 4/9 = latMargin 1`.  (Contrast
the vanishing LATTICE margin with the FIXED PHYSICAL gap above — that ratio is
exactly the point of the band.) -/
theorem phi4_latMargin_varies :
    phi4ScalingBand.latMargin 1 < phi4ScalingBand.latMargin 0 := by
  show (phi4ClusterBoundOf (vSeq 1) (vSeq_pos 1) (vSeq_lt_one 1)).floorRate
      < (phi4ClusterBoundOf (vSeq 0) (vSeq_pos 0) (vSeq_lt_one 0)).floorRate
  show vSeq 1 < vSeq 0
  decide

/-! ## 4. The CONVERGENCE-MODULUS extension `Phi4ScalingLimitModulus`

`RegScalingLimitModulus` EXTENDS `RegScalingBand` (§3) with the SUPPLIED data of
the STRONGER a→0 refinement (trichotomy (c)): an Archimedean spacing-vanishing
witness, a bare-coupling record, and a spacing-uniform two-sided CONVERGENCE
modulus on the physical-gap sequence.  Because `physGap j ≃ c_j = 1 + 1/(j+2)`
CONVERGES to the continuum value `1` (the fixed physical mass), the modulus is a
genuine `⌈1/ε⌉` Archimedean rate, NOT the trivial `M ε = 0`.  From it the
pipeline builds the single continuum physical gap `scaling_continuum_physGap`
with positivity PROVED.

# HONESTY — this validates the CONVERGENCE PLUMBING, not YM physics

  * The convergence `physGap j → 1` is a RATIONAL fact about the dialed-in
    `c_j = 1 + 1/(j+2)`; the `1/(j+2)` approach rate is put in BY HAND.  It is NOT
    dimensional transmutation / asymptotic-freedom running: YM has no mass
    parameter to dial, and the EXISTENCE of a continuum limit for the YM physical
    gap (let alone its rate) is exactly the open frontier.
  * `Phi4ScalingLimitModulus` inhabits the GENERIC pipeline structure
    `RegScalingLimitModulus`, which is NOT a guarded Clay-frontier bundle.  It is
    deliberately NOT wired into `UniformSpacingFloor` / `ClayTarget` /
    `Tier0Scorecard` / `ClayTargetPinned` / `FrontierDAG`; those stay UNINHABITED.
  * What is genuinely exercised: the SUPPLIED-modulus machinery
    (`completeLimit` of `j ↦ ofQ' (physGap j)`, positivity from the uniform
    floor, the `ModCauchy` two-sided bound), i.e. the part of the pipeline that
    most resembles the real continuum-limit obligation. -/

/-! ### 4.1 An antitone Archimedean modulus `archMod ε = ⌈1/ε⌉`

`archMod ε` is the rational ceiling of `1/ε` (`qCeilNat (recipPos ε)`), else `0`.
For `ε > 0` and `j ≥ archMod ε` it forces `invSucc (j+1) ≤ ε` (`archMod_spec`),
and it is antitone in `ε` (`archMod_antitone`).  This is the genuine
Archimedean-null witness for `a_j = invSucc(j+1) → 0` AND the convergence rate for
`c_j → 1`. -/

/-- Antitone Archimedean modulus `⌈1/ε⌉` (`qCeilNat` of the positive reciprocal),
`0` for `ε ≤ 0`. -/
def archMod (ε : Q') : Nat :=
  if h : (0 : Q') < ε then SemicircleConvClosed.qCeilNat (Q'.recipPos ε h) else 0

theorem archMod_pos_eq (ε : Q') (h : (0 : Q') < ε) :
    archMod ε = SemicircleConvClosed.qCeilNat (Q'.recipPos ε h) := by
  unfold archMod; rw [dif_pos h]

/-- **Archimedean spec:** for `ε > 0` and `j ≥ archMod ε`, `invSucc (j+1) ≤ ε`.
Route: `recipPos ε ≤ ofNat (archMod ε) ≤ ofNat j` (`q_le_qCeilNat` + `ofNat`
monotone), cross-multiplied through `recipPos_num`/`recipPos_den` to
`ε.den ≤ j·ε.num`, then `ε.den ≤ ε.num·(j+2)`. -/
theorem archMod_spec (ε : Q') (h : (0 : Q') < ε) (j : Nat) (hj : archMod ε ≤ j) :
    Q'.invSucc (j + 1) ≤ ε := by
  have hnum : 0 < ε.num := Q'.num_pos_of_pos h
  have hle : Q'.recipPos ε h ≤ Q'.ofNat (archMod ε) := by
    rw [archMod_pos_eq ε h]; exact SemicircleConvClosed.q_le_qCeilNat (Q'.recipPos ε h)
  have hMj : Q'.ofNat (archMod ε) ≤ Q'.ofNat j := by
    show (Q'.ofNat (archMod ε)).num * ((Q'.ofNat j).den : Int)
        ≤ (Q'.ofNat j).num * ((Q'.ofNat (archMod ε)).den : Int)
    have e1 : (Q'.ofNat (archMod ε)).num = (archMod ε : Int) := rfl
    have e2 : (Q'.ofNat j).num = (j : Int) := rfl
    have e3 : ((Q'.ofNat j).den : Int) = 1 := rfl
    have e4 : ((Q'.ofNat (archMod ε)).den : Int) = 1 := rfl
    rw [e1, e2, e3, e4, Int.mul_one, Int.mul_one]
    exact_mod_cast hj
  have hrecj : Q'.recipPos ε h ≤ Q'.ofNat j := Q'.le_trans' _ _ _ hle hMj
  have hcm : (ε.den : Int) ≤ (j : Int) * ε.num := by
    have h2 : (Q'.recipPos ε h).num * ((Q'.ofNat j).den : Int)
        ≤ (Q'.ofNat j).num * ((Q'.recipPos ε h).den : Int) := hrecj
    rw [Q'.recipPos_num ε h, Q'.recipPos_den ε h] at h2
    have e2 : (Q'.ofNat j).num = (j : Int) := rfl
    have e3 : ((Q'.ofNat j).den : Int) = 1 := rfl
    rw [e2, e3, Int.mul_one] at h2
    exact h2
  show (Q'.invSucc (j + 1)).num * (ε.den : Int) ≤ ε.num * ((Q'.invSucc (j + 1)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den, Int.one_mul]
  have hjj : (j : Int) ≤ (((j + 1) + 1 : Nat) : Int) := by
    exact_mod_cast (show j ≤ (j + 1) + 1 by omega)
  have hnn : (0 : Int) ≤ ε.num := Int.le_of_lt hnum
  have step : (j : Int) * ε.num ≤ (((j + 1) + 1 : Nat) : Int) * ε.num :=
    Int.mul_le_mul_of_nonneg_right hjj hnn
  have hfin : (ε.den : Int) ≤ (((j + 1) + 1 : Nat) : Int) * ε.num := Int.le_trans hcm step
  rw [Int.mul_comm]
  exact hfin

/-- **`archMod` is antitone.**  `0 < δ`, `δ ≤ ε ⟹ archMod ε ≤ archMod δ`
(a smaller tolerance needs a later stage).  Route: `recipPos_antitone` +
`qCeilNat_mono`. -/
theorem archMod_antitone : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → archMod ε ≤ archMod δ := by
  intro ε δ hδ hδε
  have hε : (0 : Q') < ε := AFExpLift.lt_of_lt_of_le hδ hδε
  rw [archMod_pos_eq ε hε, archMod_pos_eq δ hδ]
  exact BernsteinStageData.qCeilNat_mono (ArtanhMonotone.recipPos_antitone δ ε hδ hε hδε)

/-! ### 4.2 The two-sided physical-gap convergence step

The physical gap `physGap j ≃ c_j = 1 + invSucc(j+1)` converges to `1`.  For
`i ≥ archMod ε` the excess `invSucc(i+1) ≤ ε`, and since every `c_j ≥ 1`:

  `physGap i ≤ c_i = 1 + invSucc(i+1) ≤ 1 + ε ≤ c_j + ε ≤ physGap j + ε`.

Symmetrising gives the two-sided `physBound`. -/

/-- **One-sided convergence step.**  For `ε > 0` and `i ≥ archMod ε`, the physical
gap at step `i` is within `ε` above the physical gap at ANY step `j`:
`physGap i ≤ physGap j + ε`.  (Only the `i`-side Archimedean bound is used.) -/
theorem phi4_physGap_le_add (ε : Q') (hε : (0 : Q') < ε) (i j : Nat)
    (hi : archMod ε ≤ i) :
    Q'.divPos (vSeq i) (aSeq i) (aSeq_pos i)
      ≤ Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j) + ε := by
  have hpi : Q'.divPos (vSeq i) (aSeq i) (aSeq_pos i) ≤ cSeq i :=
    Q'.divPos_le_of_le_mul (vSeq i) (aSeq i) (aSeq_pos i) (Q'.le_refl' (vSeq i))
  have hpj : cSeq j ≤ Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j) :=
    Q'.le_divPos_of_mul_le (vSeq j) (aSeq j) (aSeq_pos j) (Q'.le_refl' (vSeq j))
  have hinv : Q'.invSucc (i + 1) ≤ ε := archMod_spec ε hε i hi
  have hci : cSeq i ≤ (1 : Q') + ε := Q'.add_le_add_left 1 (Q'.invSucc (i + 1)) ε hinv
  have h1e : (1 : Q') + ε ≤ cSeq j + ε := Q'.add_le_add_right 1 (cSeq j) ε (cSeq_ge_one j)
  have hpjε : cSeq j + ε ≤ Q'.divPos (vSeq j) (aSeq j) (aSeq_pos j) + ε :=
    Q'.add_le_add_right (cSeq j) _ ε hpj
  exact Q'.le_trans' _ _ _ hpi
    (Q'.le_trans' _ _ _ hci (Q'.le_trans' _ _ _ h1e hpjε))

/-! ### 4.3 The headline: `Phi4ScalingLimitModulus : RegScalingLimitModulus`

Extends `phi4ScalingBand` with the Archimedean spacing-null witness (`archMod`),
a bare-coupling record (`cSeq`, the dialed-in physical mass — data, NOT AF
running), and the genuine two-sided physical-gap convergence modulus. -/

/-- **THE φ⁴ CONVERGENCE-MODULUS INHABITANT.**  A concrete `RegScalingLimitModulus`
extending `phi4ScalingBand`: the spacings `a_j = invSucc(j+1) → 0` are genuinely
Archimedean-null (`spacing_to_zero` via `archMod`), and the physical gap
`physGap j ≃ 1 + 1/(j+2)` CONVERGES to the continuum value `1` with the explicit
antitone rate `archMod`.  The `bareCoupling` is the dialed-in physical mass
`cSeq` (data, NOT asymptotic-freedom running).  This inhabits the GENERIC
pipeline structure, NOT any guarded YM Clay-frontier type. -/
def phi4ScalingLimitModulus : RegScalingLimitModulus where
  toRegScalingBand := phi4ScalingBand
  spacingMod := archMod
  spacing_to_zero := fun ε hε j hj => archMod_spec ε hε j hj
  bareCoupling := cSeq
  physMod := archMod
  physMod_mono := archMod_antitone
  physBound := fun ε hε i j hi hj =>
    ⟨phi4_physGap_le_add ε hε i j hi, phi4_physGap_le_add ε hε j i hj⟩

/-! ### 4.4 The continuum (`a → 0`) physical gap, FIRED on φ⁴

The pipeline's supplied-modulus continuum machinery, now discharged on a concrete
genuinely-converging inhabitant: the single continuum physical gap is positive and
sits in the physical band `[1, 3/2]`. -/

/-- **The continuum (`a → 0`) physical gap of the φ⁴ model is strictly positive**
— FIRED via `scaling_continuum_physGap_isPositive`.  (φ⁴: the survival is a
dialed-in bare mass, NOT YM dimensional transmutation.) -/
theorem phi4_scaling_continuum_isPositive :
    RegularCReal.IsPositive
      (scaling_continuum_physGap phi4ScalingLimitModulus) :=
  scaling_continuum_physGap_isPositive phi4ScalingLimitModulus

/-- The continuum physical gap dominates the physical floor `ofQ' 1` — FIRED. -/
theorem phi4_scaling_continuum_ge_one :
    RegularCReal.ofQ' phi4ScalingLimitModulus.physGapMin
      ≤ scaling_continuum_physGap phi4ScalingLimitModulus :=
  scaling_continuum_physGap_ge_floor phi4ScalingLimitModulus

/-- The continuum physical gap is bounded above by the physical ceiling
`ofQ' (3/2)` — FIRED.  The continuum gap sits in the band `[1, 3/2]`. -/
theorem phi4_scaling_continuum_le_threehalves :
    scaling_continuum_physGap phi4ScalingLimitModulus
      ≤ RegularCReal.ofQ' phi4ScalingLimitModulus.physGapMax :=
  scaling_continuum_physGap_le_ceiling phi4ScalingLimitModulus

/-! ### 4.5 NON-VACUITY: the modulus is genuine and the gap really converges to 1

The convergence rate is real (`archMod` fires at concrete tolerances), and the
physical gap `physGap j ≃ 1 + 1/(j+2)` genuinely APPROACHES the continuum value
`1` — exhibited at `j = 0, 1, 10` (`3/2, 4/3, 13/12`, strictly decreasing towards
`1`). -/

/-- The convergence modulus genuinely FIRES: for `ε = 1/10` and any `j ≥
archMod (1/10)`, the physical gap is within `1/10` above `physGap` at every other
step (two-sided).  A concrete witness that `physMod` is not the trivial `0`
modulus. -/
theorem phi4_physMod_fires (i j : Nat)
    (hi : phi4ScalingLimitModulus.physMod (Q'.mkPos 1 10 (by decide)) ≤ i) :
    Q'.divPos ((phi4ScalingLimitModulus.atSpacing i).floorRate)
        (phi4ScalingLimitModulus.spacing i) (phi4ScalingLimitModulus.spacing_pos i)
      ≤ Q'.divPos ((phi4ScalingLimitModulus.atSpacing j).floorRate)
          (phi4ScalingLimitModulus.spacing j) (phi4ScalingLimitModulus.spacing_pos j)
        + Q'.mkPos 1 10 (by decide) :=
  phi4_physGap_le_add (Q'.mkPos 1 10 (by decide)) (by decide) i j hi

/-- `physGap 10 ≃ 13/12` — the physical gap at spacing `a_10 = 1/12`, strictly
closer to the continuum value `1` than `physGap 0 = 3/2` and `physGap 1 = 4/3`. -/
theorem phi4_physGap_ten : (phi4ScalingBand.physGap 10).eqv (Q'.mkPos 13 12 (by decide)) :=
  Q'.eqv_trans _ _ _ (phi4_physGap_eqv_c 10) (by decide)

/-- **The physical gap genuinely APPROACHES `1`.**  The excess `physGap j − 1 ≃
1/(j+2)` strictly decreases: `physGap 0 (3/2) > physGap 1 (4/3) > physGap 10
(13/12)`, all `> 1`.  Together with `phi4_scaling_continuum_ge_one` /
`phi4_scaling_continuum_le_threehalves`, the continuum limit is the genuine
`a → 0` value the sequence converges DOWN to. -/
theorem phi4_physGap_approaches_one :
    (phi4ScalingBand.physGap 10).eqv (Q'.mkPos 13 12 (by decide)) ∧
      Q'.mkPos 13 12 (by decide) < Q'.mkPos 4 3 (by decide) ∧
      Q'.mkPos 4 3 (by decide) < Q'.mkPos 3 2 (by decide) ∧
      (1 : Q') < Q'.mkPos 13 12 (by decide) :=
  ⟨phi4_physGap_ten, by decide, by decide, by decide⟩

end YMGap.Continuum.Phi4ScalingBand

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Phi4ScalingBand.one_sub_lt_one
#print axioms YMGap.Continuum.Phi4ScalingBand.aSeq_pos
#print axioms YMGap.Continuum.Phi4ScalingBand.aSeq_le_half
#print axioms YMGap.Continuum.Phi4ScalingBand.cSeq_ge_one
#print axioms YMGap.Continuum.Phi4ScalingBand.cSeq_le_max
#print axioms YMGap.Continuum.Phi4ScalingBand.vSeq_pos
#print axioms YMGap.Continuum.Phi4ScalingBand.vSeq_lt_one
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4ClusterBoundOf
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4ScalingBand
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_band_physGapMin_pos
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_band_gap_survives
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_band_physGap_le
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_eqv_c
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_zero
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_one
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_varies
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_latMargin_varies
#print axioms YMGap.Continuum.Phi4ScalingBand.archMod_spec
#print axioms YMGap.Continuum.Phi4ScalingBand.archMod_antitone
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_le_add
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4ScalingLimitModulus
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_scaling_continuum_isPositive
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_scaling_continuum_ge_one
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_scaling_continuum_le_threehalves
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physMod_fires
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_ten
#print axioms YMGap.Continuum.Phi4ScalingBand.phi4_physGap_approaches_one
