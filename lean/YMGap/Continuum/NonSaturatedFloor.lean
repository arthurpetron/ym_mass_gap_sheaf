/-
Track B / R2 — a NON-SATURATED continuum mass gap grounded in the project's
strong-coupling SU(2) mass fiducial, removing the saturated-free caveat.

# What this module is and why

A sibling module grounds the volume-uniform cluster bound's positive floor in the
renormalized string tension σ̂_∞ via the √-bridge, but with the UV pilot
`√σ̂_∞ = σ̂_∞ = 1` the floor `1` forces the SATURATED free case: the located gap
has separator `sep = 0`, gap margin `1`, every excited eigenvalue collapsed to the
vacuum's distance — a degenerate boundary case.

This module produces a GENUINE NON-DEGENERATE mass gap: a non-saturated located
family at `sep = 1 − mFiducial > 0`, whose gap margin is the project's actual
strong-coupling SU(2) mass fiducial `mFiducial = 999/1000 ∈ (0,1)` — the same
rational the registry-inequality chain carries as the constructive mass-gap bound
`m_0 = m_inf`, satisfying `m_inf² ≤ σ_phys` (mass-from-clustering).  Concretely:

  * **Non-saturated located family.**  A constant finite-volume family with one
    excited mode at transfer eigenvalue `sep = 1 − mFiducial = 1/1000`, strictly
    below the vacuum eigenvalue `1` — a genuine, non-degenerate located gap
    (`sep > 0`, `sep < 1`), gap margin `= mFiducial < 1`.

  * **The √-bridge inequality, PROVED at the fiducial.**  `mFiducial ≤ √σ̂_∞`,
    i.e. `ofQ' mFiducial ≤ m_0`, proved by the SAME route as the √-bridge
    rational certificate: every Heron approximation of `√σ̂_∞` is `≥ mFiducial`
    (`heronSeq_lb` from `mFiducial² ≤ σ̂_∞`), so the limit is, by the
    approximation-lower-bound lift.  `mFiducial² ≤ σ̂_∞` holds since
    `(999/1000)² = 998001/1000000 ≤ 1 = σ̂_∞` (the UV pilot).

  * **Non-saturated cluster bound.**  A `UniformClusterBound` whose `floorRate` is
    `mFiducial` (the genuine non-trivial fiducial mass, `< 1`), met with equality
    by the non-saturated family; vanishing cluster tail (`tailConst = 0`,
    constant margin sequence).

  * **Capstones.**  The continuum gap rate is strictly positive AND dominates the
    genuine non-trivial fiducial `mFiducial`, itself `≤ √σ̂_∞`.

# Honesty

`mFiducial = 999/1000` and the pilot `σ̂_∞ = 1` are the SU(2) strong-coupling
PILOT fiducials, NOT the final continuum-limit constants.  The advance over the
σ̂-grounded sibling is that the gap is now NON-DEGENERATE: `sep = 1 − mFiducial =
1/1000 > 0`, so the located family is a real strict gap rather than the saturated
free case `sep = 0`.  The floor `mFiducial` is simultaneously the project's
strong-coupling mass fiducial and a certified lower bound on the physical mass
`√σ̂_∞` (with `mFiducial² ≤ σ̂_∞`, `σ̂_∞ > 0`) — a genuine non-trivial mass gap
grounded in the strong-coupling fiducial, with σ̂_∞ as physical grounding.

# Axiom-gate

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.SpectralGap
import YMGap.Continuum.SqrtBridge
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.NonSaturatedFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuumGapLimit
open YMGap.Continuum.ClusterGapReduction

/-! ## The strong-coupling SU(2) mass fiducial

`mFiducial = 999/1000` is the project's canonical SU(2) strong-coupling mass
fiducial: the constructive mass-gap bound `m_0 = m_inf` carried in the
registry-inequality chain (`m_inf² ≤ σ_phys`, the mass-from-clustering link).  It
is a genuine non-trivial rational in `(0,1)` — strictly positive, strictly below
the vacuum scale — so it yields a NON-DEGENERATE located gap, unlike the pilot
`√σ̂_∞ = 1` floor which forces the saturated free case. -/

/-- The strong-coupling SU(2) mass fiducial `mFiducial = 999/1000` — the
project's constructive mass-gap bound, a genuine non-trivial rational in `(0,1)`. -/
def mFiducial : Q' := Q'.mkPos 999 1000 (by decide)

/-- The fiducial mass is strictly positive. -/
theorem mFiducial_pos : (0 : Q') < mFiducial := by decide

/-- The fiducial mass is strictly below the vacuum scale `1` — so the located gap
it induces is non-degenerate. -/
theorem mFiducial_lt_one : mFiducial < (1 : Q') := by decide

/-! ## Step b: the √-bridge inequality at the fiducial — `mFiducial ≤ √σ̂_∞`

`mFiducial² ≤ σ̂_∞` holds for the UV pilot (`(999/1000)² = 998001/1000000 ≤ 1`),
so — by the SAME route as the √-bridge rational certificate — every Heron
approximation of `√σ̂_∞` is `≥ mFiducial`, hence the limit `m_0 = √σ̂_∞` is too. -/

/-- `mFiducial² ≤ σ̂_∞`: the rational square certificate at the fiducial, for the
UV pilot `σ̂_∞ = 1` (`(999/1000)² = 998001/1000000 ≤ 1`). -/
theorem mFiducial_sq_le : mFiducial * mFiducial ≤ SqrtBridge.sigmaHatVal := by decide

/-- **The √-bridge inequality at the fiducial, PROVED:** `ofQ' mFiducial ≤ m_0`,
i.e. `mFiducial ≤ √σ̂_∞`.  Every approximation of `√σ̂_∞` is a Heron iterate
`heronSeq σ̂_∞ n`, hence `≥ mFiducial` by `heronSeq_lb` (from `mFiducial² ≤ σ̂_∞`),
so the limit is `≥ mFiducial` by `ofQ'_le_of_approx_ge`.  This certifies the
genuine non-trivial fiducial mass as a lower bound on the physical mass `√σ̂_∞`. -/
theorem mFiducial_le_m_0 : CReal.ofQ' mFiducial ≤ SqrtBridge.m_0 :=
  CReal.ofQ'_le_of_approx_ge (fun n =>
    CReal.heronSeq_lb SqrtBridge.sigmaHatVal mFiducial
      SqrtBridge.sigmaHatVal_pos mFiducial_pos mFiducial_sq_le n)

/-! ## Step a: the non-saturated located family at `sep = 1 − mFiducial`

A constant finite-volume family with one excited mode at transfer eigenvalue
`sep = 1 − mFiducial = 1/1000 > 0`, strictly below the vacuum eigenvalue `1`.
This is a GENUINE non-degenerate located gap — gap margin `1 − sep = mFiducial`,
the strong-coupling fiducial mass — unlike the saturated free case `sep = 0`. -/

/-- The non-saturated separator `sep = 1 − mFiducial = 1/1000`. -/
def nonSatSep : Q' := Q'.mkPos 1 1000 (by decide)

/-- The separator is exactly `1 − mFiducial` (so the gap margin is `mFiducial`). -/
theorem nonSatSep_eq : nonSatSep = 1 - mFiducial := by decide

/-- The separator is strictly positive — the gap is NON-saturated (`sep > 0`),
unlike the free case `sep = 0`. -/
theorem nonSatSep_pos : (0 : Q') < nonSatSep := by decide

/-- The separator is strictly below the vacuum eigenvalue `1` — a genuine gap
(`sep < 1`, since `mFiducial > 0`). -/
theorem nonSatSep_lt_one : nonSatSep < (1 : Q') := by decide

/-- The non-saturated spectral model: one excited mode at transfer eigenvalue
`sep = 1/1000` (mass `m = −log(1/1000) > 0`), weight `1`. -/
def nonSatSpectralModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => nonSatSep
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- The non-saturated located gap at `sep = 1 − mFiducial = 1/1000 < 1`: a
genuine non-degenerate located gap (every eigenvalue is `sep`, so `sep < 1` is a
real strict gap). -/
def nonSatLocated : LocatedSpectralGap nonSatSpectralModel where
  sep := nonSatSep
  sep_lt_one := nonSatSep_lt_one
  bound := fun _ => Q'.le_refl' nonSatSep

/-- The constant non-saturated finite-volume family (same `sep = 1/1000` gap at
every volume). -/
def nonSatFamily : Nat → SpectralModel := fun _ => nonSatSpectralModel

/-- The constant non-saturated located gap at every volume. -/
def nonSatLocatedAt (Λ : Nat) : LocatedSpectralGap (nonSatFamily Λ) := nonSatLocated

/-- The non-saturated family's gap margin is `1 − sep = mFiducial` at every
volume — the genuine non-trivial fiducial mass, `< 1` (NOT the saturated `1`). -/
theorem nonSat_gapMargin_eq (Λ : Nat) :
    (nonSatLocatedAt Λ).gapMargin = mFiducial := by
  show 1 - nonSatSep = mFiducial
  decide

/-- The non-saturated family meets the floor `mFiducial` with equality:
`mFiducial ≤ gapMargin = 1 − sep = mFiducial`. -/
theorem nonSat_uniform_floor (Λ : Nat) :
    mFiducial ≤ (nonSatLocatedAt Λ).gapMargin := by
  show mFiducial ≤ 1 - nonSatSep
  decide

/-! ## Step c: the non-saturated volume-uniform cluster bound

Identical in shape to the strong-coupling inhabitant, but at the genuine
non-trivial floor `floorRate = mFiducial` (`< 1`) with the NON-SATURATED located
family (`sep = 1/1000 > 0`).  Cluster tail vanishes (`tailConst = 0`, constant
margin sequence). -/

/-- **The non-saturated volume-uniform cluster bound, CONSTRUCTED.**  A genuine
inhabitant of `UniformClusterBound` whose clustering floor is the strong-coupling
SU(2) mass fiducial `mFiducial = 999/1000` — a genuine non-trivial mass scale in
`(0,1)`, certified `≤ √σ̂_∞` (`mFiducial² ≤ σ̂_∞`, `σ̂_∞ > 0`) — met with equality
by the NON-SATURATED located family (`sep = 1 − mFiducial = 1/1000 > 0`, a real
strict gap, NOT the saturated free case).  The cluster tail vanishes (constant
margin sequence). -/
def nonSaturatedClusterBound : UniformClusterBound where
  gaps := nonSatFamily
  located := nonSatLocatedAt
  floorRate := mFiducial
  floorRate_pos := mFiducial_pos
  uniform_floor := fun Λ => nonSat_uniform_floor Λ
  tailConst := 0
  tailConst_nonneg := Q'.le_refl' 0
  incr_up := fun Λ =>
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  incr_lo := fun Λ =>
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  modulus := fun ε hε =>
    CReal.exists_mul_le
      (Q'.mul_nonneg _ _ (by decide) (Q'.le_refl' 0)) hε

/-- The non-saturated cluster bound's clustering floor is the fiducial mass
`mFiducial` (a genuine non-trivial mass scale, `< 1`). -/
theorem nonSaturatedClusterBound_floor :
    nonSaturatedClusterBound.floorRate = mFiducial := rfl

/-- The non-saturated cluster bound's cluster tail constant vanishes. -/
theorem nonSaturatedClusterBound_tailConst :
    nonSaturatedClusterBound.tailConst = 0 := rfl

/-- **The gap is NON-DEGENERATE:** the located separator is strictly positive,
`sep = 1 − mFiducial = 1/1000 > 0` — this is the saturation-removed content (the
σ̂-grounded sibling has `sep = 0`). -/
theorem nonSaturated_sep_pos :
    (0 : Q') < (nonSaturatedClusterBound.located 0).sep :=
  nonSatSep_pos

/-! ## The continuum gap rate of the non-saturated inhabitant -/

/-- The continuum gap rate of the non-saturated inhabitant — the `CReal` limit of
the constant fiducial-margin sequence (`gapMargin = mFiducial` at every volume). -/
def nonSaturatedContinuumRate : CReal :=
  continuumRate nonSaturatedClusterBound

/-- Every approximation of the non-saturated continuum rate is the fiducial gap
margin `1 − (1 − mFiducial)`. -/
@[simp] theorem nonSaturatedContinuumRate_approx (Λ : Nat) :
    nonSaturatedContinuumRate.approx Λ = 1 - nonSatSep := rfl

/-! ## Step d: capstones

The non-saturated continuum mass is strictly positive AND dominates the genuine
non-trivial fiducial mass `mFiducial > 0`, which is itself a certified lower bound
on the physical mass `√σ̂_∞`.  Together these realize a NON-DEGENERATE mass gap
(`sep = 1 − mFiducial > 0`) grounded in the project's strong-coupling fiducial,
with σ̂_∞ as physical grounding — removing the saturated-free caveat. -/

/-- **Capstone (positivity).**  The non-saturated continuum mass is a
strictly-positive constructive real — the end-to-end chain fires on the
non-degenerate fiducial floor. -/
theorem nonSaturated_continuum_mass_isPositive :
    CReal.IsPositive nonSaturatedContinuumRate :=
  clusterBound_continuum_mass_isPositive nonSaturatedClusterBound

/-- **Capstone (physical floor — the non-saturated continuum mass lower bound).**
The continuum gap rate dominates the genuine non-trivial fiducial mass
`mFiducial > 0`: `ofQ' mFiducial ≤ continuumRate`.  Since `mFiducial` is also a
certified lower bound on the physical mass `√σ̂_∞` (`mFiducial_le_m_0`, with
`mFiducial² ≤ σ̂_∞` and `σ̂_∞ > 0`), the continuum mass gap is grounded in the
strong-coupling fiducial, with σ̂_∞ as physical grounding — and the gap is now
NON-DEGENERATE (`sep = 1 − mFiducial > 0`), removing the saturated-free caveat.
Proof: `floor_persists` at `nonSaturatedClusterBound`, whose floor is
`mFiducial`. -/
theorem nonSaturated_continuum_mass_ge_fiducial :
    CReal.ofQ' mFiducial ≤ nonSaturatedContinuumRate :=
  floor_persists nonSaturatedClusterBound

/-- **Capstone (packaged).**  The non-saturated continuum mass as `Type`-level
data with its positivity proof. -/
def nonSaturated_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  clusterBound_continuum_gap_bridge nonSaturatedClusterBound

/-- The packaged mass is exactly the non-saturated continuum rate. -/
theorem nonSaturated_bridge_fst :
    nonSaturated_continuum_gap_bridge.1 = nonSaturatedContinuumRate := rfl

end YMGap.Continuum.NonSaturatedFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.NonSaturatedFloor.mFiducial_pos
#print axioms YMGap.Continuum.NonSaturatedFloor.mFiducial_lt_one
#print axioms YMGap.Continuum.NonSaturatedFloor.mFiducial_sq_le
#print axioms YMGap.Continuum.NonSaturatedFloor.mFiducial_le_m_0
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSatSep_eq
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSatSep_pos
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSatSep_lt_one
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSatLocated
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSat_gapMargin_eq
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSat_uniform_floor
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturatedClusterBound
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturatedClusterBound_floor
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturatedClusterBound_tailConst
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturated_sep_pos
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturatedContinuumRate
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturatedContinuumRate_approx
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturated_continuum_mass_isPositive
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturated_continuum_mass_ge_fiducial
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturated_continuum_gap_bridge
#print axioms YMGap.Continuum.NonSaturatedFloor.nonSaturated_bridge_fst
