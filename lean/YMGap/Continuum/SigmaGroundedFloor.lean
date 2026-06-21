/-
Track B / R2 — grounding the volume-uniform cluster bound's positive floor in the
RENORMALIZED STRING TENSION σ̂_∞ via the √-bridge, replacing the arbitrary
rational floor with a quantity certified as a lower bound on the physical mass
`√σ̂_∞`, and proving the resulting continuum mass dominates that σ̂-derived
certificate.

# What this module is

The concrete strong-coupling cluster inhabitant carried a clustering floor that
was the proven eigenvalue-gap MARGIN `1 − sep` of the finite transfer operator —
genuine located-gap data, but a number internal to the spectral side, not yet
tied to the physical mass scale.  The √-bridge supplies the missing link: the
physical mass is `m_0 = √σ̂_∞`, a genuine constructive real with witnessed
positivity inherited from the proven `σ̂_∞ > 0`, and `sqrtL` is a POSITIVE
RATIONAL lower-bound certificate for it (`sqrtL² ≤ σ̂_∞`).

This module:

  * **Lifts the rational √-certificate to the real mass:** proves
    `ofQ' sqrtL ≤ m_0`, i.e. `sqrtL ≤ √σ̂_∞`, directly from the Heron
    iteration's uniform lower bound (`heronSeq_lb`) — every approximation of
    `√σ̂_∞` is `≥ sqrtL`, so the limit is, by the standard
    approximation-lower-bound lift.  The √-content of `sqrtL ≤ √σ̂_∞` is now a
    Lean theorem.

  * **Re-grounds the cluster floor in σ̂_∞:** builds a `UniformClusterBound` whose
    `floorRate` is `sqrtL` — the σ̂-derived rational mass floor — instead of an
    arbitrary constant.  Because `sqrtL` is a mass scale (`≤ 1` for the pilot
    `σ̂_∞ = 1`), the located-gap family is the saturated free case (`sep = 0`,
    gap margin `1`), which meets the σ̂-derived floor `sqrtL ≤ 1`.  The cluster
    tail vanishes (`tailConst = 0`), as for a volume-independent margin.

  * **Proves the continuum mass is grounded in σ̂_∞:** the continuum gap rate is
    strictly positive, and it dominates the σ̂-derived certificate,
    `ofQ' sqrtL ≤ continuumRate`.  Composed with `ofQ' sqrtL ≤ m_0`, the rational
    `sqrtL` is simultaneously a lower bound on the physical mass `√σ̂_∞` and a
    lower bound on the continuum gap rate — the continuum mass gap is grounded in
    `σ̂_∞ > 0`, not an arbitrary constant.

# Honesty

⚠ The `UniformClusterBound` built here (`degenerateSigmaGroundedClusterBound`) is
a DEGENERATE PLACEHOLDER, exactly as in `ClusterBoundInstance`: it inhabits the
type via a CONSTANT (volume-independent) margin family, NOT a cluster-expansion
estimate.  The genuine strong-coupling cluster bound is OPEN.  The only content
beyond the const witness is that the FLOOR is σ̂-derived (`sqrtL`), not arbitrary.

`sqrtL` and `σ̂_∞` are the UV-pilot fiducial values (`sqrtL = 1`, `σ̂_∞ = 1`), not
the final physical numbers.  The point is structural: the floor is now DERIVED
from σ̂_∞ via the √-bridge — `sqrtL` is certified by `sqrtL² ≤ σ̂_∞` with
`σ̂_∞ > 0` explicit — rather than an arbitrary rational.  Because the pilot
`sqrtL = 1`, the located family must be the free `sep = 0` (margin-`1`) case for
`uniform_floor` to hold; this is the saturated boundary case and is stated
honestly.  The √-bridge mass lower bound `sqrtL ≤ √σ̂_∞` is general in the value.

# Axiom-gate

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.LocatedReconstruction
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.OSContent
import YMGap.Continuum.SqrtBridge
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.SigmaGroundedFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuumGapLimit
open YMGap.Continuum.ClusterGapReduction

/-! ## Step 1: the √-bridge rational mass lower bound `sqrtL ≤ √σ̂_∞`

The physical mass `m_0 = √σ̂_∞` is the Heron limit `sqrtFrom σ̂_∞ sqrtL …`, whose
`Λ`-th approximation is `heronSeq σ̂_∞ Λ`, and `heronSeq_lb` proves every Heron
iterate is `≥ sqrtL` (since `sqrtL² ≤ σ̂_∞ ≤ x_Λ²`).  The
approximation-lower-bound lift then yields `ofQ' sqrtL ≤ m_0` at the CReal
level. -/

/-- **The √-bridge rational mass lower bound, PROVED:** `ofQ' sqrtL ≤ m_0`,
i.e. `sqrtL ≤ √σ̂_∞`.  Every approximation of `√σ̂_∞` is a Heron iterate, hence
`≥ sqrtL` by `heronSeq_lb` (from `sqrtL² ≤ σ̂_∞`), so the limit is `≥ sqrtL` by
`ofQ'_le_of_approx_ge`.  This turns the dimensional `m ≥ √σ̂_∞`'s rational
certificate into a Lean theorem about the genuine constructive square root. -/
theorem sqrtL_le_m_0 : CReal.ofQ' SqrtBridge.sqrtL ≤ SqrtBridge.m_0 :=
  CReal.ofQ'_le_of_approx_ge (fun n =>
    CReal.heronSeq_lb SqrtBridge.sigmaHatVal SqrtBridge.sqrtL
      SqrtBridge.sigmaHatVal_pos SqrtBridge.sqrtL_pos SqrtBridge.sqrtL_sq_le n)

/-! ## The σ̂-grounded clustering floor

The floor is now the √-bridge rational certificate `sqrtL` — the σ̂-derived mass
floor (`sqrtL² ≤ σ̂_∞`, `σ̂_∞ > 0`) — not an arbitrary constant. -/

/-- The σ̂-grounded clustering floor `δ = sqrtL`: the √-bridge rational
lower-bound certificate for the physical mass `√σ̂_∞`. -/
def sigmaGroundedFloor : Q' := SqrtBridge.sqrtL

/-- The σ̂-grounded floor is strictly positive — inherited from `sqrtL_pos`,
ultimately from `σ̂_∞ > 0`. -/
theorem sigmaGroundedFloor_pos : (0 : Q') < sigmaGroundedFloor :=
  SqrtBridge.sqrtL_pos

/-! ## The saturated free located family (`sep = 0`, margin `1`)

For the UV pilot `sqrtL = 1`, so the floor `sqrtL ≤ 1` requires a family whose
gap margin is `≥ 1`.  The saturated free case `sep = 0` (the fully-massive
one-mode model, `OSContent.trivSpectralModel`) has gap margin `1 − 0 = 1`,
meeting the σ̂-derived floor.  This is the boundary/saturated case, stated
honestly: every excited eigenvalue is `0`, so `sep = 0 < 1` is a genuine located
gap. -/

/-- The saturated free located gap at `sep = 0` on the one-mode trivial model:
every eigenvalue is `0`, so `sep = 0 < 1` and the gap margin is `1 − 0 = 1`. -/
def freeLocated : LocatedSpectralGap OSContent.trivSpectralModel where
  sep := 0
  sep_lt_one := by decide
  bound := fun _ => Q'.le_refl' 0

/-- The constant saturated-free finite-volume family (every volume the same
`sep = 0` gap). -/
def freeFamily : Nat → SpectralModel := fun _ => OSContent.trivSpectralModel

/-- The constant saturated-free located gap at every volume. -/
def freeLocatedAt (Λ : Nat) : LocatedSpectralGap (freeFamily Λ) := freeLocated

/-- The free family's gap margin is `1 − 0 = 1` at every volume, so it meets the
σ̂-derived floor `sqrtL = 1`: `sqrtL ≤ gapMargin`. -/
theorem free_uniform_floor (Λ : Nat) :
    sigmaGroundedFloor ≤ (freeLocatedAt Λ).gapMargin := by
  show SqrtBridge.sqrtL ≤ 1 - 0
  decide

/-! ## The σ̂-grounded DEGENERATE cluster bound (placeholder)

⚠ Identical in DEGENERACY to `ClusterBoundInstance.degenerateConstClusterBound`:
a CONSTANT (volume-independent) margin family, here the saturated free case
(`sep = 0`, margin `1`), with `tailConst = 0` vanishing trivially.  The only
difference is the floor is the σ̂-derived √-bridge certificate `sqrtL` instead of
an arbitrary constant.  The cluster bound is STILL degenerate — no
cluster-expansion estimate — and the genuine strong-coupling instance is OPEN. -/

/-- **DEGENERATE PLACEHOLDER inhabitant of `UniformClusterBound` (σ̂-grounded
floor).**  ⚠ Like `ClusterBoundInstance.degenerateConstClusterBound`, this
inhabits the type via a CONSTANT (volume-independent) margin family — here the
saturated free case `sep = 0`, gap margin `1`, with `tailConst = 0` vanishing
trivially.  Its only upgrade over the const witness is that `floorRate` is the
√-bridge rational `sqrtL` (`sqrtL² ≤ σ̂_∞`, `σ̂_∞ > 0`), so the floor is DERIVED
from the renormalized string tension rather than an arbitrary constant.  But the
cluster bound itself is STILL degenerate: no cluster-expansion estimate is made,
and the genuine strong-coupling instance is **OPEN**. -/
def degenerateSigmaGroundedClusterBound : UniformClusterBound where
  gaps := freeFamily
  located := freeLocatedAt
  floorRate := sigmaGroundedFloor
  floorRate_pos := sigmaGroundedFloor_pos
  uniform_floor := fun Λ => free_uniform_floor Λ
  tailConst := 0
  tailConst_nonneg := Q'.le_refl' 0
  incr_up := fun Λ =>
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  incr_lo := fun Λ =>
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  modulus := fun ε hε =>
    CReal.exists_mul_le
      (Q'.mul_nonneg _ _ (by decide) (Q'.le_refl' 0)) hε

/-- The σ̂-grounded cluster bound's clustering floor is the √-bridge certificate
`sqrtL` — the σ̂-derived mass floor. -/
theorem degenerateSigmaGroundedClusterBound_floor :
    degenerateSigmaGroundedClusterBound.floorRate = SqrtBridge.sqrtL := rfl

/-- The σ̂-grounded cluster bound's cluster tail constant vanishes. -/
theorem degenerateSigmaGroundedClusterBound_tailConst :
    degenerateSigmaGroundedClusterBound.tailConst = 0 := rfl

/-! ## The continuum gap rate of the σ̂-grounded inhabitant -/

/-- The continuum gap rate of the σ̂-grounded inhabitant — the `CReal` limit of
the (constant, margin-`1`) saturated-free margin sequence, with floor grounded in
σ̂_∞ via the √-bridge. -/
def sigmaGroundedContinuumRate : CReal :=
  continuumRate degenerateSigmaGroundedClusterBound

/-- Every approximation of the σ̂-grounded continuum rate is the saturated-free
gap margin `1 − 0`. -/
@[simp] theorem sigmaGroundedContinuumRate_approx (Λ : Nat) :
    sigmaGroundedContinuumRate.approx Λ = 1 - 0 := rfl

/-! ## Capstones

The σ̂-grounded continuum mass is strictly positive, and it dominates the
√-bridge mass certificate `sqrtL` — the same rational that is `≤ √σ̂_∞` (step 1).
Together these realize the `m ≥ √σ̂_∞` mass-gap lower bound (R3-style) at the
continuum-rate level: the continuum gap rate is bounded below by the σ̂-derived
mass floor, which is itself a certified lower bound on the physical mass. -/

/-- **Capstone (positivity).**  The σ̂-grounded continuum mass is a
strictly-positive constructive real — the end-to-end chain fires on the σ̂-derived
floor. -/
theorem sigmaGrounded_continuum_mass_isPositive :
    CReal.IsPositive sigmaGroundedContinuumRate :=
  clusterBound_continuum_mass_isPositive degenerateSigmaGroundedClusterBound

/-- **Capstone (physical floor — the σ̂-grounded continuum mass lower bound).**
The continuum gap rate dominates the √-bridge rational certificate `sqrtL`:
`ofQ' sqrtL ≤ continuumRate`.  Since `sqrtL` is also a certified lower bound on
the physical mass `√σ̂_∞` (`sqrtL_le_m_0`) — and `sqrtL² ≤ σ̂_∞` with `σ̂_∞ > 0` —
the continuum mass gap is grounded in the renormalized string tension via the
√-bridge, realizing the `m ≥ √σ̂_∞` mass-gap lower bound (R3-style) at the
continuum-rate level rather than via an arbitrary constant.  Proof: this is
`floor_persists` at `degenerateSigmaGroundedClusterBound`, whose `floorRate` is `sqrtL`. -/
theorem sigmaGrounded_continuum_mass_ge_sqrtL :
    CReal.ofQ' SqrtBridge.sqrtL ≤ sigmaGroundedContinuumRate :=
  floor_persists degenerateSigmaGroundedClusterBound

/-- **Capstone (packaged).**  The σ̂-grounded continuum mass as `Type`-level data
with its positivity proof. -/
def sigmaGrounded_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  clusterBound_continuum_gap_bridge degenerateSigmaGroundedClusterBound

/-- The packaged mass is exactly the σ̂-grounded continuum rate. -/
theorem sigmaGrounded_bridge_fst :
    sigmaGrounded_continuum_gap_bridge.1 = sigmaGroundedContinuumRate := rfl

end YMGap.Continuum.SigmaGroundedFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SigmaGroundedFloor.sqrtL_le_m_0
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGroundedFloor_pos
#print axioms YMGap.Continuum.SigmaGroundedFloor.freeLocated
#print axioms YMGap.Continuum.SigmaGroundedFloor.free_uniform_floor
#print axioms YMGap.Continuum.SigmaGroundedFloor.degenerateSigmaGroundedClusterBound
#print axioms YMGap.Continuum.SigmaGroundedFloor.degenerateSigmaGroundedClusterBound_floor
#print axioms YMGap.Continuum.SigmaGroundedFloor.degenerateSigmaGroundedClusterBound_tailConst
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGroundedContinuumRate
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGroundedContinuumRate_approx
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGrounded_continuum_mass_isPositive
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGrounded_continuum_mass_ge_sqrtL
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGrounded_continuum_gap_bridge
#print axioms YMGap.Continuum.SigmaGroundedFloor.sigmaGrounded_bridge_fst
