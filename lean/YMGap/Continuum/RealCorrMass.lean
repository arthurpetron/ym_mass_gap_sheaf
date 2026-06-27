/-
Track B / R2 — WIRING the REAL single-edge-correlator located gap into the
infinite-volume mass capstone.

# What this module is

`ClusterGapReduction.lean` collapses the thermodynamic Λ→∞ limit to ONE input,
`UniformClusterBound`, and PROVES from it a strictly-positive infinite-volume
mass at fixed spacing.  `UniformClusterFromKP.lean` exhibits one genuine
inhabitant `genuineUniformClusterBound` carrying a REAL geometric Λ-tail but
whose per-volume margins are a SYNTHETIC closed-form sequence
(`3/4 + (1/16)·Σ(1/2)^l` tightening toward the heat-kernel `7/8`); its abstract
clustering is not yet the actual Wilson correlator (the named `RealCorrelatorLink`
residual there).

This module assembles the COMPLEMENTARY inhabitant
`realCorrUniformClusterBound`: the per-volume located gaps here are the GENUINE
reconstructed-transfer-operator gaps `MayerClustering.reconTransfer_located_gap`,
each DERIVED (in `MayerClustering`) from the REAL `wilsonG` connected-correlator
decay (`wilsonG_decay` transported through `wilsonG_eqv_reconTransfer_corr`) plus
real Casimir-monotone excited-coefficient control (`coeffW_excited_le_one`).  The
located separator is the genuine strong-coupling rate `sep = rho gw = 2·(1/6)³`
(the real leading transfer eigenvalue `coeffW gw 1`), so every per-volume
gap-margin is the constant `1 − rho gw`.

The family is Λ-CONSTANT (`tailConst = 0`) because the single-edge transfer
operator's spectral gap is genuinely VOLUME-INDEPENDENT at fixed coupling and
spacing: each finite cutoff `M` exposes the same leading/second eigenvalues
`coeffW gw (i+1)`, so the located second eigenvalue — hence the margin — does not
move with the volume.  This constancy is an HONEST property of the real object,
NOT vacuous free-data inhabitation: the gaps are `reconTransfer_located_gap`, the
margins are the real `1 − rho gw`, and `tailConst = 0` is the true geometric tail
(there is no Λ-variation to bound).

# Honest contrast with `genuineUniformClusterBound`

`genuineUniformClusterBound` has a REAL nonzero geometric Λ-tail
(`tailConst = 1/16 > 0`, margins genuinely varying with Λ) but SYNTHETIC
closed-form margins (a constructed `3/4 + (1/16)·Σ(1/2)^l` envelope, not the
actual Wilson correlator).  `realCorrUniformClusterBound` is its mirror image: it
has GENUINE Wilson-correlator-derived margins (`reconTransfer_located_gap`, the
real `wilsonG_decay`) but a TRIVIAL Λ-tail (`tailConst = 0`, the margin is the
volume-independent `1 − rho gw`).  The two are complementary — one carries the
real Λ-variation with a synthetic margin, the other the real margin with no
Λ-variation — and NEITHER is yet the full physical object (the real correlator
WITH genuine Λ-variation, multi-plaquette, uniform-in-`w`, continuum a→0).

# Scope (underclaim, AGENTS.md Rule 6)

What is delivered: a strictly-POSITIVE infinite-volume (Λ→∞, FIXED spacing) mass
resting on the REAL single-edge transfer-operator connected-correlator gap at the
concrete strong-coupling weight `w = 1/6`.  It is NOT the continuum (a→0) limit,
NOT uniform-in-`w`, NOT a multi-plaquette correlator, and NOT the 4D Yang–Mills
mass gap.  The Λ-variation here is trivial by construction (the single-edge gap
is volume-independent); the genuine-Λ-variation-with-real-correlator object
remains open (the multi-plaquette Mayer/Ursell residual of `MayerClustering`).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat` arithmetic and the reused tower lemmas.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `sorry`, no `Classical.*`, no `native_decide`, no `decide`
on non-decidable props.  All witnesses are `Type`-level data; the located family
is the genuine `reconTransfer_located_gap`, not asserted.
-/

import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.MayerClustering
import YMGap.Continuum.TransferCorr
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.KPLimit
import YMGap.Continuum.UniformClusterFromKP

namespace YMGap.Continuum.RealCorrMass

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.ClusterGapReduction

/-! ## 0. `geoIncr 0 = 0` (the trivial tail)

With `tailConst = 0` the geometric single-step majorant `geoIncr 0 l = 0·(1/2)^l`
is `0`, so the two-sided increment bounds collapse to `m ≤ m + 0`. -/

/-- `geoIncr 0 l = 0`: a zero tail constant gives a zero increment majorant
(`0·(1/2)^l ≃ 0`). -/
theorem geoIncr_zero (l : Nat) : (geoIncr (0 : Q') l).eqv (0 : Q') := by
  show ((0 : Q') * half ^ l).eqv (0 : Q')
  exact Q'.zero_mul_eqv (half ^ l)

/-! ## 1. The genuine real-correlator located family

The per-volume model at volume `Λ` is the reconstructed single-edge transfer
operator at cutoff `Λ+1`, `reconTransfer gw gw_nonneg (Λ+1)`: a genuine
multi-mode (`k = Λ+1`) compact model whose modes/eigenvalues are the REAL
single-rep transfer eigenvalues `coeffW gw (i+1)`.  Its located gap is the
genuine `reconTransfer_located_gap Λ`, with separator `sep = rho gw = 2·(1/6)³`,
DERIVED from the real Wilson connected-correlator decay. -/

/-- The per-volume spectral model: the reconstructed single-edge transfer operator
at cutoff `Λ+1` (a real `Λ+1`-mode model, eigenvalues `coeffW gw (i+1)`). -/
def realGaps (Λ : Nat) : SpectralModel := reconTransfer gw gw_nonneg (Λ + 1)

/-- The per-volume located gap: the genuine `reconTransfer_located_gap`, derived
from the REAL Wilson connected-correlator decay, with separator `rho gw`. -/
def realLocated (Λ : Nat) : LocatedSpectralGap (realGaps Λ) :=
  reconTransfer_located_gap Λ

/-- **The real per-volume margin is the constant `1 − rho gw`.**  Definitionally:
`gapMargin = 1 − sep` and `clustering_implies_located` sets `sep := rho gw`, so
the margin is `1 − rho gw` at EVERY volume — the genuine single-edge
transfer-operator gap is volume-independent at fixed coupling/spacing. -/
theorem realLocated_gapMargin (Λ : Nat) :
    (realLocated Λ).gapMargin = (1 : Q') - rho gw := rfl

/-! ## 2. The uniform floor — the constant margin `1 − rho gw ≥ 1/2`

`rho gw = coeffW gw 1 = 2·(1/6)³ = 1/108`, so the margin is the constant
`1 − 1/108 = 107/108`.  The floor `1/2` clears it by a single decidable `Q'`
rational comparison (the margin is Λ-independent, so this is ONE inequality). -/

/-- The uniform clustering floor `1/2`. -/
def realFloor : Q' := Q'.mkPos 1 2 (by decide)

theorem realFloor_pos : (0 : Q') < realFloor := by
  show (0 : Int) * (2 : Int) < (1 : Int) * (1 : Int); decide

/-- **The constant margin clears the floor:** `1/2 ≤ 1 − rho gw` — a single
decidable `Q'` rational inequality (`rho gw = 2·(1/6)³ = 1/108`, margin
`= 107/108 ≥ 1/2`).  Λ-independent: the same comparison at every volume. -/
theorem realFloor_le_margin : realFloor ≤ (1 : Q') - rho gw := by
  show realFloor ≤ (1 : Q') - rho gw
  decide

/-- **Uniform floor (PROVED).**  `1/2 ≤ gapMargin Λ` for every `Λ` — transport the
constant inequality through `realLocated_gapMargin`.  The margin is
Λ-independent, so this is the one rational comparison `1/2 ≤ 107/108`. -/
theorem realUniform_floor (Λ : Nat) : realFloor ≤ (realLocated Λ).gapMargin := by
  rw [realLocated_gapMargin Λ]
  exact realFloor_le_margin

/-! ## 3. The trivial Λ-tail — `tailConst = 0`

The single-edge gap is volume-independent, so consecutive margins are EQUAL and
the geometric single-step bounds hold with `tailConst = 0`
(`geoIncr 0 Λ ≃ 0`, so `m ≤ m + 0`). -/

/-- **Upper single-step bound (PROVED, trivial tail).**  `gapMargin (Λ+1) ≤
gapMargin Λ + geoIncr 0 Λ`.  Both margins are the constant `1 − rho gw`, and
`geoIncr 0 Λ ≃ 0`, so this is `m ≤ m + 0`. -/
theorem realIncr_up (Λ : Nat) :
    (realLocated (Λ + 1)).gapMargin
      ≤ (realLocated Λ).gapMargin + geoIncr (0 : Q') Λ := by
  rw [realLocated_gapMargin (Λ + 1), realLocated_gapMargin Λ]
  -- (1 − rho gw) ≤ (1 − rho gw) + geoIncr 0 Λ, since geoIncr 0 Λ ≥ 0
  exact Q'.add_le_self_of_nonneg ((1 : Q') - rho gw) (geoIncr (0 : Q') Λ)
    (Q'.le_of_eqv (Q'.eqv_symm (geoIncr_zero Λ)))

/-- **Lower single-step bound (PROVED, trivial tail).**  `gapMargin Λ ≤
gapMargin (Λ+1) + geoIncr 0 Λ`.  Symmetric to `realIncr_up`. -/
theorem realIncr_lo (Λ : Nat) :
    (realLocated Λ).gapMargin
      ≤ (realLocated (Λ + 1)).gapMargin + geoIncr (0 : Q') Λ := by
  rw [realLocated_gapMargin (Λ + 1), realLocated_gapMargin Λ]
  exact Q'.add_le_self_of_nonneg ((1 : Q') - rho gw) (geoIncr (0 : Q') Λ)
    (Q'.le_of_eqv (Q'.eqv_symm (geoIncr_zero Λ)))

/-! ## 4. The rescaling modulus — `tailConst = 0` closes any tolerance

With `tailConst = 0`, `(2·0)·δ = 0 ≤ ε` for any positive `ε`; take `δ = 1`. -/

/-- **The modulus (PROVED, trivial tail).**  For any `ε > 0`, `δ := 1 > 0`
discharges `(2·0)·1 ≤ ε`: the left side is `0`, below any positive `ε`. -/
theorem realModulus (ε : Q') (hε : (0 : Q') < ε) :
    ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * (0 : Q')) * δ ≤ ε := by
  refine ⟨(1 : Q'), UniformClusterFromKP.zero_lt_one', ?_⟩
  -- (2·0)·1 ≃ 0 ≤ ε
  have hzero : ((Q'.ofNat 2 * (0 : Q')) * (1 : Q')).eqv (0 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (Q'.ofNat 2 * (0 : Q'))) ?_
    exact Q'.mul_zero_eqv (Q'.ofNat 2)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) ?_
  exact Q'.le_of_lt hε

/-! ## 5. The REAL-correlator uniform cluster bound (ASSEMBLED)

All fields PROVED, with the located family the GENUINE
`reconTransfer_located_gap` (real Wilson decay) and a trivial Λ-tail. -/

/-- **The real-correlator volume-uniform cluster bound.**  An inhabitant of
`UniformClusterBound` whose per-volume located gaps are the GENUINE
`reconTransfer_located_gap` — each derived from the REAL `wilsonG` connected-
correlator decay — with the volume-independent margin `1 − rho gw = 107/108`, a
uniform floor `1/2`, and a TRIVIAL geometric tail `tailConst = 0` (the single-edge
gap does not vary with volume).  Complementary to `genuineUniformClusterBound`
(real Λ-tail, synthetic margin); this one is real margin, no Λ-variation. -/
def realCorrUniformClusterBound : UniformClusterBound where
  gaps := realGaps
  located := realLocated
  floorRate := realFloor
  floorRate_pos := realFloor_pos
  uniform_floor := realUniform_floor
  tailConst := (0 : Q')
  tailConst_nonneg := Q'.le_refl' (0 : Q')
  incr_up := realIncr_up
  incr_lo := realIncr_lo
  modulus := realModulus

/-- The real bound's per-volume located gap IS the genuine
`reconTransfer_located_gap` (derived from the real Wilson decay). -/
theorem realCorr_located_is_reconTransfer (Λ : Nat) :
    realCorrUniformClusterBound.located Λ = reconTransfer_located_gap Λ := rfl

/-- The real bound's geometric tail constant is `0` (the single-edge gap is
volume-independent — trivial Λ-variation, the honest property of the real
object). -/
theorem realCorr_tailConst : realCorrUniformClusterBound.tailConst = (0 : Q') := rfl

/-- The real bound's per-volume margin is the volume-independent `1 − rho gw`
(`= 107/108`) — the genuine single-edge transfer-operator gap, the SAME at every
volume. -/
theorem realCorr_margin (Λ : Nat) :
    (realCorrUniformClusterBound.located Λ).gapMargin = (1 : Q') - rho gw :=
  realLocated_gapMargin Λ

/-! ## 6. Capstone: strictly-positive infinite-volume mass off the REAL gap

Composing the real-correlator bound with the proved positivity capstone yields a
strictly-positive infinite-volume mass at fixed spacing, resting on the REAL
single-edge transfer-operator correlator gap. -/

/-- The continuum gap rate built from the REAL-correlator bound: the `CReal` limit
of the (constant) per-volume margin sequence `1 − rho gw`. -/
def realContinuumRate : CReal := continuumRate realCorrUniformClusterBound

/-- Every approximation of the real continuum rate is the per-volume margin
`gapMargin Λ = 1 − rho gw` — the limit is fed by the genuine
`reconTransfer_located_gap` family. -/
@[simp] theorem realContinuumRate_approx (Λ : Nat) :
    realContinuumRate.approx Λ = (realLocated Λ).gapMargin := rfl

/-- **Capstone (positivity off the REAL gap).**  The infinite-volume mass built
from `realCorrUniformClusterBound` is a strictly-positive constructive real —
`clusterBound_continuum_mass_isPositive` at the inhabitant whose located family is
the genuine `reconTransfer_located_gap` (the real Wilson connected-correlator
gap).  This is positive infinite-volume (Λ→∞, fixed spacing) mass resting on the
REAL single-edge correlator gap at strong coupling `w = 1/6`. -/
theorem realCorr_continuum_mass_isPositive :
    CReal.IsPositive realContinuumRate :=
  clusterBound_continuum_mass_isPositive realCorrUniformClusterBound

/-- **Capstone (packaged).**  The real-correlator continuum mass as `Type`-level
data with its positivity proof, fed end-to-end by the real-correlator bound. -/
def realCorr_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  clusterBound_continuum_gap_bridge realCorrUniformClusterBound

/-- The packaged mass is exactly the real continuum rate. -/
theorem realCorr_bridge_fst :
    realCorr_continuum_gap_bridge.1 = realContinuumRate := rfl

/-- The real continuum rate's `Λ`-th approximation is the constant margin
`1 − rho gw` (`= 107/108`) — the limit of the volume-independent real-correlator
gap-margin sequence. -/
theorem realContinuumRate_approx_eq (Λ : Nat) :
    realContinuumRate.approx Λ = (1 : Q') - rho gw :=
  realLocated_gapMargin Λ

end YMGap.Continuum.RealCorrMass

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RealCorrMass.geoIncr_zero
#print axioms YMGap.Continuum.RealCorrMass.realLocated_gapMargin
#print axioms YMGap.Continuum.RealCorrMass.realFloor_le_margin
#print axioms YMGap.Continuum.RealCorrMass.realUniform_floor
#print axioms YMGap.Continuum.RealCorrMass.realIncr_up
#print axioms YMGap.Continuum.RealCorrMass.realIncr_lo
#print axioms YMGap.Continuum.RealCorrMass.realModulus
#print axioms YMGap.Continuum.RealCorrMass.realCorrUniformClusterBound
#print axioms YMGap.Continuum.RealCorrMass.realCorr_located_is_reconTransfer
#print axioms YMGap.Continuum.RealCorrMass.realCorr_margin
#print axioms YMGap.Continuum.RealCorrMass.realContinuumRate_approx
#print axioms YMGap.Continuum.RealCorrMass.realCorr_continuum_mass_isPositive
#print axioms YMGap.Continuum.RealCorrMass.realCorr_continuum_gap_bridge
#print axioms YMGap.Continuum.RealCorrMass.realContinuumRate_approx_eq
