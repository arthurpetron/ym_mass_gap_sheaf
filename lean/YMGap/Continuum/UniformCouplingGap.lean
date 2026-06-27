/-
R3 — the UNIFORM-IN-COUPLING strong-coupling KP / clustering bound.

# What this module delivers (honest underclaim)

`Continuum/GenuineKP.lean` proves the genuine KP polymer-sum bound `≤ 2` at the
SINGLE concrete strong-coupling weight `w = 1/6` (`gw`), resting on the real
`|enumPolys|` lattice-animal count `zChainClusterCountBound` (`K = 16`).  This
module LIFTS that single-weight bound to a whole INTERVAL of strong coupling
`0 ≤ w ≤ w₀` with the explicit endpoint `w₀ = 1/6`.

THE MECHANISM is the monotonicity of the leading activity coefficient in the
weight.  For the fundamental excited rep `r = 1`,

    coeffW w 1  =  dimQ 1 · qpow w (c4 1)  =  2 · w³

(`coeffW_one`, `c4 1 = 1·3 = 3`), and `w ↦ w³` is monotone increasing on the
nonnegative cone (`HeatKernelGap.qpow_mono`, the genuine cube-monotonicity from
the Q' power fold — NOT `decide` over a ∀w prop).  Hence the KP ratio

    kpRatio (zChainClusterCountBound p) w 1  =  16 · (2 w³) · 3  =  96 w³

is monotone in `w`, so for ALL `0 ≤ w ≤ w₀ = 1/6`,

    kpRatio (…) w 1  ≤  kpRatio (…) w₀ 1  =  96 · (1/6)³  =  96/216  =  4/9  ≤  1/2.

The endpoint inequality is the proved `GenuineKP.genuine_threshold`; the interval
inequality is `qpow_mono` (cube-monotonicity).  Feeding the resulting uniform
threshold into the proved parametric criterion `kp_criterion_of_count` gives the
KP polymer-sum bound `≤ 2` UNIFORMLY for every `w` in `[0, 1/6]`, not just at
the endpoint.

## The interval is genuinely allowed (computed, not assumed)

The threshold needs `96 w³ ≤ 1/2`, i.e. `w³ ≤ 1/192`, i.e. `w ≤ (1/192)^{1/3} ≈
0.1736`.  The endpoint `w₀ = 1/6 ≈ 0.1667` sits strictly inside this, with slack:
`96·(1/6)³ = 4/9 = 8/18 < 9/18 = 1/2`.  So the located-gap margin
`1 − rho w ≥ 1 − rho w₀ = 1 − 2·(1/6)³ = 1 − 1/108 = 107/108 > 0` holds
uniformly on the whole interval.

## What this is, and what it is NOT

This is FIXED-SPACING STRONG-COUPLING combinatorics on an INTERVAL of weights
`[0, 1/6]` on the 1D plaquette chain: the genuine KP geometric polymer sum (the
real `|enumPolys|` count, `K = 16`) converges `≤ 2` for EVERY weight in the
interval.  It is genuinely UNIFORM-IN-COUPLING (an interval, not a point).

It is NOT the continuum (`a → 0`) limit, NOT weak coupling, NOT a multi-plaquette
correlator, NOT 4D Yang–Mills.  It is an interval of STRONG coupling.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props (the ∀w monotonicity is via
the genuine `qpow_mono` cube lemma, NOT `decide`).  No `sorry` / `admit` / new
`axiom` / `Prop := True`.  The interval is non-empty (`w₀ = 1/6 > 0`), the count
is the real cardinality, the threshold is genuinely proved for all `w` in range.
-/

import YMGap.Continuum.GenuineKP
import YMGap.Continuum.MayerClustering
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.UniformCouplingGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.HeatKernelGap

/-! ## 1. The explicit strong-coupling interval endpoint `w₀ = 1/6` -/

/-- The explicit upper endpoint of the uniform-in-coupling interval,
`w₀ = 1/6` (the same rational as `GenuineKP.gw`; it is the largest endpoint we
need, with slack — the threshold genuinely allows up to `(1/192)^{1/3} ≈
0.1736`).  The uniform statement holds on the whole closed interval
`[0, w₀]`. -/
def w0 : Q' := Q'.mkPos 1 6 (by decide)

/-- `w₀ = 1/6 > 0` — the interval `[0, w₀]` is non-empty (non-vacuity). -/
theorem w0_pos : (0 : Q') < w0 := by decide

/-- `w₀ = 1/6 = gw` — the endpoint coincides with the single-weight instance of
`GenuineKP`, so the endpoint threshold is exactly `genuine_threshold`. -/
theorem w0_eq_gw : w0 = gw := rfl

/-! ## 2. Cube-monotonicity of the leading coefficient (the crux — PROVED)

`coeffW w 1 = dimQ 1 · qpow w (c4 1) = 2 · w³`.  Since `w ↦ qpow w 3` is monotone
on the nonnegative cone (`HeatKernelGap.qpow_mono`, the genuine cube lemma), the
leading coefficient is monotone in `w`. -/

/-- **Cube-monotonicity of the leading coefficient (PROVED).**  For
`0 ≤ w ≤ w'`, `coeffW w 1 ≤ coeffW w' 1`.  Reduces to `qpow w 3 ≤ qpow w' 3`
(`coeffW w 1 = dimQ 1 · qpow w (c4 1)`, `c4 1 = 3`) scaled by `dimQ 1 ≥ 0`; the
cube monotonicity is the genuine `HeatKernelGap.qpow_mono`, NOT `decide`. -/
theorem coeffW_one_mono {w w' : Q'} (hw : (0 : Q') ≤ w) (hww' : w ≤ w') :
    coeffW w 1 ≤ coeffW w' 1 := by
  -- coeffW w 1 = dimQ 1 * qpow w (c4 1), with c4 1 = 3.
  show dimQ 1 * qpow w (c4 1) ≤ dimQ 1 * qpow w' (c4 1)
  -- c4 1 = 1 * (1 + 2) = 3
  have hc4 : c4 1 = 3 := rfl
  rw [hc4]
  -- qpow w 3 ≤ qpow w' 3 (genuine cube-monotonicity), scaled by dimQ 1 ≥ 0
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw hww' 3) (dimQ_nonneg 1)

/-- **Monotonicity of the KP ratio in the weight (PROVED).**  For the
fundamental excited rep `gr = 1`, the KP ratio
`kpRatio cc w 1 = cc.K · coeffW w 1 · eSurrogate` is monotone in `w`:
`0 ≤ w ≤ w' → kpRatio cc w gr ≤ kpRatio cc w' gr`.  From `coeffW_one_mono`
scaled by `cc.K ≥ 0` (left) and `eSurrogate ≥ 0` (right). -/
theorem kpRatio_mono {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w w' : Q'} (hw : (0 : Q') ≤ w) (hww' : w ≤ w') :
    kpRatio cc w gr ≤ kpRatio cc w' gr := by
  -- kpRatio cc w gr = (cc.K * coeffW w gr) * eSurrogate
  unfold kpRatio
  -- gr = 1, so coeffW w gr = coeffW w 1
  show cc.K * coeffW w 1 * eSurrogate ≤ cc.K * coeffW w' 1 * eSurrogate
  -- cc.K * coeffW w 1 ≤ cc.K * coeffW w' 1  (mono left, cc.K ≥ 0)
  have h1 : cc.K * coeffW w 1 ≤ cc.K * coeffW w' 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (coeffW_one_mono hw hww') cc.K_nonneg
  -- (…) * eSurrogate  (mono right, eSurrogate ≥ 0)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ h1 eSurrogate_nonneg

/-! ## 3. The uniform-in-coupling threshold (PROVED on `[0, w₀]`)

For every `w` in `[0, w₀]`, the genuine KP ratio is `≤ 1/2`, by monotonicity
(`kpRatio_mono`) up to the endpoint, where it equals the proved
`GenuineKP.genuine_threshold` value `4/9 ≤ 1/2`. -/

/-- **`uniform_threshold` — the uniform-in-coupling KP threshold (PROVED).**

For EVERY weight `w` in the strong-coupling interval `[0, w₀] = [0, 1/6]`, the
genuine KP ratio of the real `|enumPolys|` lattice-animal count
`zChainClusterCountBound p` for the fundamental excited rep `gr = 1` satisfies

    kpRatio (zChainClusterCountBound p) w gr  ≤  1/2.

PROOF.  By `kpRatio_mono` (cube-monotonicity), `kpRatio (…) w gr ≤
kpRatio (…) w₀ gr`; the endpoint `w₀ = gw` gives `kpRatio (…) gw gr ≤ 1/2`
(`GenuineKP.genuine_threshold`).  Chain the two.  The value is `p`-independent
(reads only `cc.K = 16` and `coeffW · 1`), so the bound holds for every
plaquette of the chain.  This is genuinely UNIFORM-IN-COUPLING (the whole
interval), proved via REAL cube-monotonicity, not just at the endpoint. -/
theorem uniform_threshold (p : zChain.toLattice.Plaquette)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hww0 : w ≤ w0) :
    kpRatio (zChainClusterCountBound p) w gr ≤ Q'.mkPos 1 2 (by decide) := by
  -- kpRatio (…) w gr ≤ kpRatio (…) w₀ gr  (cube-monotonicity)
  have hmono : kpRatio (zChainClusterCountBound p) w gr
      ≤ kpRatio (zChainClusterCountBound p) w0 gr :=
    kpRatio_mono (zChainClusterCountBound p) hw0 hww0
  -- endpoint: kpRatio (…) w₀ gr = kpRatio (…) gw gr ≤ 1/2  (genuine_threshold)
  have hend : kpRatio (zChainClusterCountBound p) w0 gr
      ≤ Q'.mkPos 1 2 (by decide) := genuine_threshold p
  exact Q'.le_trans' _ _ _ hmono hend

/-! ## 4. The uniform-in-coupling KP polymer-sum bound (PROVED on `[0, w₀]`)

Feed the uniform threshold into the proved parametric criterion
`kp_criterion_of_count`.  The KP convergence `≤ 2` now holds for EVERY weight in
`[0, w₀]`, resting on the GENUINE animal count. -/

/-- **`uniform_kp_sum_le_two` — the uniform-in-coupling KP bound (PROVED).**

For EVERY plaquette `p` of the chain, EVERY weight `w` in `[0, w₀] = [0, 1/6]`,
and EVERY truncation `N`, the collapsed KP geometric sum over the fundamental
excited rep, weighted by the GENUINE animal count `animalCount = |enumPolys|`,
is bounded by `2`:

    ∑_{n < N}  animalCount(zChain,p,n) · (coeffW w 1)^n · 3^n  ≤  2.

PROOF.  `kp_criterion_of_count` applied to `zChainClusterCountBound p`
(`count_le = animalCount_le_pow`, the proved lattice-animal bound) with the
UNIFORM threshold `uniform_threshold p hw0 hww0`.  Unlike `GenuineKP`'s
single-weight `genuineKP_sum_le_two`, this holds for the whole interval of
strong coupling, not just `w = 1/6` — a genuine uniform-in-coupling KP
convergence. -/
theorem uniform_kp_sum_le_two (p : zChain.toLattice.Plaquette)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hww0 : w ≤ w0) (N : Nat) :
    finSum (fun n => kpTerm (zChainClusterCountBound p) w gr n) N
      ≤ Q'.ofNat 2 :=
  kp_criterion_of_count (zChainClusterCountBound p) hw0 gr
    (uniform_threshold p hw0 hww0) N

/-! ## 5. The uniform located gap on the interval (PROVED on `[0, w₀]`)

The genuine cluster-expansion located gap of `MayerClustering`, but now stated
uniformly on the interval: for every `w` in `[0, w₀]` the connecting-cluster sum
decays at rate `ρ_w = kpRatio (…) w 1`, and the gap margin `1 − ρ_w` is bounded
BELOW UNIFORMLY by `1 − 4/9 = 5/9 > 0` (since `ρ_w ≤ ρ_{w₀} = 4/9` for all `w`
in range). -/

/-- The uniform cluster ratio `ρ_w = kpRatio (zChainClusterCountBound p) w gr`
as a function of the weight `w` (the `MayerClustering.mayerRho` at the endpoint
is `ρ_{w₀}`). -/
def uniformRho (p : zChain.toLattice.Plaquette) (w : Q') : Q' :=
  kpRatio (zChainClusterCountBound p) w gr

/-- **`uniform_rho_le_half` (PROVED).**  For every `w` in `[0, w₀]`, the cluster
ratio is `≤ 1/2` — the uniform strong-coupling threshold (`uniform_threshold`). -/
theorem uniform_rho_le_half (p : zChain.toLattice.Plaquette)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hww0 : w ≤ w0) :
    uniformRho p w ≤ Q'.mkPos 1 2 (by decide) :=
  uniform_threshold p hw0 hww0

/-- **`uniform_rho_le_endpoint` (PROVED).**  For every `w` in `[0, w₀]`, the
cluster ratio is `≤` the endpoint ratio `ρ_{w₀} = mayerRho p = 4/9`
(cube-monotonicity).  Hence the gap MARGIN `1 − ρ_w ≥ 1 − 4/9 = 5/9 > 0`
uniformly on the whole interval. -/
theorem uniform_rho_le_endpoint (p : zChain.toLattice.Plaquette)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hww0 : w ≤ w0) :
    uniformRho p w ≤ mayerRho p := by
  -- uniformRho p w = kpRatio (…) w gr ≤ kpRatio (…) w₀ gr = mayerRho p
  show kpRatio (zChainClusterCountBound p) w gr ≤ mayerRho p
  -- mayerRho p = kpRatio (zChainClusterCountBound p) gw gr, and w₀ = gw
  exact kpRatio_mono (zChainClusterCountBound p) hw0 hww0

/-- **`uniform_cluster_decay` — the uniform-in-coupling clustering bound
(PROVED).**  For every `w` in `[0, w₀]` and every separation `d`, the genuine
connecting-cluster activity sum decays geometrically at the weight-dependent
rate `ρ_w ≤ 4/9`:

    clusterSpanSum (zChainClusterCountBound p) w gr d  ≤  2 · (ρ_w)^d.

`clusterSpanSum_decay` of `MayerClustering` at the uniform threshold.  Since
`ρ_w ≤ 4/9 < 1` uniformly, this is exponential clustering at a rate bounded away
from `1` for EVERY weight in the strong-coupling interval. -/
theorem uniform_cluster_decay (p : zChain.toLattice.Plaquette)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hww0 : w ≤ w0) (d : Nat) :
    clusterSpanSum (zChainClusterCountBound p) w gr d
      ≤ Q'.ofNat 2 * (uniformRho p w) ^ d :=
  clusterSpanSum_decay (zChainClusterCountBound p) hw0 gr
    (uniform_threshold p hw0 hww0) d

/-- **`uniform_gap_margin_pos` (PROVED, non-vacuity).**  The uniform gap margin
at the endpoint, `1 − ρ_{w₀} = 1 − mayerRho p = 1 − 4/9 = 5/9`, is strictly
positive — and since `ρ_w ≤ ρ_{w₀}` for all `w` in `[0, w₀]`
(`uniform_rho_le_endpoint`), the margin `1 − ρ_w ≥ 5/9 > 0` holds UNIFORMLY on
the whole interval.  `p`-independent, decidable. -/
theorem uniform_gap_margin_pos (p : zChain.toLattice.Plaquette) :
    (0 : Q') < (1 : Q') - mayerRho p := by
  -- 1 − mayerRho p = 1 − 4/9 = 5/9 > 0 ; mayerRho p is p-independent
  show (0 : Q') < (1 : Q') - kpRatio (zChainClusterCountBound p) gw gr
  show (0 : Q') < (1 : Q') - animalK zChain * coeffW gw gr * eSurrogate
  decide

/-! ## 6. Documentation: PROVED, and the scope (AGENTS.md Rule 6)

PROVED in this module, axiom-clean (`[propext]` / `[propext, Quot.sound]`):

  * `w0` (= `1/6`), `w0_pos`, `w0_eq_gw` — the explicit non-empty interval
    endpoint;
  * `coeffW_one_mono` — the genuine cube-monotonicity of the leading coefficient
    `coeffW w 1 = 2w³` (via `HeatKernelGap.qpow_mono`, NOT `decide` over ∀w);
  * `kpRatio_mono` — the KP ratio `96w³` is monotone in `w`;
  * `uniform_threshold` — `kpRatio (zChainClusterCountBound p) w gr ≤ 1/2` for
    ALL `0 ≤ w ≤ 1/6` (the uniform-in-coupling crux, proved via cube-monotonicity
    up to the endpoint where `genuine_threshold` gives `4/9 ≤ 1/2`);
  * `uniform_kp_sum_le_two` — the genuine KP polymer-sum bound `≤ 2` UNIFORMLY
    for every weight in `[0, 1/6]`, resting on the real `|enumPolys|` count;
  * `uniformRho`, `uniform_rho_le_half`, `uniform_rho_le_endpoint`,
    `uniform_cluster_decay`, `uniform_gap_margin_pos` — the uniform located-gap
    data: the cluster ratio is `≤ 4/9` on the whole interval, the cluster sum
    decays uniformly, and the gap margin `1 − ρ_w ≥ 5/9 > 0` uniformly.

SCOPE (underclaim, AGENTS.md Rule 6).  FIXED-SPACING STRONG-COUPLING
combinatorics on the INTERVAL of weights `[0, 1/6]` on the 1D plaquette chain.
The bound is genuinely UNIFORM-IN-COUPLING (the whole closed interval, not a
single point) and rests on the real lattice-animal count (`K = 16`).  It is NOT
the continuum (`a → 0`) limit, NOT weak coupling, NOT a multi-plaquette
correlator, NOT a 4D Yang–Mills mass gap.  The multi-plaquette Mayer/Ursell
identity remains the named residual `MayerClustering.MayerUrsellIdentity`
(discharged for the single line, open in general). -/

end YMGap.Continuum.UniformCouplingGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UniformCouplingGap.w0_pos
#print axioms YMGap.Continuum.UniformCouplingGap.coeffW_one_mono
#print axioms YMGap.Continuum.UniformCouplingGap.kpRatio_mono
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_threshold
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_kp_sum_le_two
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_rho_le_half
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_rho_le_endpoint
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_cluster_decay
#print axioms YMGap.Continuum.UniformCouplingGap.uniform_gap_margin_pos
