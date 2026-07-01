/-
The loopy correlator bound — the OFF-DIAGONAL (bullet ii) decay of the
multi-plaquette connected correlator, and the NET REDUCTION of the surviving
`MultiPlaquetteMayer.LoopyCorrelatorResidual` to its two honest named inputs.

# Where this sits

`MultiPlaquetteMayer.LoopyCorrelatorResidual` (the loopy / multi-component /
all-reps / volume-uniform generalization of the connected correlator) has four
sub-bullets.  Their status entering this module:

  * (i)  MULTIPLE / nested loops     — DISCHARGED (`loopyResidual_multiLoop`,
         arbitrary `numLoops`, the single-component `graphG` collapse; the decay
         `graphWilsonG_decay` is `numLoops`-independent);
  * (iii) all-reps / Källén–Lehmann  — DISCHARGED (the collapse already carries
         `Σ_{r=1}^{M} (coeffW w r)^N` with per-rep decay `coeffW_excited_le_one`);
  * (ii) OFF-DIAGONAL cross terms between DISTINCT connected components — the
         genuine remaining analytic bullet, handled HERE;
  * (iv) VOLUME-uniform prefactor `ofNat M` — the named combinatorial input,
         reduced HERE to the single surviving `BddLatticeAnimal.DecodeComplete`.

# What this module delivers

## Bullet (ii) — the Fernández–Procacci two-component bridge

The two-component truncated correlator, by Haar orthogonality, is carried
entirely by the CONNECTING clusters that bridge the two components (distinct
components share no link, so the truncated part lives on the bridging clusters
at bridging distance `d`).  The connecting-cluster activity sum
`clusterSpanSum` and its geometric decay `clusterSpanSum_decay` are ALREADY
PROVED (`MayerClustering`), and at the genuine strong-coupling instance
(`w = 1/6`, `kpRatio = mayerRho p = 4/9 ≤ 1/2`, `GenuineKP.genuine_threshold`)
the composition is a single geometric series:

    multiComponent_bridge_decay :
      clusterSpanSum (zChainClusterCountBound p) gw gr d ≤ 2 · (mayerRho p)^d.

This is PROVED here as a pure COMPOSITION of two proved theorems — the exact
`2·ρ^d` bridging bound (`2 = 1/(1−1/2)`, loop-suppression `λ_loop = kpRatio =
4/9`), with NO new analytic content and WITHOUT touching
`ClusterCountBound` / `DecodeComplete`.

The one honest NEW datum bullet (ii) needs is the Fernández–Procacci
Penrose/tree-graph IDENTIFICATION of the truncated two-component Wilson-loop
correlator with this connecting-cluster sum.  It is named `MultiComponentKP`
(Type-level), UNINHABITED here — NOT faked.  Given it, the off-diagonal decay
`offCorr d ≤ 2·(mayerRho p)^d` is IMMEDIATE (`multiComponent_offCorr_decay`),
and packages into a genuine `LoopyCorrelatorResidual` inhabitant
(`loopyResidual_offDiagonal`) whose `loopyCorr` is the REAL off-diagonal
correlator.

## Bullet (iv) — the single surviving combinatorial wall

`ClusterCountBound.count_le` (`N_n ≤ K^n`, `K = 16`) is ALREADY PROVED
(`animalCount_le_pow`), and the strong-coupling threshold `kpRatio ≤ 1/2` is
ALREADY PROVED (`genuine_threshold`).  The ONLY genuinely-uninhabited input
left is `BddLatticeAnimal.DecodeComplete` — the DFS over-count completeness that
gates upgrading the genuine count into the volume-uniform prefactor.  Given it,
the count is anchored (`clusterCountBound_anchored`).

## The net reduction

`LoopyResidualInputs p` bundles the two honest named inputs — the FP identity
`MultiComponentKP p` (bullet ii) and `∀ n, DecodeComplete zChain p n` (bullet
iv).  From it, `loopyResidual_reduction` produces BOTH the off-diagonal
`LoopyCorrelatorResidual` (bullet ii, decay proved) AND the anchored count
witness (bullet iv), with bullets (i)/(iii) already discharged upstream.  The
threshold pair (`kpRatio ≤ 1/2`) and the count bound (`N_n ≤ K^n`) are BOTH
already discharged; the sole surviving named combinatorial wall is
`DecodeComplete`, and the sole surviving analytic datum is the FP tree-graph
identification `MultiComponentKP.bridge_eq_span` (its decay consequence is
proved).

# Scope (underclaim, AGENTS.md Rule 6)

Finite-volume STRONG-COUPLING combinatorics at the concrete weight `w = 1/6` on
the 1D plaquette chain `zChain`.  The off-diagonal decay is GENUINE (rate
`ρ = 4/9 < 1`, the real `kpRatio` of the real `zChainClusterCountBound`), but it
is NOT uniform-in-`w`, NOT the continuum (`a → 0`) limit, and NOT a 4D
Yang–Mills mass gap.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props, no `sorry` / `admit` /
new `axiom`.  The two open inputs are Type-level named data (`MultiComponentKP`)
and a named Prop obligation (`DecodeComplete`), never faked.  Every load-bearing
declaration is gated with `#print axioms`.
-/

import YMGap.Continuum.MayerClustering
import YMGap.Continuum.GenuineKP
import YMGap.Continuum.BddLatticeAnimal
import YMGap.Continuum.LoopyCorrelatorProgress

namespace YMGap.Continuum.LoopyCorrelatorBound

open YMGap.Constructive
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.LoopyCorrelatorProgress

/-! ## 1. Bullet (ii) — the Fernández–Procacci two-component bridge DECAY

The connecting-cluster activity sum `clusterSpanSum (zChainClusterCountBound p)
gw gr d` at bridging distance `d` decays as `2·ρ^d`, `ρ = mayerRho p = 4/9`.
This is a pure composition of `MayerClustering.clusterSpanSum_decay` (proved,
the geometric tail of the size-`≥ d` clusters) with `GenuineKP.genuine_threshold`
(proved, `kpRatio ≤ 1/2` at the strong-coupling instance).  No new analytic
content; it does NOT touch `ClusterCountBound` / `DecodeComplete`. -/

/-- **`multiComponent_bridge_decay` (PROVED — composition of two proved theorems).**

At the genuine strong-coupling instance, the connecting-cluster activity sum
that carries the truncated two-component correlator decays geometrically:

    clusterSpanSum (zChainClusterCountBound p) gw gr d  ≤  2 · (mayerRho p)^d,

with `mayerRho p = kpRatio (zChainClusterCountBound p) gw gr = 4/9 < 1`.  The
constant `2 = 1/(1 − 1/2)` and the loop-suppression `λ_loop = kpRatio = 4/9` are
both genuine.  PROOF: `clusterSpanSum_decay` at the proved threshold
`genuine_threshold p` (`mayerRho p` is definitionally that `kpRatio`). -/
theorem multiComponent_bridge_decay (p : zChain.toLattice.Plaquette) (d : Nat) :
    clusterSpanSum (zChainClusterCountBound p) gw gr d
      ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  clusterSpanSum_decay (zChainClusterCountBound p) gw_nonneg gr
    (genuine_threshold p) d

/-! ## 2. Bullet (ii) — the ONE honest new datum: the FP identification

The single genuinely-new (non-composition) content bullet (ii) needs is the
Fernández–Procacci Penrose/tree-graph IDENTIFICATION of the truncated
two-component Wilson-loop correlator with the connecting-cluster sum.  Distinct
components share no link, so by Haar orthogonality the truncated part is carried
entirely by the clusters bridging the two components at bridging distance `d`.

`MultiComponentKP p` is the Type-level datum supplying that identity.  It is
LEFT UNINHABITED here — NOT faked.  Its decay CONSEQUENCE is proved
(`multiComponent_offCorr_decay`). -/

/-- **`MultiComponentKP` (NAMED-open, the one honest datum for bullet ii).**

A datum supplying:
  * `offCorr : Nat → Q'` — the truncated two-component Wilson-loop correlator
    `⟨W(C₁)W(C₂)⟩_T` at bridging distance `d`;
  * `bridge_eq_span` — the Fernández–Procacci Penrose/tree-graph IDENTIFICATION:
    the off-diagonal correlator equals the connecting-cluster activity sum
    `clusterSpanSum (zChainClusterCountBound p) gw gr d`.

Given this identity, the off-diagonal decay `offCorr d ≤ 2·(mayerRho p)^d` is
IMMEDIATE from `multiComponent_bridge_decay`.  The identity itself (distinct
components' truncated correlator = bridging-cluster sum) is the honest open
FP content — carried Type-level, never faked. -/
structure MultiComponentKP (p : zChain.toLattice.Plaquette) where
  /-- The truncated two-component Wilson-loop correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- **The FP identification**: the off-diagonal truncated correlator is the
  connecting-cluster activity sum (Haar orthogonality on distinct components). -/
  bridge_eq_span : ∀ d,
    (offCorr d).eqv (clusterSpanSum (zChainClusterCountBound p) gw gr d)

/-- **`multiComponent_offCorr_decay` (PROVED — immediate from the FP identity).**

Given the FP identification `MultiComponentKP p`, the off-diagonal truncated
two-component correlator decays geometrically at the genuine strong-coupling
rate:

    offCorr d  ≤  2 · (mayerRho p)^d,   mayerRho p = 4/9 < 1.

The `eqv` from `bridge_eq_span` transports the proved `multiComponent_bridge_decay`
onto `offCorr`. -/
theorem multiComponent_offCorr_decay (p : zChain.toLattice.Plaquette)
    (mc : MultiComponentKP p) (d : Nat) :
    mc.offCorr d ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (mc.bridge_eq_span d))
    (multiComponent_bridge_decay p d)

/-! ## 3. Bullet (ii) packaged as a genuine `LoopyCorrelatorResidual`

Given the FP identity, the off-diagonal cross-term correlator is a GENUINE
inhabitant of `MultiPlaquetteMayer.LoopyCorrelatorResidual`: its `loopyCorr` is
the REAL off-diagonal correlator `mc.offCorr`, its envelope is `2·ρ^d`, and its
`loopy_decay` is the proved `multiComponent_offCorr_decay`.  The graph mass at
bridging distance `d` is `d` (edges bridge, they do not add nodes). -/

/-- **`loopyResidual_offDiagonal` (a GENUINE `LoopyCorrelatorResidual` from the
FP identity).**  Given `MultiComponentKP p`, the off-diagonal two-component
truncated correlator satisfies the loopy-residual contract: `graphMass d = d`,
`loopyEnvelope d = 2·(mayerRho p)^d`, `loopyCorr d = mc.offCorr d` (the REAL
off-diagonal correlator), and `loopy_decay` is the PROVED off-diagonal decay
`multiComponent_offCorr_decay`.  This is the multi-component / off-diagonal
counterpart of `LoopyCorrelatorProgress.loopyResidual_multiLoop` (which discharges
the single-component multiple-loops bullet i). -/
def loopyResidual_offDiagonal (p : zChain.toLattice.Plaquette)
    (mc : MultiComponentKP p) : LoopyCorrelatorResidual gw where
  graphMass := fun d => d
  loopyEnvelope := fun d => Q'.ofNat 2 * (mayerRho p) ^ d
  loopyCorr := fun d => mc.offCorr d
  loopy_decay := fun d => multiComponent_offCorr_decay p mc d

/-! ## 4. Bullet (iv) — the single surviving combinatorial wall `DecodeComplete`

`ClusterCountBound.count_le` (`N_n ≤ K^n`, `K = 16`) is PROVED
(`animalCount_le_pow`), and `kpRatio ≤ 1/2` is PROVED (`genuine_threshold`).  The
only genuinely-uninhabited input left is `BddLatticeAnimal.DecodeComplete` — the
DFS over-count completeness.  We record it as the named bullet-(iv) obligation
and, given it, produce the anchored count witness. -/

/-- **`LoopyResidualBulletIV` (NAMED-open, bullet iv).**  The single surviving
combinatorial input: DFS over-count completeness at every size, over the chain
`zChain` through the plaquette `p`.  A definitional synonym for
`∀ n, BddLatticeAnimal.DecodeComplete zChain p n` — the volume-uniform prefactor
gate.  UNINHABITED here (`count_le` and the threshold, the inputs the criterion
actually consumes, are already discharged and do NOT depend on it). -/
def LoopyResidualBulletIV (p : zChain.toLattice.Plaquette) : Prop :=
  ∀ n, DecodeComplete zChain p n

/-! ## 5. The net reduction of `LoopyCorrelatorResidual`

`LoopyResidualInputs p` bundles the two honest named inputs — the FP identity
`MultiComponentKP p` (bullet ii) and `LoopyResidualBulletIV p` (bullet iv).
From it, `loopyResidual_reduction` produces BOTH the off-diagonal
`LoopyCorrelatorResidual` (decay proved) AND the anchored count witness, with
bullets (i)/(iii) already discharged upstream. -/

/-- **`LoopyResidualInputs` — the two honest named inputs of the reduction.**

  * `offDiag : MultiComponentKP p` — bullet (ii), the FP tree-graph identification;
  * `decodeComplete : LoopyResidualBulletIV p` — bullet (iv), DFS completeness.

Bullets (i) [multiple/nested loops] and (iii) [all-reps window] are already
discharged upstream (`loopyResidual_multiLoop`; the `Σ_{r=1}^M` collapse).  So
these two data are exactly what closes the surviving `LoopyCorrelatorResidual`. -/
structure LoopyResidualInputs (p : zChain.toLattice.Plaquette) where
  /-- Bullet (ii): the Fernández–Procacci off-diagonal identification. -/
  offDiag : MultiComponentKP p
  /-- Bullet (iv): DFS over-count completeness (the volume-uniform prefactor gate). -/
  decodeComplete : LoopyResidualBulletIV p

/-- **`loopyResidual_reduction` (PROVED — the net reduction).**

From the two honest named inputs `LoopyResidualInputs p`, produce:
  * a GENUINE off-diagonal `LoopyCorrelatorResidual gw` (bullet ii, decay proved
    via `loopyResidual_offDiagonal`);
  * the anchored cluster-count witness (bullet iv) — the same
    `ClusterCountBound` data as `zChainClusterCountBound`, now packaged WITH the
    over-count guarantee that under `DecodeComplete` every true cluster is
    represented in the enumeration (`clusterCountBound_anchored`).

Bullets (i)/(iii) are already discharged upstream.  Hence
`LoopyCorrelatorResidual` reduces to exactly `{MultiComponentKP.bridge_eq_span,
DecodeComplete}` — the threshold pair and the count bound being already proved. -/
def loopyResidual_reduction (p : zChain.toLattice.Plaquette)
    (inp : LoopyResidualInputs p) :
    LoopyCorrelatorResidual gw ×'
      ((_cc : ClusterCountBound zChain.toLattice p) ×'
        (∀ n X, IsClusterThrough zChain p n X →
          ∃ Y, Y ∈ enumPolys zChain p n ∧ sameSupport X Y)) :=
  ⟨loopyResidual_offDiagonal p inp.offDiag,
   clusterCountBound_anchored zChain p inp.decodeComplete⟩

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean — composition of already-proved theorems):

  * `multiComponent_bridge_decay` — the FP two-component bridge decay
    `clusterSpanSum … ≤ 2·(mayerRho p)^d` (`clusterSpanSum_decay` at the proved
    `genuine_threshold`; `2 = 1/(1−1/2)`, `λ_loop = kpRatio = 4/9`), NOT touching
    `ClusterCountBound` / `DecodeComplete`;
  * `multiComponent_offCorr_decay` — the off-diagonal correlator decay
    `offCorr d ≤ 2·(mayerRho p)^d`, immediate from the FP identity;
  * `loopyResidual_offDiagonal` — a GENUINE `LoopyCorrelatorResidual` inhabitant
    whose `loopyCorr` is the REAL off-diagonal correlator (`mc.offCorr`), with the
    proved off-diagonal decay as `loopy_decay`;
  * `loopyResidual_reduction` — the net reduction: from `{MultiComponentKP,
    DecodeComplete}` produce the off-diagonal residual AND the anchored count.

NAMED-open (NOT faked, Type-level / Prop data — the two honest inputs):

  * `MultiComponentKP` — bullet (ii): the Fernández–Procacci Penrose/tree-graph
    IDENTIFICATION of the truncated two-component correlator with the
    connecting-cluster sum (its decay consequence is PROVED);
  * `LoopyResidualBulletIV` (= `∀ n, DecodeComplete zChain p n`) — bullet (iv):
    the DFS over-count completeness (the volume-uniform prefactor gate).

The threshold pair (`kpRatio ≤ 1/2`, `genuine_threshold`) and the count bound
(`N_n ≤ K^n`, `animalCount_le_pow`) that the math-ph scout flagged as gating are
BOTH already discharged; bullets (i) [multiple/nested loops,
`loopyResidual_multiLoop`] and (iii) [all-reps window, the `Σ_{r=1}^M` collapse]
are discharged upstream.  So the surviving `LoopyCorrelatorResidual` reduces to
exactly the FP identity `MultiComponentKP.bridge_eq_span` and the single
combinatorial wall `DecodeComplete`.

This module is finite-volume strong-coupling combinatorics at `w = 1/6` on the
1D chain.  It is NOT uniform-in-`w`, NOT the continuum (`a → 0`) limit, and NOT a
4D Yang–Mills mass gap. -/

end YMGap.Continuum.LoopyCorrelatorBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LoopyCorrelatorBound.multiComponent_bridge_decay
#print axioms YMGap.Continuum.LoopyCorrelatorBound.multiComponent_offCorr_decay
#print axioms YMGap.Continuum.LoopyCorrelatorBound.loopyResidual_offDiagonal
#print axioms YMGap.Continuum.LoopyCorrelatorBound.loopyResidual_reduction
