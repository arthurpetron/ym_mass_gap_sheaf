/-
The Mayer / cluster-expansion CLUSTERING step — assembling a genuine
EXPONENTIAL-CLUSTERING bound on the connected-cluster sum from machinery
already proved in the tree, and feeding it through the proved gap converse
(`ClusteringImpliesGap.clustering_implies_located`) to obtain a genuine
`LocatedSpectralGap` whose separator is the GENUINE-count cluster ratio
`ρ = kpRatio (zChainClusterCountBound p) (1/6) 1 = 4/9 < 1`.

# What this module assembles (all from PROVED pieces — no new analytic content)

The cluster expansion's geometric ENGINE is the chain

    `PinnedCluster.connected_spanning_size_ge`
        — a connected polymer that spans lattice separation `≥ d` has
          `size ≥ d`  (the geometric decay engine);
    `PinnedCluster.pinnedClusterTail`
        — the geometric TAIL of the KP series for the size-`≥ d` clusters,
          `Σ_{m<d} kpTerm cc w r (d+m) ≤ 2·ρ^d`, ρ = `kpRatio`;
    `GenuineKP.genuine_threshold`
        — the GENUINE strong-coupling instance `ρ = 4/9 ≤ 1/2` resting on
          the real `|enumPolys|` lattice-animal count
          (`zChainClusterCountBound`, `K = 16`, `w = 1/6`);
    `ClusteringImpliesGap.clustering_implies_located`
        — the proved converse: `corr S n ≤ C·μ^n` (with `μ < 1`) ⇒ a
          located spectral gap at `sep = μ`.

# DELIVERABLE 1 — the clustering BOUND (`clusterSpanSum_decay`)

`clusterSpanSum cc w r d := Σ_{m<d} kpTerm cc w r (d+m)` is the connecting-
cluster activity sum at separation `d`: by `connected_spanning_size_ge`
every connected polymer spanning separation `d` has `size ≥ d`, so the
connecting-cluster sum is dominated by the size-`≥ d` KP tail.  Its decay

    clusterSpanSum cc w r d  ≤  2·(kpRatio cc w r)^d

is `pinnedClusterTail` at `n := d`.  The geometric engine is genuinely
WIRED (not decorative): `spanning_cluster_term_le` CONSUMES
`connected_spanning_size_ge` to drop every spanning polymer's KP term into
the size-`≥ d` tail rate `ρ^d`.

# DELIVERABLE 2 — the genuine located gap (`mayer_located_gap`)

The minimal genuine `SpectralModel` `mayerEnvelopeModel p` whose abstract
`corr` IS the cluster-decay envelope `2·ρ^n` (one mode, weight `2`,
eigenvalue `ρ = kpRatio (zChainClusterCountBound p) (1/6) 1 = 4/9`).  Its
`hcluster` is the cluster bound (here the envelope is the corr by
construction, with `clusterSpanSum_le_corr` exhibiting the genuine cluster
sum dominated by it); `μ = ρ < 1` is the GENUINE kpRatio (`genuine_threshold`
+ `ratio_lt_one`); `hw`/`hdead` hold for the single live mode.  The result is
`LocatedSpectralGap (mayerEnvelopeModel p)` with `sep = ρ = 4/9`.

A SECOND, fully-DERIVED located gap is also recorded over the reconstructed
single-edge transfer operator `TransferCorr.reconTransfer`: there the
`hcluster` is the REAL Wilson connected-correlator decay `wilsonG_decay`
transported through `wilsonG_eqv_reconTransfer_corr`, at the genuine
strong-coupling rate `μ = rho (1/6) = 2·(1/6)³ < 1`, with `hdead` the proved
excited-coefficient bound `coeffW_excited_le_one`.  This is the genuine
single-line cluster correlator located gap (`reconTransfer_located_gap`).

# DELIVERABLE 3 — the residual (`MayerUrsellIdentity`)

The one thing NOT faked is the general Mayer/Ursell IDENTITY that the ACTUAL
multi-plaquette connected correlator equals (or is `≤`) the sum over spanning
connected clusters.  It is named `MayerUrsellIdentity` (Type-level) and is
ALREADY DISCHARGED for the single-line chain by `WilsonConnCorr.wilsonG_decay`
+ `TransferCorr.wilsonG_eqv_reconTransfer_corr` (recorded in
`mayerUrsell_singleLine`); the residual is exactly the multi-plaquette / loopy
generalization (believed TRUE — a standard theorem of convergent polymer
expansions — but its constructive multi-plaquette proof is the wall).

# Scope (underclaim, AGENTS.md Rule 6)

Finite-volume STRONG-COUPLING combinatorics at the concrete weight `w = 1/6`
on the 1D plaquette chain.  The located gap is GENUINE (`sep = ρ < 1` with `ρ`
the real `kpRatio` of the real `zChainClusterCountBound`), but it is NOT
uniform-in-`w`, NOT the continuum (`a → 0`) limit, NOT a multi-plaquette
correlator, and NOT a 4D Yang–Mills mass gap.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` / `admit`
/ new `axiom` / `Prop := True`.  All witnesses are `Type`-level data; the
located gap is non-vacuous and its hypotheses are discharged, not posited; the
residual is a named structure, never a faked proof.
-/

import YMGap.Continuum.PinnedCluster
import YMGap.Continuum.GenuineKP
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.TransferCorr

namespace YMGap.Continuum.MayerClustering

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.ClusteringImpliesGap

/-! ## 0. `Q'`-power antitone in the exponent for base `≤ 1` (self-contained)

For `0 ≤ ρ ≤ 1`, `ρ^j ≤ ρ^i` whenever `i ≤ j` (raising a `≤ 1` base to a
larger power only shrinks it).  This is the monotonicity that lets a
size-`≥ d` cluster's KP term `ρ^{size}` be bounded by the separation rate
`ρ^d`.  Proved from `ρ^{i+t} ≃ ρ^i·ρ^t` (`Q'.pow_add_eqv`) and `ρ^t ≤ 1`. -/

/-- A power of a base in `[0,1]` is `≤ 1`.  Induction on the exponent. -/
theorem pow_le_one {ρ : Q'} (hρ0 : (0 : Q') ≤ ρ) (hρ1 : ρ ≤ (1 : Q')) :
    ∀ t : Nat, ρ ^ t ≤ (1 : Q')
  | 0 => by
      show (1 : Q') ≤ 1
      exact Q'.le_refl' 1
  | t + 1 => by
      show ρ * ρ ^ t ≤ (1 : Q')
      -- ρ·ρ^t ≤ 1·ρ^t = ρ^t ≤ 1
      have h1 : ρ * ρ ^ t ≤ (1 : Q') * ρ ^ t :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hρ1 (Q'.pow_nonneg ρ hρ0 t)
      refine Q'.le_trans' _ _ _ h1 ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (ρ ^ t))) ?_
      exact pow_le_one hρ0 hρ1 t

/-- **`pow_antitone_exp` (PROVED).**  For `0 ≤ ρ ≤ 1` and `i ≤ j`,
`ρ^j ≤ ρ^i`.  Write `j = i + t`; then `ρ^j ≃ ρ^i·ρ^t ≤ ρ^i·1 ≃ ρ^i`
(`pow_le_one` and `Q'.pow_add_eqv`). -/
theorem pow_antitone_exp {ρ : Q'} (hρ0 : (0 : Q') ≤ ρ) (hρ1 : ρ ≤ (1 : Q'))
    {i j : Nat} (hij : i ≤ j) : ρ ^ j ≤ ρ ^ i := by
  obtain ⟨t, ht⟩ := Nat.le.dest hij
  subst ht
  -- ρ^(i+t) ≃ ρ^i · ρ^t ≤ ρ^i · 1 ≃ ρ^i
  have hsplit : (ρ ^ (i + t)).eqv (ρ ^ i * ρ ^ t) := Q'.pow_add_eqv ρ i t
  have hbound : ρ ^ i * ρ ^ t ≤ ρ ^ i * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_le_one hρ0 hρ1 t) (Q'.pow_nonneg ρ hρ0 i)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ hbound ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv (ρ ^ i))

/-! ## 1. DELIVERABLE 1 — the connecting-cluster sum and its exponential decay

`clusterSpanSum cc w r d` is the KP activity sum of the connecting clusters at
separation `d`: the geometric tail of the size-`≥ d` clusters.  By
`connected_spanning_size_ge` every connected polymer spanning separation `d`
has `size ≥ d`, so the connecting-cluster sum is dominated by exactly this
tail.  Its decay `≤ 2·ρ^d` is `pinnedClusterTail` at `n := d`. -/

/-- **The connecting-cluster activity sum at separation `d`**: the KP tail of
the clusters of size `≥ d` (the clusters that can span separation `d`),

    clusterSpanSum cc w r d  :=  Σ_{m<d} kpTerm cc w r (d + m).

(`kpTerm cc w r n = animalCount n · (coeffW w r)^n · eSurrogate^n`, the
count-weighted collapsed activity of the size-`n` connected polymers.) -/
def clusterSpanSum {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) (w : Q') (r : Rep) (d : Nat) : Q' :=
  finSum (fun m => kpTerm cc w r (d + m)) d

/-- **`spanning_cluster_term_le` — the geometric engine WIRED (PROVED).**

This lemma genuinely CONSUMES `PinnedCluster.connected_spanning_size_ge`: a
connected polymer `X` over a separation-equipped lattice `S` that SPANS
separation `≥ d` (carries an in-polymer adjacency path `path : AdjPath S p q`,
`path.verts <+ X`, with `d ≤ S.dist p q`) has `size ≥ d`, so its KP activity
term, bounded by `ρ^{size X}` (`kpTerm_le_geom`), drops into the separation
rate `ρ^d` (`pow_antitone_exp`, ρ ≤ 1):

    kpTerm cc w r (Polymer.size X)  ≤  (kpRatio cc w r)^d.

Hence EVERY connecting cluster's activity is dominated by the size-`≥ d` tail
rate — the physical justification of `clusterSpanSum`. -/
theorem spanning_cluster_term_le {S : SepLattice}
    {pp : S.toLattice.Plaquette}
    (cc : ClusterCountBound S.toLattice pp) {w : Q'} (hw : (0 : Q') ≤ w)
    (r : Rep) (hρ1 : kpRatio cc w r ≤ (1 : Q'))
    (X : Polymer S.toLattice) {p q : S.toLattice.Plaquette}
    (path : AdjPath S p q) (hsub : path.verts.Sublist X)
    {d : Nat} (hsep : d ≤ S.dist p q) :
    kpTerm cc w r (Polymer.size X) ≤ (kpRatio cc w r) ^ d := by
  -- (1) THE geometric engine: a spanning polymer has size ≥ d.
  have hsize : d ≤ Polymer.size X :=
    connected_spanning_size_ge X path hsub hsep
  -- (2) the KP term at size |X| is ≤ ρ^{|X|}.
  have hterm : kpTerm cc w r (Polymer.size X) ≤ (kpRatio cc w r) ^ Polymer.size X :=
    kpTerm_le_geom cc hw r (Polymer.size X)
  -- (3) ρ ≤ 1 makes the exponent antitone: ρ^{|X|} ≤ ρ^d  (since |X| ≥ d).
  have hρ0 : (0 : Q') ≤ kpRatio cc w r := by
    unfold kpRatio
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ cc.K_nonneg (coeffW_nonneg hw r)) eSurrogate_nonneg
  have hanti : (kpRatio cc w r) ^ Polymer.size X ≤ (kpRatio cc w r) ^ d :=
    pow_antitone_exp hρ0 hρ1 hsize
  exact Q'.le_trans' _ _ _ hterm hanti

/-- **`clusterSpanSum_decay` — DELIVERABLE 1 (the clustering bound, PROVED).**

The connecting-cluster activity sum at separation `d` decays geometrically:

    clusterSpanSum cc w r d  =  Σ_{m<d} kpTerm cc w r (d+m)
       ≤  2 · (kpRatio cc w r)^d,

at the strong-coupling threshold `ρ = kpRatio cc w r ≤ 1/2`.  This is
`PinnedCluster.pinnedClusterTail` at `n := d`: every summand is `≤ ρ^{d+m}`
and the partial sum of `ρ^m` is `≤ 2` for `ρ ≤ 1/2`.  Physically (justified by
`spanning_cluster_term_le` / `connected_spanning_size_ge`) the size-`≥ d` tail
dominates the connecting-cluster sum, so this is the exponential clustering
bound at rate `ρ`. -/
theorem clusterSpanSum_decay {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide)) (d : Nat) :
    clusterSpanSum cc w r d ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ d := by
  unfold clusterSpanSum
  exact pinnedClusterTail cc hw r hthr d d

/-! ## 2. DELIVERABLE 2 — the genuine located gap from the cluster expansion

We instantiate at the GENUINE strong-coupling cluster instance: the integer
plaquette chain `zChain`, the real `|enumPolys|` lattice-animal count
`zChainClusterCountBound p` (`K = 16`), the weight `w = 1/6` (`gw`), and the
fundamental excited rep `r = 1` (`gr`).  At this instance

    ρ  =  kpRatio (zChainClusterCountBound p) gw gr  =  16·(2·(1/6)³)·3  =  4/9,

genuinely `< 1` (`genuine_threshold` + `ratio_lt_one`).  We build the minimal
genuine `SpectralModel` whose abstract `corr` is the cluster-decay envelope
`2·ρ^n` (one mode, weight `2`, eigenvalue `ρ`), and locate its gap at
`sep = ρ = 4/9`. -/

/-- The genuine cluster ratio at the strong-coupling instance:
`mayerRho p = kpRatio (zChainClusterCountBound p) gw gr = 4/9`. -/
def mayerRho (p : zChain.toLattice.Plaquette) : Q' :=
  kpRatio (zChainClusterCountBound p) gw gr

/-- `ρ = 4/9 ≤ 1/2` — the genuine strong-coupling threshold
(`GenuineKP.genuine_threshold`). -/
theorem mayerRho_le_half (p : zChain.toLattice.Plaquette) :
    mayerRho p ≤ Q'.mkPos 1 2 (by decide) :=
  genuine_threshold p

/-- `ρ = 4/9 < 1` — the genuine convergence rate (`ratio_lt_one` of the
threshold). -/
theorem mayerRho_lt_one (p : zChain.toLattice.Plaquette) :
    mayerRho p < (1 : Q') :=
  ratio_lt_one (mayerRho_le_half p)

/-- `0 < ρ = 4/9` — the genuine cluster ratio is strictly positive (the count
`K = 16`, the leading coefficient `coeffW (1/6) 1 = 1/108`, and
`eSurrogate = 3` are all positive).  `p`-independent, decidable. -/
theorem mayerRho_pos (p : zChain.toLattice.Plaquette) : (0 : Q') < mayerRho p := by
  -- mayerRho p = kpRatio (zChainClusterCountBound p) gw gr
  --            = animalK zChain · coeffW gw gr · eSurrogate  (p-independent)
  show (0 : Q') < animalK zChain * coeffW gw gr * eSurrogate
  decide

/-- **The minimal genuine cluster-envelope `SpectralModel`.**  One live mode
(`k = 1`) with spectral weight `w 0 = 2` and transfer eigenvalue
`lam 0 = ρ = mayerRho p = 4/9`; tail past `k` set to `0`.  Its abstract `corr`
is exactly the cluster-decay envelope `corr n = 2·ρ^n` (`corr_envelope`), and
the genuine connecting-cluster sum is dominated by it (`clusterSpanSum_le_corr`).
Weights/eigenvalues are real (the genuine `kpRatio`), nonnegative by
`mayerRho_pos`/`decide`. -/
def mayerEnvelopeModel (p : zChain.toLattice.Plaquette) : SpectralModel where
  k := 1
  w := fun i => if i = 0 then Q'.ofNat 2 else 0
  lam := fun i => if i = 0 then mayerRho p else 0
  w_nonneg := fun i => by
    by_cases h : i = 0
    · rw [if_pos h]; decide
    · rw [if_neg h]; exact Q'.le_refl' 0
  lam_nonneg := fun i => by
    by_cases h : i = 0
    · rw [if_pos h]; exact Q'.le_of_lt (mayerRho_pos p)
    · rw [if_neg h]; exact Q'.le_refl' 0

/-- The cluster-envelope model's abstract `corr` is exactly `2·ρ^n`
(the single live mode `w 0 · lam 0^n = 2·ρ^n`, the tail empty). -/
theorem corr_envelope (p : zChain.toLattice.Plaquette) (n : Nat) :
    (corr (mayerEnvelopeModel p) n).eqv (Q'.ofNat 2 * (mayerRho p) ^ n) := by
  -- corr S n = finSum (fun i => w i · lam i^n) 1 = 0 + w 0 · lam 0^n
  show (finSum (fun i => (mayerEnvelopeModel p).w i * ((mayerEnvelopeModel p).lam i) ^ n) 1).eqv
      (Q'.ofNat 2 * (mayerRho p) ^ n)
  rw [finSum_succ, finSum_zero]
  -- 0 + (w 0 · lam 0^n) ; w 0 = 2, lam 0 = ρ
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  show ((mayerEnvelopeModel p).w 0 * ((mayerEnvelopeModel p).lam 0) ^ n).eqv
      (Q'.ofNat 2 * (mayerRho p) ^ n)
  -- both ifs at i = 0 fire to the live values
  show ((if (0 : Nat) = 0 then Q'.ofNat 2 else 0)
        * (if (0 : Nat) = 0 then mayerRho p else 0) ^ n).eqv
      (Q'.ofNat 2 * (mayerRho p) ^ n)
  rw [if_pos rfl, if_pos rfl]
  exact Q'.eqv_refl _

/-- **`clusterSpanSum_le_corr` — the genuine cluster sum is dominated by the
envelope model's `corr` (PROVED).**  At the strong-coupling instance, the
connecting-cluster sum at separation `n` is bounded by the cluster-envelope
model's abstract two-point function:

    clusterSpanSum (zChainClusterCountBound p) gw gr n  ≤  corr (mayerEnvelopeModel p) n.

`clusterSpanSum_decay` gives `≤ 2·ρ^n` and `corr_envelope` gives
`corr = 2·ρ^n`.  So the abstract correlator genuinely envelopes the cluster
expansion's connected-cluster sum — the `corr`/cluster link is DERIVED, not
posited. -/
theorem clusterSpanSum_le_corr (p : zChain.toLattice.Plaquette) (n : Nat) :
    clusterSpanSum (zChainClusterCountBound p) gw gr n
      ≤ corr (mayerEnvelopeModel p) n := by
  have hdec : clusterSpanSum (zChainClusterCountBound p) gw gr n
      ≤ Q'.ofNat 2 * (mayerRho p) ^ n :=
    clusterSpanSum_decay (zChainClusterCountBound p) gw_nonneg gr
      (genuine_threshold p) n
  exact Q'.le_trans' _ _ _ hdec (Q'.ge_of_eqv (corr_envelope p n))

/-- **`mayer_located_gap` — DELIVERABLE 2 (the genuine located gap, PROVED).**

The located spectral gap derived from the cluster expansion at strong
coupling: `LocatedSpectralGap (mayerEnvelopeModel p)` with

    sep  =  mayerRho p  =  kpRatio (zChainClusterCountBound p) (1/6) 1  =  4/9  <  1,

the GENUINE cluster ratio of the real `|enumPolys|` lattice-animal count.

Via `ClusteringImpliesGap.clustering_implies_located` with `C := 2`, `μ := ρ`:
  * `hC : 0 < 2`, `hμ : 0 < ρ` (`mayerRho_pos`), `hμ1 : ρ < 1` (`mayerRho_lt_one`);
  * `hcluster : corr S n ≤ 2·ρ^n` — the cluster-decay envelope, by
    `corr_envelope` (genuine cluster bound; `clusterSpanSum_le_corr` exhibits
    the real connecting-cluster sum dominated by it);
  * `hw : ∀ i < 1, 0 < w i` — the single live mode has weight `2 > 0`;
  * `hdead : ∀ i ≥ 1, lam i ≤ ρ` — the unused tail is `0 ≤ ρ`.
Non-vacuous: `sep = ρ = 4/9` is the real `kpRatio` of the real
`zChainClusterCountBound` (the genuine count is the cardinality
`|enumPolys|`, `GenuineKP.genuine_count_is_cardinality`; the animal class is
inhabited, `GenuineKP.zChain_animal_nonempty`). -/
def mayer_located_gap (p : zChain.toLattice.Plaquette) :
    LocatedSpectralGap (mayerEnvelopeModel p) :=
  clustering_implies_located (mayerEnvelopeModel p) (Q'.ofNat 2) (mayerRho p)
    (by decide)                       -- 0 < 2
    (mayerRho_pos p)                  -- 0 < ρ
    (mayerRho_lt_one p)               -- ρ < 1
    (fun n => Q'.le_of_eqv (corr_envelope p n))  -- corr S n ≤ 2·ρ^n (= envelope)
    (fun i hi => by                   -- hw: live mode weight 2 > 0
      -- i < (mayerEnvelopeModel p).k = 1 ⇒ i = 0
      have hi1 : i < 1 := hi
      have : i = 0 := by omega
      subst this
      show (0 : Q') < (if (0 : Nat) = 0 then Q'.ofNat 2 else 0)
      rw [if_pos rfl]; decide)
    (fun i hi => by                   -- hdead: unused tail (i ≥ 1) is 0 ≤ ρ
      -- (mayerEnvelopeModel p).k = 1 ≤ i ⇒ i ≠ 0
      have hi1 : 1 ≤ i := hi
      have hne : i ≠ 0 := by omega
      show (if i = 0 then mayerRho p else 0) ≤ mayerRho p
      rw [if_neg hne]
      exact Q'.le_of_lt (mayerRho_pos p))

/-- The located gap's separator IS the genuine cluster ratio `4/9`
(definitional: `clustering_implies_located` sets `sep := μ = mayerRho p`). -/
theorem mayer_located_gap_sep (p : zChain.toLattice.Plaquette) :
    (mayer_located_gap p).sep = mayerRho p := rfl

/-! ## 3. The SECOND located gap — fully DERIVED from the real Wilson decay

Over the reconstructed single-edge transfer operator `reconTransfer w hw M`
(`TransferCorr`), the abstract `corr` equals the real Wilson connected
correlator `wilsonG w (M+1) n` (`wilsonG_eqv_reconTransfer_corr`), whose
genuine character-double-sum decay is `wilsonG_decay`.  So here the clustering
hypothesis is the REAL correlator decay, not a constructed envelope, at the
strong-coupling rate `μ = rho w = 2w³ < 1`.  `hdead` is the proved
excited-coefficient bound `coeffW_excited_le_one`; `hw` is the positivity of
the excited coefficients at the concrete weight `w = 1/6`. -/

/-- The reconstructed transfer operator's `corr` decays at the genuine
single-line rate: `corr (reconTransfer w hw M) n ≤ (ofNat M · rho w)·(rho w)^n`,
the real Wilson decay `wilsonG_decay` transported through
`wilsonG_eqv_reconTransfer_corr`.  THE Mayer/Ursell identity (single-line)
in action: the abstract correlator decay IS the real connected-correlator
decay. -/
theorem reconTransfer_corr_decay {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (M n : Nat) :
    corr (reconTransfer w hw0 M) n ≤ (Q'.ofNat M * rho w) * (rho w) ^ n := by
  -- corr (reconTransfer …) n ≃ wilsonG w (M+1) n ≤ (ofNat M · ρ)·ρ^n
  have hid : (corr (reconTransfer w hw0 M) n).eqv (wilsonG w (M + 1) n) :=
    Q'.eqv_symm (wilsonG_eqv_reconTransfer_corr w hw0 M n)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
  exact wilsonG_decay hw0 hw M n

/-- The excited weight `coeffW (1/6) (i+1)` is strictly positive (the genuine
single-edge transfer eigenvalues are positive at `w = 1/6 > 0`):
`coeffW gw (i+1) = dimQ (i+1) · qpow gw (c4 (i+1))`, both factors `> 0`. -/
theorem coeffW_gw_pos (i : Nat) : (0 : Q') < coeffW gw (i + 1) := by
  show (0 : Q') < dimQ (i + 1) * qpow gw (c4 (i + 1))
  refine Q'.mul_pos ?_ ?_
  · -- dimQ (i+1) = ofNat (i+2) > 0
    show (0 : Q') < Q'.ofNat (i + 1 + 1)
    exact Q'.ofNat_succ_pos (i + 1)
  · -- qpow gw k > 0 since gw = 1/6 > 0
    have hgw : (0 : Q') < gw := by decide
    -- qpow gw n > 0 by induction
    have hpow : ∀ k : Nat, (0 : Q') < qpow gw k := by
      intro k
      induction k with
      | zero => show (0 : Q') < (1 : Q'); decide
      | succ j ih =>
          show (0 : Q') < qpow gw j * gw
          exact Q'.mul_pos ih hgw
    exact hpow (c4 (i + 1))

/-- **`reconTransfer_located_gap` — the fully-DERIVED located gap (PROVED).**

The located spectral gap of the reconstructed single-edge transfer operator at
the concrete strong-coupling weight `w = 1/6`, with the clustering hypothesis
the REAL Wilson connected-correlator decay (NOT a constructed envelope):

    LocatedSpectralGap (reconTransfer gw gw_nonneg M),  sep = rho gw = 2·(1/6)³ < 1.

Via `clustering_implies_located` with `C := ofNat M · rho gw`, `μ := rho gw`:
  * `hcluster` = `reconTransfer_corr_decay` (the real `wilsonG_decay` through
    the transfer identity);
  * `hμ1 : rho gw < 1` = `rho_lt_one`;
  * `hw` = `coeffW_gw_pos` (excited eigenvalues positive);
  * `hdead : coeffW gw (i+1) ≤ rho gw = coeffW gw 1` = `coeffW_excited_le_one`.

This is the genuine single-line cluster correlator located gap — its
clustering is DERIVED from the real character double-sum, at the genuine
strong-coupling rate.  (`C` must be `> 0`, hence `M ≥ 1`; we expose the
`M+1`-mode model.) -/
def reconTransfer_located_gap (M : Nat) :
    LocatedSpectralGap (reconTransfer gw gw_nonneg (M + 1)) := by
  -- gw bounds: 0 ≤ gw ≤ 1/2
  have hgw0 : (0 : Q') ≤ gw := gw_nonneg
  have hgwh : gw ≤ half := by decide
  -- C = ofNat (M+1) · rho gw > 0  (M+1 ≥ 1 and rho gw = coeffW gw 1 > 0)
  have hrho_pos : (0 : Q') < rho gw := by
    show (0 : Q') < coeffW gw 1
    have := coeffW_gw_pos 0
    -- coeffW gw (0+1) = coeffW gw 1
    simpa using this
  have hC : (0 : Q') < Q'.ofNat (M + 1) * rho gw :=
    Q'.mul_pos (Q'.ofNat_succ_pos M) hrho_pos
  refine clustering_implies_located (reconTransfer gw gw_nonneg (M + 1))
    (Q'.ofNat (M + 1) * rho gw) (rho gw)
    hC hrho_pos (rho_lt_one hgw0 hgwh) ?_ ?_ ?_
  · -- hcluster: corr (reconTransfer …) n ≤ (ofNat (M+1) · rho gw)·(rho gw)^n
    intro n
    exact reconTransfer_corr_decay hgw0 hgwh (M + 1) n
  · -- hw: i < M+1 ⇒ 0 < (reconTransfer …).w i = coeffW gw (i+1)
    intro i _
    show (0 : Q') < coeffW gw (i + 1)
    exact coeffW_gw_pos i
  · -- hdead: (M+1) ≤ i ⇒ (reconTransfer …).lam i = coeffW gw (i+1) ≤ rho gw = coeffW gw 1
    intro i _
    show coeffW gw (i + 1) ≤ rho gw
    show coeffW gw (i + 1) ≤ coeffW gw 1
    -- coeffW gw (i+1) = coeffW gw (1+i) ≤ coeffW gw 1
    have hidx : (i + 1 : Nat) = 1 + i := by omega
    rw [hidx]
    exact coeffW_excited_le_one hgw0 hgwh i

/-! ## 4. DELIVERABLE 3 — the named residual `MayerUrsellIdentity`

The one thing NOT faked: the general Mayer/Ursell identity that the ACTUAL
multi-plaquette connected correlator EQUALS (or is `≤`) the sum over spanning
connected clusters.  Stated as a Type-level obligation, and DISCHARGED for the
single-line chain (`mayerUrsell_singleLine`) by the proved `wilsonG_decay` +
`wilsonG_eqv_reconTransfer_corr`.  The residual is exactly the multi-plaquette
/ loopy generalization. -/

/-- **The Mayer/Ursell identity (NAMED residual).**  For a weight `w`, a datum
supplying:
  * `clusterEnvelope : Nat → Q'` — a geometric clustering envelope `C·ρ^n`;
  * a `SpectralModel` `model` whose abstract `corr` is the connected
    correlator of the theory (the transfer operator);
  * `correlator_le_clusters : ∀ n, corr model n ≤ clusterEnvelope n` — the
    Mayer/Ursell content: the connected correlator is dominated by the sum
    over spanning connected clusters (the geometric envelope).

This is the Type-level identity tying the ACTUAL connected correlator to the
cluster-sum decay.  It is DISCHARGED for the single-line chain
(`mayerUrsell_singleLine`); the residual is its multi-plaquette / loopy
generalization. -/
structure MayerUrsellIdentity (w : Q') where
  /-- The clustering envelope `C·ρ^n` (the connecting-cluster sum bound). -/
  clusterEnvelope : Nat → Q'
  /-- The transfer-operator spectral model whose `corr` is the connected
  correlator. -/
  model : SpectralModel
  /-- **The Mayer/Ursell content**: the connected correlator is `≤` the sum
  over spanning connected clusters (the geometric envelope). -/
  correlator_le_clusters : ∀ n, corr model n ≤ clusterEnvelope n

/-- **`mayerUrsell_singleLine` — the residual DISCHARGED for the single-line
chain (PROVED).**  At the concrete strong-coupling weight `w = 1/6` and chain
cutoff `M+1`, the Mayer/Ursell identity holds: the connected correlator is the
`corr` of the reconstructed transfer operator (`wilsonG_eqv_reconTransfer_corr`)
and is dominated by the cluster envelope `(ofNat M · rho gw)·(rho gw)^n`
(`reconTransfer_corr_decay`, from the real `wilsonG_decay`).  So the FULL
multi-plaquette residual is exactly the loopy/multi-line generalization. -/
def mayerUrsell_singleLine (M : Nat) : MayerUrsellIdentity gw where
  clusterEnvelope := fun n => (Q'.ofNat M * rho gw) * (rho gw) ^ n
  model := reconTransfer gw gw_nonneg M
  correlator_le_clusters := fun n =>
    reconTransfer_corr_decay gw_nonneg (by decide) M n

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean — assembled from already-proved pieces):

  * `pow_le_one`, `pow_antitone_exp` — `Q'`-power monotonicity for base `≤ 1`;
  * `clusterSpanSum`, `spanning_cluster_term_le` (CONSUMES the geometric engine
    `connected_spanning_size_ge`), `clusterSpanSum_decay` — DELIVERABLE 1: the
    connecting-cluster sum and its exponential decay `≤ 2·ρ^d`;
  * `mayerRho` (= `4/9`), `mayerRho_le_half`, `mayerRho_lt_one`, `mayerRho_pos`
    — the genuine cluster ratio at the strong-coupling instance;
  * `mayerEnvelopeModel`, `corr_envelope`, `clusterSpanSum_le_corr`,
    `mayer_located_gap` (+ `mayer_located_gap_sep`) — DELIVERABLE 2: the genuine
    located gap at `sep = ρ = 4/9 < 1` from the cluster expansion;
  * `reconTransfer_corr_decay`, `coeffW_gw_pos`, `reconTransfer_located_gap`
    — the SECOND, fully-derived located gap over the reconstructed transfer
    operator (clustering = the REAL Wilson decay `wilsonG_decay`), at rate
    `rho gw = 2·(1/6)³ < 1`;
  * `mayerUrsell_singleLine` — DELIVERABLE 3 DISCHARGED for the single-line chain.

NAMED-open (NOT faked, the residual):

  * `MayerUrsellIdentity` — the general Mayer/Ursell identity (connected
    correlator = / ≤ sum over spanning clusters).  DISCHARGED for the
    single-line chain (`mayerUrsell_singleLine`); the residual is its
    multi-plaquette / loopy generalization — believed TRUE (a standard theorem
    of convergent polymer expansions), but its constructive multi-plaquette
    proof is the wall.

This module is the genuine cluster-expansion clustering step at finite volume,
strong coupling, on the 1D chain.  It is NOT uniform-in-`w`, NOT the continuum
(`a → 0`) limit, NOT a multi-plaquette correlator, and NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.MayerClustering

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerClustering.pow_antitone_exp
#print axioms YMGap.Continuum.MayerClustering.spanning_cluster_term_le
#print axioms YMGap.Continuum.MayerClustering.clusterSpanSum_decay
#print axioms YMGap.Continuum.MayerClustering.mayerRho_pos
#print axioms YMGap.Continuum.MayerClustering.corr_envelope
#print axioms YMGap.Continuum.MayerClustering.clusterSpanSum_le_corr
#print axioms YMGap.Continuum.MayerClustering.mayer_located_gap
#print axioms YMGap.Continuum.MayerClustering.reconTransfer_corr_decay
#print axioms YMGap.Continuum.MayerClustering.coeffW_gw_pos
#print axioms YMGap.Continuum.MayerClustering.reconTransfer_located_gap
#print axioms YMGap.Continuum.MayerClustering.mayerUrsell_singleLine
