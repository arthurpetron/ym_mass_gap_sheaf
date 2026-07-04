/-
The genuine `BridgeDecomposition` witness at the CLOSED 4D count instance
`(z4ClusterCountBound p, w4 = 1/20, gr = 1)` — as a REDUCTION to a single named
residual, the z4 Mayer–Ursell identity.

# What is being built

`Ursell4DProgress.BridgeDecomposition cc w r` is the (D) half of a
`PenroseUrsellSplit`: an off-diagonal correlator `offCorr : Nat → Q'`, a
size-graded bridge term `bridgeTerm : Nat → Q'`, a truncation length
`tailLen d ≥ d`, and the SOLE content field

    decompose : ∀ d, offCorr d ≤ finSum (fun m => bridgeTerm (d+m)) (tailLen d).

At the physical 4D instance we fix `bridgeTerm := kpTerm (z4ClusterCountBound p)
w4 gr` and `tailLen := id`, so the RHS is *definitionally*

    finSum (fun m => kpTerm (z4ClusterCountBound p) w4 gr (d+m)) d
      =  MayerClustering.clusterSpanSum (z4ClusterCountBound p) w4 gr d,

the already-PROVED connecting-cluster activity sum, whose decay
`clusterSpanSum_decay : clusterSpanSum ≤ 2·(kpRatio)^d` is entirely green.  So
the resummation/geometry infrastructure on the RHS is closed; the ONLY open
question is whether the LHS off-diagonal correlator is a genuine correlator and
whether `decompose` is a theorem.

# The single named residual

`MayerUrsellIdentity_z4 p` is the z4 (multi-plaquette / loopy) instance of the
already-named `MayerClustering.MayerUrsellIdentity`: a `SpectralModel` `model`
whose abstract `corr` is the true two-component connected correlator, together
with the Mayer–Ursell content

    correlator_le_span : ∀ d, corr model d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d

— "the connected correlator is dominated by the sum over spanning connecting
clusters from the size floor `d`."  The size floor is already baked into
`clusterSpanSum` (its terms range over sizes `d … 2d-1`, the size-`≥ d` tail),
so this ONE inequality subsumes both the Mayer–Ursell expansion (D1) and the
size-floor geometry (D2) that `Ursell4DProgress.SepLatticeZ4` would supply to
*prove* it.  It is the exact z4 analog of `MayerClustering.MayerUrsellIdentity`,
which is DISCHARGED for the single line (`mayerUrsell_singleLine`).  LEFT
UNINHABITED, NOT faked — it is the multi-plaquette generalization wall.

# What is PROVED here (given the residual)

  * `bridgeDecomposition_of_data (MU) : BridgeDecomposition (z4ClusterCountBound p)
    w4 gr` — the genuine (D) witness: `offCorr := corr MU.model` (a REAL
    correlator, not `0`), `decompose := MU.correlator_le_span` (the RHS is
    definitionally `clusterSpanSum`).
  * `penroseSplit_of_data (MU) : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr`
    — the FULL split: the (T) field `treeGraph` is reflexivity here
    (`bridgeTerm = kpTerm`), so the single residual `MU` supplies the whole
    factored datum.
  * `correlator_decay_of_data (MU) (d) : corr MU.model d ≤ 2·(kpRatio …)^d` — the
    concrete 4D geometric decay at the PROVED strong-coupling threshold
    `z4_genuine_threshold` (`kpRatio (z4ClusterCountBound p) w4 gr = 15/32 ≤ 1/2`),
    via the generic PROVED `PenroseUrsellSplit.offCorr_decay`.

# Honest verdict (AGENTS.md Rule 6)

There is NO no-open-field inhabitant of `BridgeDecomposition (z4ClusterCountBound
p) w4 gr` today; the only zero-residual constructions set `offCorr := 0` (or
`offCorr := clusterSpanSum` itself), which are vacuous (Rule-6 fakes) and are
NOT landed.  The genuine witness reduces to exactly ONE named Type-level
residual, `MayerUrsellIdentity_z4` — no NEW wall: it is the z4 instance of the
pre-existing `MayerClustering.MayerUrsellIdentity` (proved for the single line).
Every other step (`clusterSpanSum` def, `clusterSpanSum_decay`,
`connTailPartialG_decay`, `PenroseUrsellSplit.offCorr_decay`,
`z4_genuine_threshold`) is PROVED and axiom-clean.  This is a FIXED-SPACING
reduction (`ρ4 = 15/32 < 1`); it is NOT the spacing-uniform continuum modulus and
NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The single
open item (`MayerUrsellIdentity_z4`) is a NAMED Type-level structure, left
uninhabited, never faked.  Load-bearing declarations are gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.Ursell4DProgress

namespace YMGap.Continuum.MayerBridgeDecomposition

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.Ursell4DProgress

/-! ## 1. The single named residual — the z4 Mayer–Ursell identity -/

/-- **`MayerUrsellIdentity_z4` (NAMED — the sole (D) residual).**  The z4
(multi-plaquette / loopy) instance of `MayerClustering.MayerUrsellIdentity` at
the CLOSED 4D count `z4ClusterCountBound p`, weight `w4 = 1/20`, rep `gr = 1`:

  * `model : SpectralModel` — the transfer-operator model whose abstract `corr`
    IS the true two-component connected correlator;
  * `correlator_le_span : ∀ d, corr model d ≤ clusterSpanSum (z4ClusterCountBound
    p) w4 gr d` — the Mayer–Ursell content: the connected correlator is dominated
    by the sum over spanning connecting clusters from the size floor `d`.

The size floor is already encoded in `clusterSpanSum` (terms of size `d … 2d-1`),
so this single inequality subsumes both the connecting-cluster expansion and the
size-floor geometry that `Ursell4DProgress.SepLatticeZ4` would supply to prove
it.  This is the exact z4 analog of `MayerClustering.MayerUrsellIdentity`, which
is DISCHARGED for the single line by `mayerUrsell_singleLine`.  LEFT UNINHABITED
(the multi-plaquette generalization wall), NOT faked. -/
structure MayerUrsellIdentity_z4 (p : z4Chain.toLattice.Plaquette) where
  /-- The transfer-operator spectral model whose `corr` is the connected
  two-component correlator. -/
  model : SpectralModel
  /-- **The Mayer–Ursell content** (the one open atom): the connected correlator
  is dominated by the connecting-cluster sum from the size floor `d`. -/
  correlator_le_span : ∀ d,
    corr model d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d

/-! ## 2. The genuine `BridgeDecomposition` witness (PROVED given the residual) -/

/-- **`bridgeDecomposition_of_data` (PROVED — the genuine (D) witness).**  From the
single residual `MU : MayerUrsellIdentity_z4 p`, the (D) half of the Penrose–Ursell
split is inhabited with a GENUINE off-diagonal correlator `offCorr := corr
MU.model` (NOT the vacuous `0`).  The bridge term is the assembled Ueltschi
majorant `kpTerm`, the truncation length is the size floor `d`, and `decompose`
is `MU.correlator_le_span` — the RHS `finSum (fun m => kpTerm … (d+m)) d` being
DEFINITIONALLY `clusterSpanSum (z4ClusterCountBound p) w4 gr d`. -/
def bridgeDecomposition_of_data (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4 p) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr where
  offCorr    := fun d => corr MU.model d
  bridgeTerm := fun n => kpTerm (z4ClusterCountBound p) w4 gr n
  tailLen    := fun d => d
  tailLen_ge := fun d => Nat.le_refl d
  decompose  := fun d => MU.correlator_le_span d

/-! ## 3. The full split and the concrete 4D decay (PROVED given the residual)

Because `bridgeTerm = kpTerm`, the (T) tree-graph field is reflexivity, so the
single residual `MU` supplies the *entire* factored `PenroseUrsellSplit` — and
hence the concrete geometric decay at the PROVED strong-coupling threshold. -/

/-- **`penroseSplit_of_data` (PROVED — the full factored split).**  The single
residual `MU` yields a complete `PenroseUrsellSplit`: the (D) field is
`bridgeDecomposition_of_data`, and the (T) field `treeGraph` is reflexivity
(`bridgeTerm n = kpTerm … n`). -/
def penroseSplit_of_data (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4 p) :
    PenroseUrsellSplit (z4ClusterCountBound p) w4 gr where
  offCorr    := fun d => corr MU.model d
  tailLen    := fun d => d
  tailLen_ge := fun d => Nat.le_refl d
  bridgeTerm := fun n => kpTerm (z4ClusterCountBound p) w4 gr n
  treeGraph  := fun n => Q'.le_refl' (kpTerm (z4ClusterCountBound p) w4 gr n)
  decompose  := fun d => MU.correlator_le_span d

/-- **`correlator_decay_of_data` (PROVED — the concrete 4D decay).**  From the
single residual `MU`, the genuine two-component connected correlator decays at
the physical 4D rate `ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`:

    corr MU.model d  ≤  2 · (kpRatio (z4ClusterCountBound p) w4 gr)^d.

Chains `penroseSplit_of_data` through the generic PROVED
`PenroseUrsellSplit.offCorr_decay` at the PROVED threshold
`z4_genuine_threshold`. -/
theorem correlator_decay_of_data (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4 p) (d : Nat) :
    corr MU.model d
      ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  PenroseUrsellSplit.offCorr_decay (z4ClusterCountBound p) w4_nonneg gr
    (z4_genuine_threshold p) (penroseSplit_of_data p MU) d

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean, given the single residual `MU`):

  * `bridgeDecomposition_of_data` — the genuine (D) witness with a REAL
    off-diagonal correlator `corr MU.model`;
  * `penroseSplit_of_data` — the full factored `PenroseUrsellSplit` (the (T)
    field is reflexivity, `bridgeTerm = kpTerm`);
  * `correlator_decay_of_data` — the concrete 4D geometric decay `≤ 2·(15/32)^d`
    at the PROVED `z4_genuine_threshold`, via the generic PROVED
    `PenroseUrsellSplit.offCorr_decay`.

NAMED-open (NOT faked, the sole residual):

  * `MayerUrsellIdentity_z4` — the z4 (multi-plaquette / loopy) Mayer–Ursell
    identity (connected correlator ≤ connecting-cluster sum from the size floor).
    The exact z4 analog of `MayerClustering.MayerUrsellIdentity`, which is
    DISCHARGED for the single line (`mayerUrsell_singleLine`); the residual is its
    multi-plaquette generalization — believed TRUE (a standard theorem of
    convergent polymer expansions), its constructive multi-plaquette proof the
    wall (`Ursell4DProgress.SepLatticeZ4` supplies the size-floor geometry used
    in that proof).

This is the genuine cluster-expansion (D) step at FIXED spacing, strong coupling,
on the CLOSED 4D count.  It is NOT uniform-in-`w`, NOT the continuum (`a → 0`)
limit, and NOT the Clay Yang–Mills mass gap. -/

end YMGap.Continuum.MayerBridgeDecomposition

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerBridgeDecomposition.bridgeDecomposition_of_data
#print axioms YMGap.Continuum.MayerBridgeDecomposition.penroseSplit_of_data
#print axioms YMGap.Continuum.MayerBridgeDecomposition.correlator_decay_of_data
