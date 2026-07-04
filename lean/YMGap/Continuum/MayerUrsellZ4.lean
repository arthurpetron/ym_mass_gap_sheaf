/-
`MayerUrsellZ4` — the loopy z4 Mayer–Ursell identity as a VERIFIED REDUCTION, not
a close.  The literal identity `MayerBridgeDecomposition.MayerUrsellIdentity_z4 p`
is provably UNSATISFIABLE for every nontrivial model (it forces the zero model at
coincident separation `d = 0`); leaving it uninhabited is the correct, honest
state.  This module (1) PROVES that obstruction in Lean, (2) routes the honest
replacement through the satisfiable free-`tailLen` node
`Ursell4DProgress.BridgeDecomposition` and the factored `PenroseUrsellSplit`,
(3) collapses the whole obligation onto the two sharpest named atoms — (T′)
`TreeGraphBound.tree_graph` and (D2) `SepLatticeZ4` — via the PROVED
`kpTerm_from_atoms`, and (4) certifies non-vacuity with a genuine tree instance
`mayerUrsell_tree` (backed by the PROVED `treeWilsonG_decay`).

# What is being built

## §1 — the d = 0 obstruction (PROVED — MU_z4 is unsatisfiable for nontrivial models)

`clusterSpanSum cc w r 0 = finSum … 0 = 0`, and `corr model 0 ≃ Σ_i w_i` (the
total spectral weight).  So `MU.correlator_le_span 0` forces
`Σ_i (MU.model).w_i ≤ 0` — every weight vanishes, i.e. the trivial zero model.
`mu_z4_total_weight_le_zero` PROVES exactly this.  This is correct physics: the
length-`d` connecting-cluster majorant vanishes at coincident separation, yet the
loopy correlator carries positive total spectral weight, so domination cannot hold
at `d = 0`.  Any no-open-field inhabitant of `MayerUrsellIdentity_z4` would be a
Rule-6 fake; UNINHABITED is correct.

## §2 — the honest replacement: the free-`tailLen` `BridgeDecomposition` (PROVED wiring)

The fix is to NOT hard-code the truncation length to `d`.  The satisfiable node is
`Ursell4DProgress.BridgeDecomposition`, which carries a FREE `tailLen d ≥ d`.  With
`tailLen 0 ≥ 1` the RHS at `d = 0` is `finSum bridgeTerm (tailLen 0)`, which
INCLUDES the size-`0` bridge term rather than being structurally `0`
(`bridge_rhs_at_zero`) — escaping the obstruction.  `bridgeDecomposition_of_split`
projects a `PenroseUrsellSplit` onto this free node; `offCorr_decay_of_split`
supplies the concrete 4D geometric decay `offCorr d ≤ 2·(15/32)^d` at the PROVED
`z4_genuine_threshold`, and `loopyResidual_of_split` packages it as a genuine
`LoopyCorrelatorResidual`.

## §3 — collapse onto the two sharpest named atoms (PROVED assembly)

`Z4BridgeAtoms p` carries the off-diagonal correlator, a free `tailLen ≥ d`,
per-size tree-graph weights `phiT` and activities `zeta`, and the two atom fields
— (T′) `tree_graph : phiT n ≤ eSurrogate^n` (Penrose 1967 / Poghosyan–Ueltschi
2009) and the activity bound `activity_le : zeta n ≤ (coeffW w4 gr)^n` (backed by
the PROVED `PinnedCluster.activity_le_leading`) — plus the (D1) `decompose` field
(the absolute Mayer–Ursell connecting-cluster expansion, whose size-floor geometry
`Ursell4DProgress.SepLatticeZ4` = (D2) would supply).  `splitOfAtoms` PROVES that
these assemble into a `PenroseUrsellSplit` via the PROVED `kpTerm_from_atoms`
(count folded in as `animalCount`).  So the entire z4 decay chain rests on exactly
(T′) + (D1)/(D2); count, threshold, tree-graph assembly, and geometric decay are
all green.

## §4 — non-vacuity certificate (PROVED — the pattern is genuinely inhabited)

`nonvacuity_tree` is a genuine `MayerClustering.MayerUrsellIdentity gw` inhabitant
for the acyclic branching sub-geometry (`mayerUrsell_tree`), whose
`correlator_le_clusters` field is the PROVED `treeWilsonG_decay` (shared-link
orthogonality forcing one common excited rep at each branch point) — NOT
`eqv_refl`, NOT the zero model.  This certifies the free-envelope pattern the
literal `MayerUrsellIdentity_z4` destroyed by hard-coding `clusterSpanSum`.  The
residual delta (tree → z4 loopy) is exactly the named `LoopyCorrelatorResidual`:
loops/cycles (a closing link re-shares an edge), multi-component cross terms, and
all excited reps.

# Honest verdict (AGENTS.md Rule 6)

Genuine REDUCTION, NOT a close.  Net new closed physics: zero.  `MayerUrsellIdentity_z4`
is LEFT UNINHABITED (provably unsatisfiable for nontrivial models, `mu_z4_total_weight_le_zero`).
The honest satisfiable target is `BridgeDecomposition` (free `tailLen`), reduced to
the two sharpest named atoms (T′) `TreeGraphBound.tree_graph` and (D2) `SepLatticeZ4`;
everything else is PROVED and WIRED.  Fixed spacing only
(`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`); NOT the spacing-uniform
continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The open items
((T′), (D1), (D2)) and the deliberately-unsatisfiable `MayerUrsellIdentity_z4` are
NAMED Type-level structures, left uninhabited, never faked.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.MayerBridgeDecomposition
import YMGap.Continuum.MultiPlaquetteMayer

namespace YMGap.Continuum.MayerUrsellZ4

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.MayerBridgeDecomposition
open YMGap.Continuum.MultiPlaquetteMayer

/-! ## 1. The d = 0 obstruction — `MayerUrsellIdentity_z4` is unsatisfiable
(PROVED)

The literal identity hard-codes the length-`d` connecting-cluster majorant
`clusterSpanSum`, which VANISHES at `d = 0` (empty sum).  Any inhabitant therefore
forces the connected correlator's total spectral weight to be `≤ 0`, i.e. the
trivial zero model. -/

/-- **`mu_z4_span_zero` (PROVED — the hard-coded RHS vanishes at `d = 0`).**  The
length-`d` connecting-cluster majorant is the empty sum at coincident separation:
`clusterSpanSum (z4ClusterCountBound p) w4 gr 0 = 0`.  This is the load-bearing
obstruction: the RHS of `MayerUrsellIdentity_z4`'s domination is `0` at `d = 0`. -/
theorem mu_z4_span_zero (p : z4Chain.toLattice.Plaquette) :
    clusterSpanSum (z4ClusterCountBound p) w4 gr 0 = 0 := by
  unfold clusterSpanSum
  exact finSum_zero _

/-- **`mu_z4_total_weight_le_zero` (PROVED — the obstruction).**  Every inhabitant
`MU : MayerUrsellIdentity_z4 p` forces the total spectral weight of its connected
correlator to be nonpositive:

    Σ_i (MU.model).w_i  ≤  0.

Since spectral weights are nonnegative (`w_nonneg`), this pins `MU.model` to the
trivial ZERO model — no genuine loopy correlator inhabits `MayerUrsellIdentity_z4`.
Proof: `corr MU.model 0 ≤ clusterSpanSum … 0 = 0` (`correlator_le_span 0` +
`mu_z4_span_zero`), and `corr MU.model 0 ≃ Σ_i (MU.model).w_i` (`corr_zero`).  This
is why `MayerUrsellIdentity_z4` is LEFT UNINHABITED — uninhabited is CORRECT, not a
gap in effort. -/
theorem mu_z4_total_weight_le_zero (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4 p) :
    finSum (MU.model).w (MU.model).k ≤ (0 : Q') := by
  have h1 : corr MU.model 0 ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr 0 :=
    MU.correlator_le_span 0
  rw [mu_z4_span_zero p] at h1
  have h2 : finSum (MU.model).w (MU.model).k ≤ corr MU.model 0 :=
    Q'.le_of_eqv (Q'.eqv_symm (corr_zero MU.model))
  exact Q'.le_trans' _ _ _ h2 h1

/-! ## 2. The honest replacement — the free-`tailLen` `BridgeDecomposition`
(PROVED)

The fix (postulate §1): restore the FREE truncation length.  `BridgeDecomposition`
carries `tailLen d ≥ d` rather than the hard-coded length `d`, so the RHS at
`d = 0` includes the size-`0` bridge term and ESCAPES the obstruction. -/

/-- **`bridgeDecomposition_of_split` (PROVED — the honest free-`tailLen` node).**
A factored `PenroseUrsellSplit` over the CLOSED 4D count projects onto the
satisfiable `BridgeDecomposition` node with a GENUINE off-diagonal correlator
`S.offCorr` and a FREE truncation length `S.tailLen d ≥ d` (unlike
`MayerUrsellIdentity_z4`, which hard-codes `clusterSpanSum` = length `d`). -/
def bridgeDecomposition_of_split (p : z4Chain.toLattice.Plaquette)
    (S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr where
  offCorr := S.offCorr
  bridgeTerm := S.bridgeTerm
  tailLen := S.tailLen
  tailLen_ge := S.tailLen_ge
  decompose := S.decompose

/-- **`bridge_rhs_at_zero` (PROVED — the escape).**  With a free truncation length
`S.tailLen 0 = k + 1 ≥ 1`, the `d = 0` RHS of the split's domination is

    finSum (fun m => S.bridgeTerm (0 + m)) (k + 1)
      =  finSum (fun m => S.bridgeTerm (0 + m)) k  +  S.bridgeTerm (0 + k),

which INCLUDES the size-`k` bridge term — it is NOT structurally `0` (contrast
`mu_z4_span_zero`, where the hard-coded length-`0` sum vanishes).  This is exactly
why the free-`tailLen` node escapes the obstruction that kills
`MayerUrsellIdentity_z4`. -/
theorem bridge_rhs_at_zero (p : z4Chain.toLattice.Plaquette)
    (S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr) (k : Nat)
    (htl : S.tailLen 0 = k + 1) :
    finSum (fun m => S.bridgeTerm (0 + m)) (S.tailLen 0)
      = finSum (fun m => S.bridgeTerm (0 + m)) k + S.bridgeTerm (0 + k) := by
  rw [htl]
  exact finSum_succ (fun m => S.bridgeTerm (0 + m)) k

/-- **`offCorr_decay_of_split` (PROVED — the concrete 4D geometric decay).**  The
free-`tailLen` split's off-diagonal correlator decays at the physical 4D rate
`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`:

    S.offCorr d  ≤  2 · (kpRatio (z4ClusterCountBound p) w4 gr)^d.

Chains the generic PROVED `PenroseUrsellSplit.offCorr_decay` at the PROVED
`z4_genuine_threshold`.  The decay side NEVER touches the `d = 0` zero-forcing —
it routes through the full connecting tail (free `tailLen`), as Ursell yields. -/
theorem offCorr_decay_of_split (p : z4Chain.toLattice.Plaquette)
    (S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr) (d : Nat) :
    S.offCorr d ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  PenroseUrsellSplit.offCorr_decay (z4ClusterCountBound p) w4_nonneg gr
    (z4_genuine_threshold p) S d

/-- **`loopyResidual_of_split` (PROVED — a genuine `LoopyCorrelatorResidual`).**
The free-`tailLen` split's off-diagonal correlator satisfies the loopy-residual
contract at the 4D majorant rate: `graphMass d = d`,
`loopyEnvelope L = 2·(15/32)^L`, `loopyCorr d = S.offCorr d`, and `loopy_decay` is
the PROVED `offCorr_decay_of_split`.  The z4 counterpart of
`MultiComponentKPProgress.loopyResidual_penroseUrsell`. -/
def loopyResidual_of_split (p : z4Chain.toLattice.Plaquette)
    (S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr) :
    LoopyCorrelatorResidual gw where
  graphMass := fun d => d
  loopyEnvelope := fun L => Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ L
  loopyCorr := fun d => S.offCorr d
  loopy_decay := fun d => offCorr_decay_of_split p S d

/-! ## 3. Collapse onto the two sharpest named atoms (PROVED assembly)

`Z4BridgeAtoms` carries the two atom fields — (T′) the spanning-tree inequality
and the activity bound (backed by `PinnedCluster.activity_le_leading`) — plus the
(D1) connecting-cluster expansion.  `splitOfAtoms` PROVES they assemble into a
`PenroseUrsellSplit` via the PROVED `kpTerm_from_atoms`, folding the count into
`animalCount`.  So the whole z4 decay chain rests on exactly (T′) + (D1)/(D2). -/

/-- **`Z4BridgeAtoms` (the collapsed datum — carries only the two named atoms).**
Bundles:
  * `offCorr`, `tailLen`, `tailLen_ge` — a genuine off-diagonal correlator with a
    FREE truncation length `≥ d`;
  * `phiT`, `zeta` — per-size tree-graph weights and activities;
  * `zeta_nonneg` — activities are nonnegative;
  * **(T′) `tree_graph`** — the Penrose / Poghosyan–Ueltschi spanning-tree
    inequality `phiT n ≤ eSurrogate^n` (`eSurrogate = 3 ≥ e`), the sole sharp
    analytic atom;
  * `activity_le` — the activity bound `zeta n ≤ (coeffW w4 gr)^n`, BACKED by the
    PROVED `PinnedCluster.activity_le_leading`;
  * **(D1) `decompose`** — the absolute Mayer–Ursell connecting-cluster expansion
    (its size-floor geometry supplied by (D2) `Ursell4DProgress.SepLatticeZ4`).

The count factor is folded into `animalCount` by `kpTerm_from_atoms`; count and
threshold are already discharged.  So this datum names exactly the open atoms. -/
structure Z4BridgeAtoms (p : z4Chain.toLattice.Plaquette) where
  /-- The off-diagonal truncated two-component correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- A finite-volume connecting-tail truncation length. -/
  tailLen : Nat → Nat
  /-- The truncation is at least as long as the size floor `d`. -/
  tailLen_ge : ∀ d, d ≤ tailLen d
  /-- The per-size truncated Ursell tree-graph weight `|φ^T|`. -/
  phiT : Nat → Q'
  /-- The per-size cluster activity `|ζ|`. -/
  zeta : Nat → Q'
  /-- Activities are nonnegative. -/
  zeta_nonneg : ∀ n, (0 : Q') ≤ zeta n
  /-- **(T′) — the spanning-tree inequality** (the sharp analytic atom):
  `phiT n ≤ eSurrogate^n`. -/
  tree_graph : ∀ n, phiT n ≤ eSurrogate ^ n
  /-- The activity bound `zeta n ≤ (coeffW w4 gr)^n` (backed by
  `PinnedCluster.activity_le_leading`). -/
  activity_le : ∀ n, zeta n ≤ (coeffW w4 gr) ^ n
  /-- **(D1) — the absolute Mayer–Ursell connecting-cluster expansion** (the
  size-floor geometry supplied by (D2) `SepLatticeZ4`): the off-diagonal
  correlator is dominated by the count-folded per-cluster bridge tail. -/
  decompose : ∀ d, offCorr d ≤
    finSum (fun m => (z4ClusterCountBound p).animalCount (d + m)
      * (phiT (d + m) * zeta (d + m))) (tailLen d)

/-- **`splitOfAtoms` (PROVED — the assembly onto the atoms).**  A `Z4BridgeAtoms`
datum assembles into a full `PenroseUrsellSplit` over the CLOSED 4D count: the
bridge term is the count-folded per-cluster weight
`animalCount n · (phiT n · zeta n)`, the (T) field `treeGraph` is the PROVED
`kpTerm_from_atoms` (from (T′) `tree_graph` plus the activity bound), and the (D)
field is `decompose`.  This collapses the entire obligation onto (T′) + (D1)/(D2). -/
def splitOfAtoms (p : z4Chain.toLattice.Plaquette) (A : Z4BridgeAtoms p) :
    PenroseUrsellSplit (z4ClusterCountBound p) w4 gr where
  offCorr := A.offCorr
  tailLen := A.tailLen
  tailLen_ge := A.tailLen_ge
  bridgeTerm := fun n => (z4ClusterCountBound p).animalCount n * (A.phiT n * A.zeta n)
  treeGraph := fun n =>
    kpTerm_from_atoms (z4ClusterCountBound p) w4_nonneg gr n
      (A.zeta_nonneg n) (A.tree_graph n) (A.activity_le n)
  decompose := A.decompose

/-- **`offCorr_decay_of_atoms` (PROVED — end-to-end 4D decay from the atoms).**
From a `Z4BridgeAtoms` datum (i.e. from (T′) + the activity bound + (D1)), the
off-diagonal correlator decays at the physical 4D rate:

    A.offCorr d  ≤  2 · (kpRatio (z4ClusterCountBound p) w4 gr)^d,   ρ4 = 15/32 < 1.

Composes `splitOfAtoms` with `offCorr_decay_of_split`. -/
theorem offCorr_decay_of_atoms (p : z4Chain.toLattice.Plaquette)
    (A : Z4BridgeAtoms p) (d : Nat) :
    A.offCorr d ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  offCorr_decay_of_split p (splitOfAtoms p A) d

/-! ## 4. Non-vacuity certificate — the pattern is genuinely inhabited (PROVED)

The free-envelope `MayerUrsellIdentity` pattern (which `MayerUrsellIdentity_z4`
destroyed by hard-coding `clusterSpanSum`) is genuinely inhabited for the acyclic
branching sub-geometry by `mayerUrsell_tree`, whose `correlator_le_clusters` field
is the PROVED `treeWilsonG_decay` (shared-link orthogonality → one common excited
rep at each branch point) — NOT `eqv_refl`, NOT the zero model. -/

/-- **`nonvacuity_tree` (PROVED — the non-vacuity certificate).**  A GENUINE
`MayerClustering.MayerUrsellIdentity gw` inhabitant for the branching (tree)
sub-geometry — here the single-plaquette leaf `PlaqTree.node []` at rep window
`M + 1 = 4`.  Its `correlator_le_clusters` is the PROVED `treeWilsonG_decay`, so
this is a genuine free-envelope Mayer–Ursell identity, NOT the trivial zero model
that `MayerUrsellIdentity_z4` collapses to.  This certifies that restoring the free
envelope (postulate §1) yields a satisfiable identity; the residual delta to the z4
loopy case is exactly `LoopyCorrelatorResidual` (loops/cycles + multi-component +
all reps). -/
def nonvacuity_tree : MayerUrsellIdentity gw :=
  mayerUrsell_tree 3 (PlaqTree.node [])

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `mu_z4_span_zero`, `mu_z4_total_weight_le_zero` — the d = 0 OBSTRUCTION:
    `MayerUrsellIdentity_z4` forces the total spectral weight `≤ 0` (the trivial
    zero model), so it is UNSATISFIABLE for nontrivial models — LEFT UNINHABITED is
    correct, not a gap;
  * `bridgeDecomposition_of_split` — the honest free-`tailLen` replacement node;
  * `bridge_rhs_at_zero` — the ESCAPE: with `tailLen 0 ≥ 1` the d = 0 RHS is
    non-degenerate (includes the size-`k` bridge term), unlike the hard-coded
    `clusterSpanSum`;
  * `offCorr_decay_of_split`, `loopyResidual_of_split` — the concrete 4D geometric
    decay `≤ 2·(15/32)^d` at the PROVED `z4_genuine_threshold`, packaged as a
    genuine `LoopyCorrelatorResidual`;
  * `Z4BridgeAtoms`, `splitOfAtoms`, `offCorr_decay_of_atoms` — the collapse of the
    entire obligation onto exactly the two named atoms (T′) + (D1)/(D2) via the
    PROVED `kpTerm_from_atoms` (count folded into `animalCount`, activity backed by
    `activity_le_leading`);
  * `nonvacuity_tree` — the non-vacuity certificate: a genuine free-envelope
    `MayerUrsellIdentity gw` inhabitant (`mayerUrsell_tree`, backed by the PROVED
    `treeWilsonG_decay`), NOT the zero model.

NAMED-open / deliberately-UNINHABITED (NOT faked):

  * `MayerBridgeDecomposition.MayerUrsellIdentity_z4` — provably unsatisfiable for
    nontrivial models (`mu_z4_total_weight_le_zero`); UNINHABITED is CORRECT;
  * (T′) `Ursell4DProgress.TreeGraphBound.tree_graph` — the per-cluster
    Penrose / Poghosyan–Ueltschi spanning-tree inequality `|φ^T(Y)| ≤ e^{|Y|}`, the
    single sharp analytic atom;
  * (D1) `Ursell4DProgress.BridgeDecomposition.decompose` — the absolute
    Mayer–Ursell connecting-cluster expansion (= the named
    `MayerClustering.MayerUrsellIdentity` residual);
  * (D2) `Ursell4DProgress.SepLatticeZ4` — the `SepLattice` metric refining
    `z4Chain` (plaquette-graph BFS distance + constructive triangle), the size-floor
    geometry (D1) consumes, currently MISSING.

This module is a genuine REDUCTION at FIXED SPACING
(`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`).  It is NOT the
spacing-uniform continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN). -/

end YMGap.Continuum.MayerUrsellZ4

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerUrsellZ4.mu_z4_span_zero
#print axioms YMGap.Continuum.MayerUrsellZ4.mu_z4_total_weight_le_zero
#print axioms YMGap.Continuum.MayerUrsellZ4.bridgeDecomposition_of_split
#print axioms YMGap.Continuum.MayerUrsellZ4.bridge_rhs_at_zero
#print axioms YMGap.Continuum.MayerUrsellZ4.offCorr_decay_of_split
#print axioms YMGap.Continuum.MayerUrsellZ4.loopyResidual_of_split
#print axioms YMGap.Continuum.MayerUrsellZ4.splitOfAtoms
#print axioms YMGap.Continuum.MayerUrsellZ4.offCorr_decay_of_atoms
#print axioms YMGap.Continuum.MayerUrsellZ4.nonvacuity_tree
