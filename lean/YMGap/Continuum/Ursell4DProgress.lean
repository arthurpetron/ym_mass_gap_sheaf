/-
Factoring the monolithic Penrose–Ursell atom `PenroseUrsellDatumG.penrose_ursell`
into its logically distinct ingredients — a genuine REDUCTION that exposes the
single sharp analytic core (the Poghosyan–Ueltschi spanning-tree inequality) and
routes everything else through already-PROVED in-repo bookkeeping.

# The object being factored

`Stage1LoopyReduction.PenroseUrsellDatumG cc w r` bundles ONE open field

    penrose_ursell : ∀ d, offCorr d ≤ connTailPartialG cc w r d (tailLen d)

whose RHS `connTailPartialG cc w r d N = Σ_{m<N} kpTerm cc w r (d+m)` is the
fully-assembled size-graded Ueltschi majorant, with

    kpTerm cc w r n = animalCount n · (coeffW w r)^n · eSurrogate^n

whose three per-`n` factors are exactly the three ingredients of the connecting-
cluster bound `|φ^T(X)| ≤ Σ_{connected Y ⊇ bridge} |ζ(Y)|·e^{|Y|}`:

  * `animalCount n`   — # size-`n` connected clusters through the bridge
                        (backed: `count_le`, PROVED in `KPCriterion`);
  * `(coeffW w r)^n`  — per-cluster activity `|ζ(Y)|`
                        (backed: `activity_le_leading`, PROVED in `PinnedCluster`);
  * `eSurrogate^n`    — tree-graph weight `e^{|Y|}` (`eSurrogate = 3 ≥ e`)
                        — the Penrose / Poghosyan–Ueltschi tree inequality, the
                        SINGLE unbacked factor.

# What this module delivers (all GREEN, axiom-clean, unless marked NAMED-open)

## §1 — the (T)∧(D) split of `penrose_ursell` (PROVED assembly)

`PenroseUrsellSplit cc w r` interposes a size-graded bridge-Ursell term
`bridgeTerm : Nat → Q'` and splits the monolith into TWO named fields:

  * (T) `treeGraph : ∀ n, bridgeTerm n ≤ kpTerm cc w r n`   — per-size tree-graph;
  * (D) `decompose : ∀ d, offCorr d ≤ Σ_{m<tailLen d} bridgeTerm (d+m)`
        — the absolute Mayer–Ursell connecting-cluster expansion.

`PenroseUrsellSplit.toDatum` PROVES `penrose_ursell` from (T) ∧ (D), chaining
`decompose` with the termwise `CharacterTail.finSum_le_termwise` of (T) into the
definitional `connTailPartialG`.  This is the split of §2 of the postulate.

## §2 — factoring (T) into the sharp atom (T′) (PROVED assembly)

`kpTerm_from_atoms` PROVES the per-size (T) bound

    animalCount n · (phiTn · zetan)  ≤  kpTerm cc w r n

from the two per-cluster ingredients `phiTn ≤ eSurrogate^n` (the tree-graph atom
(T′)) and `zetan ≤ (coeffW w r)^n` (the activity bound).  So (T) reduces to (T′)
plus the activity bound — and the activity bound is discharged in-repo.

## §3 — the sharp atom (T′) and its activity backing

`TreeGraphBound S w r` isolates the SOLE unbacked factor: the per-cluster
spanning-tree inequality `phiT Y ≤ eSurrogate^{size Y}` (Penrose 1967;
Poghosyan–Ueltschi 2009; sharp `e^{|Y|}` Fernández–Procacci 2007).  `perCluster_le`
PROVES that, GIVEN (T′), the per-cluster product `phiT Y · activity w Y label` is
dominated by `(coeffW w 1)^{size Y}·eSurrogate^{size Y}` — the activity factor
supplied by the PROVED `PinnedCluster.activity_le_leading`.  So (T′) is genuinely
the only factor without a proved bound.

## §4 — the (D) residuals: Mayer–Ursell expansion (D1) + `SepLattice` (D2)

`BridgeDecomposition` names (D1) (the absolute connecting-cluster expansion, the
already-named `MayerClustering.MayerUrsellIdentity` residual).  `SepLatticeZ4` names
(D2): a `SepLattice` metric refining `z4Chain` (currently only a `BddLattice`) — a
structural geometry prerequisite (plaquette-graph BFS distance + triangle), left
UNINHABITED, not faked.

## §5 — the z4Chain / w4 top-level wiring

`splitToDatumZ4` wires a `PenroseUrsellSplit` over the CLOSED 4D count
`z4ClusterCountBound p` at `w4 = 1/20` into a `PenroseUrsellDatumG`; the generic
`PenroseUrsellSplit.offCorr_decay` supplies the geometric decay
`offCorr d ≤ 2·(15/32)^d` at the PROVED threshold `z4_genuine_threshold`.

# Honest verdict (AGENTS.md Rule 6)

This is a genuine REDUCTION, not a closure.  Net new closed physics: zero.  The
monolithic `penrose_ursell` is factored into exactly ONE new sharp analytic atom
— (T′) the spanning-tree inequality `TreeGraphBound.tree_graph` — one pre-existing
named identity (D1 = `MayerUrsellIdentity`), and one geometry instance (D2 =
`SepLatticeZ4`, missing).  Everything else (`count_le`, `activity_le_leading`,
`finSum_le_termwise`, the geometric tail) is already PROVED and now WIRED.  Fixed
spacing only (`ρ4 = 15/32 < 1`); NOT the spacing-uniform continuum modulus, NOT the
Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The three
open items ((T′), (D1), (D2)) are NAMED Type-level fields / types, uninhabited,
never faked.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.Stage1LoopyReduction

namespace YMGap.Continuum.Ursell4DProgress

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction

/-! ## 1. The (T)∧(D) split of `penrose_ursell` (PROVED assembly)

The postulate's §2 interposes a size-graded bridge-Ursell term over the
connecting-cluster tail.  `PenroseUrsellSplit` carries it as `bridgeTerm`, and
splits the single monolithic `penrose_ursell` field into two logically distinct
named fields:

  * (T) `treeGraph` — the per-size tree-graph domination `bridgeTerm n ≤ kpTerm n`;
  * (D) `decompose` — the absolute Mayer–Ursell connecting-cluster expansion
    `offCorr d ≤ Σ_{m<tailLen d} bridgeTerm (d+m)`.

`toDatum` PROVES that (T) ∧ (D) inhabit `PenroseUrsellDatumG` — the genuine split. -/

/-- **`PenroseUrsellSplit` — the factored Penrose–Ursell datum.**  Carries an
abstract off-diagonal correlator `offCorr`, a finite truncation length
`tailLen d ≥ d`, the size-graded bridge-Ursell term `bridgeTerm`, and the TWO
named-open fields (T) `treeGraph` and (D) `decompose`.  The single monolithic
`penrose_ursell` of `PenroseUrsellDatumG` is recovered by `toDatum`. -/
structure PenroseUrsellSplit {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) (w : Q') (r : Rep) where
  /-- The off-diagonal truncated two-component correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- A finite-volume connecting-tail truncation length. -/
  tailLen : Nat → Nat
  /-- The truncation is at least as long as the size floor `d`. -/
  tailLen_ge : ∀ d, d ≤ tailLen d
  /-- The size-`n` bridge-Ursell term
  `Σ_{Y connected, bridge ⊆ Y, |Y|=n} |φ^T(Y)|·|ζ(Y)|`. -/
  bridgeTerm : Nat → Q'
  /-- **(T) — the per-size tree-graph domination** (NAMED): each bridge-Ursell
  term is bounded by the assembled Ueltschi majorant `kpTerm`. -/
  treeGraph : ∀ n, bridgeTerm n ≤ kpTerm cc w r n
  /-- **(D) — the absolute Mayer–Ursell connecting-cluster expansion** (NAMED):
  the off-diagonal correlator is dominated by the bridge-Ursell tail from the size
  floor `d`. -/
  decompose : ∀ d, offCorr d ≤ finSum (fun m => bridgeTerm (d + m)) (tailLen d)

/-- **`PenroseUrsellSplit.toDatum` (PROVED — the core reduction).**  From the two
factored fields (T) `treeGraph` and (D) `decompose`, the monolithic
`penrose_ursell` follows: `decompose` bounds `offCorr d` by the bridge-Ursell tail,
which `treeGraph` (termwise, via `CharacterTail.finSum_le_termwise`) bounds by the
`kpTerm` tail — definitionally `connTailPartialG cc w r d (tailLen d)`. -/
def PenroseUrsellSplit.toDatum {L : Lattice} {p : L.Plaquette}
    {cc : ClusterCountBound L p} {w : Q'} {r : Rep}
    (S : PenroseUrsellSplit cc w r) : PenroseUrsellDatumG cc w r where
  offCorr := S.offCorr
  tailLen := S.tailLen
  tailLen_ge := S.tailLen_ge
  penrose_ursell := fun d => by
    refine Q'.le_trans' _ _ _ (S.decompose d) ?_
    -- termwise (T): Σ bridgeTerm (d+·) ≤ Σ kpTerm (d+·) = connTailPartialG
    have hterm : ∀ m, S.bridgeTerm (d + m) ≤ kpTerm cc w r (d + m) :=
      fun m => S.treeGraph (d + m)
    have hle := CharacterTail.finSum_le_termwise
      (fun m => S.bridgeTerm (d + m)) (fun m => kpTerm cc w r (d + m)) hterm (S.tailLen d)
    -- `connTailPartialG cc w r d N` is definitionally `Σ_{m<N} kpTerm cc w r (d+m)`
    show finSum (fun m => S.bridgeTerm (d + m)) (S.tailLen d)
        ≤ connTailPartialG cc w r d (S.tailLen d)
    exact hle

/-! ## 2. Factoring (T) into the sharp atom (T′) (PROVED assembly)

The per-size (T) bound `bridgeTerm n ≤ kpTerm n` itself decomposes.  Modelling the
size-`n` bridge-Ursell term as `animalCount n · (phiTn · zetan)` (count folded in
as the multiplicative over-count `# clusters ≤ animalCount n`, each cluster's
weight `≤ phiTn · zetan`), the (T) bound reduces to the two per-cluster
ingredients:

  * (T′) the tree-graph factor `phiTn ≤ eSurrogate^n`  (the SOLE unbacked atom);
  * the activity factor `zetan ≤ (coeffW w r)^n`  (backed by `activity_le_leading`).

`kpTerm_from_atoms` PROVES this.  The count `animalCount n ≤ K^n` is PROVED in
`KPCriterion.count_le` and is already inside `kpTerm`. -/

/-- **`kpTerm_from_atoms` (PROVED — the (T) → (T′) factoring).**  From the
per-cluster tree-graph bound `phiTn ≤ eSurrogate^n` (the atom (T′)) and the
per-cluster activity bound `zetan ≤ (coeffW w r)^n`, the count-folded bridge term
is dominated by the assembled `kpTerm`:

    animalCount n · (phiTn · zetan)  ≤  kpTerm cc w r n
                                     =  animalCount n · (coeffW w r)^n · eSurrogate^n.

Proof: `phiTn·zetan ≤ eSurrogate^n·(coeffW w r)^n` (both factors dominated,
nonneg), scale by `animalCount n ≥ 0`, then commute/re-associate the product to
`kpTerm`. -/
theorem kpTerm_from_atoms {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (_hw : (0 : Q') ≤ w) (r : Rep) (n : Nat)
    {phiTn zetan : Q'} (hzeta0 : (0 : Q') ≤ zetan)
    (htree : phiTn ≤ eSurrogate ^ n) (hact : zetan ≤ (coeffW w r) ^ n) :
    cc.animalCount n * (phiTn * zetan) ≤ kpTerm cc w r n := by
  unfold kpTerm
  have hE_nn : (0 : Q') ≤ eSurrogate ^ n := Q'.pow_nonneg _ eSurrogate_nonneg n
  have hA_nn : (0 : Q') ≤ cc.animalCount n := cc.animalCount_nonneg n
  -- per-cluster: phiTn·zetan ≤ E·zetan ≤ E·C
  have h1 : phiTn * zetan ≤ eSurrogate ^ n * zetan :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ htree hzeta0
  have h2 : eSurrogate ^ n * zetan ≤ eSurrogate ^ n * (coeffW w r) ^ n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hact hE_nn
  have hpc : phiTn * zetan ≤ eSurrogate ^ n * (coeffW w r) ^ n :=
    Q'.le_trans' _ _ _ h1 h2
  -- scale by A = animalCount n ≥ 0
  have h3 : cc.animalCount n * (phiTn * zetan)
      ≤ cc.animalCount n * (eSurrogate ^ n * (coeffW w r) ^ n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpc hA_nn
  -- reorder A·(E·C) ≃ A·(C·E) ≃ (A·C)·E
  have hcomm : (cc.animalCount n * (eSurrogate ^ n * (coeffW w r) ^ n)).eqv
      (cc.animalCount n * ((coeffW w r) ^ n * eSurrogate ^ n)) :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (eSurrogate ^ n) ((coeffW w r) ^ n))
  have hassoc : (cc.animalCount n * ((coeffW w r) ^ n * eSurrogate ^ n)).eqv
      (cc.animalCount n * (coeffW w r) ^ n * eSurrogate ^ n) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (cc.animalCount n) ((coeffW w r) ^ n) (eSurrogate ^ n))
  refine Q'.le_trans' _ _ _ h3 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) ?_
  exact Q'.le_of_eqv hassoc

/-! ## 3. The sharp atom (T′) and its activity backing (NAMED (T′) + PROVED backing)

`TreeGraphBound` isolates the single unbacked factor: the per-cluster spanning-tree
inequality `|φ^T(Y)| ≤ e^{|Y|}` (Penrose 1967; Poghosyan–Ueltschi 2009; sharp
constant Fernández–Procacci 2007).  `perCluster_le` PROVES that, given (T′), the
per-cluster product `phiT Y · activity w Y label` is dominated by
`(coeffW w 1)^{size Y}·eSurrogate^{size Y}` — the activity factor supplied by the
PROVED `PinnedCluster.activity_le_leading`.  This is the concrete evidence that
(T′) is the ONLY factor without a proved bound. -/

/-- **`TreeGraphBound` (NAMED — the sharp atom (T′)).**  Carries the per-cluster
truncated Ursell weight `phiT Y = |φ^T(Y)|` and the SINGLE open field `tree_graph`,
the Penrose / Poghosyan–Ueltschi spanning-tree inequality
`|φ^T(Y)| ≤ eSurrogate^{size Y}` (`eSurrogate = 3 ≥ e`).  LEFT UNINHABITED for a
physical lattice, NOT faked. -/
structure TreeGraphBound (S : SepLattice) (w : Q') (r : Rep) where
  /-- The per-cluster truncated Ursell weight `|φ^T(Y)|`. -/
  phiT : Polymer S.toLattice → Q'
  /-- `|φ^T(Y)| ≥ 0`. -/
  phiT_nonneg : ∀ Y, (0 : Q') ≤ phiT Y
  /-- **The spanning-tree inequality** (the one open atom): the truncated Ursell
  weight of a connecting cluster is bounded by the tree-graph weight
  `e^{|Y|} ≤ eSurrogate^{size Y}`. -/
  tree_graph : ∀ Y, phiT Y ≤ eSurrogate ^ (Polymer.size Y)

/-- **`perCluster_le` (PROVED — the activity factor is backed).**  For a connected
constrained polymer `Y` all of whose plaquettes carry the common rep `r ≥ 1`, at
strong coupling `0 ≤ w ≤ 1/2`, the per-cluster product `phiT Y · activity w Y label`
is dominated by `(coeffW w 1)^{size Y}·eSurrogate^{size Y}`:

  * `phiT Y ≤ eSurrogate^{size Y}` is the atom (T′) (`TreeGraphBound.tree_graph`);
  * `activity w Y label ≤ (coeffW w 1)^{size Y}` is the PROVED
    `PinnedCluster.activity_le_leading`.

So the tree-graph factor is the SOLE unbacked one; the activity factor is already
a proved theorem. -/
theorem perCluster_le {S : SepLattice} {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (r : Rep) (hr : 1 ≤ r)
    (tgb : TreeGraphBound S w r) (Y : Polymer S.toLattice)
    (label : S.toLattice.Plaquette → Rep) (hall : ∀ q, q ∈ Y → label q = r) :
    tgb.phiT Y * activity w Y label
      ≤ (coeffW w 1) ^ Polymer.size Y * eSurrogate ^ Polymer.size Y := by
  have htree : tgb.phiT Y ≤ eSurrogate ^ Polymer.size Y := tgb.tree_graph Y
  have hact : activity w Y label ≤ (coeffW w 1) ^ Polymer.size Y :=
    activity_le_leading hw0 hw Y label r hr hall
  have hact_nn : (0 : Q') ≤ activity w Y label :=
    activity_nonneg hw0 Y label
  have hE_nn : (0 : Q') ≤ eSurrogate ^ Polymer.size Y :=
    Q'.pow_nonneg _ eSurrogate_nonneg _
  -- phiT·act ≤ E·act ≤ E·C, then commute to C·E
  have h1 : tgb.phiT Y * activity w Y label
      ≤ eSurrogate ^ Polymer.size Y * activity w Y label :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ htree hact_nn
  have h2 : eSurrogate ^ Polymer.size Y * activity w Y label
      ≤ eSurrogate ^ Polymer.size Y * (coeffW w 1) ^ Polymer.size Y :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hact hE_nn
  have hcomm : (eSurrogate ^ Polymer.size Y * (coeffW w 1) ^ Polymer.size Y).eqv
      ((coeffW w 1) ^ Polymer.size Y * eSurrogate ^ Polymer.size Y) :=
    Q'.mul_comm_eqv _ _
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ h2 ?_
  exact Q'.le_of_eqv hcomm

/-! ## 4. The (D) residuals: Mayer–Ursell expansion (D1) + `SepLattice` (D2)

The (D) field `decompose` (the absolute connecting-cluster expansion, with size
floor `d`) is exactly the already-named `MayerClustering.MayerUrsellIdentity`
residual, plus a structural geometry prerequisite: the size-floor half needs a
`SepLattice` metric on the plaquette graph (the PROVED
`PinnedCluster.connected_spanning_size_ge` consumes `SepLattice`, not the raw
`BddLattice`).  `z4Chain` is only a `BddLattice`, so a `SepLattice` refining it is
(D2), a genuine geometry obligation (plaquette-graph BFS distance + triangle),
left UNINHABITED. -/

/-- **`BridgeDecomposition` (NAMED — the (D1) residual).**  Names the absolute
Mayer–Ursell connecting-cluster expansion: the off-diagonal correlator is
dominated by the bridge-Ursell tail from the size floor `d`.  This is the
already-named `MayerClustering.MayerUrsellIdentity` residual specialized to the
size-graded bridge terms; `attaches_to` exhibits that it is EXACTLY the (D) field
of a `PenroseUrsellSplit`. -/
structure BridgeDecomposition {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) (w : Q') (r : Rep) where
  /-- The off-diagonal truncated two-component correlator. -/
  offCorr : Nat → Q'
  /-- The size-graded bridge-Ursell term. -/
  bridgeTerm : Nat → Q'
  /-- A finite-volume truncation length `≥ d` (the size floor). -/
  tailLen : Nat → Nat
  /-- `tailLen d ≥ d`. -/
  tailLen_ge : ∀ d, d ≤ tailLen d
  /-- **The absolute Mayer–Ursell connecting-cluster expansion** (the (D1) atom). -/
  decompose : ∀ d, offCorr d ≤ finSum (fun m => bridgeTerm (d + m)) (tailLen d)

/-- **`SepLatticeZ4` (NAMED — the (D2) structural prerequisite).**  A `SepLattice`
metric refining the CLOSED 4D count lattice `z4Chain` (currently only a
`BddLattice`): a plaquette `dist` with `dist_adj_le` (adjacency step `≤ 1`) and
`dist_triangle`.  The natural surrogates fail (base-vertex `‖·‖₁` breaks
`dist_adj_le`; `⌊‖·‖₁/2⌋` restores it but breaks the triangle inequality); the
clean construction is the plaquette-graph BFS distance with a constructive triangle
inequality — real geometry work.  LEFT UNINHABITED, NOT faked. -/
def SepLatticeZ4 : Type 1 :=
  { S : SepLattice // S.toLattice = z4Chain.toLattice }

/-! ## 5. Assembling the split (given (T)∧(D)) — the z4Chain / w4 wiring

Given a `PenroseUrsellSplit` over the CLOSED 4D count `z4ClusterCountBound p` at
`w4 = 1/20`, `splitToDatumZ4` produces the `PenroseUrsellDatumG`; the generic
`PenroseUrsellSplit.offCorr_decay` gives the geometric decay
`offCorr d ≤ 2·(15/32)^d` at the PROVED
`Stage1LoopyReduction.z4_genuine_threshold`. -/

/-- **`splitToDatumZ4` (PROVED).**  A factored split over the CLOSED 4D count at
`w4` yields the monolithic `PenroseUrsellDatumG` — the (T)∧(D) → penrose_ursell
reduction at the physical 4D instance. -/
def splitToDatumZ4 (p : z4Chain.toLattice.Plaquette)
    (S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr) :
    PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr :=
  S.toDatum

/-- **`PenroseUrsellSplit.offCorr_decay` (PROVED — generic).**  For any count
bound, weight, and rep at the strong-coupling threshold `kpRatio cc w r ≤ 1/2`,
the factored split's off-diagonal correlator decays geometrically:

    S.offCorr d  ≤  2 · (kpRatio cc w r)^d.

Chains (D) `decompose`, the termwise (T) `treeGraph` (via
`CharacterTail.finSum_le_termwise`), and the PROVED geometric tail
`connTailPartialG_decay` — the same content as `toDatum` composed with
`penroseUrsell_offCorr_decayG`, phrased directly on `S`'s fields. -/
theorem PenroseUrsellSplit.offCorr_decay {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide))
    (S : PenroseUrsellSplit cc w r) (d : Nat) :
    S.offCorr d ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ d := by
  -- termwise (T): Σ bridgeTerm (d+·) ≤ Σ kpTerm (d+·) = connTailPartialG
  have hle : finSum (fun m => S.bridgeTerm (d + m)) (S.tailLen d)
      ≤ finSum (fun m => kpTerm cc w r (d + m)) (S.tailLen d) :=
    CharacterTail.finSum_le_termwise _ _ (fun m => S.treeGraph (d + m)) (S.tailLen d)
  -- geometric tail: connTailPartialG cc w r d N ≤ 2·ρ^d (uniform in N)
  have hdec : finSum (fun m => kpTerm cc w r (d + m)) (S.tailLen d)
      ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ d :=
    connTailPartialG_decay cc hw r hthr d (S.tailLen d)
  exact Q'.le_trans' _ _ _ (S.decompose d) (Q'.le_trans' _ _ _ hle hdec)

/-! **The concrete 4D decay (as an expression, not a compiled lemma).**  For a
factored split `S : PenroseUrsellSplit (z4ClusterCountBound p) w4 gr`, its
off-diagonal correlator decays at the genuine 4D rate `ρ4 = 15/32 < 1`:

    S.offCorr_decay (z4ClusterCountBound p) w4_nonneg gr (z4_genuine_threshold p) d
      :  S.offCorr d  ≤  2 · (kpRatio (z4ClusterCountBound p) w4 gr)^d.

(Recorded as prose because writing the concrete `kpRatio (z4ClusterCountBound p)
w4 gr` in a stated goal triggers a `whnf` blow-up over the `z4Chain` DFS animal
machinery during unification through `kpRatio` — an elaborator artifact, not a
mathematical gap; the generic `PenroseUrsellSplit.offCorr_decay` above IS the
proved decay content, and `splitToDatumZ4` supplies the concrete 4D datum.) -/

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `PenroseUrsellSplit.toDatum` — the core reduction: (T) ∧ (D) ⟹ the monolithic
    `penrose_ursell`, via `CharacterTail.finSum_le_termwise` into the definitional
    `connTailPartialG`;
  * `kpTerm_from_atoms` — factoring (T) into the sharp atom (T′) `phiTn ≤
    eSurrogate^n` plus the activity bound `zetan ≤ (coeffW w r)^n`, with the count
    `animalCount n` already inside `kpTerm`;
  * `perCluster_le` — GIVEN (T′), the per-cluster product `phiT Y · activity` is
    dominated by `(coeffW w 1)^{|Y|}·eSurrogate^{|Y|}`, the activity factor
    supplied by the PROVED `activity_le_leading` (evidence that (T′) is the only
    unbacked factor);
  * `PenroseUrsellSplit.offCorr_decay` — the generic factored-split decay
    `S.offCorr d ≤ 2·(kpRatio cc w r)^d` at the strong-coupling threshold (D + T +
    the PROVED geometric tail `connTailPartialG_decay`);
  * `splitToDatumZ4` — the z4Chain/w4 wiring of the (T)∧(D) → penrose_ursell
    reduction; the concrete 4D decay `≤ 2·(15/32)^d` is `offCorr_decay` at the
    PROVED `z4_genuine_threshold` (recorded as prose, see above).

NAMED-open (NOT faked — the SOLE irreducible items exposed by the factoring):

  * (T′) `TreeGraphBound.tree_graph` — the per-cluster Penrose / Poghosyan–Ueltschi
    spanning-tree inequality `|φ^T(Y)| ≤ e^{|Y|}` — the single sharp analytic atom,
    the ONLY factor of `kpTerm` with no proved bound;
  * (D1) `BridgeDecomposition.decompose` — the absolute Mayer–Ursell connecting-
    cluster expansion; NOT new — the already-named
    `MayerClustering.MayerUrsellIdentity` residual;
  * (D2) `SepLatticeZ4` — a `SepLattice` metric refining `z4Chain` (only a
    `BddLattice`); a structural geometry prerequisite (BFS graph distance +
    constructive triangle), currently MISSING.

This module is a genuine REDUCTION at FIXED SPACING (`ρ4 = 15/32 < 1`); it factors
the monolithic Penrose–Ursell atom into ONE sharp analytic core (T′), one
pre-existing named identity (D1), and one missing geometry instance (D2), wiring
everything else through already-PROVED in-repo bookkeeping.  It is NOT the spacing-
uniform continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN). -/

end YMGap.Continuum.Ursell4DProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Ursell4DProgress.PenroseUrsellSplit.toDatum
#print axioms YMGap.Continuum.Ursell4DProgress.kpTerm_from_atoms
#print axioms YMGap.Continuum.Ursell4DProgress.perCluster_le
#print axioms YMGap.Continuum.Ursell4DProgress.PenroseUrsellSplit.offCorr_decay
#print axioms YMGap.Continuum.Ursell4DProgress.splitToDatumZ4
