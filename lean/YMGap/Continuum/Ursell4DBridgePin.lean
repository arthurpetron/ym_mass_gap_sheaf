/-
# (D1) the absolute Mayer–Ursell connecting-cluster expansion — a RIGOROUS
#   satisfiability + adequacy audit against the FRESH Ursell-pin machinery,
#   with the honest verdict machine-checked.

The (D1) atom is `Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p)
w4 gr` (the `d1Mayer` field of `FrontierDAG`).  The commissioning brief asked
whether the fresh Ursell-pin machinery (`UrsellPinComplete`: for the const
hard-core weight the interaction graph is `K_n` and `n!·φ^T = |C(K_n)|`, with
`|C| ≤ τ` PROVED) discharges (D1) — the second Category-A D-move.

This module performs the mandated **satisfiability-FIRST** check and reports the
HONEST result, all machine-checked:

## §1 — the parameters of `BridgeDecomposition` are PHANTOM (under-constraint)

`castBridge` PROVES that `(cc, w, r)` occur in NONE of the fields of
`BridgeDecomposition` — any inhabitant transports verbatim to arbitrary
parameters.  Hence `BridgeDecomposition (z4ClusterCountBound p) w4 gr` carries NO
z4-specific content: it is the bare shape "some `offCorr` dominated by some tail
of some `bridgeTerm`".  Consequences:

  * it is TYPE-satisfiable trivially (`offCorr := 0`) — but VACUOUSLY;
  * it is even satisfiable by a WRONG-instance genuine correlator (the already
    discharged single-line `reconTransfer` at `gw = 1/6`, whose own envelope
    fills `bridgeTerm`) — still not the z4 multi-plaquette physics.

So "discharging the bare `BridgeDecomposition` type" is NOT the same as
discharging the (D1) physics; a bare-type inhabitant would be a Rule-6 fake.
This is exactly why the repo routes the genuine content through the CONSTRAINED
residual `MayerUrsellIdentity_z4_v2` (whose `corr` is pinned to a genuine
`SpectralModel` and whose RHS is pinned to `clusterSpanSum (z4…) w4 gr`).  The
historical `MayerUrsellIdentity_z4` (v1) bug — UNSATISFIABLE because the
hard-coded `tailLen := d` forced the zero model at `d = 0`
(`MayerUrsellZ4.mu_z4_total_weight_le_zero`) — is ALREADY escaped by the free
`tailLen ≥ d` and the `d ≥ 1`-separated v2 (satisfiable by `diagModel`); this
module does not re-open it.

## §2 — what the Ursell pin DOES cover: the per-SIZE tree-graph bound (T′)

`ursellPhiTsize n := |C(K_n)|/n!` is the genuine const hard-core Ursell
coefficient at size `n` (`= 1/2` at `n = 2`, etc.), and `ursellPhiTsize_le`
PROVES `ursellPhiTsize n ≤ eSurrogate^n` by reusing EXACTLY the fresh pin chain
— `penroseIneqConst (-1)` (`|C(K_n)| ≤ τ(K_n)`), `cayleyLooseBound_closed`
(`τ(K_n) ≤ n^{n-1}`), and `legA_loose cubicEulerBound` (`n^{n-1} ≤ eSurrogateⁿⁿΙ`)
— folded through the reciprocal cancellation `ofNat_mul_mkPos_recip_eqv`.  This
is the per-size form of the atom (T′) `TreeGraphBound.tree_graph`, ALREADY
discharged unconditionally by `UrsellPinComplete.treeGraphBoundHardCore`.

**Crucially (§3): (T′) lives on the (T) side of `PenroseUrsellSplit`
(`bridgeTerm n ≤ kpTerm n`, the per-cluster majorant), NOT the (D1) side.**

## §3 — what (D1) actually needs, and why the pin does NOT supply it

In the split anatomy `offCorr d ≤ Σ bridgeTerm ≤ Σ kpTerm`:

  * (T)/(T′) = `bridgeTerm ≤ kpTerm` = the tree-graph majorant `|φ^T| ≤ eⁿΙ`.
    DISCHARGED by the pin (§2).
  * (D1) = `offCorr d ≤ Σ bridgeTerm` = the PHYSICAL Mayer–Ursell expansion:
    the true connected z4 correlator is dominated by the connecting-cluster sum.

The pin discharges (T′); (D1) is the ORTHOGONAL, still-open physical bound.
Its genuine, non-degenerate form is `MayerUrsellIdentity_z4_v2.correlator_le_span_sep`,
and `bridgeDecomposition_of_physical` (re-exposing the PROVED
`MayerUrsellZ4Restated.bridgeDecomposition_of_data_v2`) shows the genuine (D1)
witness reduces EXACTLY to that single physical field — with the tree-graph
majorant kept on the RHS (`bridgeTerm := kpTerm`, whose `eSurrogate^n` factor is
the (T′) content the pin closed).

Sharpening the RHS to the genuine coefficient `ursellPhiTsize` does NOT help:
`ursellPhiTsize n ≤ eSurrogate^n` makes the folded bridge term SMALLER than
`kpTerm n`, so the physical bound `corr ≤ Σ kpTerm` no longer suffices — the
majorant `eSurrogate^n` is exactly what gives the RHS enough room.  So the pin
cannot be repurposed onto the (D1) side.

## Honest verdict (AGENTS.md Rule 6)

**(D1) is NOT the second Category-A D-move via the Ursell-pin machinery.**  The
pin discharges the neighbouring atom (T′) (the tree-graph majorant, the (T)
side); (D1) is the orthogonal PHYSICAL Mayer–Ursell expansion (the (D) side),
whose sole open content is `MayerUrsellIdentity_z4_v2.correlator_le_span_sep` —
a genuine multi-plaquette z4 correlator ≤ connecting-cluster bound that needs
(D2) `SepLatticeZ4` (to run `connected_spanning_size_ge` on the z4 correlator's
own cluster expansion) plus the multi-plaquette expansion identity, NOT the
tree-graph combinatorics the pin provides.  `BridgeDecomposition` as a bare type
is under-constrained (phantom parameters), so its bare-type satisfiability is
vacuous; the genuine target is the constrained v2 residual, LEFT UNINHABITED.

Nothing here inhabits any Clay-frontier guard type; the frontier guard stays at
5.  Fixed spacing only (`ρ4 = 15/32 < 1`); NOT the spacing-uniform continuum
modulus, NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  Every
load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.UrsellPinComplete
import YMGap.Continuum.MayerUrsellZ4Restated

namespace YMGap.Continuum.Ursell4DBridgePin

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseConstWeightDC
open YMGap.Continuum.PenroseConstInRange
open YMGap.Continuum.CayleyLooseReduction
open YMGap.Continuum.CayleyParentInj
open YMGap.Continuum.CubicEulerBoundProof
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.UrsellPinComplete
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.MayerBridgeDecomposition
open YMGap.Continuum.MayerUrsellZ4Restated

/-! ## 1. The parameters of `BridgeDecomposition` are PHANTOM (under-constraint) -/

/-- **`castBridge` (PROVED — the phantom-parameter diagnostic).**  The parameters
`(cc, w, r)` occur in NONE of the fields of `BridgeDecomposition` (each field
type mentions only `offCorr` / `bridgeTerm` / `tailLen`).  Hence any inhabitant
transports verbatim to ARBITRARY parameters — machine-proof that
`BridgeDecomposition (z4ClusterCountBound p) w4 gr` carries no z4-specific
content, so its bare-type satisfiability is VACUOUS (an `offCorr := 0`, or a
wrong-instance genuine correlator, both inhabit it without capturing the z4
physics).  This is why the genuine (D1) target is the CONSTRAINED
`MayerUrsellIdentity_z4_v2`, not the bare `BridgeDecomposition`. -/
def castBridge {L : Lattice} {p : L.Plaquette}
    {cc cc' : ClusterCountBound L p} {w w' : Q'} {r r' : Rep}
    (B : BridgeDecomposition cc w r) : BridgeDecomposition cc' w' r' where
  offCorr := B.offCorr
  bridgeTerm := B.bridgeTerm
  tailLen := B.tailLen
  tailLen_ge := B.tailLen_ge
  decompose := B.decompose

/-! ## 2. What the Ursell pin DOES cover — the per-SIZE tree-graph bound (T′) -/

/-- **`ursellPhiTsize n` — the genuine const hard-core Ursell coefficient at size
`n`.**  `|C(K_n)| / n!` (the signed connected-subgraph sum over the complete
graph `K_n`, the interaction graph of the constant pair weight `wConst (-1)`,
divided by `n!`).  Genuine and non-vacuous (`= 1/2` at `n = 2`): the LHS is the
real signed-cluster combinatorial object, NOT the majorant `eSurrogate^n`. -/
def ursellPhiTsize (n : Nat) : Q' :=
  Q'.abs (Csum (wConst (-1)) n (completeEdges n))
    * Q'.mkPos 1 (fact n) (fact_pos n)

/-- `ursellPhiTsize n ≥ 0` (an absolute value times a positive reciprocal). -/
theorem ursellPhiTsize_nonneg (n : Nat) : (0 : Q') ≤ ursellPhiTsize n :=
  Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (mkPos_recip_nonneg _ (fact_pos n))

/-- **`ursellPhiTsize_le` (PROVED — the per-size atom (T′), via the FRESH pin
chain).**  `ursellPhiTsize n ≤ eSurrogate^n`.  Reuses EXACTLY the Ursell-pin
combinatorics:

  * `penroseIneqConst (-1)` : `|C(K_n)| ≤ τ(K_n)`  (Penrose sign-domination,
    deletion–contraction, in-range `K_n`);
  * `cayleyLooseBound_closed` : `τ(K_n) ≤ n^{n-1}`  (loose Cayley, simple `K_n`);
  * `legA_loose cubicEulerBound` : `n^{n-1} ≤ eSurrogate^n · n!`  (Euler `e < 3`);

chained to `|C(K_n)| ≤ eSurrogate^n · n!`, then divided by `n!` via the reciprocal
cancellation `ofNat_mul_mkPos_recip_eqv`.  This is the per-size form of the atom
(T′) `TreeGraphBound.tree_graph` already discharged by
`UrsellPinComplete.treeGraphBoundHardCore`. -/
theorem ursellPhiTsize_le (n : Nat) : ursellPhiTsize n ≤ eSurrogate ^ n := by
  -- (P) Penrose sign-domination on the in-range complete graph K_n
  have hP : Q'.abs (Csum (wConst (-1)) n (completeEdges n))
      ≤ Q'.ofNat (treeCount n (completeEdges n)) :=
    penroseIneqConst (-1) (by decide) (by decide) n (completeEdges n)
      (compEdges_inRange n)
  -- (C′) loose Cayley on the simple graph K_n
  have hC : treeCount n (completeEdges n) ≤ n ^ (n - 1) :=
    cayleyLooseBound_closed n (completeEdges n) (compEdges_simple n)
  have hCq : Q'.ofNat (treeCount n (completeEdges n)) ≤ Q'.ofNat (n ^ (n - 1)) :=
    ofNat_le_ofNat hC
  -- (A) Euler crux n^{n-1} ≤ eSurrogate^n · n!
  have hA : Q'.ofNat (n ^ (n - 1)) ≤ eSurrogate ^ n * Q'.ofNat (fact n) :=
    legA_loose cubicEulerBound n
  -- chain: |C(K_n)| ≤ eSurrogate^n · n!
  have hchain : Q'.abs (Csum (wConst (-1)) n (completeEdges n))
      ≤ eSurrogate ^ n * Q'.ofNat (fact n) :=
    Q'.le_trans' _ _ _ hP (Q'.le_trans' _ _ _ hCq hA)
  -- divide by n! : multiply on the right by the nonneg reciprocal
  have hrec_nn : (0 : Q') ≤ Q'.mkPos 1 (fact n) (fact_pos n) :=
    mkPos_recip_nonneg _ (fact_pos n)
  have hscaled :
      Q'.abs (Csum (wConst (-1)) n (completeEdges n)) * Q'.mkPos 1 (fact n) (fact_pos n)
        ≤ (eSurrogate ^ n * Q'.ofNat (fact n)) * Q'.mkPos 1 (fact n) (fact_pos n) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hchain hrec_nn
  -- RHS ≃ eSurrogate^n · (n! · 1/n!) ≃ eSurrogate^n · 1 ≃ eSurrogate^n
  have hassoc :
      ((eSurrogate ^ n * Q'.ofNat (fact n)) * Q'.mkPos 1 (fact n) (fact_pos n)).eqv
        (eSurrogate ^ n * (Q'.ofNat (fact n) * Q'.mkPos 1 (fact n) (fact_pos n))) :=
    Q'.mul_assoc_eqv _ _ _
  have hrecip : (Q'.ofNat (fact n) * Q'.mkPos 1 (fact n) (fact_pos n)).eqv 1 :=
    ofNat_mul_mkPos_recip_eqv (fact n) (fact_pos n)
  have hcong :
      (eSurrogate ^ n * (Q'.ofNat (fact n) * Q'.mkPos 1 (fact n) (fact_pos n))).eqv
        (eSurrogate ^ n * 1) :=
    Q'.mul_eqv_congr_left _ _ _ hrecip
  have hone : (eSurrogate ^ n * (1 : Q')).eqv (eSurrogate ^ n) := Q'.mul_one_eqv _
  have hRHS :
      ((eSurrogate ^ n * Q'.ofNat (fact n)) * Q'.mkPos 1 (fact n) (fact_pos n)).eqv
        (eSurrogate ^ n) :=
    Q'.eqv_trans _ _ _ hassoc (Q'.eqv_trans _ _ _ hcong hone)
  show Q'.abs (Csum (wConst (-1)) n (completeEdges n)) * Q'.mkPos 1 (fact n) (fact_pos n)
      ≤ eSurrogate ^ n
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hRHS)

/-! ## 3. What (D1) actually needs — the PHYSICAL Mayer–Ursell bound (the wall) -/

/-- **`bridgeDecomposition_of_physical` (PROVED — the genuine (D1) reduction).**
The genuine, non-vacuous (D1) witness reduces EXACTLY to the single physical
field `correlator_le_span_sep` of `MayerUrsellIdentity_z4_v2`: given a genuine z4
`SpectralModel` whose connected correlator is dominated (off the diagonal) by the
connecting-cluster sum, the (D1) atom `BridgeDecomposition (z4ClusterCountBound p)
w4 gr` is inhabited with a REAL correlator `offCorr := corr MU.model` and the
majorant `bridgeTerm := kpTerm` (whose `eSurrogate^n` factor is the (T′) content
the pin closed).  Re-exposes the PROVED
`MayerUrsellZ4Restated.bridgeDecomposition_of_data_v2`.

The input `MayerUrsellIdentity_z4_v2` is LEFT UNINHABITED — its
`correlator_le_span_sep` is the orthogonal PHYSICAL wall the Ursell pin does NOT
reach (the pin discharges the (T′) tree-graph majorant, §2, a DIFFERENT atom). -/
def bridgeDecomposition_of_physical (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr :=
  bridgeDecomposition_of_data_v2 p MU

/-- **`physical_bound_is_the_open_field` (PROVED — the sole open content named).**
The physical off-diagonal content of (D1) at the z4/w4 instance IS the separated
Mayer–Ursell bound: for a `MayerUrsellIdentity_z4_v2 p` witness and any `d ≥ 1`,

    corr MU.model d  ≤  clusterSpanSum (z4ClusterCountBound p) w4 gr d.

This is `MU.correlator_le_span_sep` verbatim — recorded here to pin the exact
lemma that resists: it is a bound on the GENUINE z4 correlator (a `SpectralModel`
`corr`), NOT on the per-cluster tree weight, hence NOT supplied by the
tree-graph pin. -/
theorem physical_bound_is_the_open_field (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) (d : Nat) (hd : 1 ≤ d) :
    corr MU.model d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d :=
  MU.correlator_le_span_sep d hd

/-! ## 4. Documentation: PROVED vs the OPEN wall (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean, non-vacuous):

  * `castBridge` — the phantom-parameter diagnostic: `BridgeDecomposition`'s
    `(cc, w, r)` are unused, so the bare type is under-constrained and its bare
    satisfiability is vacuous;
  * `ursellPhiTsize`, `ursellPhiTsize_nonneg`, `ursellPhiTsize_le` — the per-size
    atom (T′) `|C(K_n)|/n! ≤ eSurrogate^n` via the FRESH pin chain
    (`penroseIneqConst (-1)` + `cayleyLooseBound_closed` + `legA_loose
    cubicEulerBound` + reciprocal cancellation) — exactly the (T) side the pin
    covers;
  * `bridgeDecomposition_of_physical` — the genuine (D1) reduction to the single
    physical field (re-exposing `bridgeDecomposition_of_data_v2`);
  * `physical_bound_is_the_open_field` — the exact resisting lemma named:
    `corr MU.model d ≤ clusterSpanSum … d` (the z4 correlator bound).

OPEN (deliberately UNINHABITED — the orthogonal wall, NOT faked):

  * (D1) genuine content = `MayerUrsellIdentity_z4_v2.correlator_le_span_sep` —
    the PHYSICAL multi-plaquette z4 Mayer–Ursell expansion.  The Ursell-pin
    machinery discharges the neighbouring atom (T′) (tree-graph majorant, (T)
    side), NOT this (D) side.  Needs (D2) `SepLatticeZ4` + the multi-plaquette
    expansion identity.

VERDICT: (D1) is NOT the second Category-A D-move via the Ursell pin; it is the
orthogonal physical atom.  Fixed spacing only (`ρ4 = 15/32 < 1`); NOT the
spacing-uniform continuum modulus, NOT the Clay Yang–Mills mass gap (OPEN). -/

end YMGap.Continuum.Ursell4DBridgePin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Ursell4DBridgePin.castBridge
#print axioms YMGap.Continuum.Ursell4DBridgePin.ursellPhiTsize_nonneg
#print axioms YMGap.Continuum.Ursell4DBridgePin.ursellPhiTsize_le
#print axioms YMGap.Continuum.Ursell4DBridgePin.bridgeDecomposition_of_physical
#print axioms YMGap.Continuum.Ursell4DBridgePin.physical_bound_is_the_open_field
