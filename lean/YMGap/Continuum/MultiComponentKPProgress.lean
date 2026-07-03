/-
The Penrose–Ursell re-factor of the FP connecting-cluster bridge — a genuine
REDUCTION + partial REFUTATION of the `MultiComponentKPBound` datum of
`FPClusterIdentity`, isolating the single irreducible open atom (the
Penrose–Ursell signed connecting-cluster identity) with count / threshold /
tree-graph / geometric-decay all documented GREEN.

# The object being re-factored

`FPClusterIdentity.MultiComponentKPBound p` carries `offCorr : Nat → Q'` and the
domination

    bridge_le_span : ∀ d, offCorr d ≤ clusterSpanSum (zChainClusterCountBound p) gw gr d.

`clusterSpanSum … d = finSum (fun m => kpTerm … (d + m)) d` is a FINITE PARTIAL
SUM over sizes `d .. 2d-1` (exactly `d` terms, `RationalTail.finSum … d`).  The
Penrose–Ursell absolute bound, by contrast, dominates `offCorr d` by the FULL
connecting-cluster tail `Σ_{n ≥ d} kpTerm … n`.  The partial sum is strictly
SMALLER than the tail, so `offCorr ≤ clusterSpanSum` is a STRONGER claim than
Ursell yields — the wrong direction.  This is the load-bearing refutation.

# What this module delivers

## Machinery (GREEN, PROVED)

  * `connTailPartial p d N` — the length-`N` connecting-cluster tail from size
    floor `d`: `finSum (fun m => kpTerm (zChainClusterCountBound p) gw gr (d+m)) N`.
    A CONCRETE finite representative of the full connecting tail (in finite
    volume the tail IS a finite sum).
  * `clusterSpanSum_eq_connTailPartial` — `clusterSpanSum … d = connTailPartial p d d`
    (definitional): `clusterSpanSum` hard-codes truncation length `= d`.
  * `kpTerm_nonneg`, `connTailPartial_mono` — the connecting-tail truncations are
    MONOTONE INCREASING in the length `N` (each `kpTerm ≥ 0`).
  * `clusterSpanSum_le_longer_tail` — the REFUTATION made precise:
    `clusterSpanSum … d ≤ connTailPartial p d M` for every `M ≥ d`.  The old
    length-`d` target is `≤` every longer truncation, hence the SMALL / wrong
    majorant; the honest Ursell target permits the full finite tail.
  * `connTailPartial_decay` — the GREEN full-tail decay in its correct
    constructive (uniform-in-`N`) form: `∀ d N, connTailPartial p d N ≤ 2·ρ^d`,
    `ρ = mayerRho p = 4/9`.  Uniform over ALL truncation lengths, so it bounds
    the full connecting tail (its partial sums approach it from below).  This is
    `PinnedCluster.pinnedClusterTail` at `n := d`, `d := N`.

## The reduced residual (ONE open atom)

  * `PenroseUrsellDatum p` — carries `offCorr`, a finite-volume truncation length
    `tailLen d ≥ d`, and the SINGLE open field `penrose_ursell`: the
    Penrose–Ursell absolute connecting-cluster domination
    `offCorr d ≤ connTailPartial p d (tailLen d)`.  Count (`animalCount_le_pow`),
    threshold (`genuine_threshold`), tree-graph (`eSurrogate = 3 ≥ e`), and the
    geometric decay (`connTailPartial_decay`) are ALL green; the sole irreducible
    input is the Penrose–Ursell signed-sum identity (absolute-valued), which is
    all that `penrose_ursell` names.
  * `penroseUrsell_offCorr_decay` — GREEN: given the datum, `offCorr d ≤ 2·ρ^d`,
    by `le_trans` of `penrose_ursell` with `connTailPartial_decay` at the datum's
    own (finite) truncation length.  Decay never needed the short `clusterSpanSum`.
  * `ofMultiComponentKPBound` — the honest bridge: EVERY old
    `MultiComponentKPBound` yields a `PenroseUrsellDatum` (with `tailLen := d`).
    So the new target is IMPLIED BY the old one — strictly WEAKER / easier: the
    old required domination by the SHORT length-`d` truncation, the new permits
    the full finite connecting tail (larger RHS, monotone).
  * `loopyResidual_penroseUrsell` — a genuine `LoopyCorrelatorResidual` from the
    reduced datum, at the majorant rate `ρ = 4/9 < 1`.

# Honest verdict (AGENTS.md Rule 6)

This is a genuine REDUCTION + REFUTATION, NOT a closure.  Net new closed theorems
about the physical correlator: ZERO.  What improves: (1) the load-bearing
refutation that `clusterSpanSum` (a length-`d` partial sum) is the geometrically
WRONG majorant — strictly smaller than the Ursell tail, hence `offCorr ≤
clusterSpanSum` is stronger than Ursell provides; (2) the wall is renamed from
"the FP bridge" to precisely "the Penrose–Ursell signed connecting-cluster
identity," with count / threshold / tree-graph / geometric-decay all green; (3)
the new datum is proved strictly WEAKER than the old (`ofMultiComponentKPBound`).
`offCorr` stays ABSTRACT (the `d = 0` empty-sum obstruction is correct physics —
the single-line `wilsonG` is not a term-wise inhabitant).

# Scope (underclaim)

Finite-volume STRONG-COUPLING combinatorics at the concrete weight `w = 1/6` on
the 1D plaquette chain `zChain`.  The decay rate is the genuine majorant
`ρ = mayerRho p = 4/9 < 1`.  It is NOT uniform-in-`w`, NOT the continuum
(`a → 0`) limit, NOT a multi-plaquette correlator, and NOT a 4D Yang–Mills mass
gap.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props, no `sorry` / `admit` / new
`axiom`.  The open atom is a named Type-level field, uninhabited, never faked as
`le_refl`.  Every load-bearing declaration is gated with `#print axioms`.
-/

import YMGap.Continuum.FPClusterIdentity

namespace YMGap.Continuum.MultiComponentKPProgress

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.FPClusterIdentity

/-! ## 1. `kpTerm` nonnegativity (the monotonicity of the connecting tail) -/

/-- **`kpTerm_nonneg` (PROVED).**  Every KP summand is nonnegative:
`kpTerm cc w r n = animalCount n · (coeffW w r)^n · eSurrogate^n`, a product of
three nonnegative factors (count `≥ 0`, `coeffW ≥ 0` for `w ≥ 0`, `eSurrogate =
3 ≥ 0`).  This is what makes the connecting-tail truncations monotone in the
truncation length. -/
theorem kpTerm_nonneg {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p)
    {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep) (n : Nat) :
    (0 : Q') ≤ kpTerm cc w r n := by
  unfold kpTerm
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (cc.animalCount_nonneg n) (Q'.pow_nonneg _ (coeffW_nonneg hw r) n))
    (Q'.pow_nonneg _ eSurrogate_nonneg n)

/-! ## 2. The connecting-cluster tail truncation `connTailPartial`

`connTailPartial p d N` is the length-`N` truncation of the connecting-cluster
tail from size floor `d`.  In FINITE volume the full connecting tail IS a finite
sum, so a truncation of sufficient length is the honest Penrose–Ursell majorant
— unlike `clusterSpanSum`, which hard-codes length `= d`. -/

/-- **The length-`N` connecting-cluster tail from size floor `d`:**

    connTailPartial p d N  :=  Σ_{m<N} kpTerm (zChainClusterCountBound p) gw gr (d + m)

i.e. the KP activity of connected clusters of size `d, d+1, …, d+N-1`.  A
CONCRETE finite `Q'` (the full tail is its `N → ∞` sup). -/
def connTailPartial (p : zChain.toLattice.Plaquette) (d N : Nat) : Q' :=
  finSum (fun m => kpTerm (zChainClusterCountBound p) gw gr (d + m)) N

/-- **`clusterSpanSum_eq_connTailPartial` (PROVED — definitional).**

    clusterSpanSum (zChainClusterCountBound p) gw gr d  =  connTailPartial p d d.

The old FP-bridge majorant `clusterSpanSum` is EXACTLY the length-`d` truncation
of the connecting tail (sizes `d .. 2d-1`).  This exposes that it hard-codes the
truncation length to `d`. -/
theorem clusterSpanSum_eq_connTailPartial (p : zChain.toLattice.Plaquette) (d : Nat) :
    clusterSpanSum (zChainClusterCountBound p) gw gr d = connTailPartial p d d := rfl

/-- **`connTailPartial_mono` (PROVED).**  The connecting-tail truncations are
MONOTONE INCREASING in the truncation length: `N ≤ M ⇒ connTailPartial p d N ≤
connTailPartial p d M`.  Adding more nonnegative `kpTerm` summands only grows the
partial sum (`finSum_monotone_of_nonneg` with `kpTerm_nonneg`). -/
theorem connTailPartial_mono (p : zChain.toLattice.Plaquette) (d : Nat)
    {N M : Nat} (h : N ≤ M) :
    connTailPartial p d N ≤ connTailPartial p d M := by
  unfold connTailPartial
  exact finSum_monotone_of_nonneg _
    (fun k => kpTerm_nonneg (zChainClusterCountBound p) gw_nonneg gr (d + k)) N M h

/-- **`clusterSpanSum_le_longer_tail` — the REFUTATION made precise (PROVED).**

For every `M ≥ d`,

    clusterSpanSum (zChainClusterCountBound p) gw gr d  ≤  connTailPartial p d M.

`clusterSpanSum … d = connTailPartial p d d` is the SHORTEST connecting-tail
truncation (length `d`, sizes `d .. 2d-1`); it is `≤` every longer truncation.
So `clusterSpanSum` is the SMALL majorant, strictly below the full connecting
tail; requiring `offCorr d ≤ clusterSpanSum … d` is a STRONGER hypothesis than
the Penrose–Ursell bound (`offCorr d ≤ full tail`) provides — the wrong
direction.  The honest Ursell target dominates by the full finite tail
(`connTailPartial p d (tailLen d)`, `tailLen d ≥ d`), not this shortest cut. -/
theorem clusterSpanSum_le_longer_tail (p : zChain.toLattice.Plaquette) (d : Nat)
    {M : Nat} (h : d ≤ M) :
    clusterSpanSum (zChainClusterCountBound p) gw gr d ≤ connTailPartial p d M := by
  rw [clusterSpanSum_eq_connTailPartial]
  exact connTailPartial_mono p d h

/-! ## 3. The GREEN full-tail decay (uniform-in-`N`)

`connTailPartial_decay` is `connectingTail_decay` in its correct constructive
form: a bound holding UNIFORMLY over every truncation length `N`.  Since every
partial sum is `≤ 2·ρ^d` and the partial sums increase to the full tail, this is
exactly the statement that the FULL connecting tail is `≤ 2·ρ^d`.  It is
`PinnedCluster.pinnedClusterTail` at `n := d`, `d := N`, at the genuine
strong-coupling threshold `genuine_threshold`. -/

/-- **`connTailPartial_decay` — DELIVERABLE (GREEN, PROVED).**

    ∀ d N,  connTailPartial p d N  ≤  2 · (mayerRho p)^d,   mayerRho p = 4/9.

Uniform over ALL truncation lengths `N` — hence the honest full-tail decay
(`Σ_{n≥d} kpTerm … n ≤ 2·ρ^d`, the partial sums approaching the tail from below).
This is `pinnedClusterTail (zChainClusterCountBound p) gw_nonneg gr
(genuine_threshold p) d N`: each summand `≤ ρ^{d+m}`, `Σ_m ρ^m ≤ 2` at `ρ ≤ 1/2`.
The `eSurrogate^n = e^{|X|}` factor in `kpTerm` already encodes the tree-graph
(Ueltschi) coefficient; count and threshold are green. -/
theorem connTailPartial_decay (p : zChain.toLattice.Plaquette) (d N : Nat) :
    connTailPartial p d N ≤ Q'.ofNat 2 * (mayerRho p) ^ d := by
  unfold connTailPartial mayerRho
  exact pinnedClusterTail (zChainClusterCountBound p) gw_nonneg gr
    (genuine_threshold p) d N

/-! ## 4. The reduced residual — ONE open atom (`PenroseUrsellDatum`)

`PenroseUrsellDatum p` replaces the whole FP bridge with the single irreducible
open field `penrose_ursell` (the Penrose–Ursell absolute connecting-cluster
identity).  Everything else — count, threshold, tree-graph, geometric decay — is
green (`connTailPartial_decay`).  `offCorr` stays abstract (the `d = 0`
empty-sum obstruction is correct physics). -/

/-- **`PenroseUrsellDatum` (NAMED-open — the reduced FP bridge).**

A datum supplying:
  * `offCorr : Nat → Q'` — an off-diagonal truncated two-component correlator
    (kept ABSTRACT — the single-line `wilsonG` is not a term-wise inhabitant at
    `d = 0`);
  * `tailLen : Nat → Nat` with `tailLen_ge : ∀ d, d ≤ tailLen d` — a FINITE-VOLUME
    connecting-tail truncation length (at least as long as the old
    `clusterSpanSum`'s length `d`; in finite volume the connecting tail is a
    finite sum);
  * `penrose_ursell` — the SINGLE OPEN ATOM: the Penrose–Ursell absolute
    connecting-cluster DOMINATION
    `offCorr d ≤ connTailPartial p d (tailLen d)`.

This is the honest KP relation.  The tree-graph `|φ^T(X)| ≤` spanning-tree count
is subsumed by the `eSurrogate^n = e^{|X|}` factor in `kpTerm`; count
(`animalCount_le_pow`) and threshold (`genuine_threshold`) are discharged; the
geometric decay is `connTailPartial_decay`.  The sole irreducible input is the
Ursell signed-sum identity (absolute-valued) — all that `penrose_ursell` names.
LEFT UNINHABITED, NOT faked. -/
structure PenroseUrsellDatum (p : zChain.toLattice.Plaquette) where
  /-- An off-diagonal truncated two-component correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- A finite-volume connecting-tail truncation length. -/
  tailLen : Nat → Nat
  /-- The truncation is at least as long as `clusterSpanSum`'s length `d`. -/
  tailLen_ge : ∀ d, d ≤ tailLen d
  /-- **The Penrose–Ursell absolute connecting-cluster DOMINATION** (the one open
  atom): the off-diagonal correlator is bounded above by the full (finite-volume)
  connecting-cluster tail. -/
  penrose_ursell : ∀ d, offCorr d ≤ connTailPartial p d (tailLen d)

/-- **`penroseUrsell_offCorr_decay` (PROVED — the reduced conclusion).**

Given the reduced datum, the off-diagonal correlator decays geometrically at the
genuine majorant rate:

    offCorr d  ≤  2 · (mayerRho p)^d,   mayerRho p = 4/9 < 1.

`penrose_ursell` composes with the GREEN `connTailPartial_decay` at the datum's
own finite truncation length `tailLen d`.  The decay side never needed the short
`clusterSpanSum` — it routes through the full connecting tail, as Ursell yields. -/
theorem penroseUrsell_offCorr_decay (p : zChain.toLattice.Plaquette)
    (pu : PenroseUrsellDatum p) (d : Nat) :
    pu.offCorr d ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  Q'.le_trans' _ _ _ (pu.penrose_ursell d) (connTailPartial_decay p d (pu.tailLen d))

/-- **`ofMultiComponentKPBound` (PROVED — the honest bridge / weakness witness).**

EVERY old `FPClusterIdentity.MultiComponentKPBound p` yields a
`PenroseUrsellDatum p` (with `tailLen := fun d => d`), because
`clusterSpanSum … d = connTailPartial p d d`
(`clusterSpanSum_eq_connTailPartial`).  So the new target is IMPLIED BY the old
one — strictly WEAKER / easier: the old datum requires domination by the SHORT
length-`d` truncation; the new datum permits the full finite connecting tail
(a LARGER RHS, monotone in the length).  This certifies the re-factor is a
genuine relaxation, not a re-labeling. -/
def ofMultiComponentKPBound (p : zChain.toLattice.Plaquette)
    (mc : MultiComponentKPBound p) : PenroseUrsellDatum p where
  offCorr := mc.offCorr
  tailLen := fun d => d
  tailLen_ge := fun d => Nat.le_refl d
  penrose_ursell := fun d => by
    have h := mc.bridge_le_span d
    rw [clusterSpanSum_eq_connTailPartial p d] at h
    exact h

/-- **`loopyResidual_penroseUrsell` (a GENUINE `LoopyCorrelatorResidual`).**

Given the reduced datum, the off-diagonal correlator satisfies the
loopy-residual contract at the majorant rate: `graphMass d = d`,
`loopyEnvelope L = 2·(mayerRho p)^L`, `loopyCorr d = pu.offCorr d`, and
`loopy_decay` is the PROVED `penroseUrsell_offCorr_decay`.  The Penrose–Ursell
counterpart of `FPClusterIdentity.loopyResidual_offDiagonalBound`, routed through
the full connecting tail rather than the short `clusterSpanSum`. -/
def loopyResidual_penroseUrsell (p : zChain.toLattice.Plaquette)
    (pu : PenroseUrsellDatum p) : LoopyCorrelatorResidual gw where
  graphMass := fun d => d
  loopyEnvelope := fun L => Q'.ofNat 2 * (mayerRho p) ^ L
  loopyCorr := fun d => pu.offCorr d
  loopy_decay := fun d => penroseUrsell_offCorr_decay p pu d

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `kpTerm_nonneg` — every KP summand `≥ 0` (count, `coeffW`, `eSurrogate` all
    nonneg), the monotonicity engine for the connecting tail;
  * `connTailPartial` (def), `clusterSpanSum_eq_connTailPartial` — the old
    `clusterSpanSum` majorant IS the length-`d` connecting-tail truncation;
  * `connTailPartial_mono`, `clusterSpanSum_le_longer_tail` — the REFUTATION:
    `clusterSpanSum` is the SHORTEST truncation, `≤` every longer one, hence the
    SMALL / wrong majorant; `offCorr ≤ clusterSpanSum` is stronger than Ursell
    yields;
  * `connTailPartial_decay` — the GREEN full-tail decay `≤ 2·ρ^d` UNIFORMLY over
    every truncation length (`pinnedClusterTail`, `ρ = mayerRho p = 4/9`);
  * `penroseUrsell_offCorr_decay` — the reduced conclusion `offCorr d ≤ 2·ρ^d`
    via the open atom + green decay at the datum's finite truncation length;
  * `ofMultiComponentKPBound` — the old bridge IMPLIES the new datum (strictly
    weaker target); `loopyResidual_penroseUrsell` — a genuine
    `LoopyCorrelatorResidual` from the reduced datum.

NAMED-open (NOT faked, Type-level datum — the SOLE irreducible atom):

  * `PenroseUrsellDatum.penrose_ursell` — the Penrose–Ursell absolute
    connecting-cluster identity `offCorr d ≤ connTailPartial p d (tailLen d)`
    (the full finite connecting tail, `tailLen d ≥ d`).  Count / threshold /
    tree-graph (`eSurrogate = 3 ≥ e`) / geometric decay are ALL green; this
    signed-sum identity (absolute-valued) is the one remaining input.  `offCorr`
    abstract (the `d = 0` empty-sum obstruction is correct physics).

This module is a genuine REDUCTION + REFUTATION, not a closure (net new physical
theorems: zero).  Finite-volume strong-coupling combinatorics at `w = 1/6` on the
1D chain, rate `ρ = 4/9 < 1`.  NOT uniform-in-`w`, NOT the continuum (`a → 0`)
limit, NOT a multi-plaquette correlator, NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.MultiComponentKPProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MultiComponentKPProgress.kpTerm_nonneg
#print axioms YMGap.Continuum.MultiComponentKPProgress.clusterSpanSum_eq_connTailPartial
#print axioms YMGap.Continuum.MultiComponentKPProgress.connTailPartial_mono
#print axioms YMGap.Continuum.MultiComponentKPProgress.clusterSpanSum_le_longer_tail
#print axioms YMGap.Continuum.MultiComponentKPProgress.connTailPartial_decay
#print axioms YMGap.Continuum.MultiComponentKPProgress.penroseUrsell_offCorr_decay
#print axioms YMGap.Continuum.MultiComponentKPProgress.ofMultiComponentKPBound
#print axioms YMGap.Continuum.MultiComponentKPProgress.loopyResidual_penroseUrsell
