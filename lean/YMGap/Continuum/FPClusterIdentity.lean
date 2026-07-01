/-
The Fernández–Procacci / Ueltschi connecting-cluster bound — the HONEST
`≤` reframing of the off-diagonal (bullet ii) two-component bridge, replacing
the impossible `.eqv` identity of `LoopyCorrelatorBound.MultiComponentKP`.

# Where this sits (the correction to the `.eqv` bridge)

`LoopyCorrelatorBound.MultiComponentKP` carries an off-diagonal correlator
`offCorr` together with the field

    bridge_eq_span : ∀ d, (offCorr d).eqv
                            (clusterSpanSum (zChainClusterCountBound p) gw gr d).

That `.eqv` is NOT honestly inhabitable.  `clusterSpanSum` is a Kotecký–Preiss
MAJORANT: it carries the lattice-animal count `animalCount n` and the surrogate
weight `eSurrogate^n = 3^n`, whereas every real single-component correlator in
the tree collapses to a plain excited-rep sum with NO count factor and NO
`eSurrogate` (`WilsonConnCorr.wilsonG_collapse`, `treeG`, `graphG`).  These
differ term-by-term, and numerically the real single-line rate is
`rho gw = coeffW gw 1 = 1/108`, whereas the majorant rate is
`mayerRho p = 4/9`.  So `offCorr d ≃ clusterSpanSum d` can hold ONLY if `offCorr`
is DEFINED to be `clusterSpanSum` — the forbidden `eqv_refl` gaming hole
(rejected exactly as `WilsonCorrelator.genuineRealCorrelatorLink`).  The honest
relation between a real truncated correlator and a KP majorant is DOMINATION
`≤` (the Ueltschi-2004 connecting-cluster BOUND), not equality.

# What this module delivers (two honest tracks)

## Track A — the REAL single-line object, discharged by its OWN proved decay

`twoCompOffCorr M d := WilsonConnCorr.wilsonG gw (M+1) d` is the connecting-chain
truncated correlator — a GENUINE character double-sum, NOT `clusterSpanSum`.  Its
geometric decay is ALREADY PROVED (`WilsonConnCorr.wilsonG_decay`), so it packages
DIRECTLY into a genuine `MultiPlaquetteMayer.LoopyCorrelatorResidual` whose
`loopyCorr` is the REAL correlator and whose `loopy_decay` is proved outright —
NO named residual needed.  This mirrors the honesty of
`LoopyCorrelatorProgress.loopyResidual_multiLoop` (real `graphG`).  The real
single-line rate `rho gw = 1/108` is even faster than the majorant `mayerRho p =
4/9` (`rho_gw_le_mayerRho`), consistent with domination.

## Track B — the honest `≤` reframing, reduced to ONE named domination datum

`MultiComponentKPBound p` replaces the impossible `.eqv` bridge with the honest
DOMINATION `bridge_le_span : ∀ d, offCorr d ≤ clusterSpanSum … d`.  `offCorr` is
kept ABSTRACT (NOT fixed to `wilsonG`): the literal domination
`wilsonG gw (M+1) d ≤ clusterSpanSum … d` FAILS at `d = 0` (there
`clusterSpanSum … 0` is the empty sum `= 0` while `wilsonG … 0 > 0`), so the
single-line `wilsonG` is not a term-wise inhabitant — the honest FP content is
the connecting-cluster domination for the TRUE multi-component truncated
correlator at proper bridging indexing.  The structure is LEFT UNINHABITED (the
one named Ueltschi combinatorial datum), NOT faked.  Given it, the off-diagonal
decay `offCorr d ≤ 2·(mayerRho p)^d` at the majorant rate is PROVED
(`bound_offCorr_decay`, via the already-proved `multiComponent_bridge_decay`),
and packages into a genuine `LoopyCorrelatorResidual`.

# Honesty note (AGENTS.md Rule 8, "verify a named obligation is satisfiable")

The `≤` form is the mathematically correct KP relation, strictly more honest than
the `.eqv` form (which is inhabitable only by the forbidden `eqv_refl`).  We do
NOT claim the single-line `wilsonG` inhabits it (it does not, at `d = 0`); the
real single-line object is discharged independently in Track A via its own faster
decay.  Track B's structure is the general connecting-cluster domination, carried
Type-level and uninhabited.

# Scope (underclaim, AGENTS.md Rule 6)

Finite-volume STRONG-COUPLING combinatorics at the concrete weight `w = 1/6` on
the 1D plaquette chain `zChain`.  Track A's decay is GENUINE (rate
`rho gw = 2·(1/6)³ = 1/108 < 1`); Track B's rate is the genuine majorant
`mayerRho p = 4/9 < 1`.  It is NOT uniform-in-`w`, NOT the continuum (`a → 0`)
limit, and NOT a 4D Yang–Mills mass gap.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props, no `sorry` / `admit` / new
`axiom`.  Track A is a REAL correlator with proved decay; Track B's domination is
a named Type-level structure, uninhabited, never faked as `eqv_refl` or `le_refl`.
Every load-bearing declaration is gated with `#print axioms`.
-/

import YMGap.Continuum.LoopyCorrelatorBound

namespace YMGap.Continuum.FPClusterIdentity

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.LoopyCorrelatorBound

/-! ## 1. Track A — the REAL single-line off-diagonal correlator

`twoCompOffCorr M d = wilsonG gw (M+1) d` is the connecting-chain truncated
two-component correlator: a GENUINE vacuum-subtracted character double-sum
(`WilsonConnCorr.wilsonG`), NOT `clusterSpanSum`.  It is the honest REAL object
for the off-diagonal bullet — its own geometric decay is already proved. -/

/-- **The REAL off-diagonal two-component correlator** at bridging distance `d`:
the connecting-chain truncated correlator `wilsonG gw (M+1) d`.  A genuine
character double-sum (`WilsonConnCorr.wilsonG`), NOT defined to equal
`clusterSpanSum`. -/
def twoCompOffCorr (M : Nat) : Nat → Q' := fun d => wilsonG gw (M + 1) d

/-- **`twoCompOffCorr_decay` (PROVED — the real object's own geometric decay).**

The real connecting-chain off-diagonal correlator decays geometrically at the
genuine strong-coupling single-line rate:

    twoCompOffCorr M d  =  wilsonG gw (M+1) d  ≤  (ofNat M · rho gw)·(rho gw)^d,

`rho gw = coeffW gw 1 = 2·(1/6)³ = 1/108 < 1`.  This is the proved
`WilsonConnCorr.wilsonG_decay` at `w = gw` (`0 ≤ gw ≤ 1/2`), NOT posited. -/
theorem twoCompOffCorr_decay (M d : Nat) :
    twoCompOffCorr M d ≤ (Q'.ofNat M * rho gw) * (rho gw) ^ d :=
  wilsonG_decay gw_nonneg (by decide) M d

/-- **`loopyResidual_offDiagonalReal` (a GENUINE `LoopyCorrelatorResidual` from
the REAL object).**  The real off-diagonal correlator satisfies the loopy-residual
contract with NO named residual: `graphMass d = d`, `loopyEnvelope L =
(ofNat M · rho gw)·(rho gw)^L`, `loopyCorr d = twoCompOffCorr M d` (the REAL
correlator), and `loopy_decay` is the PROVED `twoCompOffCorr_decay`.  This
discharges the off-diagonal bullet with a real object at rate `rho gw = 1/108 < 1`
— the off-diagonal counterpart of `LoopyCorrelatorProgress.loopyResidual_multiLoop`
(whose `loopyCorr` is the real `graphG`). -/
def loopyResidual_offDiagonalReal (M : Nat) : LoopyCorrelatorResidual gw where
  graphMass := fun d => d
  loopyEnvelope := fun L => (Q'.ofNat M * rho gw) * (rho gw) ^ L
  loopyCorr := fun d => twoCompOffCorr M d
  loopy_decay := fun d => twoCompOffCorr_decay M d

/-! ## 2. The genuine rate ordering: the real object is at least as fast as the
majorant

The real single-line rate `rho gw = coeffW gw 1 = 1/108` is `≤` the KP majorant
rate `mayerRho p = kpRatio (zChainClusterCountBound p) gw gr = 4/9`, consistent
with the domination `real correlator ≤ connecting-cluster majorant`.  Both are
closed rationals (p-independent), so the ordering is decidable. -/

/-- **`rho_gw_le_mayerRho` (PROVED).**  The real single-line decay rate is
dominated by the KP majorant rate: `rho gw = 1/108 ≤ 4/9 = mayerRho p`.
`mayerRho p = animalK zChain · coeffW gw gr · eSurrogate` and
`rho gw = coeffW gw 1 = coeffW gw gr` are closed rationals (p-independent), so
this reduces to the decidable `Int` cross-product `1·9 ≤ 4·108`.  Consistent with
`real correlator ≤ connecting-cluster majorant`. -/
theorem rho_gw_le_mayerRho (p : zChain.toLattice.Plaquette) :
    rho gw ≤ mayerRho p := by
  -- rho gw = coeffW gw 1 ;  mayerRho p = animalK zChain · coeffW gw gr · eSurrogate
  show coeffW gw 1 ≤ animalK zChain * coeffW gw gr * eSurrogate
  decide

/-! ## 3. Track B — the honest `≤` reframing of the FP bridge

`MultiComponentKPBound p` replaces the impossible `.eqv` bridge of
`LoopyCorrelatorBound.MultiComponentKP` with the honest DOMINATION `≤`.  `offCorr`
is kept ABSTRACT: the single-line `wilsonG` is NOT a term-wise inhabitant (the
domination fails at `d = 0`, where `clusterSpanSum … 0 = 0 < wilsonG … 0`).  The
structure is the general connecting-cluster domination — the one named Ueltschi
combinatorial datum — LEFT UNINHABITED, NOT faked. -/

/-- **`MultiComponentKPBound` (NAMED-open — the honest `≤` reframe of the FP
bridge).**

A datum supplying:
  * `offCorr : Nat → Q'` — an off-diagonal truncated two-component correlator;
  * `bridge_le_span` — the Ueltschi connecting-cluster DOMINATION: the off-diagonal
    correlator is bounded ABOVE by the connecting-cluster activity sum
    `clusterSpanSum (zChainClusterCountBound p) gw gr d` at every bridging distance.

This is the mathematically correct KP relation (`≤`, the Ueltschi-2004 bound),
replacing the impossible `.eqv` of `MultiComponentKP` (which is inhabitable only
by the forbidden `eqv_refl`).  `offCorr` is abstract — the single-line `wilsonG`
is NOT a term-wise inhabitant (domination fails at `d = 0`; the real single-line
object is discharged in Track A via its own faster decay).  LEFT UNINHABITED — the
one named FP/Ueltschi combinatorial datum, NOT faked. -/
structure MultiComponentKPBound (p : zChain.toLattice.Plaquette) where
  /-- An off-diagonal truncated two-component correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- **The Ueltschi connecting-cluster DOMINATION** (the honest KP relation):
  the off-diagonal correlator is bounded above by the connecting-cluster sum. -/
  bridge_le_span : ∀ d,
    offCorr d ≤ clusterSpanSum (zChainClusterCountBound p) gw gr d

/-- **`bound_offCorr_decay` (PROVED — immediate from the domination).**

Given the honest domination `MultiComponentKPBound p`, the off-diagonal
correlator decays geometrically at the genuine majorant rate:

    offCorr d  ≤  2·(mayerRho p)^d,   mayerRho p = 4/9 < 1.

The domination `bridge_le_span` composes with the already-proved connecting-cluster
decay `multiComponent_bridge_decay` (`clusterSpanSum … ≤ 2·(mayerRho p)^d`).  The
decay side never needed equality — only the upper bound `≤`. -/
theorem bound_offCorr_decay (p : zChain.toLattice.Plaquette)
    (mc : MultiComponentKPBound p) (d : Nat) :
    mc.offCorr d ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  Q'.le_trans' _ _ _ (mc.bridge_le_span d) (multiComponent_bridge_decay p d)

/-- **`loopyResidual_offDiagonalBound` (a GENUINE `LoopyCorrelatorResidual` from
the honest domination).**  Given `MultiComponentKPBound p`, the off-diagonal
correlator satisfies the loopy-residual contract at the majorant rate:
`graphMass d = d`, `loopyEnvelope L = 2·(mayerRho p)^L`, `loopyCorr d = mc.offCorr d`
(the REAL off-diagonal correlator, whatever it is), and `loopy_decay` is the PROVED
`bound_offCorr_decay`.  The honest-`≤` counterpart of the (impossible-`.eqv`)
`LoopyCorrelatorBound.loopyResidual_offDiagonal`. -/
def loopyResidual_offDiagonalBound (p : zChain.toLattice.Plaquette)
    (mc : MultiComponentKPBound p) : LoopyCorrelatorResidual gw where
  graphMass := fun d => d
  loopyEnvelope := fun L => Q'.ofNat 2 * (mayerRho p) ^ L
  loopyCorr := fun d => mc.offCorr d
  loopy_decay := fun d => bound_offCorr_decay p mc d

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `twoCompOffCorr` (= the REAL `wilsonG gw (M+1)`), `twoCompOffCorr_decay`
    (its own geometric decay `≤ (ofNat M · rho gw)·(rho gw)^d`, from the proved
    `WilsonConnCorr.wilsonG_decay`), `loopyResidual_offDiagonalReal` — Track A:
    a GENUINE `LoopyCorrelatorResidual` whose `loopyCorr` is the REAL off-diagonal
    correlator, decay proved OUTRIGHT (no named residual), rate `rho gw = 1/108 < 1`;
  * `rho_gw_le_mayerRho` — the real single-line rate is `≤` the KP majorant rate
    (`1/108 ≤ 4/9`), consistent with `real correlator ≤ connecting-cluster majorant`;
  * `bound_offCorr_decay` — Track B: given the honest domination, the off-diagonal
    decay `offCorr d ≤ 2·(mayerRho p)^d` at the majorant rate `4/9`, via the
    already-proved `multiComponent_bridge_decay`;
  * `loopyResidual_offDiagonalBound` — a GENUINE `LoopyCorrelatorResidual` from the
    honest domination.

NAMED-open (NOT faked, Type-level datum):

  * `MultiComponentKPBound` — the honest `≤` reframing of the FP bridge: the
    Ueltschi connecting-cluster DOMINATION `offCorr d ≤ clusterSpanSum … d`.  This
    is the mathematically correct KP relation, replacing the impossible `.eqv` of
    `LoopyCorrelatorBound.MultiComponentKP` (inhabitable only by the forbidden
    `eqv_refl`).  `offCorr` is abstract — the single-line `wilsonG` is NOT a
    term-wise inhabitant (domination fails at `d = 0`); LEFT UNINHABITED, the one
    named FP/Ueltschi combinatorial datum.

This module is finite-volume strong-coupling combinatorics at `w = 1/6` on the 1D
chain.  Track A's decay is genuine (`rho gw = 1/108 < 1`); Track B's majorant rate
is genuine (`mayerRho p = 4/9 < 1`).  It is NOT uniform-in-`w`, NOT the continuum
(`a → 0`) limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FPClusterIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FPClusterIdentity.twoCompOffCorr_decay
#print axioms YMGap.Continuum.FPClusterIdentity.loopyResidual_offDiagonalReal
#print axioms YMGap.Continuum.FPClusterIdentity.rho_gw_le_mayerRho
#print axioms YMGap.Continuum.FPClusterIdentity.bound_offCorr_decay
#print axioms YMGap.Continuum.FPClusterIdentity.loopyResidual_offDiagonalBound
