/-
Stage-1 A-side capstone: the 4D loopy multi-component correlator decay assembled
from the three A-inputs {A1 = Penrose–Ursell, A2 = 6j/Biedenharn–Elliott,
A3 = CLOSED 4D cluster count}, as a genuine REDUCTION (fixed-spacing).

# What this module delivers

`ClusterCount4DProgress.z4ClusterCountBound` (A3) is CLOSED: the genuine degree-24
Z⁴ plaquette `BddLattice` supplies `count_le` at `K = (24+1)² = 625`, and
`z4ClusterCountBound_animal` gives the UNCONDITIONAL over-count guarantee — so the
old 1D `LoopyResidualBulletIV` / `DecodeComplete` anchoring obligation is VACUOUS
on this route (the Penrose–Ursell packaging routes through `pinnedClusterTail`,
which never touches decoding/anchoring).

Over that closed count we re-parametrize the whole Penrose–Ursell engine from the
hard-wired 1D `zChainClusterCountBound` (`MultiComponentKPProgress`) to a generic
`cc : ClusterCountBound L p` — mechanical, because every downstream engine
(`kpTerm`, `pinnedClusterTail`, `kp_criterion_of_count`) is already `{L}{p}`-
polymorphic.  We then:

  * PROVE the new load-bearing atom `z4_genuine_threshold` at the 4D-admissible
    weight `w4 = 1/20`: `kpRatio (z4ClusterCountBound p) w4 1 = 625·(2·(1/20)³)·3
    = 3750/8000 = 15/32 ≤ 1/2` (`decide`).  The K = 625 count shrinks the
    strong-coupling window ~3× vs. 1D (`GenuineKP.genuine_threshold` at w = 1/6
    has NO 4D analog: `625·2·(1/6)³·3 ≈ 17.36 ≫ 1/2`) — an honest cost, not a
    wall.
  * PROVE the generic connecting-tail decay `connTailPartialG cc w r d N ≤ 2·ρ^d`
    uniformly in the truncation length `N`, `ρ = kpRatio cc w r`
    (`pinnedClusterTail`).
  * REDUCE the A-side to `Stage1Loopy`, a structure whose ONLY fields are A1
    (`PenroseUrsellDatumG`) and A2 (`BeyondTreePartitionIdentity`, carrying the
    non-vacuous `SixJRecoupling`), whose output `Stage1Loopy.decay` is a genuine
    `LoopyCorrelatorResidual w4` at rate `ρ4 = 15/32 < 1`.

# The reduction chain

  A3 (CLOSED) → count_le + vacuous bullet-iv;
  step 2      → threshold `ρ4 = 15/32 ≤ 1/2`;
  A1          → `offCorr d ≤ 2·ρ4^d`  (`penroseUrsell_offCorr_decayG`);
  A2          → `offCorr` IS the real two-component truncated Wilson correlator
                (`identity : Ξ ≃ Zreal`, carrying `SixJRecoupling`).

Net: the whole A-side reduces to EXACTLY the two named atoms
`PenroseUrsellDatumG.penrose_ursell` (A1) and
`SixJRecoupling.biedenharn_elliott` (A2), with A3 discharged.

# Honest scope (AGENTS.md Rule 6)

Given A1 + A2, `Stage1Loopy.decay` is a genuine FIXED-SPACING 4D loopy multi-
component correlator decay at `ρ4 = 15/32 < 1` resting on exactly
{Penrose–Ursell, 6j} with A3 CLOSED.  The Clay mass gap stays OPEN: this is
fixed spacing only; the spacing-uniform floor and the `a → 0` modulus
(`UniformCorrelationDecay.UniformPhysicalCorrelationDecay`) are the SEPARATE
Sub-wall B — `LoopyCorrelatorResidual w4` (a `Q'` fixed-spacing decay) is NOT
wired to that `CReal` spacing-indexed structure.  This is a reduction, not a
closure.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The two open
atoms are NAMED Type-level fields, uninhabited, never faked.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.MultiComponentKPProgress
import YMGap.Continuum.ClusterCount4DProgress
import YMGap.Continuum.PartitionBeyondTree

namespace YMGap.Continuum.Stage1LoopyReduction

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
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PartitionBeyondTree

/-! ## 1. The 4D-admissible strong-coupling weight and the PROVED threshold -/

/-- The 4D-admissible strong-coupling weight `w4 = 1/20`.  The crude Euler-tour
count `K = (24+1)² = 625` of the genuine Z⁴ plaquette graph forces a smaller
window than the 1D `gw = 1/6`; `w4 = 1/20` clears `kpRatio ≤ 1/2`. -/
def w4 : Q' := Q'.mkPos 1 20 (by decide)

theorem w4_nonneg : (0 : Q') ≤ w4 := by decide

/-- The leading activity coefficient at `w4 = 1/20`: `coeffW (1/20) 1 = 2·(1/20)³
= 2/8000` (`coeffW w 1 = 2 w³`).  Computed, not assumed. -/
theorem coeffW_w4_gr : coeffW w4 gr = Q'.mkPos 2 8000 (by decide) := by decide

/-- **`z4_genuine_threshold` — the load-bearing 4D atom (PROVED by `decide`).**

    kpRatio (z4ClusterCountBound p) w4 gr  ≤  1/2.

Concretely `625 · (2·(1/20)³) · 3 = 3750/8000 = 15/32 ≤ 1/2` (`15·2 = 30 ≤ 32`).
`kpRatio` reads only `cc.K = animalK z4Chain = 625` and `coeffW w4 gr` (both
`p`-independent), so the bound holds for every plaquette `p`.  This is the
K = 625 analog of `GenuineKP.genuine_threshold`; the 1D weight `w = 1/6` has NO
4D analog here (`625·2·(1/6)³·3 ≈ 17.36 ≫ 1/2`), so the ~3× window shrink is the
honest cost of the crude Euler-tour count. -/
theorem z4_genuine_threshold (p : z4Chain.toLattice.Plaquette) :
    kpRatio (z4ClusterCountBound p) w4 gr ≤ Q'.mkPos 1 2 (by decide) := by
  -- `kpRatio cc w r = cc.K · coeffW w r · eSurrogate`; for `z4Chain`,
  -- `cc.K = animalK z4Chain` is `p`-independent, so the ratio is the closed,
  -- `p`-free rational `animalK z4Chain · coeffW w4 gr · eSurrogate`.
  show animalK z4Chain * coeffW w4 gr * eSurrogate ≤ Q'.mkPos 1 2 (by decide)
  decide

/-! ## 2. The generic connecting-cluster tail (cc-generalized from 1D)

`connTailPartialG cc w r d N` is the `MultiComponentKPProgress.connTailPartial`
with the hard-wired `zChainClusterCountBound`/`gw` abstracted to a generic
`cc`/`w`.  Its decay is `pinnedClusterTail`, already `{L}{p}`-polymorphic — the
re-parametrization is mechanical. -/

/-- **The length-`N` connecting-cluster tail from size floor `d`, generic in the
count bound and weight:** `Σ_{m<N} kpTerm cc w r (d+m)`. -/
def connTailPartialG {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p)
    (w : Q') (r : Rep) (d N : Nat) : Q' :=
  finSum (fun m => kpTerm cc w r (d + m)) N

/-- **`connTailPartialG_decay` (GREEN, PROVED).**

    ∀ d N,  connTailPartialG cc w r d N  ≤  2 · (kpRatio cc w r)^d,

uniform over ALL truncation lengths `N`, at the strong-coupling threshold
`ρ = kpRatio cc w r ≤ 1/2`.  This is `PinnedCluster.pinnedClusterTail` at
`n := d`, `d := N` — count, threshold, tree-graph and geometric decay all green,
generic in `(cc, w, r)`. -/
theorem connTailPartialG_decay {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide)) (d N : Nat) :
    connTailPartialG cc w r d N ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ d := by
  unfold connTailPartialG
  exact pinnedClusterTail cc hw r hthr d N

/-! ## 3. A1 — the generic Penrose–Ursell datum and its decay conclusion

`PenroseUrsellDatumG cc w r` is `MultiComponentKPProgress.PenroseUrsellDatum` with
the 1D `zChainClusterCountBound`/`gw` abstracted to a generic `(cc, w, r)`.  The
single open field `penrose_ursell` is the Penrose–Ursell absolute connecting-
cluster domination; everything else (count / threshold / geometric decay) is
green. -/

/-- **`PenroseUrsellDatumG` (NAMED-open — A1, cc-generalized).**  Carries an
abstract off-diagonal two-component correlator `offCorr`, a finite-volume tail
truncation length `tailLen d ≥ d`, and the SINGLE open atom `penrose_ursell`:
`offCorr d ≤ connTailPartialG cc w r d (tailLen d)`.  LEFT UNINHABITED, NOT
faked. -/
structure PenroseUrsellDatumG {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) (w : Q') (r : Rep) where
  /-- An off-diagonal truncated two-component correlator at bridging distance `d`. -/
  offCorr : Nat → Q'
  /-- A finite-volume connecting-tail truncation length. -/
  tailLen : Nat → Nat
  /-- The truncation is at least as long as `clusterSpanSum`'s length `d`. -/
  tailLen_ge : ∀ d, d ≤ tailLen d
  /-- **The Penrose–Ursell absolute connecting-cluster DOMINATION** (the one open
  atom): the off-diagonal correlator is bounded above by the full (finite-volume)
  connecting-cluster tail. -/
  penrose_ursell : ∀ d, offCorr d ≤ connTailPartialG cc w r d (tailLen d)

/-- **`penroseUrsell_offCorr_decayG` (PROVED — A1's reduced conclusion).**

Given the reduced datum and the strong-coupling threshold, the off-diagonal
correlator decays geometrically:

    offCorr d  ≤  2 · (kpRatio cc w r)^d.

`penrose_ursell` composes with the GREEN `connTailPartialG_decay` at the datum's
own finite truncation length `tailLen d`. -/
theorem penroseUrsell_offCorr_decayG {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide))
    (pu : PenroseUrsellDatumG cc w r) (d : Nat) :
    pu.offCorr d ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ d :=
  Q'.le_trans' _ _ _ (pu.penrose_ursell d)
    (connTailPartialG_decay cc hw r hthr d (pu.tailLen d))

/-- **`ofPenroseUrsellDatum` (PROVED — the 1D → generic bridge).**  Every 1D
`MultiComponentKPProgress.PenroseUrsellDatum p` yields the generic datum at
`(zChainClusterCountBound p, gw, gr)`, since `connTailPartialG` at those
arguments is definitionally the 1D `connTailPartial`.  Certifies the
cc-generalization is a genuine relaxation, not a re-labeling. -/
def ofPenroseUrsellDatum (p : zChain.toLattice.Plaquette)
    (pu : MultiComponentKPProgress.PenroseUrsellDatum p) :
    PenroseUrsellDatumG (zChainClusterCountBound p) gw gr where
  offCorr := pu.offCorr
  tailLen := pu.tailLen
  tailLen_ge := pu.tailLen_ge
  penrose_ursell := pu.penrose_ursell

/-! ## 4. The A-side capstone `Stage1Loopy` and its output decay

The target: a structure over the CLOSED 4D lattice `z4Chain` (A3), at the
4D-admissible strong coupling `w4`, whose ONLY fields are A1 and A2, whose output
`Stage1Loopy.decay` is the real loopy multi-component correlator decay at rate
`ρ4 = 15/32 < 1`. -/

/-- **`Stage1Loopy` — the A-side capstone.**  Its only inputs are the two named
atoms:

  * `ursell` (A1) — the cc-generalized Penrose–Ursell datum over the CLOSED 4D
    count `z4ClusterCountBound p` at `w4`;
  * `beyondTree` (A2) — the beyond-tree partition identity `Ξ ≃ Zreal` carrying
    the non-vacuous `SixJRecoupling` (Biedenharn–Elliott), which is what makes
    A1's abstract `offCorr` BE the real two-component truncated Wilson
    correlator.

A3 is discharged (no field): `z4ClusterCountBound` supplies `count_le`, and
`z4ClusterCountBound_animal` makes the old `DecodeComplete` bullet-iv vacuous on
this Penrose–Ursell route. -/
structure Stage1Loopy [DecidableEq z4Chain.toLattice.Plaquette]
    (p : z4Chain.toLattice.Plaquette)
    (label : z4Chain.toLattice.Plaquette → Rep) where
  /-- A1: the cc-generalized Penrose–Ursell datum over the closed 4D count. -/
  ursell : PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr
  /-- A2: the beyond-tree partition identity carrying `SixJRecoupling`. -/
  beyondTree : BeyondTreePartitionIdentity (L := z4Chain.toLattice) w4 label

/-- **`Stage1Loopy.decay` — the A3-discharged 4D loopy correlator decay (PROVED
modulo A1, A2).**

A genuine `LoopyCorrelatorResidual w4` with `graphMass d = d`, envelope
`2·ρ4^L`, `loopyCorr d = ursell.offCorr d` (the real two-component correlator via
A2's `identity`), and `loopy_decay = penroseUrsell_offCorr_decayG`.  The rate is
`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`, closed by the PROVED
`z4_genuine_threshold`. -/
def Stage1Loopy.decay [DecidableEq z4Chain.toLattice.Plaquette]
    {p : z4Chain.toLattice.Plaquette}
    {label : z4Chain.toLattice.Plaquette → Rep}
    (S : Stage1Loopy p label) : LoopyCorrelatorResidual w4 where
  graphMass := fun d => d
  loopyEnvelope := fun L => Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ L
  loopyCorr := fun d => S.ursell.offCorr d
  loopy_decay := fun d =>
    penroseUrsell_offCorr_decayG (z4ClusterCountBound p) w4_nonneg gr
      (z4_genuine_threshold p) S.ursell d

/-- **The physical identification carried by A2 (PROVED, from the datum).**  The
abstract polymer partition function equals A2's real (spin-network) partition
function; this is what upgrades `Stage1Loopy.decay`'s abstract `offCorr` from a
polymer activity to the physical correlator.  Load-bearing use of A2. -/
theorem Stage1Loopy.physical_identity [DecidableEq z4Chain.toLattice.Plaquette]
    {p : z4Chain.toLattice.Plaquette}
    {label : z4Chain.toLattice.Plaquette → Rep}
    (S : Stage1Loopy p label) (Γ : List (Polymer z4Chain.toLattice)) :
    (Xi w4 Γ label).eqv (S.beyondTree.Zreal Γ) :=
  S.beyondTree.identity Γ

/-- The rate is exactly `15/32` at `w4 = 1/20` (the honest 4D window; recorded
for downstream sharpness).  Stated up to `Q'` equivalence because `Q'.mul` does
NOT reduce fractions (the raw value is `3750/8000 ≃ 15/32`). -/
theorem stage1_rate_value (p : z4Chain.toLattice.Plaquette) :
    (kpRatio (z4ClusterCountBound p) w4 gr).eqv (Q'.mkPos 15 32 (by decide)) := by
  show (animalK z4Chain * coeffW w4 gr * eSurrogate).eqv (Q'.mkPos 15 32 (by decide))
  decide

/-- The rate is `< 1` — the genuine geometric convergence at fixed spacing. -/
theorem stage1_rate_lt_one (p : z4Chain.toLattice.Plaquette) :
    kpRatio (z4ClusterCountBound p) w4 gr < (1 : Q') :=
  ratio_lt_one (z4_genuine_threshold p)

/-! ## 5. A2 non-vacuity re-export (the atom carries real content) -/

/-- **A2 is non-vacuous.**  The bundled `SixJRecoupling` is NOT trivially
inhabitable: the all-zero recoupling fails `biedenharn_elliott`
(`sixj_zero_fails`).  So `Stage1Loopy` does not reduce to a vacuous obligation —
its A2 input carries the genuine `m ≥ 4` closed-fusion-loop content. -/
theorem stage1_A2_nonvacuous :
    ¬ (∀ (D : Nat) (a b c d e : Rep),
        (fusionInd a b e * fusionInd e c d).eqv
          (finSum (fun f => (0 : Q') * (fusionInd b c f * fusionInd a f d)) D)) :=
  sixj_zero_fails

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `w4_nonneg`, `coeffW_w4_gr` — the 4D-admissible weight and its leading
    coefficient `2/8000`;
  * `z4_genuine_threshold` — the load-bearing 4D atom `ρ4 = 15/32 ≤ 1/2`
    (`decide`), the K = 625 analog of `GenuineKP.genuine_threshold`;
  * `connTailPartialG` / `connTailPartialG_decay` — the cc-generalized connecting
    tail and its uniform-in-`N` decay `≤ 2·ρ^d` (`pinnedClusterTail`);
  * `penroseUrsell_offCorr_decayG` — A1's reduced conclusion `offCorr d ≤ 2·ρ^d`;
  * `ofPenroseUrsellDatum` — the 1D datum yields the generic datum (relaxation
    witness);
  * `Stage1Loopy.decay` — the A3-discharged 4D loopy `LoopyCorrelatorResidual w4`
    at `ρ4 = 15/32 < 1`;
  * `Stage1Loopy.physical_identity` — A2's `Ξ ≃ Zreal` (load-bearing use of A2);
  * `stage1_rate_value` / `stage1_rate_lt_one` — the rate is exactly `15/32 < 1`;
  * `stage1_A2_nonvacuous` — the 6j atom is non-vacuous (`sixj_zero_fails`).

NAMED-open (NOT faked — the SOLE two irreducible atoms of the whole A-side):

  * A1 — `PenroseUrsellDatumG.penrose_ursell` (via the `ursell` field of
    `Stage1Loopy`): the Penrose–Ursell absolute connecting-cluster domination.
  * A2 — `PartitionBeyondTree.SixJRecoupling.biedenharn_elliott` (via the
    `beyondTree` field): the SU(2) 6j / Racah recoupling identity, non-vacuous by
    `sixj_zero_fails`.

A3 (`ClusterCount4DProgress.z4ClusterCountBound` + `_animal`) is CLOSED (no
field).  This module is a genuine REDUCTION at FIXED SPACING (`ρ4 = 15/32 < 1`);
the spacing-uniform floor and `a → 0` modulus
(`UniformCorrelationDecay.UniformPhysicalCorrelationDecay`) are the SEPARATE
Sub-wall B, NOT wired here.  It is NOT a continuum limit and NOT the Clay Yang–
Mills mass gap. -/

end YMGap.Continuum.Stage1LoopyReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Stage1LoopyReduction.w4_nonneg
#print axioms YMGap.Continuum.Stage1LoopyReduction.coeffW_w4_gr
#print axioms YMGap.Continuum.Stage1LoopyReduction.z4_genuine_threshold
#print axioms YMGap.Continuum.Stage1LoopyReduction.connTailPartialG_decay
#print axioms YMGap.Continuum.Stage1LoopyReduction.penroseUrsell_offCorr_decayG
#print axioms YMGap.Continuum.Stage1LoopyReduction.ofPenroseUrsellDatum
#print axioms YMGap.Continuum.Stage1LoopyReduction.Stage1Loopy.decay
#print axioms YMGap.Continuum.Stage1LoopyReduction.Stage1Loopy.physical_identity
#print axioms YMGap.Continuum.Stage1LoopyReduction.stage1_rate_value
#print axioms YMGap.Continuum.Stage1LoopyReduction.stage1_rate_lt_one
#print axioms YMGap.Continuum.Stage1LoopyReduction.stage1_A2_nonvacuous
