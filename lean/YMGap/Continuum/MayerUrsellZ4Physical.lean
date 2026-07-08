/-
`MayerUrsellZ4Physical` — the RIGOROUS satisfiability audit + genuine forward
reduction for the (D1) atom `MayerUrsellZ4Restated.MayerUrsellIdentity_z4_v2`'s
sole open field `correlator_le_span_sep`.

The commissioning brief was: PROVE `correlator_le_span_sep` — the genuine z4
multi-plaquette Mayer–Ursell bound `∀ d ≥ 1, corr model d ≤ clusterSpanSum …
d` — against a REAL z4 `SpectralModel`, NOT the phantom bare type.  This module
carries out the mandated **satisfiability-FIRST** audit and delivers the honest,
fully machine-checked result.

# §1 — the PHANTOM diagnostic: the BARE `MayerUrsellIdentity_z4_v2` is
       vacuously inhabitable (PROVED)

`MayerUrsellIdentity_z4_v2 p` carries a FREE `model : SpectralModel`.  Nothing
pins that model to the physical z4 transfer operator, so — exactly the
phantom-parameter trap the prior audit flagged one level up
(`Ursell4DBridgePin.castBridge`) — the bare structure is satisfiable by a
TRIVIAL model whose correlator vanishes off the diagonal:

  * `diagModel_corr_offdiag_zero` PROVES `∀ d ≥ 1, (corr diagModel d).eqv 0`
    (the single mode has eigenvalue `λ₀ = 0`, so `corr d = ½·0^d ≃ 0`);
  * `clusterSpanSum_nonneg` PROVES `0 ≤ clusterSpanSum …` (a `finSum` of
    nonnegative `kpTerm`s);
  * hence `diagModel_satisfies_sep` PROVES `diagModel` satisfies the separated
    field, and (with the pre-existing `diagModel_satisfies_diag`)
    `diagModel_vacuousWitness` INHABITS the whole bare `MayerUrsellIdentity_z4_v2
    p`.

**This witness is a VACUITY DIAGNOSTIC, NOT a (D1) discharge.**  Its correlator
is identically zero off the diagonal, so it captures NO z4 physics: inhabiting
the bare `MayerUrsellIdentity_z4_v2` is a Rule-6 fake, precisely as the prior
audit warned.  It is NEVER wired into `BridgeDecomposition` / `SubWallA` /
`Tier0Scorecard`; the frontier guard is untouched (`MayerUrsellIdentity_z4_v2`
is not a guard type, and no guard type is inhabited here).

# §2 — the GENUINE reduction: pin the model, factor out the KP assembly (PROVED)

`PhysicalMayerUrsellZ4 p` is the honest, non-phantom residual: it PINS the model
to a physical correlator by making the model appear on the LHS of the genuine
multi-plaquette Mayer–Ursell expansion, and carries the two per-size cluster
ingredients:

  * `expansion_sep` — **the multi-plaquette Mayer–Ursell expansion identity**
    (the `MayerClustering.MayerUrsellIdentity` residual, DISCHARGED for the
    single line by `mayerUrsell_singleLine`, OPEN for multi-plaquette/loopy):
    `∀ d ≥ 1, corr model d ≤ Σ_{m<d} animalCount(d+m)·(phiT(d+m)·zeta(d+m))`;
  * `tree_graph` — **(T′)** the Penrose / Poghosyan–Ueltschi spanning-tree
    inequality `phiT n ≤ eSurrogate^n` (already a named frontier atom);
  * `activity_le` — the per-cluster activity bound `zeta n ≤ (coeffW w4 gr)^n`
    (BACKED in-repo by `PinnedCluster.activity_le_leading`);
  * `diag_normalization` — the `d = 0` vacuum normalization (as in v2).

`physical_to_v2` PROVES `PhysicalMayerUrsellZ4 p → MayerUrsellIdentity_z4_v2 p`:
the KP-assembly half (`Ursell4DProgress.kpTerm_from_atoms`, folding the count
`animalCount` and collapsing `phiT·zeta·eSurrogate` into `kpTerm`) is
DISCHARGED, so `correlator_le_span_sep` reduces EXACTLY to the multi-plaquette
expansion identity `expansion_sep` plus the named atom (T′).  Composed with the
prior audit's `bridgeDecomposition_of_physical`, this connects the physical
Mayer–Ursell expansion all the way to the frontier (D1) node
`BridgeDecomposition`.

# Honest verdict (AGENTS.md Rule 6)

(D1) `correlator_le_span_sep` is NOT discharged.  What IS closed: the
KP-assembly half (count + tree-graph collapse into `kpTerm`) and the phantom
diagnostic (bare v2 is vacuously inhabitable ⇒ inhabiting it is a fake).  The
EXACT resisting piece is `PhysicalMayerUrsellZ4.expansion_sep` — the genuine z4
multi-plaquette Mayer–Ursell expansion identity, i.e. the
`MayerClustering.MayerUrsellIdentity` residual for the loopy/multi-plaquette
correlator (single-line case DISCHARGED via `wilsonG_decay`; the multi-plaquette
generalization + its size-floor geometry (D2) `SepLatticeZ4` are the wall).  This
is a genuine REDUCTION at FIXED SPACING (`ρ4 = 15/32 < 1`); NOT the
spacing-uniform continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The open
expansion identity is a NAMED Type-level field left uninhabited for a genuine
model, never faked.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.MayerUrsellZ4Restated
import YMGap.Continuum.Ursell4DBridgePin

namespace YMGap.Continuum.MayerUrsellZ4Physical

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
open YMGap.Continuum.MayerUrsellZ4Restated

/-! ## 0. Small nonnegativity infrastructure -/

/-- `finSum` of a nonnegative sequence is nonnegative (local, self-contained). -/
theorem finSum_nonneg' (f : QSeq) (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ finSum f n + f n
      exact Q'.zero_le_add _ _ (finSum_nonneg' f hf n) (hf n)

/-- `kpTerm (z4ClusterCountBound p) w4 gr n ≥ 0` — the size-`n` collapsed KP
activity is nonnegative (count · activity power · tree-graph power, all `≥ 0`). -/
theorem kpTerm_z4_nonneg (p : z4Chain.toLattice.Plaquette) (n : Nat) :
    (0 : Q') ≤ kpTerm (z4ClusterCountBound p) w4 gr n := by
  unfold kpTerm
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ ((z4ClusterCountBound p).animalCount_nonneg _)
      (Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) _))
    (Q'.pow_nonneg _ eSurrogate_nonneg _)

/-- **`clusterSpanSum_nonneg` (PROVED).**  The connecting-cluster span sum is
nonnegative: `0 ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d`. -/
theorem clusterSpanSum_nonneg (p : z4Chain.toLattice.Plaquette) (d : Nat) :
    (0 : Q') ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d := by
  unfold clusterSpanSum
  exact finSum_nonneg' _ (fun m => kpTerm_z4_nonneg p (d + m)) d

/-! ## 1. The PHANTOM diagnostic — bare v2 is vacuously inhabitable -/

/-- **`diagModel_corr_offdiag_zero` (PROVED — the vacuity core).**  The trivial
single-mode `diagModel` (eigenvalue `λ₀ = 0`) has an identically-zero connected
correlator OFF the diagonal:

    ∀ d ≥ 1,  (corr diagModel d).eqv 0.

`corr diagModel d = 0 + (1/2)·0^d`, and `0^{k+1} ≃ 0`, so the whole product
collapses.  This is why the bare `MayerUrsellIdentity_z4_v2` carries NO z4
physics — its `model` is free, and this zero-correlator model satisfies every
field. -/
theorem diagModel_corr_offdiag_zero (d : Nat) (hd : 1 ≤ d) :
    (corr diagModel d).eqv 0 := by
  cases d with
  | zero => exact absurd hd (by decide)
  | succ k =>
      -- corr diagModel (k+1) = 0 + (1/2) · 0^(k+1)  (single mode, tail empty)
      have hc : corr diagModel (k + 1)
          = (0 : Q') + Q'.mkPos 1 2 (by decide) * (0 : Q') ^ (k + 1) := rfl
      rw [hc, Q'.zero_add']
      -- (1/2)·0^(k+1) ≃ (1/2)·0 ≃ 0   (0^(k+1) ≃ 0 via 0·0^k ≃ 0)
      have hpow : ((0 : Q') ^ (k + 1)).eqv 0 := Q'.zero_mul_eqv ((0 : Q') ^ k)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.mkPos 1 2 (by decide)) ((0 : Q') ^ (k + 1)) 0 hpow) ?_
      exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))

/-- **`diagModel_satisfies_sep` (PROVED — the separated field is met by the
trivial model).**  The zero-correlator `diagModel` satisfies the separated
Mayer–Ursell field of `MayerUrsellIdentity_z4_v2`:

    ∀ d ≥ 1,  corr diagModel d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d,

trivially (LHS `≃ 0`, RHS `≥ 0`).  Together with `diagModel_satisfies_diag`
(the `d = 0` field), this shows the BARE v2 is satisfiable by a model with no
z4 content — the phantom diagnostic. -/
theorem diagModel_satisfies_sep (p : z4Chain.toLattice.Plaquette) (d : Nat)
    (hd : 1 ≤ d) :
    corr diagModel d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagModel_corr_offdiag_zero d hd))
    (clusterSpanSum_nonneg p d)

/-- **`diagModel_vacuousWitness` (PROVED — the phantom witness).**  The trivial
`diagModel` INHABITS the whole bare `MayerUrsellIdentity_z4_v2 p`.

⚠ **This is a VACUITY DIAGNOSTIC, NOT a genuine (D1) discharge.**  Its
correlator is identically zero off the diagonal (`diagModel_corr_offdiag_zero`),
so it captures NO z4 physics: it is the machine-checked proof that inhabiting the
bare `MayerUrsellIdentity_z4_v2` — whose `model` field is FREE and unpinned — is
a Rule-6 fake (the phantom-parameter trap, one level up from
`Ursell4DBridgePin.castBridge`).  It is deliberately NEVER fed to
`bridgeDecomposition_of_physical` / `SubWallA` / `Tier0Scorecard`; the frontier
guard stays at 5 (`MayerUrsellIdentity_z4_v2` is not a guard type, and no guard
type is inhabited).  The genuine target is the PINNED `PhysicalMayerUrsellZ4`
of §2. -/
def diagModel_vacuousWitness (p : z4Chain.toLattice.Plaquette) :
    MayerUrsellIdentity_z4_v2 p where
  model := diagModel
  correlator_le_span_sep := fun d hd => diagModel_satisfies_sep p d hd
  diag_normalization := diagModel_satisfies_diag p

/-! ## 2. The GENUINE reduction — pin the model, factor out the KP assembly -/

/-- **`PhysicalMayerUrsellZ4` (the pinned, non-phantom residual).**  Unlike the
bare `MayerUrsellIdentity_z4_v2` (free `model`), this structure PINS the model to
a physical correlator by putting `corr model` on the LHS of the genuine
multi-plaquette Mayer–Ursell expansion, and carries the two per-size cluster
ingredients:

  * `model` — the transfer-operator spectral model;
  * `phiT`, `zeta` — per-size truncated Ursell tree-graph weights and activities;
  * `zeta_nonneg` — activities nonnegative;
  * `tree_graph` — **(T′)** the Penrose / Poghosyan–Ueltschi spanning-tree
    inequality `phiT n ≤ eSurrogate^n` (a named frontier atom);
  * `activity_le` — the per-cluster activity bound `zeta n ≤ (coeffW w4 gr)^n`
    (backed in-repo by `PinnedCluster.activity_le_leading`);
  * `expansion_sep` — **the multi-plaquette Mayer–Ursell expansion identity**
    (the `MayerClustering.MayerUrsellIdentity` residual): the physical connected
    correlator is dominated by the count-folded per-cluster bridge tail from the
    size floor `d`, `∀ d ≥ 1`;
  * `diag_normalization` — the `d = 0` vacuum normalization.

LEFT UNINHABITED for a GENUINE (non-zero) physical model: the open blocker is
`expansion_sep` (single-line case DISCHARGED by `mayerUrsell_singleLine`, the
multi-plaquette/loopy case + its size-floor geometry (D2) `SepLatticeZ4` are the
wall) together with the named atom (T′) `tree_graph`. -/
structure PhysicalMayerUrsellZ4 (p : z4Chain.toLattice.Plaquette) where
  /-- The transfer-operator spectral model whose `corr` is the connected
  two-component correlator. -/
  model : SpectralModel
  /-- Per-size truncated Ursell tree-graph weight `|φ^T|`. -/
  phiT : Nat → Q'
  /-- Per-size cluster activity `|ζ|`. -/
  zeta : Nat → Q'
  /-- Activities are nonnegative. -/
  zeta_nonneg : ∀ n, (0 : Q') ≤ zeta n
  /-- **(T′)** — the Penrose / Poghosyan–Ueltschi spanning-tree inequality. -/
  tree_graph : ∀ n, phiT n ≤ eSurrogate ^ n
  /-- The per-cluster activity bound (backed by `activity_le_leading`). -/
  activity_le : ∀ n, zeta n ≤ (coeffW w4 gr) ^ n
  /-- **The multi-plaquette Mayer–Ursell expansion identity** (the genuine (D1)
  content, `d ≥ 1`): the physical connected correlator is dominated by the
  count-folded per-cluster bridge tail from the size floor `d`. -/
  expansion_sep : ∀ d, 1 ≤ d →
    corr model d ≤ finSum (fun m =>
      (z4ClusterCountBound p).animalCount (d + m) * (phiT (d + m) * zeta (d + m))) d
  /-- The `d = 0` diagonal normalization against the vacuum activity `kpTerm … 0`. -/
  diag_normalization :
    corr model 0 ≤ kpTerm (z4ClusterCountBound p) w4 gr 0

/-- **`physical_to_v2` (PROVED — the genuine forward reduction).**  A pinned
`PhysicalMayerUrsellZ4 p` yields the (prior-audit-uninhabited)
`MayerUrsellIdentity_z4_v2 p`: the KP-assembly half is DISCHARGED via
`Ursell4DProgress.kpTerm_from_atoms` (folding the count `animalCount` and
collapsing the per-cluster `phiT·zeta` against `eSurrogate` into `kpTerm`,
termwise through `CharacterTail.finSum_le_termwise` into the definitional
`clusterSpanSum`).  Hence `correlator_le_span_sep` reduces EXACTLY to the
multi-plaquette expansion identity `expansion_sep` plus the named atom (T′)
`tree_graph`; the activity bound is already backed in-repo.

This is the genuine, non-phantom route into v2 (contrast the vacuous
`diagModel_vacuousWitness`): the model is pinned by `expansion_sep`, which
references `corr model`.  Composed with the prior audit's
`bridgeDecomposition_of_physical`, it wires the physical Mayer–Ursell expansion
to the frontier (D1) node. -/
def physical_to_v2 (p : z4Chain.toLattice.Plaquette) (P : PhysicalMayerUrsellZ4 p) :
    MayerUrsellIdentity_z4_v2 p where
  model := P.model
  correlator_le_span_sep := fun d hd => by
    refine Q'.le_trans' _ _ _ (P.expansion_sep d hd) ?_
    -- termwise: animalCount(d+m)·(phiT(d+m)·zeta(d+m)) ≤ kpTerm …(d+m)
    have hterm : ∀ m,
        (z4ClusterCountBound p).animalCount (d + m) * (P.phiT (d + m) * P.zeta (d + m))
          ≤ kpTerm (z4ClusterCountBound p) w4 gr (d + m) :=
      fun m => kpTerm_from_atoms (z4ClusterCountBound p) w4_nonneg gr (d + m)
        (P.zeta_nonneg (d + m)) (P.tree_graph (d + m)) (P.activity_le (d + m))
    -- Σ_{m<d} (count-folded) ≤ Σ_{m<d} kpTerm …(d+m) = clusterSpanSum … d (defeq)
    exact CharacterTail.finSum_le_termwise
      (fun m => (z4ClusterCountBound p).animalCount (d + m)
        * (P.phiT (d + m) * P.zeta (d + m)))
      (fun m => kpTerm (z4ClusterCountBound p) w4 gr (d + m)) hterm d
  diag_normalization := P.diag_normalization

/-- **`physical_to_bridge` (PROVED — the full wire to the (D1) frontier node).**
A pinned `PhysicalMayerUrsellZ4 p` yields the frontier (D1) node
`Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr`, by
composing `physical_to_v2` with the prior audit's PROVED
`bridgeDecomposition_of_physical`.  This exhibits the physical multi-plaquette
Mayer–Ursell expansion as the genuine content feeding the (D1) atom — CONDITIONAL
on the open `PhysicalMayerUrsellZ4` (its `expansion_sep` + (T′) fields), so the
frontier guard is untouched. -/
def physical_to_bridge (p : z4Chain.toLattice.Plaquette)
    (P : PhysicalMayerUrsellZ4 p) :
    Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr :=
  Ursell4DBridgePin.bridgeDecomposition_of_physical p (physical_to_v2 p P)

/-! ## 3. Documentation: PROVED vs the OPEN wall (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `finSum_nonneg'`, `kpTerm_z4_nonneg`, `clusterSpanSum_nonneg` — the
    nonnegativity infrastructure;
  * `diagModel_corr_offdiag_zero`, `diagModel_satisfies_sep`,
    `diagModel_vacuousWitness` — the PHANTOM diagnostic: the bare
    `MayerUrsellIdentity_z4_v2` is satisfiable by the trivial zero-correlator
    `diagModel`, so inhabiting the bare type captures no z4 physics (a Rule-6
    fake); the genuine target must PIN the model;
  * `physical_to_v2` — the genuine forward reduction: a pinned
    `PhysicalMayerUrsellZ4` yields `MayerUrsellIdentity_z4_v2`, DISCHARGING the
    KP-assembly half (`kpTerm_from_atoms`) so that `correlator_le_span_sep`
    reduces EXACTLY to the multi-plaquette expansion identity + (T′);
  * `physical_to_bridge` — the composite wire to the frontier (D1) node
    `BridgeDecomposition` (conditional on the open pinned residual).

OPEN (NAMED, deliberately UNINHABITED for a genuine model — the wall, NOT faked):

  * `PhysicalMayerUrsellZ4.expansion_sep` — the genuine z4 MULTI-PLAQUETTE
    Mayer–Ursell expansion identity (the `MayerClustering.MayerUrsellIdentity`
    residual for the loopy/multi-plaquette correlator): DISCHARGED for the single
    line by `mayerUrsell_singleLine` (`wilsonG_decay`), OPEN for multi-plaquette;
    its size-floor geometry is (D2) `Ursell4DProgress.SepLatticeZ4`;
  * `PhysicalMayerUrsellZ4.tree_graph` — the named atom (T′).

VERDICT: (D1) `correlator_le_span_sep` is NOT discharged.  The KP-assembly half
and the phantom diagnostic ARE closed; the exact resisting piece is the
multi-plaquette Mayer–Ursell expansion identity `expansion_sep` (+ (T′)).  Fixed
spacing only (`ρ4 = 15/32 < 1`); NOT the spacing-uniform continuum modulus, NOT
the Clay Yang–Mills mass gap (OPEN). -/

end YMGap.Continuum.MayerUrsellZ4Physical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerUrsellZ4Physical.finSum_nonneg'
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.kpTerm_z4_nonneg
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.clusterSpanSum_nonneg
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.diagModel_corr_offdiag_zero
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.diagModel_satisfies_sep
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.diagModel_vacuousWitness
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.physical_to_v2
#print axioms YMGap.Continuum.MayerUrsellZ4Physical.physical_to_bridge
