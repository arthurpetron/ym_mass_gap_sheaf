/-
`MayerUrsellZ4Restated` — the NON-DEGENERATE restatement of the z4 Mayer–Ursell
identity.  The v1 identity `MayerBridgeDecomposition.MayerUrsellIdentity_z4` is
provably UNSATISFIABLE for every nontrivial model: its single domination field
`correlator_le_span` hard-codes the length-`d` connecting-cluster majorant
`clusterSpanSum`, which VANISHES at `d = 0` (empty sum), forcing the connected
correlator's total spectral weight `Σᵢ wᵢ ≤ 0` — the trivial zero model
(`MayerUrsellZ4.mu_z4_total_weight_le_zero`).

This module restates the identity so that the `d = 0` diagonal is normalized
against the POSITIVE vacuum activity `kpTerm … 0 = animalCount 0 = 1` rather than
against the vanishing span, and the domination content is carried only in the
SEPARATED regime `d ≥ 1`.  The free-`tailLen := d + 1` escape (scaffolded in
`MayerUrsellZ4`) collapses the `d = 0` right-hand side to exactly that vacuum
activity, so the restated residual reduces to the SAME two named atoms as v1
((T′) `TreeGraphBound.tree_graph` and (D2) `SepLatticeZ4`) with NO new wall — but
is now genuinely NON-degenerate (a positive-weight model satisfies the diagonal).

# What is built

## §1 — the non-degenerate restated residual `MayerUrsellIdentity_z4_v2`

Splits the single degenerate `correlator_le_span` into

  * `correlator_le_span_sep : ∀ d, 1 ≤ d → corr model d ≤ clusterSpanSum … d`
    (the separated regime — the honest (D1)/(D2) cluster-expansion content), and
  * `diag_normalization : corr model 0 ≤ kpTerm … 0`
    (the `d = 0` diagonal normalized against the vacuum activity, NOT the
    vanishing span).

`diag_normalization` unfolds (via `corr_zero`) to `Σᵢ wᵢ ≤ kpTerm … 0`, and
`kpTerm … 0 = animalCount 0 = 1 > 0`, so it does NOT force the zero model.

## §2 — the free-`tailLen` reduction to `BridgeDecomposition` (PROVED)

`decompose_v2` proves the free-`tailLen := d + 1` domination:

    corr model d ≤ finSum (fun m => kpTerm … (d + m)) (d + 1),

by cases: at `d = 0` the RHS collapses to `kpTerm … 0` (`finSum_succ` /
`finSum_zero` / `zero_add`), which is exactly `diag_normalization`; at `d = k+1`
the RHS is `clusterSpanSum … (k+1)` extended by one nonnegative bridge term, so
`correlator_le_span_sep (k+1)` plus `add_le_self_of_nonneg` closes it.
`bridgeDecomposition_of_data_v2` / `penroseSplit_of_data_v2` /
`correlator_decay_of_data_v2` port the v1 wiring verbatim (the (T) tree-graph
field is reflexivity since `bridgeTerm = kpTerm`), yielding the concrete 4D decay
`corr model d ≤ 2·(15/32)^d` at the PROVED `z4_genuine_threshold` — with NO
zero-model collapse.

## §3 — non-degeneracy certificate (PROVED)

`diagModel` is a genuine single-mode `SpectralModel` with weight `w₀ = 1/2 > 0`.
`vacuum_activity_eq_one` PROVES `kpTerm … 0 = 1` (from `animalCount 0 = 1`, i.e.
`enumPolys_length` at `n = 0`: `(D+1)^(2·(0−1)) = (D+1)^0 = 1`).
`diagModel_satisfies_diag` PROVES `corr diagModel 0 ≤ kpTerm … 0`, and
`diagModel_weight_pos` PROVES `¬ (Σᵢ (diagModel).wᵢ ≤ 0)` — the exact CONTRAST
with `mu_z4_total_weight_le_zero`, which forces `≤ 0` for v1.  So the restated
diagonal is satisfiable by a positive-weight model: the degeneracy is removed
WITHOUT adding a wall.

# Honest verdict (AGENTS.md Rule 6)

Genuine REDUCTION + de-degeneration, NOT a close.  Net new closed physics: zero.
The separated-regime field `correlator_le_span_sep` is the SAME honest open
cluster-expansion content as v1's `correlator_le_span` (the named atoms (T′) and
(D2) are unchanged); `MayerUrsellIdentity_z4_v2` is therefore LEFT UNINHABITED as
a whole (the (D1)/(D2) wall persists).  What IS closed here: the `d = 0`
self-contradiction is gone (`diagModel_satisfies_diag` + `diagModel_weight_pos`),
and every wiring lemma is PROVED and axiom-clean.  Fixed spacing only
(`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`); NOT the spacing-uniform
continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The open
separated-regime content is a NAMED Type-level field left uninhabited, never
faked.  Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.MayerUrsellZ4

namespace YMGap.Continuum.MayerUrsellZ4Restated

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

/-! ## 1. The non-degenerate restated residual -/

/-- **`MayerUrsellIdentity_z4_v2` (NAMED — the non-degenerate (D) residual).**  The
restatement of `MayerBridgeDecomposition.MayerUrsellIdentity_z4` that separates the
`d = 0` diagonal (normalized against the POSITIVE vacuum activity `kpTerm … 0`)
from the `d ≥ 1` separated regime (the honest cluster-expansion content):

  * `model : SpectralModel` — the transfer-operator model whose abstract `corr` is
    the true two-component connected correlator;
  * `correlator_le_span_sep : ∀ d, 1 ≤ d → corr model d ≤ clusterSpanSum … d` — the
    SEPARATED-regime Mayer–Ursell content (`d ≥ 1`); the SAME open (D1)/(D2)
    cluster-expansion atoms as v1, restricted off the diagonal;
  * `diag_normalization : corr model 0 ≤ kpTerm … 0` — the `d = 0` diagonal,
    normalized against the vacuum activity `kpTerm … 0 = animalCount 0 = 1 > 0`
    (NOT the vanishing span `clusterSpanSum … 0 = 0`).

Unlike v1 (whose `correlator_le_span 0` forced `Σᵢ wᵢ ≤ 0`, the zero model), the
`diag_normalization` bound is satisfiable by a positive-weight model
(`diagModel_satisfies_diag` + `diagModel_weight_pos`).  LEFT UNINHABITED as a whole
(the separated-regime (D1)/(D2) wall persists), NOT faked. -/
structure MayerUrsellIdentity_z4_v2 (p : z4Chain.toLattice.Plaquette) where
  /-- The transfer-operator spectral model whose `corr` is the connected
  two-component correlator. -/
  model : SpectralModel
  /-- **The separated-regime Mayer–Ursell content** (`d ≥ 1`): the connected
  correlator is dominated by the connecting-cluster sum from the size floor `d`.
  The SAME open (D1)/(D2) atoms as v1, off the diagonal. -/
  correlator_le_span_sep : ∀ d, 1 ≤ d →
    corr model d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d
  /-- **The `d = 0` diagonal normalization** against the positive vacuum activity
  `kpTerm … 0` (NOT the vanishing span) — removes the v1 zero-model collapse. -/
  diag_normalization :
    corr model 0 ≤ kpTerm (z4ClusterCountBound p) w4 gr 0

/-! ## 2. The free-`tailLen := d + 1` reduction to `BridgeDecomposition` (PROVED) -/

/-- **`decompose_v2` (PROVED — the free-`tailLen` domination).**  From the restated
residual, the free-`tailLen := d + 1` bridge domination holds at EVERY `d`:

    corr model d  ≤  finSum (fun m => kpTerm … (d + m)) (d + 1).

At `d = 0` the RHS collapses (`finSum_succ` / `finSum_zero` / `zero_add`) to
`kpTerm … 0` — exactly `diag_normalization`.  At `d = k + 1` the RHS is
`clusterSpanSum … (k+1)` (definitionally `finSum (fun m => kpTerm … ((k+1)+m))
(k+1)`) extended by the single nonnegative bridge term `kpTerm … ((k+1)+(k+1))`,
so `correlator_le_span_sep (k+1)` plus `add_le_self_of_nonneg` closes it. -/
theorem decompose_v2 (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) (d : Nat) :
    corr MU.model d
      ≤ finSum (fun m => kpTerm (z4ClusterCountBound p) w4 gr (d + m)) (d + 1) := by
  cases d with
  | zero =>
      rw [finSum_succ, finSum_zero, Q'.zero_add']
      exact MU.diag_normalization
  | succ k =>
      rw [finSum_succ]
      have hsep := MU.correlator_le_span_sep (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      have hcs : clusterSpanSum (z4ClusterCountBound p) w4 gr (k + 1)
          = finSum (fun m => kpTerm (z4ClusterCountBound p) w4 gr ((k + 1) + m)) (k + 1) :=
        rfl
      rw [hcs] at hsep
      have hnn : (0 : Q') ≤ kpTerm (z4ClusterCountBound p) w4 gr ((k + 1) + (k + 1)) := by
        unfold kpTerm
        exact Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ ((z4ClusterCountBound p).animalCount_nonneg _)
            (Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) _))
          (Q'.pow_nonneg _ eSurrogate_nonneg _)
      exact Q'.le_trans' _ _ _ hsep (Q'.add_le_self_of_nonneg _ _ hnn)

/-- **`bridgeDecomposition_of_data_v2` (PROVED — the genuine (D) witness).**  From
the restated residual `MU`, the (D) half of the Penrose–Ursell split is inhabited
with a GENUINE off-diagonal correlator `offCorr := corr MU.model`, bridge term
`kpTerm`, the FREE truncation length `tailLen := d + 1`, and `decompose :=
decompose_v2` — escaping the v1 `d = 0` zero-forcing. -/
def bridgeDecomposition_of_data_v2 (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr where
  offCorr    := fun d => corr MU.model d
  bridgeTerm := fun n => kpTerm (z4ClusterCountBound p) w4 gr n
  tailLen    := fun d => d + 1
  tailLen_ge := fun d => Nat.le_succ d
  decompose  := fun d => decompose_v2 p MU d

/-- **`penroseSplit_of_data_v2` (PROVED — the full factored split).**  The restated
residual `MU` yields a complete `PenroseUrsellSplit`: the (D) field is
`decompose_v2`, and the (T) field `treeGraph` is reflexivity (`bridgeTerm n =
kpTerm … n`). -/
def penroseSplit_of_data_v2 (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) :
    PenroseUrsellSplit (z4ClusterCountBound p) w4 gr where
  offCorr    := fun d => corr MU.model d
  tailLen    := fun d => d + 1
  tailLen_ge := fun d => Nat.le_succ d
  bridgeTerm := fun n => kpTerm (z4ClusterCountBound p) w4 gr n
  treeGraph  := fun n => Q'.le_refl' (kpTerm (z4ClusterCountBound p) w4 gr n)
  decompose  := fun d => decompose_v2 p MU d

/-- **`correlator_decay_of_data_v2` (PROVED — the concrete 4D decay).**  From the
restated residual `MU`, the genuine two-component connected correlator decays at
the physical 4D rate `ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`:

    corr MU.model d  ≤  2 · (kpRatio (z4ClusterCountBound p) w4 gr)^d.

Chains `penroseSplit_of_data_v2` through the generic PROVED
`PenroseUrsellSplit.offCorr_decay` at the PROVED threshold `z4_genuine_threshold`. -/
theorem correlator_decay_of_data_v2 (p : z4Chain.toLattice.Plaquette)
    (MU : MayerUrsellIdentity_z4_v2 p) (d : Nat) :
    corr MU.model d
      ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  PenroseUrsellSplit.offCorr_decay (z4ClusterCountBound p) w4_nonneg gr
    (z4_genuine_threshold p) (penroseSplit_of_data_v2 p MU) d

/-! ## 3. Non-degeneracy certificate — a positive-weight model satisfies the
diagonal (PROVED)

Where v1's `correlator_le_span 0` forced `Σᵢ wᵢ ≤ 0` (the zero model,
`MayerUrsellZ4.mu_z4_total_weight_le_zero`), the restated `diag_normalization`
bounds `Σᵢ wᵢ` by the POSITIVE vacuum activity `kpTerm … 0 = 1`, so a
positive-weight model satisfies it. -/

/-- **`vacuum_activity_eq_one` (PROVED — the positive normalization RHS).**  The
`d = 0` vacuum activity is `1`:

    kpTerm (z4ClusterCountBound p) w4 gr 0  =  1,

because `animalCount 0 = |enumPolys … 0| = (D+1)^(2·(0−1)) = (D+1)^0 = 1` and the
two `·^0` factors are `1`.  This is the load-bearing NON-degeneracy fact: the RHS
of `diag_normalization` is strictly positive, so the diagonal does not force the
zero model. -/
theorem vacuum_activity_eq_one (p : z4Chain.toLattice.Plaquette) :
    kpTerm (z4ClusterCountBound p) w4 gr 0 = Q'.ofNat 1 := by
  have hac : (z4ClusterCountBound p).animalCount 0 = Q'.ofNat 1 := by
    show BddLatticeAnimal.animalCount z4Chain p 0 = Q'.ofNat 1
    unfold BddLatticeAnimal.animalCount
    rw [BddLatticeAnimal.enumPolys_length]
    rfl
  unfold kpTerm
  rw [Q'.pow_zero, Q'.pow_zero, hac]
  decide

/-- **`diagModel` (a genuine single-mode positive-weight `SpectralModel`).**  One
mode, spectral weight `w₀ = 1/2 > 0`, eigenvalue `λ₀ = 0`.  This certifies that
the restated diagonal is satisfiable by a NON-trivial model (contrast the v1 zero
model). -/
def diagModel : SpectralModel where
  k := 1
  w := fun _ => Q'.mkPos 1 2 (by decide)
  lam := fun _ => 0
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => Q'.le_refl' 0

/-- **`diagModel_satisfies_diag` (PROVED — the diagonal is satisfiable).**  The
positive-weight `diagModel` satisfies the restated `diag_normalization` bound:

    corr diagModel 0  =  1/2  ≤  1  =  kpTerm (z4ClusterCountBound p) w4 gr 0.

Impossible for the v1 identity, which would demand `1/2 ≤ 0`. -/
theorem diagModel_satisfies_diag (p : z4Chain.toLattice.Plaquette) :
    corr diagModel 0 ≤ kpTerm (z4ClusterCountBound p) w4 gr 0 := by
  have hk0 : (Q'.mkPos 1 2 (by decide) : Q')
      ≤ kpTerm (z4ClusterCountBound p) w4 gr 0 := by
    rw [vacuum_activity_eq_one p]; decide
  have hc : corr diagModel 0
      = (0 : Q') + Q'.mkPos 1 2 (by decide) * (0 : Q') ^ 0 := rfl
  rw [hc, Q'.zero_add']
  exact Q'.le_trans' _ _ _ (by decide) hk0

/-- **`diagModel_weight_pos` (PROVED — the CONTRAST with the v1 obstruction).**  The
total spectral weight of `diagModel` is NOT `≤ 0`:

    ¬ (Σᵢ (diagModel).wᵢ  ≤  0),   since Σᵢ wᵢ = 1/2.

This is the exact contrast with `MayerUrsellZ4.mu_z4_total_weight_le_zero`, which
PROVES every v1 inhabitant forces `Σᵢ wᵢ ≤ 0`.  Together with
`diagModel_satisfies_diag`, it certifies that the restated diagonal removes the
forced-zero degeneracy. -/
theorem diagModel_weight_pos :
    ¬ (finSum diagModel.w diagModel.k ≤ (0 : Q')) := by
  have hfs : finSum diagModel.w diagModel.k
      = (0 : Q') + Q'.mkPos 1 2 (by decide) := rfl
  rw [hfs, Q'.zero_add']
  decide

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `decompose_v2` — the free-`tailLen := d + 1` bridge domination at every `d`
    (diagonal collapses to the vacuum activity; separated regime extends the span
    by one nonneg term);
  * `bridgeDecomposition_of_data_v2`, `penroseSplit_of_data_v2`,
    `correlator_decay_of_data_v2` — the (D) witness, the full factored split, and
    the concrete 4D geometric decay `≤ 2·(15/32)^d` at the PROVED
    `z4_genuine_threshold`, all from the restated residual (NO zero-model collapse);
  * `vacuum_activity_eq_one` — `kpTerm … 0 = 1 > 0` (the positive normalization
    RHS: `animalCount 0 = 1` via `enumPolys_length`);
  * `diagModel`, `diagModel_satisfies_diag`, `diagModel_weight_pos` — a genuine
    positive-weight model satisfying the restated diagonal, with total weight
    `Σᵢ wᵢ = 1/2 ≠ 0` — the exact contrast with the v1 zero-forcing
    `mu_z4_total_weight_le_zero`.

NAMED-open / deliberately-UNINHABITED (NOT faked):

  * `MayerUrsellIdentity_z4_v2` — its `correlator_le_span_sep` field carries the
    SAME open (D1)/(D2) cluster-expansion content as v1's `correlator_le_span`
    (off the diagonal); LEFT UNINHABITED as a whole (the separated-regime wall
    persists);
  * the underlying atoms are unchanged — (T′)
    `Ursell4DProgress.TreeGraphBound.tree_graph` and (D2)
    `Ursell4DProgress.SepLatticeZ4` — no NEW wall is introduced by the restatement.

This module removes the v1 `d = 0` self-contradiction WITHOUT adding a wall.  It
is a genuine REDUCTION at FIXED SPACING
(`ρ4 = kpRatio (z4ClusterCountBound p) w4 gr = 15/32 < 1`).  It is NOT the
spacing-uniform continuum modulus and NOT the Clay Yang–Mills mass gap (OPEN). -/

end YMGap.Continuum.MayerUrsellZ4Restated

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerUrsellZ4Restated.decompose_v2
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.bridgeDecomposition_of_data_v2
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.penroseSplit_of_data_v2
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.correlator_decay_of_data_v2
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.vacuum_activity_eq_one
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.diagModel_satisfies_diag
#print axioms YMGap.Continuum.MayerUrsellZ4Restated.diagModel_weight_pos
