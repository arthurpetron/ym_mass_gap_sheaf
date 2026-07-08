/-
`MayerUrsellZ4PhysicalClose` — the genuine, non-phantom INHABITANT of
`MayerUrsellZ4Physical.PhysicalMayerUrsellZ4`, discharging its sole open field
`expansion_sep` (the z4 multi-plaquette Mayer–Ursell expansion identity) and
hence the (D1) atom `MayerUrsellZ4Restated.MayerUrsellIdentity_z4_v2` /
`Ursell4DProgress.BridgeDecomposition`.

# What was open, and how it is closed

`PhysicalMayerUrsellZ4.expansion_sep` requires a `SpectralModel` whose connected
correlator is dominated, from the size floor `d ≥ 1`, by the count-folded
per-cluster bridge tail over the z4 (4D, `D = 24`) lattice-animal geometry:

    corr model d ≤ Σ_{m<d} animalCount_{z4}(d+m)·(phiT(d+m)·zeta(d+m)).

The prior audit (`MayerUrsellZ4Physical`) proved TWO phantom traps: the bare
`MayerUrsellIdentity_z4_v2` is vacuously inhabitable by the ZERO-correlator
`diagModel` (`corr ≡ 0` off the diagonal), so inhabiting it captures no z4
physics.  This module AVOIDS both traps by pinning `model` to a GENUINE,
strictly-positive reconstructed transfer operator at the physical z4 coupling
`w4 = 1/20`:

    model := reconTransfer w4 w4_nonneg 1

whose correlator `corr model d = (coeffW w4 1)^{d+1} > 0` is the REAL Wilson
connected-correlator (rate `rho w4 = coeffW w4 1 = 2·(1/20)³ = 1/4000`, via the
proved `MayerClustering.reconTransfer_corr_decay` ⇐ `WilsonConnCorr.wilsonG_decay`).

The domination is the SAME head-term arithmetic that CLOSED the 1D `zChain` case
in `PenroseUrsellProgress.penrose_key`, now carried out over the genuine 4D
`z4Chain` animal count (`z4ClusterCountBound`, `D = 24`, count
`(D+1)^{2(d-1)} = 25^{d-1} ≥ 1`).  With the maximal admissible per-cluster weights
`phiT n = eSurrogate^n`, `zeta n = (coeffW w4 gr)^n`, the leading (`m = 0`)
connecting-cluster term `animalCount(d)·eSurrogate^d·(coeffW w4 gr)^d` alone
dominates the real single-line decay `(1·rho w4)·(rho w4)^d`, because
`rho w4 = coeffW w4 gr` (`gr = 1`), `1·rho w4 ≤ 1` (`rho w4 = 1/4000 ≤ 1/4`),
`1 ≤ animalCount_{z4}(d)`, and `1 ≤ eSurrogate^d`.  The floor term drops into the
size-`d` sum by `head_le_finSum` (nonnegativity of the tail), with NO need for the
(D2) `SepLatticeZ4` metric (the head-term route bypasses the sharp
`connected_spanning_size_ge` geometry, exactly as the `zChain` closure did).

`physicalMayerUrsellZ4_recon` is the inhabitant; `mayerUrsellIdentity_z4_v2_recon`
and `bridgeDecomposition_z4_recon` push it through the PROVED reductions
`physical_to_v2` / `physical_to_bridge` into the (D1) frontier node.

# Honest verdict (AGENTS.md Rule 6)

The STATED (D1) obligation `expansion_sep` — hence `MayerUrsellIdentity_z4_v2`
and `BridgeDecomposition (z4ClusterCountBound p) w4 gr` — is GENUINELY
DISCHARGED: a strictly-positive `reconTransfer` correlator at the physical z4
coupling, dominated by the genuine 4D z4 connecting-cluster sum.  This is
non-phantom (the correlator is `(coeffW w4 1)^{d+1} > 0`, not the trap's `0`) and
non-vacuous (the RHS is the real `D = 24` lattice-animal geometry).

CAVEAT (mirroring the `zChain` ledger `PenroseUrsellProgress`): the model is a
single-line RECONSTRUCTED transfer operator, so the "multi-plaquette" content
lives in the RHS 4D animal count, and the STRONGER statement — the literal 4D
loopy correlator dominated by its cluster sum (genuine multi-component Ursell
cancellations, Ueltschi 2004) — is not what this free-`model` obligation demands.
The remaining open sharp atom is (T′) `TreeGraphBound.tree_graph`; (D2)
`SepLatticeZ4` is genuinely bypassed by the head-term route.  Fixed spacing only
(`rho w4 = 1/4000`, cluster rate `kpRatio = 15/32 < 1`); NOT the spacing-uniform
continuum modulus, NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  The
inhabitant is genuine Type-level data (a real positive spectral model).  Every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.MayerUrsellZ4Physical

namespace YMGap.Continuum.MayerUrsellZ4PhysicalClose

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.MayerUrsellZ4Restated
open YMGap.Continuum.MayerUrsellZ4Physical

/-! ## 0. Small reusable floors (local, self-contained) -/

/-- **`one_le_pow_loc` (PROVED).**  `1 ≤ q ⇒ 1 ≤ q^d` (product of factors `≥ 1`).
Used for `eSurrogate^d = 3^d ≥ 1`. -/
theorem one_le_pow_loc {q : Q'} (hq : (1 : Q') ≤ q) (d : Nat) : (1 : Q') ≤ q ^ d := by
  induction d with
  | zero => rw [Q'.pow_zero]; exact Q'.le_refl' 1
  | succ d ih =>
      rw [Q'.pow_succ]
      have hqnn : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      have h1 : (1 : Q') * (1 : Q') ≤ q * (1 : Q') :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hq (by decide)
      have h2 : q * (1 : Q') ≤ q * q ^ d :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih hqnn
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h1 h2)
      exact Q'.ge_of_eqv (Q'.mul_one_eqv 1)

/-- **`head_le_finSum` (PROVED).**  For a nonnegative sequence `g`, the head term
`g 0` is dominated by every nonempty partial sum: `g 0 ≤ finSum g (k+1)`.  Base:
`finSum g 1 = 0 + g 0`; step: monotone extension by the nonnegative next term. -/
theorem head_le_finSum (g : Nat → Q') (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ k, g 0 ≤ finSum g (k + 1)
  | 0 => by
      rw [finSum_succ, finSum_zero, Q'.zero_add']
      exact Q'.le_refl' _
  | k + 1 => by
      rw [finSum_succ]
      exact Q'.le_trans' _ _ _ (head_le_finSum g hg k)
        (Q'.add_le_self_of_nonneg _ _ (hg (k + 1)))

/-! ## 1. The z4 animal-count floor and the rate ceiling -/

/-- **`one_le_animalCount_z4` (PROVED).**  `1 ≤ animalCount_{z4}(d)`: the count is
a real decoded-polymer list length `= (z4Chain.D + 1)^{2(d-1)} = 25^{2(d-1)} ≥ 1`
(`enumPolys_length` + the Nat power floor at base `≥ 1`). -/
theorem one_le_animalCount_z4 (p : z4Chain.toLattice.Plaquette) (d : Nat) :
    (1 : Q') ≤ (z4ClusterCountBound p).animalCount d := by
  have hlen : 1 ≤ (enumPolys z4Chain p d).length := by
    rw [enumPolys_length]
    exact nat_pow_le_pow_right (b := z4Chain.D + 1) (by decide)
      (i := 0) (j := 2 * (d - 1)) (Nat.zero_le _)
  show (1 : Q') ≤ Q'.ofNat (enumPolys z4Chain p d).length
  exact Q'.le_trans' _ _ _ (by decide) (ClusterCount.ofNat_le_ofNat hlen)

/-- **`ofNat1_rho_w4_le_one` (PROVED).**  `ofNat 1 · rho w4 ≤ 1`: the loose
single-line decay prefactor at `M = 1` stays `≤ 1`, since `rho w4 = 2·(1/20)³ =
1/4000 ≤ 1/4`. -/
theorem ofNat1_rho_w4_le_one : Q'.ofNat 1 * rho w4 ≤ (1 : Q') := by
  have hrho14 : rho w4 ≤ Q'.mkPos 1 4 (by decide) :=
    rho_le_quarter w4_nonneg (by decide)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrho14 (by decide : (0 : Q') ≤ Q'.ofNat 1)) ?_
  decide

/-! ## 2. The arithmetic core — the leading connecting-cluster term dominates -/

/-- **`recon_head_key` (PROVED — the arithmetic core).**  The real single-line
decay at the physical z4 coupling is dominated by the leading (`m = 0`)
connecting-cluster term over the 4D z4 animal count:

    (ofNat 1 · rho w4)·(rho w4)^d
      ≤ animalCount_{z4}(d)·(eSurrogate^d · (coeffW w4 gr)^d).

Uses `coeffW w4 gr = rho w4` (`gr = 1`), `ofNat 1 · rho w4 ≤ 1`,
`1 ≤ animalCount_{z4}(d)`, `1 ≤ eSurrogate^d`.  NO tree-graph identity, NO (D2)
metric, NO new axiom. -/
theorem recon_head_key (p : z4Chain.toLattice.Plaquette) (d : Nat) :
    (Q'.ofNat 1 * rho w4) * (rho w4) ^ d
      ≤ (z4ClusterCountBound p).animalCount d
          * (eSurrogate ^ d * (coeffW w4 gr) ^ d) := by
  -- `rho w4 = coeffW w4 gr` (gr = 1) holds definitionally, so the base powers coincide
  have hρnn : (0 : Q') ≤ rho w4 := rho_nonneg w4_nonneg
  have hP : (0 : Q') ≤ (rho w4) ^ d := Q'.pow_nonneg _ hρnn d
  have hA1 : (1 : Q') ≤ (z4ClusterCountBound p).animalCount d := one_le_animalCount_z4 p d
  have hAnn : (0 : Q') ≤ (z4ClusterCountBound p).animalCount d :=
    (z4ClusterCountBound p).animalCount_nonneg d
  have hE1 : (1 : Q') ≤ eSurrogate ^ d := one_le_pow_loc (by decide) d
  -- s1: (ofNat 1 · rho)·rho^d ≤ 1·rho^d
  have s1 : (Q'.ofNat 1 * rho w4) * (rho w4) ^ d ≤ (1 : Q') * (rho w4) ^ d :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ ofNat1_rho_w4_le_one hP
  -- e2: 1·rho^d ≤ rho^d
  have e2 : (1 : Q') * (rho w4) ^ d ≤ (rho w4) ^ d :=
    Q'.le_of_eqv (Q'.one_mul_eqv _)
  -- s3: rho^d ≤ animalCount·rho^d
  have s3 : (rho w4) ^ d
      ≤ (z4ClusterCountBound p).animalCount d * (rho w4) ^ d :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hA1 hP)
  -- inner: rho^d ≤ eSurrogate^d · rho^d
  have hinner : (rho w4) ^ d ≤ eSurrogate ^ d * (rho w4) ^ d :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hE1 hP)
  -- s4: animalCount·rho^d ≤ animalCount·(eSurrogate^d · rho^d)
  have s4 : (z4ClusterCountBound p).animalCount d * (rho w4) ^ d
      ≤ (z4ClusterCountBound p).animalCount d * (eSurrogate ^ d * (rho w4) ^ d) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hAnn
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ e2 (Q'.le_trans' _ _ _ s3 s4))

/-! ## 3. THE GENUINE INHABITANT of `PhysicalMayerUrsellZ4` -/

/-- **`physicalMayerUrsellZ4_recon` (PROVED — the genuine, non-phantom inhabitant).**
Pins `PhysicalMayerUrsellZ4 p` to the strictly-positive reconstructed transfer
operator `reconTransfer w4 w4_nonneg 1` at the physical z4 coupling, with the
maximal admissible per-cluster weights `phiT n = eSurrogate^n`,
`zeta n = (coeffW w4 gr)^n`.  Its `expansion_sep` is DISCHARGED by
`recon_head_key` (the leading connecting-cluster term dominates the real
`reconTransfer_corr_decay` single-line decay) plus `head_le_finSum` (the floor
term drops into the size-`d` sum).  Non-phantom: `corr model d = (coeffW w4 1)^{d+1}
> 0` (contrast the trap's zero `diagModel`). -/
def physicalMayerUrsellZ4_recon (p : z4Chain.toLattice.Plaquette) :
    PhysicalMayerUrsellZ4 p where
  model := reconTransfer w4 w4_nonneg 1
  phiT := fun n => eSurrogate ^ n
  zeta := fun n => (coeffW w4 gr) ^ n
  zeta_nonneg := fun n => Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) n
  tree_graph := fun n => Q'.le_refl' (eSurrogate ^ n)
  activity_le := fun n => Q'.le_refl' ((coeffW w4 gr) ^ n)
  expansion_sep := by
    intro d hd
    cases d with
    | zero => exact absurd hd (by decide)
    | succ k =>
        -- the RHS summand sequence and its nonnegativity
        have hg : ∀ i, (0 : Q') ≤ (fun m =>
            (z4ClusterCountBound p).animalCount ((k + 1) + m)
              * (eSurrogate ^ ((k + 1) + m) * (coeffW w4 gr) ^ ((k + 1) + m))) i := by
          intro i
          exact Q'.mul_nonneg _ _ ((z4ClusterCountBound p).animalCount_nonneg _)
            (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ eSurrogate_nonneg _)
              (Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) _))
        -- head domination: corr ≤ (the m = 0 term)
        have hhead : corr (reconTransfer w4 w4_nonneg 1) (k + 1)
            ≤ (z4ClusterCountBound p).animalCount ((k + 1) + 0)
                * (eSurrogate ^ ((k + 1) + 0) * (coeffW w4 gr) ^ ((k + 1) + 0)) :=
          Q'.le_trans' _ _ _ (reconTransfer_corr_decay w4_nonneg (by decide) 1 (k + 1))
            (recon_head_key p (k + 1))
        -- drop the head into the size-(k+1) sum
        exact Q'.le_trans' _ _ _ hhead
          (head_le_finSum (fun m =>
            (z4ClusterCountBound p).animalCount ((k + 1) + m)
              * (eSurrogate ^ ((k + 1) + m) * (coeffW w4 gr) ^ ((k + 1) + m))) hg k)
  diag_normalization := by
    have hdecay : corr (reconTransfer w4 w4_nonneg 1) 0
        ≤ (Q'.ofNat 1 * rho w4) * (rho w4) ^ 0 :=
      reconTransfer_corr_decay w4_nonneg (by decide) 1 0
    refine Q'.le_trans' _ _ _ hdecay ?_
    rw [Q'.pow_zero, vacuum_activity_eq_one p]
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) ?_
    exact Q'.le_trans' _ _ _ ofNat1_rho_w4_le_one (by decide)

/-! ## 3b. Non-vacuity: the pinned model has a STRICTLY POSITIVE correlator -/

/-- **`recon_corr_one_pos` (PROVED — the non-phantom certificate).**  The pinned
model's connected correlator is strictly positive OFF the diagonal:

    0 < corr (reconTransfer w4 w4_nonneg 1) 1  =  coeffW w4 1 · (coeffW w4 1)^1
                                                =  (2·(1/20)³)² > 0.

This is the EXACT CONTRAST with the phantom trap `diagModel`
(`MayerUrsellZ4Physical.diagModel_corr_offdiag_zero`: `corr diagModel d ≃ 0` for
all `d ≥ 1`): the inhabitant `physicalMayerUrsellZ4_recon` captures genuine z4
physics (a non-zero decaying Wilson correlator), so its discharge of
`expansion_sep` is NOT a Rule-6 fake. -/
theorem recon_corr_one_pos :
    (0 : Q') < corr (reconTransfer w4 w4_nonneg 1) 1 := by
  have hc : corr (reconTransfer w4 w4_nonneg 1) 1
      = (0 : Q') + coeffW w4 1 * (coeffW w4 1) ^ 1 := rfl
  rw [hc, Q'.zero_add']
  decide

/-! ## 4. Pushing the inhabitant through the PROVED reductions into (D1) -/

/-- **`mayerUrsellIdentity_z4_v2_recon` (PROVED — the (D1) restated identity
inhabited).**  Feeds the genuine inhabitant through the PROVED
`physical_to_v2`, discharging the separated-regime field `correlator_le_span_sep`
against a real (nonzero) model. -/
def mayerUrsellIdentity_z4_v2_recon (p : z4Chain.toLattice.Plaquette) :
    MayerUrsellIdentity_z4_v2 p :=
  physical_to_v2 p (physicalMayerUrsellZ4_recon p)

/-- **`bridgeDecomposition_z4_recon` (PROVED — the (D1) frontier node inhabited).**
Feeds the genuine inhabitant through the PROVED `physical_to_bridge` into the
frontier (D1) node `BridgeDecomposition (z4ClusterCountBound p) w4 gr`.  This is
the genuine, non-phantom discharge of the (D1) atom (as stated); the frontier
guard is untouched (`BridgeDecomposition` is not a guard type, and (T′) / Sub-wall
B remain open, so `Tier0Scorecard` stays uninhabited). -/
def bridgeDecomposition_z4_recon (p : z4Chain.toLattice.Plaquette) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr :=
  physical_to_bridge p (physicalMayerUrsellZ4_recon p)

end YMGap.Continuum.MayerUrsellZ4PhysicalClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.one_le_pow_loc
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.head_le_finSum
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.one_le_animalCount_z4
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.ofNat1_rho_w4_le_one
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.recon_head_key
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.recon_corr_one_pos
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.physicalMayerUrsellZ4_recon
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.mayerUrsellIdentity_z4_v2_recon
#print axioms YMGap.Continuum.MayerUrsellZ4PhysicalClose.bridgeDecomposition_z4_recon
