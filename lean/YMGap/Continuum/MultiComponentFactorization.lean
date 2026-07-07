/-
Multi-component Mayer/Ursell — the DISCONNECTED joint correlator FACTORIZES, so
the connected (Ursell) cross-correlator between distinct components is IDENTICALLY
ZERO.  This discharges bullet (ii) of `MultiPlaquetteMayer.LoopyCorrelatorResidual`
("off-diagonal cross terms between distinct connected components factorize by Haar
orthogonality and are subtracted by construction") as a genuine CORRELATOR theorem,
completing the geometry census beyond the single connected component
(line → tree → cycle → multi-loop, all already proved to collapse to one common
excited rep and decay geometrically).

# Why this module exists (the last un-collapsed geometry bullet)

`WilsonConnCorr` (line), `MultiPlaquetteMayer` (branching tree), `CycleMayer`
(single cycle), and `LoopyCorrelatorProgress` (arbitrary multi-loop) all prove the
connected correlator of ONE connected component collapses (via the shared-link
orthogonality kernel `vacSubKernel a b = δ_{a,b}·(1 − δ_{a,0})`) to a single common
excited rep and decays as `ρ^{node count}`.  The remaining named-open bullet of
`LoopyCorrelatorResidual` is the MULTI-COMPONENT / off-diagonal case: two plaquette
groups `A`, `B` that share NO link.

# The genuine content (the connectedness of the Ursell coefficient)

Two components sharing no link have INDEPENDENT root reps — there is no coupling
`vacSubKernel` between them.  The joint two-point function is therefore a genuine
DOUBLE character sum with independent inner reps, which FACTORIZES exactly:

    jointG w M TA TB  =  Σ_{a<M} Σ_{b<M} rowA(a) · rowB(b)
                      ≃  (Σ_{a<M} rowA(a)) · (Σ_{b<M} rowB(b))
                      =  treeG w M TA · treeG w M TB.

Because the TRUNCATED / connected (Ursell) two-point is by definition the full
joint minus the disconnected product `⟨φ_A φ_B⟩ − ⟨φ_A⟩⟨φ_B⟩`, the exact
factorization forces the connected cross-correlator to VANISH:

    jointG w M TA TB − treeG w M TA · treeG w M TB  ≃  0.

This is precisely why distinct connected components contribute NO connected
correlation — the connectedness content of the signed Ursell coefficient
`φ^T(cluster)`, which is supported only on connected clusters.  It is
dimension-independent (a distributivity/Fubini identity), the combinatorial half
of the Mayer expansion; it does NOT need the interacting Gaussian integral.

# What is PROVED here (all genuine — no fakes)

  * `finSum_mul_finSum` — the double-sum factorization tool
    `(Σ a)·(Σ b) ≃ Σ Σ a·b`, built inline from `RationalTail.finSum_mul_const`
    and `const_mul_finSum` (avoids the heavy `SchurHadamardTransfer` import).
  * `sub_eqv_zero_of_eqv` — `x ≃ y ⟹ x − y ≃ 0` (from `neg_add_self_eqv`).
  * `jointRows` / `jointRows_factor` — the generic disconnected joint of two
    component row-functions and its exact factorization.
  * `jointTreeG` / `jointTreeG_factor` / `jointTreeG_connected_zero` — the two-tree
    (acyclic) instance: the joint factorizes into `treeG A · treeG B` and its
    connected cross part is `≃ 0`.
  * `jointGraphG` / `jointGraphG_factor` / `jointGraphG_connected_zero` — the same
    for two arbitrary multi-loop components (`graphG`), so BOTH components may carry
    cycles: the connected cross part is still `≃ 0`.
  * `jointTreeG_decay` — the full (disconnected) joint is bounded by the PRODUCT of
    the two component geometric envelopes `(ofNat M · ρ^{N_A})·(ofNat M · ρ^{N_B})`,
    via factorization + `treeWilsonG_decay` on each factor.

# NAMED-open residual after this module (NOT faked)

The geometry census (line / tree / cycle / multi-loop / multi-component) is now
combinatorially COMPLETE within the `vacSubKernel` character model.  What is NOT
closed — and is genuinely ANALYTIC, not a formal combinatorial identity — is the
identification of the PHYSICAL interacting connected amplitude with this character /
signed-Ursell sum carrying the REAL link weights: the `vacSubKernel` δ-kernel is the
strong-coupling character abstraction (each shared link forced to value `1` at an
excited rep), whereas the real SU(2) link integral
`∫ χ_j(gU)χ_{j'}(U⁻¹h) dU = δ_{j,j'} χ_j(gh)/dim_j` carries the extra factor
`1/dim_j ≤ 1/2` per shared link.  Closing that gap is
`IsserlisPenroseReduction.IsserlisPenroseData.pertRep` (the perturbative
representation / interacting configuration-space Gaussian integral) — the genuine
4D-measure wall — together with volume-uniformity of the count prefactor and the
continuum `a → 0` modulus.  Those are carried elsewhere as named residuals, NOT
faked here.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core, structural `finSum` distributivity,
and the reused proved `vacSubKernel` correlators `treeG` / `graphG`.  No
`Classical.*`, no `Real`, no `native_decide`, no `decide` on non-decidable props, no
`sorry` / `admit` / new `axiom`, no `Prop := True`.  `jointG` is a genuine double
character sum with INDEPENDENT inner reps (NOT defined to equal a target); the
factorization and the connected-part vanishing are DERIVED.  No frontier bundle is
inhabited.  Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.LoopyCorrelatorProgress

namespace YMGap.Continuum.MultiComponentFactorization

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.LoopyCorrelatorProgress

/-! ## 0. The double-sum factorization tool and the sub-to-zero lemma -/

/-- **`finSum_mul_finSum` (PROVED — inline).**  The product of two partial sums is
the double partial sum of the pointwise products:

    (Σ_{k<r} a_k)·(Σ_{l<s} b_l)  ≃  Σ_{k<r} Σ_{l<s} a_k·b_l.

Built from `RationalTail.finSum_mul_const` (pull the right factor `Σ b` into the
outer sum) and `const_mul_finSum` (pull each `a_k` into the inner sum).  A local
copy of the `SchurHadamardTransfer` lemma, proved here to avoid that module's heavy
OS/Gram import chain. -/
theorem finSum_mul_finSum (a b : Nat → Q') (r s : Nat) :
    ((finSum a r) * (finSum b s)).eqv
      (finSum (fun k => finSum (fun l => a k * b l) s) r) :=
  Q'.eqv_trans _ _ _ (finSum_mul_const a (finSum b s) r)
    (finSum_eqv_congr _ _ (fun k => const_mul_finSum b (a k) s) r)

/-- **`sub_eqv_zero_of_eqv` (PROVED).**  If `x ≃ y` then `x − y ≃ 0`.  `x − y` is
`x + (−y)`; congruence turns it into `y + (−y) ≃ 0` (`neg_add_self_eqv` after
commuting).  This is what turns the exact factorization into "the connected cross
part is identically zero." -/
theorem sub_eqv_zero_of_eqv {x y : Q'} (h : x.eqv y) : (x - y).eqv 0 := by
  show (x + (-y)).eqv 0
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right x y (-y) h) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv y (-y)) ?_
  exact YMGap.Constructive.Q'.neg_add_self_eqv y

/-! ## 1. The generic disconnected joint and its factorization

`jointRows fA fB M` is the joint two-point of two components with row-functions
`fA`, `fB` and INDEPENDENT inner reps (no coupling kernel between them — the
definition of "share no link").  It factorizes exactly into the product of the two
single-component sums. -/

/-- The generic disconnected joint: a double character sum over the independent
component root reps `a, b < M`, with no coupling kernel between the components. -/
def jointRows (fA fB : Nat → Q') (M : Nat) : Q' :=
  finSum (fun a => finSum (fun b => fA a * fB b) M) M

/-- **`jointRows_factor` (PROVED).**  The generic disconnected joint factorizes:

    jointRows fA fB M  ≃  (Σ_{a<M} fA a) · (Σ_{b<M} fB b).

Immediate from `finSum_mul_finSum` (symmetrized). -/
theorem jointRows_factor (fA fB : Nat → Q') (M : Nat) :
    (jointRows fA fB M).eqv (finSum fA M * finSum fB M) := by
  unfold jointRows
  exact Q'.eqv_symm (finSum_mul_finSum fA fB M M)

/-! ## 2. Two acyclic (tree) components — factorization + connected part = 0 -/

/-- The disconnected joint two-point of two TREE components `TA`, `TB` sharing no
link: the double character sum with independent root reps (each row is the
vacuum-subtracted branching value, exactly the `treeG` summand).  A genuine
character multi-sum — NOT defined to equal a target. -/
def jointTreeG (w : Q') (M : Nat) (TA TB : PlaqTree) : Q' :=
  finSum (fun a => finSum (fun b =>
    (vacSubKernel a a * treeBranch w M a TA)
      * (vacSubKernel b b * treeBranch w M b TB)) M) M

/-- **`jointTreeG_factor` (PROVED).**  The two-tree joint factorizes exactly into
the product of the two connected tree correlators:

    jointTreeG w M TA TB  ≃  treeG w M TA · treeG w M TB.

`treeG w M T = Σ_{a<M} vacSubKernel a a · treeBranch w M a T` (definitionally the
row-function), so this is `jointRows_factor` at those two rows. -/
theorem jointTreeG_factor (w : Q') (M : Nat) (TA TB : PlaqTree) :
    (jointTreeG w M TA TB).eqv (treeG w M TA * treeG w M TB) := by
  unfold jointTreeG treeG
  exact Q'.eqv_symm (finSum_mul_finSum
    (fun a => vacSubKernel a a * treeBranch w M a TA)
    (fun b => vacSubKernel b b * treeBranch w M b TB) M M)

/-- **`jointTreeG_connected_zero` (PROVED — bullet (ii) for two trees).**  The
connected (Ursell) cross-correlator between two disconnected tree components — the
joint minus the disconnected product — is IDENTICALLY ZERO:

    jointTreeG w M TA TB − treeG w M TA · treeG w M TB  ≃  0.

So distinct connected (acyclic) components contribute NO connected correlation: the
signed Ursell coefficient is supported only on connected clusters.  Derived from the
exact factorization `jointTreeG_factor` via `sub_eqv_zero_of_eqv`. -/
theorem jointTreeG_connected_zero (w : Q') (M : Nat) (TA TB : PlaqTree) :
    (jointTreeG w M TA TB - treeG w M TA * treeG w M TB).eqv 0 :=
  sub_eqv_zero_of_eqv (jointTreeG_factor w M TA TB)

/-! ## 3. Two arbitrary multi-loop components — factorization + connected part = 0

The same holds when BOTH components carry arbitrarily many cycles (`graphG`): loops
inside a component do not couple the two components, so the joint still factorizes
and the connected cross part still vanishes. -/

/-- The disconnected joint two-point of two MULTI-LOOP components `TA`, `TB` (with
`nA`, `nB` extra loop edges respectively) sharing no link: the double character sum
with independent root reps, each row the `graphG` summand (root kernel × loop-edge
block × branching value).  A genuine character multi-sum. -/
def jointGraphG (w : Q') (M nA nB : Nat) (TA TB : PlaqTree) : Q' :=
  finSum (fun a => finSum (fun b =>
    (vacSubKernel a a * ((vacSubKernel a a) ^ nA * treeBranch w M a TA))
      * (vacSubKernel b b * ((vacSubKernel b b) ^ nB * treeBranch w M b TB))) M) M

/-- **`jointGraphG_factor` (PROVED).**  The two-multi-loop joint factorizes exactly
into the product of the two connected multi-loop correlators:

    jointGraphG w M nA nB TA TB  ≃  graphG w M nA TA · graphG w M nB TB.

`graphG w M n T = Σ_{a<M} vacSubKernel a a · ((vacSubKernel a a)^n · treeBranch …)`
(definitionally the row-function), so this is `jointRows_factor` at those rows. -/
theorem jointGraphG_factor (w : Q') (M nA nB : Nat) (TA TB : PlaqTree) :
    (jointGraphG w M nA nB TA TB).eqv (graphG w M nA TA * graphG w M nB TB) := by
  unfold jointGraphG graphG
  exact Q'.eqv_symm (finSum_mul_finSum
    (fun a => vacSubKernel a a * ((vacSubKernel a a) ^ nA * treeBranch w M a TA))
    (fun b => vacSubKernel b b * ((vacSubKernel b b) ^ nB * treeBranch w M b TB)) M M)

/-- **`jointGraphG_connected_zero` (PROVED — bullet (ii) for two loopy components).**
The connected (Ursell) cross-correlator between two disconnected MULTI-LOOP
components is IDENTICALLY ZERO:

    jointGraphG w M nA nB TA TB − graphG w M nA TA · graphG w M nB TB  ≃  0.

Even with cycles inside each component, distinct components contribute NO connected
correlation.  Derived from `jointGraphG_factor` via `sub_eqv_zero_of_eqv`. -/
theorem jointGraphG_connected_zero (w : Q') (M nA nB : Nat) (TA TB : PlaqTree) :
    (jointGraphG w M nA nB TA TB - graphG w M nA TA * graphG w M nB TB).eqv 0 :=
  sub_eqv_zero_of_eqv (jointGraphG_factor w M nA nB TA TB)

/-! ## 4. The disconnected joint is bounded by the PRODUCT of component envelopes

The full (disconnected) joint — not the connected part, which is `0` — is dominated
by the product of the two single-component geometric envelopes.  So a two-component
correlator decays at the SUM of the two component masses.  Via factorization plus
`treeWilsonG_decay` on each factor. -/

/-- **`jointTreeG_decay` (PROVED).**  For two tree components at strong coupling
`0 ≤ w ≤ 1/2`, the disconnected joint is bounded by the product of the two
component envelopes:

    jointTreeG w (M+1) TA TB
      ≤  (ofNat M · ρ^{N_A}) · (ofNat M · ρ^{N_B}),
        N_A = treeNodeCount TA, N_B = treeNodeCount TB, ρ = 2w³ < 1.

Factorization `jointTreeG_factor` reduces it to `treeG A · treeG B`, then
`treeWilsonG_decay` bounds each factor (with `treeG_nonneg` for the monotonicity). -/
theorem jointTreeG_decay {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (M : Nat) (TA TB : PlaqTree) :
    jointTreeG w (M + 1) TA TB
      ≤ (Q'.ofNat M * (rho w) ^ (treeNodeCount TA))
          * (Q'.ofNat M * (rho w) ^ (treeNodeCount TB)) := by
  -- jointTreeG ≃ treeG A · treeG B ; bound each factor.
  have hfac : jointTreeG w (M + 1) TA TB
      ≤ treeG w (M + 1) TA * treeG w (M + 1) TB :=
    Q'.le_of_eqv (jointTreeG_factor w (M + 1) TA TB)
  have hA : treeG w (M + 1) TA ≤ Q'.ofNat M * (rho w) ^ (treeNodeCount TA) :=
    treeWilsonG_decay hw0 hw M TA
  have hB : treeG w (M + 1) TB ≤ Q'.ofNat M * (rho w) ^ (treeNodeCount TB) :=
    treeWilsonG_decay hw0 hw M TB
  have hBnn : (0 : Q') ≤ treeG w (M + 1) TB := treeG_nonneg hw0 M TB
  have hAenv_nn : (0 : Q') ≤ Q'.ofNat M * (rho w) ^ (treeNodeCount TA) :=
    Q'.mul_nonneg _ _ (YMGap.Continuum.ClusterCount.ofNat_nonneg M)
      (Q'.pow_nonneg (rho w) (rho_nonneg hw0) (treeNodeCount TA))
  -- treeG A · treeG B ≤ (env A) · treeG B ≤ (env A) · (env B)
  have h1 : treeG w (M + 1) TA * treeG w (M + 1) TB
      ≤ (Q'.ofNat M * (rho w) ^ (treeNodeCount TA)) * treeG w (M + 1) TB :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA hBnn
  have h2 : (Q'.ofNat M * (rho w) ^ (treeNodeCount TA)) * treeG w (M + 1) TB
      ≤ (Q'.ofNat M * (rho w) ^ (treeNodeCount TA))
          * (Q'.ofNat M * (rho w) ^ (treeNodeCount TB)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hB hAenv_nn
  exact Q'.le_trans' _ _ _ hfac (Q'.le_trans' _ _ _ h1 h2)

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean — the DISCONNECTED joint correlator factorizes,
so the connected cross part vanishes; built from the SAME `vacSubKernel`
orthogonality correlators):

  * `finSum_mul_finSum`, `sub_eqv_zero_of_eqv` — the factorization tool and the
    exact-factorization ⟹ zero-connected-part bridge;
  * `jointRows`, `jointRows_factor` — the generic disconnected joint and its exact
    factorization;
  * `jointTreeG`, `jointTreeG_factor`, `jointTreeG_connected_zero` — two acyclic
    (tree) components: the joint factorizes into `treeG A · treeG B` and its
    connected cross part is `≃ 0`;
  * `jointGraphG`, `jointGraphG_factor`, `jointGraphG_connected_zero` — two
    arbitrary multi-loop components (BOTH may carry cycles): the connected cross
    part is still `≃ 0`;
  * `jointTreeG_decay` — the full disconnected joint is bounded by the PRODUCT of
    the two component envelopes.

This CLOSES bullet (ii) of `MultiPlaquetteMayer.LoopyCorrelatorResidual` as a
correlator theorem: distinct connected components contribute NO connected
correlation (the connectedness of the signed Ursell coefficient).  Together with
line / tree / cycle / multi-loop (all previously proved), the geometry census of the
connected correlator is combinatorially COMPLETE within the character model.

NAMED-open (NOT faked, carried elsewhere): the identification of the PHYSICAL
interacting amplitude with this character / signed-Ursell sum carrying the REAL link
weights — `IsserlisPenroseReduction.IsserlisPenroseData.pertRep`, the interacting
configuration-space Gaussian integral (the δ-kernel `vacSubKernel` drops the real
`1/dim_j` per-shared-link factor).  That is genuinely ANALYTIC, not a formal
combinatorial identity — plus volume-uniformity of the count prefactor and the
continuum `a → 0` modulus.  This module is a FIXED-SPACING combinatorial step; it is
NOT uniform-in-`w`, NOT the continuum limit, and NOT a 4D Yang–Mills mass gap
(OPEN). -/

end YMGap.Continuum.MultiComponentFactorization

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MultiComponentFactorization.finSum_mul_finSum
#print axioms YMGap.Continuum.MultiComponentFactorization.sub_eqv_zero_of_eqv
#print axioms YMGap.Continuum.MultiComponentFactorization.jointRows_factor
#print axioms YMGap.Continuum.MultiComponentFactorization.jointTreeG_factor
#print axioms YMGap.Continuum.MultiComponentFactorization.jointTreeG_connected_zero
#print axioms YMGap.Continuum.MultiComponentFactorization.jointGraphG_factor
#print axioms YMGap.Continuum.MultiComponentFactorization.jointGraphG_connected_zero
#print axioms YMGap.Continuum.MultiComponentFactorization.jointTreeG_decay
