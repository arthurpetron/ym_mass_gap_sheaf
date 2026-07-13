/-
# Completed globally projected SU(2) bigon block

The first multiple-shared-link cycle is a two-link bigon.  After each link is
fused locally, gauge compatibility keeps only equal irreducible labels on the
two links.  Thus the corrected gluing is the diagonal product

    (a_s,b_s) |-> a_s b_s,

not the product of the two local norms.  The latter has cross-label terms and
is machine-refuted below on the double-fundamental packet.

This file proves the exact gauge-collapse/time intertwiner, removes the unique
common-label vacuum, and completes the two-link transfer as the square of the
completed one-link shared-fusion transfer.  The surviving projected double
excitation is exactly the quadratic loop and has eigenvalue
`(1/256)^2`.

Honest scope: this is the smallest correlated closed cycle.  General lattice
spin networks require the analogous vertex-intertwiner contraction, including
higher-valence multiplicity spaces.
-/

import YMGap.Continuum.SU2SharedLinkFusionGNSCompleted
import YMGap.Continuum.SU2GlobalVacuumCycleQuotient
import YMGap.Continuum.SelfAdjointHamiltonian

namespace YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted

set_option maxHeartbeats 500000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionBlock
open YMGap.Continuum.SU2SharedLinkFusionGNSCompleted
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Gauge-compatible diagonal gluing -/

/-- Keep only equal irreducible labels on the two bivalent-cycle links. -/
def bigonGaugeCollapse (a b : IrrepVec) : IrrepVec :=
  (a.1 * b.1, (a.2.1 * b.2.1, a.2.2 * b.2.2))

/-- Two heat-kernel link crossings act on the common label. -/
def bigonTransfer (a : IrrepVec) : IrrepVec :=
  irrepTransfer (irrepTransfer a)

theorem bigonGaugeCollapse_transfer_intertwines (a b : IrrepVec) :
    IrrepEq (bigonGaugeCollapse (irrepTransfer a) (irrepTransfer b))
      (bigonTransfer (bigonGaugeCollapse a b)) := by
  unfold IrrepEq bigonGaugeCollapse bigonTransfer irrepTransfer
  exact ⟨Q'.eqv_refl _, by ring_qeqv, by ring_qeqv⟩

/-- Local norm multiplication is not the gauge-compatible global Gram: it
retains off-diagonal label pairs that the bivalent quotient removes. -/
theorem local_norm_product_not_global_gram :
    ¬ (irrepGram
        (bigonGaugeCollapse bigonDoubleLocal bigonDoubleLocal)
        (bigonGaugeCollapse bigonDoubleLocal bigonDoubleLocal) ≈
      irrepGram bigonDoubleLocal bigonDoubleLocal *
        irrepGram bigonDoubleLocal bigonDoubleLocal) := by
  unfold bigonGaugeCollapse bigonDoubleLocal irrepGram fusionCollapse doubleMode
    vacuumCoord fundamentalCoord quadraticCoord
  decide

/-! ## The unique global vacuum projection -/

def projectGlobalVacuum (a : IrrepVec) : IrrepVec :=
  (0, (a.2.1, a.2.2))

theorem projectGlobalVacuum_idempotent (a : IrrepVec) :
    IrrepEq (projectGlobalVacuum (projectGlobalVacuum a))
      (projectGlobalVacuum a) :=
  ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

theorem projectGlobalVacuum_transfer_commutes (a : IrrepVec) :
    IrrepEq (bigonTransfer (projectGlobalVacuum a))
      (projectGlobalVacuum (bigonTransfer a)) := by
  unfold IrrepEq bigonTransfer projectGlobalVacuum irrepTransfer
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

/-- Two local double-fundamental packets give diagonal labels `0` and `2`;
after global vacuum removal only the quadratic loop survives. -/
theorem projected_double_is_quadratic :
    IrrepEq
      (projectGlobalVacuum
        (bigonGaugeCollapse bigonDoubleLocal bigonDoubleLocal))
      quotientQuadratic := by
  unfold IrrepEq projectGlobalVacuum bigonGaugeCollapse bigonDoubleLocal
    fusionCollapse doubleMode vacuumCoord fundamentalCoord quadraticCoord
    quotientQuadratic
  exact ⟨by decide, by decide, by decide⟩

/-! ## Completion of the correlated two-link transfer -/

def completedBigonTransfer
    (x : GNSCompletionSpace sharedIrrepGNS) :
    GNSCompletionSpace sharedIrrepGNS :=
  completedIrrepTransfer (completedIrrepTransfer x)

theorem completedBigonTransfer_embed (a : IrrepVec) :
    completedBigonTransfer (embedV sharedIrrepGNS a) =
      embedV sharedIrrepGNS (bigonTransfer a) := by
  unfold completedBigonTransfer bigonTransfer
  rw [completedIrrepTransfer_embed, completedIrrepTransfer_embed]

theorem completedBigonTransfer_selfAdjoint
    (x y : GNSCompletionSpace sharedIrrepGNS) :
    sharedIrrepGNS.cinnerCompl (completedBigonTransfer x) y =
      sharedIrrepGNS.cinnerCompl x (completedBigonTransfer y) := by
  unfold completedBigonTransfer
  rw [completedIrrepTransfer_selfAdjoint,
    completedIrrepTransfer_selfAdjoint]

theorem completedBigonTransfer_positive
    (x : GNSCompletionSpace sharedIrrepGNS) :
    CReal.RCnonneg
      (sharedIrrepGNS.cinnerCompl (completedBigonTransfer x) x) := by
  unfold completedBigonTransfer
  rw [completedIrrepTransfer_selfAdjoint]
  exact sharedIrrepGNS.cinner_self_nonneg (completedIrrepTransfer x)

theorem completedBigonTransfer_contraction
    (x : GNSCompletionSpace sharedIrrepGNS) :
    CReal.RCle
      (sharedIrrepGNS.cinnerCompl (completedBigonTransfer x)
        (completedBigonTransfer x))
      (sharedIrrepGNS.cinnerCompl x x) := by
  unfold completedBigonTransfer
  exact CReal.RCle_trans
    (completedIrrepTransfer_contraction (completedIrrepTransfer x))
    (completedIrrepTransfer_contraction x)

theorem bigonTransfer_exact_spectrum :
    IrrepEq (bigonTransfer quotientVacuum) quotientVacuum ∧
    IrrepEq (bigonTransfer quotientFundamental)
      ((0, (eighth * eighth, 0)) : IrrepVec) ∧
    IrrepEq (bigonTransfer quotientQuadratic)
      ((0, (0, quadraticEigen * quadraticEigen)) : IrrepVec) := by
  unfold IrrepEq bigonTransfer irrepTransfer quotientVacuum
    quotientFundamental quotientQuadratic
  decide

def completedBigonTransferOperator :
    TransferOperator sharedIrrepGNS.gnsComplete where
  T := completedBigonTransfer
  vacuum := embedV sharedIrrepGNS quotientVacuum
  selfAdjoint := completedBigonTransfer_selfAdjoint
  positive := completedBigonTransfer_positive
  contraction := completedBigonTransfer_contraction

/-! ## Exact projected spectrum -/

theorem completedBigon_vacuum_eigen :
    completedBigonTransferOperator.T
        (embedV sharedIrrepGNS quotientVacuum) =
      embedV sharedIrrepGNS quotientVacuum := by
  refine Eq.trans (completedBigonTransfer_embed quotientVacuum) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS bigonTransfer_exact_spectrum.1)

theorem completedBigon_fundamental_eigen :
    completedBigonTransferOperator.T
        (embedV sharedIrrepGNS quotientFundamental) =
      embedV sharedIrrepGNS
        ((0, (eighth * eighth, 0)) : IrrepVec) := by
  refine Eq.trans (completedBigonTransfer_embed quotientFundamental) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS bigonTransfer_exact_spectrum.2.1)

/-- The globally projected double excitation is the nonzero quadratic loop
with exact two-link eigenvalue `(1/256)^2`. -/
theorem completedBigon_projected_double_eigen :
    completedBigonTransferOperator.T
        (embedV sharedIrrepGNS quotientQuadratic) =
      embedV sharedIrrepGNS
        ((0, (0, quadraticEigen * quadraticEigen)) : IrrepVec) := by
  refine Eq.trans (completedBigonTransfer_embed quotientQuadratic) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS bigonTransfer_exact_spectrum.2.2)

theorem completed_quadratic_ne_zero :
    embedV sharedIrrepGNS quotientQuadratic ≠
      embedV sharedIrrepGNS sharedIrrepGNS.zero := by
  intro h
  have hr : sharedIrrepGNS.rad quotientQuadratic sharedIrrepGNS.zero :=
    constCauchy_null_imp_rad sharedIrrepGNS (Quotient.exact h)
  have hz : sharedIrrepGNS.B quotientQuadratic quotientQuadratic ≈ 0 :=
    (sharedIrrepGNS.rad_zero_iff quotientQuadratic).mp hr
  have hn : sharedIrrepGNS.B quotientQuadratic quotientQuadratic ≈ 1 :=
    Q'.eqv_trans _ _ _
      (sharedIrrepGNS_B_eq_irrepGram quotientQuadratic quotientQuadratic)
      (by decide)
  exact (by decide : ¬ ((1 : Q') ≈ 0))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hn) hz)

end YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted

#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.bigonGaugeCollapse_transfer_intertwines
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.local_norm_product_not_global_gram
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.projected_double_is_quadratic
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completedBigonTransfer
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completedBigonTransferOperator
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.bigonTransfer_exact_spectrum
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completedBigon_vacuum_eigen
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completedBigon_fundamental_eigen
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completedBigon_projected_double_eigen
#print axioms YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted.completed_quadratic_ne_zero
