/-
Exact theta-sector interface for the variable retained-head schedule.

The variable-anchor PF2 theorem leaves one head comparison whose adjacent
cutoff is one step longer than its diagonal cutoff.  This file translates
that mismatch exactly into the finite integer/half-integer theta sectors, so
the Pascal/Bernstein certificate can feed the actual all-later-cutoffs theorem
without any normalization change.
-/

import YMGap.Continuum.HarmonicVariableAnchorRetune
import YMGap.Continuum.HarmonicThetaRepresentation

namespace YMGap.Continuum.HarmonicVariableAnchorThetaBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicVariableAnchorRetune
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- Exact mismatched-cutoff theta consumer.  The half-integer sector is
retained through edge `b`, while the integer sector is retained only through
node `b`; this is precisely the head comparison required by the variable
anchor theorem. -/
theorem theta_head_comparison_implies_retained_head {w R : Q'}
    (hw0 : (0 : Q') < w) (b : Nat)
    (htheta :
      w * halfThetaSum w (b + 1) ≤ R * integerThetaSum w b) :
    adjCorr w (b + 1) ≤ R * coordNormSq w b := by
  have hww : (0 : Q') < qpow w 2 := qpow_pos hw0 2
  have hL : qpow w 2 * adjCorr w (b + 1) ≈
      w * halfThetaSum w (b + 1) := by
    have hq2 : qpow w 2 ≈ w * w := by
      change ((1 : Q') * w) * w ≈ w * w
      exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (adjCorr w (b + 1)) hq2) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv w w (adjCorr w (b + 1))) ?_
    exact Q'.mul_eqv_congr_left w _ _ (adjCorr_theta_eqv w (b + 1))
  have hR : qpow w 2 * (R * coordNormSq w b) ≈
      R * integerThetaSum w b := by
    have hreorder : qpow w 2 * (R * coordNormSq w b) ≈
        R * (qpow w 2 * coordNormSq w b) := by
      ring_qeqv
    exact Q'.eqv_trans _ _ _ hreorder
      (Q'.mul_eqv_congr_left R _ _ (coordNormSq_theta_eqv w b))
  have hscaled : qpow w 2 * adjCorr w (b + 1) ≤
      qpow w 2 * (R * coordNormSq w b) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ htheta (Q'.ge_of_eqv hR))
  exact Q'.le_of_mul_le_mul_left hscaled hww

/-- A theta certificate at the explicit growing head closes every later
cutoff through the already-proved scalar-cross/PF2 engine. -/
theorem growing_anchor_retune_of_theta_head (k M : Nat)
    (htheta : harmW k *
          halfThetaSum (harmW k) (growingAnchor k + 1) ≤
        retuneCube (harmW k) *
          integerThetaSum (harmW k) (growingAnchor k)) :
    adjCorr (harmW k) (growingAnchor k + 1 + M) ≤
      retuneCube (harmW k) *
        coordNormSq (harmW k) (growingAnchor k + 1 + M) := by
  apply growing_anchor_retune_of_head k M
  exact theta_head_comparison_implies_retained_head
    (harmW_pos k) (growingAnchor k) htheta

/-- From the first nontrivial harmonic scale onward, the first propagated
cutoff lies inside the physical quadratic cutoff.  (`k=0` is the exact base
anchor and has `growingAnchor 0 = Ncut 0`.) -/
theorem growingAnchor_succ_le_Ncut {k : Nat} (hk : 1 ≤ k) :
    growingAnchor k + 1 ≤ Ncut k := by
  unfold growingAnchor Ncut
  have hthree : 3 ≤ k + 2 := by omega
  have hmul := Nat.mul_le_mul_right (k + 2) hthree
  have hlin : 2 * (k + 2) + 1 ≤ 3 * (k + 2) := by omega
  exact Nat.le_trans hlin (by simpa [Nat.mul_comm] using hmul)

/-- The sole variable-head theta inequality closes the retune comparison at
the actual physical cutoff `Ncut k` for every `k ≥ 1`. -/
theorem harmonic_retune_Ncut_of_theta_head {k : Nat} (hk : 1 ≤ k)
    (htheta : harmW k *
          halfThetaSum (harmW k) (growingAnchor k + 1) ≤
        retuneCube (harmW k) *
          integerThetaSum (harmW k) (growingAnchor k)) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  have hb := growingAnchor_succ_le_Ncut hk
  have h := growing_anchor_retune_of_theta_head k
    (Ncut k - (growingAnchor k + 1)) htheta
  have hcut : growingAnchor k + 1 +
      (Ncut k - (growingAnchor k + 1)) = Ncut k := Nat.add_sub_of_le hb
  simpa [hcut] using h

/-- The same single theta premise controls the normalized fundamental
Peter--Weyl eigenvalue at the physical cutoff. -/
theorem harmonic_lamPW_le_retune_of_theta_head {k : Nat} (hk : 1 ≤ k)
    (htheta : harmW k *
          halfThetaSum (harmW k) (growingAnchor k + 1) ≤
        retuneCube (harmW k) *
          integerThetaSum (harmW k) (growingAnchor k)) :
    lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k) := by
  have hcorr := harmonic_retune_Ncut_of_theta_head hk htheta
  have heq : lamPW (harmW k) (Ncut k) 1 ≈
      Q'.divPos (adjCorr (harmW k) (Ncut k))
        (coordNormSq (harmW k) (Ncut k))
        (coordNormSq_pos (harmW_nonneg k) (Ncut k)) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 (harmW_nonneg k) (harmW_le_one k) (Ncut k) 0)
      (vacNorm_fundamental_eq_ratio
        (harmW_nonneg k) (harmW_le_one k) (Ncut k))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.divPos_le_of_le_mul _ _ _ hcorr)

/-- The explicit theta residual therefore implies the uniform rational mass
floor used by the coupled-shell spacing construction. -/
theorem harmonicMass_floor_of_theta_head {k : Nat} (hk : 1 ≤ k)
    (htheta : harmW k *
          halfThetaSum (harmW k) (growingAnchor k + 1) ≤
        retuneCube (harmW k) *
          integerThetaSum (harmW k) (growingAnchor k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (harmonic_lamPW_le_retune_of_theta_head hk htheta))

#print axioms theta_head_comparison_implies_retained_head
#print axioms growing_anchor_retune_of_theta_head
#print axioms growingAnchor_succ_le_Ncut
#print axioms harmonic_retune_Ncut_of_theta_head
#print axioms harmonic_lamPW_le_retune_of_theta_head
#print axioms harmonicMass_floor_of_theta_head

end YMGap.Continuum.HarmonicVariableAnchorThetaBridge
