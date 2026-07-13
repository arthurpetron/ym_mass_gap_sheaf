/-
`EndpointCutoffTailClose` — closes the quotient left by the symbolic endpoint
power sums and lands it on the quadratic moving-cutoff schedule.

For every cutoff `N`, the fundamental p=2 fused eigenvalue at `w=1` is
exactly `2N/(2N+3)` and its vacuum-normalized defect is exactly
`3/(2N+3)`.  At `Ncut(k)=(k+2)^2`, that defect is therefore the already
proved inverse-square-summable `tailCut(k)`.
-/

import YMGap.Continuum.EndpointCutoffTailFormula
import YMGap.Continuum.QuadraticCutoffSchedule

namespace YMGap.Continuum.EndpointCutoffTailClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CutoffEndpointDefect
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3
private def q6 : Q' := Q'.ofNat 6

private theorem mul_eqv_both {a b c d : Q'} (hac : a ≈ c) (hbd : b ≈ d) :
    a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

/-- Positive denominator `2N+3`. -/
theorem endpointDen_pos (N : Nat) : (0 : Q') < Q'.ofNat (2 * N + 3) :=
  Q'.ofNat_succ_pos (2 * N + 2)

/-- The exact finite-cutoff endpoint eigenvalue. -/
def endpointRate (N : Nat) : Q' :=
  Q'.divPos (Q'.ofNat (2 * N)) (Q'.ofNat (2 * N + 3)) (endpointDen_pos N)

/-- The exact complementary cutoff tail. -/
def endpointTail (N : Nat) : Q' :=
  Q'.divPos (Q'.ofNat 3) (Q'.ofNat (2 * N + 3)) (endpointDen_pos N)

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul hq hcancel

theorem bondMovedCoeff_one_eq_twice_adjCorr (N : Nat) :
    bondMovedCoeff N (1 : Q') 2 1 ≈ q2 * adjCorr (1 : Q') N :=
  Q'.eqv_trans _ _ _ (bondMovedCoeff_eq_boxSum N 1)
    (boxSum_one_eq_twice_adjCorr 1 N)

theorem bondMovedCoeff_zero_eq_coordNormSq (N : Nat) :
    bondMovedCoeff N (1 : Q') 2 0 ≈ coordNormSq (1 : Q') N :=
  g0_diag N

theorem coordNormSq_endpoint_pos (N : Nat) :
    (0 : Q') < coordNormSq (1 : Q') N :=
  pos_of_eqv_of_pos (Q'.eqv_symm (bondMovedCoeff_zero_eq_coordNormSq N))
    (S1Dominance.bmc_zero_pos N (by decide) (by decide) 2 (by decide))

private theorem endpoint_num_eq (N : Nat) :
    Q'.ofNat (2 * N) ≈ q2 * Q'.ofNat N := by
  exact Q'.eqv_trans _ _ _
    (ofNat_mul_eqv 2 N)
    (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.ofNat 2 ≈ q2))

private theorem endpoint_den_eq (N : Nat) :
    Q'.ofNat (2 * N + 3) ≈ q2 * Q'.ofNat N + 3 := by
  refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (2 * N) 3) ?_
  exact Q'.add_eqv_congr' (endpoint_num_eq N) (by decide)

/-- Cross-multiplied form of `A_N/D_N = 2N/(2N+3)`. -/
theorem adjCorr_endpoint_cross (N : Nat) :
    adjCorr (1 : Q') N * Q'.ofNat (2 * N + 3) ≈
      Q'.ofNat (2 * N) * coordNormSq (1 : Q') N := by
  let x := Q'.ofNat N
  let A := adjCorr (1 : Q') N
  let D := coordNormSq (1 : Q') N
  let F := (x + 1) * (x + 2)
  let den := q2 * x + 3
  have hA : q3 * A ≈ x * F := by
    simpa [q3, x, A, F] using
      (Q'.eqv_trans _ _ _ (adjCorr_endpoint_closed N)
        (Q'.mul_assoc_eqv (Q'.ofNat N) (Q'.ofNat N + 1) (Q'.ofNat N + 2)))
  have hD : q6 * D ≈ F * den := by
    simpa [q6, q2, x, D, F, den] using coordNormSq_endpoint_closed N
  have h32 : q3 * q2 ≈ q6 := by decide
  have hL : q3 * (A * den) ≈ x * (F * den) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q3 A den)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ den hA) ?_
    exact Q'.mul_assoc_eqv x F den
  have hR : q3 * ((q2 * x) * D) ≈ x * (F * den) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q3 (q2 * x) D)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ D
        (Q'.eqv_symm (Q'.mul_assoc_eqv q3 q2 x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ D (Q'.mul_eqv_congr_right _ _ x h32)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv q6 x)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x q6 D) ?_
    exact Q'.mul_eqv_congr_left x _ _ hD
  have hcore : A * den ≈ (q2 * x) * D :=
    Q'.mul_left_cancel_of_pos (by decide : (0 : Q') < q3)
      (Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left A _ _ (endpoint_den_eq N)) ?_
  refine Q'.eqv_trans _ _ _ hcore ?_
  exact Q'.mul_eqv_congr_right _ _ D (Q'.eqv_symm (endpoint_num_eq N))

/-- **General fixed-cutoff endpoint eigenvalue formula.** -/
theorem vacNorm_endpoint_formula (N : Nat) :
    vacNorm N 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) 1 ≈ endpointRate N := by
  let A := adjCorr (1 : Q') N
  let D := coordNormSq (1 : Q') N
  have hnum := bondMovedCoeff_one_eq_twice_adjCorr N
  have hzero := bondMovedCoeff_zero_eq_coordNormSq N
  have hdim : dimQ 1 ≈ q2 := by decide
  have hden : dimQ 1 * bondMovedCoeff N (1 : Q') 2 0 ≈ q2 * D :=
    mul_eqv_both hdim hzero
  have hcross0 :
      bondMovedCoeff N (1 : Q') 2 1 * D ≈
        A * (dimQ 1 * bondMovedCoeff N (1 : Q') 2 0) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ D hnum) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv q2 A)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A q2 D) ?_
    exact Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm hden)
  have hAD :
      Q'.divPos (bondMovedCoeff N (1 : Q') 2 1)
          (dimQ 1 * bondMovedCoeff N (1 : Q') 2 0)
          (Q'.mul_pos (Q'.ofNat_succ_pos 1)
            (S1Dominance.bmc_zero_pos N (by decide) (by decide) 2 (by decide))) ≈
        Q'.divPos A D (coordNormSq_endpoint_pos N) :=
    divPos_eqv_divPos_of_cross _ _ hcross0
  refine Q'.eqv_trans _ _ _ hAD ?_
  unfold endpointRate
  exact divPos_eqv_divPos_of_cross (coordNormSq_endpoint_pos N)
    (endpointDen_pos N) (adjCorr_endpoint_cross N)

private theorem absQ_eqv_abs_local (x : Q') : absQ x ≈ Q'.abs x := by
  unfold absQ Q'.abs
  by_cases hx : (0 : Int) ≤ x.num
  · rw [if_pos hx]
    have hx' : (0 : Q') ≤ x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_pos hx']
    exact Q'.eqv_refl _
  · rw [if_neg hx]
    have hx' : ¬ (0 : Q') ≤ x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_neg hx']
    exact Q'.eqv_refl _

private theorem absQ_eqv_congr_local {x y : Q'} (h : x ≈ y) : absQ x ≈ absQ y :=
  Q'.eqv_trans _ _ _ (absQ_eqv_abs_local x)
    (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr h)
      (Q'.eqv_symm (absQ_eqv_abs_local y)))

theorem endpointTail_pos (N : Nat) : (0 : Q') < endpointTail N := by
  unfold endpointTail
  exact Q'.divPos_pos _ _ _ (by decide)

theorem one_sub_endpointRate (N : Nat) :
    ((1 : Q') - endpointRate N) ≈ endpointTail N := by
  unfold endpointRate endpointTail
  let den := Q'.ofNat (2 * N + 3)
  let num := Q'.ofNat (2 * N)
  have hsub : den - num ≈ (Q'.ofNat 3) := by
    have hd : den ≈ num + Q'.ofNat 3 := by
      simpa [den, num] using Q'.ofNat_add_eqv (2 * N) 3
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-num) hd) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv num (Q'.ofNat 3) (-num)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left num _ _ (Q'.add_comm_eqv (Q'.ofNat 3) (-num))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv num (-num) (Q'.ofNat 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv num)) ?_
    exact QPoly.q_zero_add_eqv _
  refine Q'.eqv_trans _ _ _ (one_sub_divPos_eqv num den (endpointDen_pos N)) ?_
  exact divPos_eqv_divPos_of_cross (endpointDen_pos N) (endpointDen_pos N)
    (Q'.mul_eqv_congr_right _ _ den hsub)

private theorem absQ_neg_endpointTail (N : Nat) :
    absQ (-(endpointTail N)) ≈ endpointTail N := by
  have ht : (0 : Q') < endpointTail N := endpointTail_pos N
  unfold absQ
  rw [if_neg]
  · exact Q'.neg_neg_eqv _
  · intro hnum
    have hneg0 : (0 : Q') ≤ -(endpointTail N) := by
      rw [Q'.zero_le_iff_num_nonneg]
      exact hnum
    have hle0 : endpointTail N ≤ (0 : Q') := by
      have h := Q'.neg_le_neg hneg0
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv _)) h
    have hz : (0 : Q') < (0 : Q') :=
      ClusteringImpliesGap.lt_of_lt_of_le ht hle0
    exact (by decide : ¬ ((0 : Q') < (0 : Q'))) hz

/-- **General fixed-cutoff endpoint defect formula.** -/
theorem normEigShift_endpoint_formula (N : Nat) :
    normEigShift N 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) 1 ≈ endpointTail N := by
  have hv := vacNorm_endpoint_formula N
  have hret := retEig2_endpoint 2 (by decide) 0 1
  have hret0 : retEig 2 (by decide) (1 : Q') 1 ≈ (1 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (retEig2_param_zero 2 (by decide) 1 1)) hret
  have harg0 :
      vacNorm N 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
          (by decide : (1 : Q') ≤ (1 : Q')) 1 +
          -(retEig 2 (by decide) (1 : Q') 1) ≈
        endpointRate N + -(1 : Q') :=
    Q'.add_eqv_congr' hv (Q'.neg_eqv_congr _ _ hret0)
  have hflip : endpointRate N + -(1 : Q') ≈ -((1 : Q') - endpointRate N) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(endpointRate N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) _ _ (Q'.neg_neg_eqv (endpointRate N))) ?_
    exact Q'.add_comm_eqv (-1) (endpointRate N)
  have harg :
      vacNorm N 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
          (by decide : (1 : Q') ≤ (1 : Q')) 1 +
          -(retEig 2 (by decide) (1 : Q') 1) ≈ -(endpointTail N) :=
    Q'.eqv_trans _ _ _ harg0
      (Q'.eqv_trans _ _ _ hflip (Q'.neg_eqv_congr _ _ (one_sub_endpointRate N)))
  exact Q'.eqv_trans _ _ _ (absQ_eqv_congr_local harg) (absQ_neg_endpointTail N)

/-- At the quadratic moving cutoff, the exact endpoint defect is precisely
the summable arithmetic envelope. -/
theorem normEigShift_endpoint_Ncut (k : Nat) :
    normEigShift (Ncut k) 2 (by decide)
      (by decide : (0 : Q') ≤ (1 : Q')) (by decide : (1 : Q') ≤ (1 : Q')) 1 ≈
      tailCut k := by
  refine Q'.eqv_trans _ _ _ (normEigShift_endpoint_formula (Ncut k)) ?_
  unfold endpointTail tailCut
  exact divPos_eqv_divPos_of_cross (endpointDen_pos (Ncut k))
    (by exact Q'.ofNat_succ_pos (2 * Ncut k + 2)) (by
      exact Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ (Q'.eqv_refl _))

end YMGap.Continuum.EndpointCutoffTailClose

#print axioms YMGap.Continuum.EndpointCutoffTailClose.adjCorr_endpoint_cross
#print axioms YMGap.Continuum.EndpointCutoffTailClose.vacNorm_endpoint_formula
#print axioms YMGap.Continuum.EndpointCutoffTailClose.one_sub_endpointRate
#print axioms YMGap.Continuum.EndpointCutoffTailClose.normEigShift_endpoint_formula
#print axioms YMGap.Continuum.EndpointCutoffTailClose.normEigShift_endpoint_Ncut
