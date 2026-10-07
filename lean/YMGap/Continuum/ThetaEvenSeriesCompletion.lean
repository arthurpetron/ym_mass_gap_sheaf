/-
# Completion of the actual bilateral even theta prefixes

The literal signed intervals retain both endpoints and the central term.
Their angular values and endpoint frequency jets are completed with the
same explicit cubic Gaussian-shell cutoff as the one-sided series.
All uniformity is in x on [-1,1] at a named strict nome, not in nome,
lattice spacing, or physical volume. No derivative of a limit is used.
-/

import YMGap.Continuum.ThetaOneSidedSeriesCompletion
import YMGap.Continuum.ThetaJointValuePin
import YMGap.Continuum.ThetaParityShellWeights

namespace YMGap.Continuum.ThetaEvenSeriesCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaOneSidedSeriesCompletion
open YMGap.Continuum.ThetaJointValuePin (sum_perm signed_succ_perm)
open YMGap.Continuum.ThetaParityConvolution (signedIndices)
open YMGap.Continuum.ThetaParityWeights (evenThetaTerm)
open YMGap.Continuum.ThetaAlternatingMixedRectangle (evenPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle
  (evenEndpointTerm evenEndpointJet)
open YMGap.Continuum.ThetaAngularShellTail (shellTerm)
open YMGap.Continuum.ThetaParityShellWeights (chebT_abs_le_one)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_nonneg ofNat_mul_eqv ofNat_le_ofNat)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem signed_prefix_step (f : Int → Q') (hneg : ∀ k, f (-k) = f k)
    (N : Nat) :
    listQSum f (signedIndices (N+1)) ≈
      listQSum f (signedIndices N) + 2*f ((N+1 : Nat) : Int) := by
  refine Q'.eqv_trans _ _ _ (sum_perm f (signed_succ_perm N)) ?_
  change f (-((N+1 : Nat) : Int)) +
    listQSum f (signedIndices N ++ [((N+1 : Nat) : Int)]) ≈ _
  rw [hneg]
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (QPoly.q_add_zero_eqv _)))) ?_
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1) (.var 0)))
    (.add (.var 1) (.mul (.const 2) (.var 0))) (by decide)
    (fun | 0 => f ((N+1 : Nat) : Int) | _ => listQSum f (signedIndices N))

private theorem evenTerm_neg (w x : Q') (k : Int) :
    evenThetaTerm w x (-k) = evenThetaTerm w x k := by
  simp only [evenThetaTerm, Int.natAbs_neg, Int.mul_neg, Int.natAbs_neg]

private theorem evenEndpointTerm_neg (w : Q') (k : Int) :
    evenEndpointTerm w (-k) = evenEndpointTerm w k := by
  simp only [evenEndpointTerm, Int.natAbs_neg, Int.mul_neg, Int.natAbs_neg]

/-- The actual two-endpoint increment, with no central-term modification. -/
theorem evenPartial_step (w x : Q') (N : Nat) :
    evenPartial w x (N+1) ≈ evenPartial w x N +
      2*evenThetaTerm w x ((N+1 : Nat) : Int) :=
  signed_prefix_step _ (evenTerm_neg w x) N

theorem evenEndpointJet_step (w : Q') (N : Nat) :
    evenEndpointJet w (N+1) ≈ evenEndpointJet w N +
      2*evenEndpointTerm w ((N+1 : Nat) : Int) :=
  signed_prefix_step _ (evenEndpointTerm_neg w) N

private theorem shell_coefficient_le {c n : Nat} (hc : c ≤ 16*(n*n*n)) :
    Q'.ofNat c ≤ 16*Q'.ofNat (n*n*n) :=
  Q'.le_trans' _ _ _ (ofNat_le_ofNat hc)
    (Q'.le_of_eqv (ofNat_mul_eqv 16 (n*n*n)))

private theorem square_le_cube (n : Nat) (hn : 1 ≤ n) : n*n ≤ n*n*n := by
  have h := Nat.mul_le_mul_left (n*n) hn
  simpa only [Nat.mul_one] using h

/-- Literal paired angular terms fit the existing cubic Gaussian shell. -/
theorem evenPairedTerm_shell_abs_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (n : Nat) (hn : 1 ≤ n) :
    Q'.abs (2*evenThetaTerm w x (n : Int)) ≤ shellTerm w n := by
  let P := w^(2*(n*n))
  have hP : (0 : Q') ≤ P := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have hterm : Q'.abs (evenThetaTerm w x (n : Int)) ≤ P := by
    change Q'.abs (P*Cheb.T (2*(n : Int)).natAbs x) ≤ P
    exact Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (chebT_abs_le_one _ hx0 hx1) (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
          (TsumDeriv.Q'.abs_of_nonneg hP))))
  have hc : (2 : Q') ≤ 16*Q'.ofNat (n*n*n) := shell_coefficient_le (c := 2) (by
    have h1 := Nat.mul_le_mul hn hn
    have h2 := Nat.mul_le_mul h1 hn
    omega)
  have hp : P ≤ w^(n*n) := HKConvGen.pow_base_antitone
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (by omega)
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  change Q'.abs (2 : Q')*Q'.abs (evenThetaTerm w x (n : Int)) ≤ _
  have htwo : Q'.abs (2 : Q') ≈ 2 := by decide
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ _ htwo)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hterm (by decide)) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hc hP)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
      (Q'.mul_nonneg _ _ (by decide) (ofNat_nonneg _)))

/-- Literal paired endpoint-frequency terms fit the SAME shell. -/
theorem evenPairedEndpoint_shell_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) (hn : 1 ≤ n) :
    Q'.abs (2*evenEndpointTerm w (n : Int)) ≤ shellTerm w n := by
  let P := w^(2*(n*n))
  have hP : (0 : Q') ≤ P := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have hf : (2*(n : Int)).natAbs = 2*n := by
    rw [Int.natAbs_mul]
    rfl
  have hpin : 2*evenEndpointTerm w (n : Int) ≈ Q'.ofNat (8*(n*n))*P := by
    unfold evenEndpointTerm
    rw [hf]
    have hs : (2*n)*(2*n) = 4*(n*n) := by
      calc
        (2*n)*(2*n) = (2*2)*(n*n) := by ac_rfl
        _ = 4*(n*n) := rfl
    rw [hs]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    have hc := Q'.eqv_symm (ofNat_mul_eqv 2 (4*(n*n)))
    have h8 : 2*(4*(n*n)) = 8*(n*n) := by omega
    rw [h8] at hc
    exact Q'.mul_eqv_congr_right _ _ P hc
  have hc : Q'.ofNat (8*(n*n)) ≤ 16*Q'.ofNat (n*n*n) :=
    shell_coefficient_le (by
      have h := square_le_cube n hn
      omega)
  have hp : P ≤ w^(n*n) := HKConvGen.pow_base_antitone
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (by omega)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hpin)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg
    (Q'.mul_nonneg _ _ (ofNat_nonneg _) hP))) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hc hP)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
      (Q'.mul_nonneg _ _ (by decide) (ofNat_nonneg _)))

/-- Explicit SAME cutoff, uniform in the coordinate at the named nome. -/
theorem even_cauchy {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    evenPartial w x m ≤ evenPartial w x n+epsilon ∧
      evenPartial w x n ≤ evenPartial w x m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (evenPartial w x)
    (fun n => 2*evenThetaTerm w x (n : Int)) (evenPartial_step w x)
    (evenPairedTerm_shell_abs_le hw0 hw1 hx0 hx1) epsilon he m n hm hn

theorem evenEndpoint_cauchy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    evenEndpointJet w m ≤ evenEndpointJet w n+epsilon ∧
      evenEndpointJet w n ≤ evenEndpointJet w m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (evenEndpointJet w)
    (fun n => 2*evenEndpointTerm w (n : Int)) (evenEndpointJet_step w)
    (evenPairedEndpoint_shell_abs_le hw0 hw1) epsilon he m n hm hn

/-- No reindexing: the original bilateral prefix is the approximant. -/
def evenCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (evenPartial w x)
    (fun n => 2*evenThetaTerm w x (n : Int)) (evenPartial_step w x)
    (evenPairedTerm_shell_abs_le hw0 hw1 hx0 hx1)

def evenEndpointCReal {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (evenEndpointJet w)
    (fun n => 2*evenEndpointTerm w (n : Int)) (evenEndpointJet_step w)
    (evenPairedEndpoint_shell_abs_le hw0 hw1)

@[simp] theorem evenCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (evenCReal hw0 hw1 hx0 hx1).approx N = evenPartial w x N := rfl

@[simp] theorem evenEndpointCReal_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    (evenEndpointCReal hw0 hw1).approx N = evenEndpointJet w N := rfl

end YMGap.Continuum.ThetaEvenSeriesCompletion

#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenPartial_step
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenEndpointJet_step
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenPairedTerm_shell_abs_le
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenPairedEndpoint_shell_abs_le
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.even_cauchy
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenEndpoint_cauchy
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenCReal
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenEndpointCReal
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenCReal_approx
#print axioms YMGap.Continuum.ThetaEvenSeriesCompletion.evenEndpointCReal_approx
