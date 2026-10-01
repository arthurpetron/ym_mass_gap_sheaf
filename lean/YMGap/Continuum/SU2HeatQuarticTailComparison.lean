/-
# High-output-spin scalar comparison for the finite quartic heat expansion

All coefficients are the original zero-extended finite heat coefficients.
This file estimates only the high output labels; it does not supply an
interacting variance comparison or a physical scaling law.
-/

import YMGap.Continuum.SU2HeatQuarticFiniteRegroup
import YMGap.Continuum.SU2HeatDimensionBlockTail
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatQuarticTailComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CReal
open YMGap.Continuum.RGTransport (dimQ c4 qpow)
open YMGap.Continuum.RGTransport (dimQ_nonneg)
open YMGap.Continuum.HeatKernelRGStep (ofNat_mul_eqv)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)
open YMGap.Continuum.BondMovingScaledNorm (tailTerm tailTerm_nonneg)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatDimensionBlockTail
open YMGap.Continuum.FiveHolonomyPerronCutoff (finSum_split)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem cutCoeff_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (K j : Nat) : (0 : Q') ≤ cutCoeff w K j := by
  by_cases hj : j ≤ K
  · simp only [cutCoeff, if_pos hj]
    exact coeffW_nonneg hw j
  · simp only [cutCoeff, if_neg hj]
    exact Q'.le_refl' 0

private theorem cutCoeff_le_raw {w : Q'} (hw : (0 : Q') ≤ w)
    (K j : Nat) : cutCoeff w K j ≤ coeffW w j := by
  by_cases hj : j ≤ K
  · simp only [cutCoeff, if_pos hj]
    exact Q'.le_refl' _
  · simp only [cutCoeff, if_neg hj]
    exact coeffW_nonneg hw j

/-- The negative off-diagonal coefficients may be dropped only after a
nonnegative response has been supplied.  This preliminary scalar order is
for a single output spin `k+2`, including the upper cutoff edge. -/
private theorem quarticCoeff_upper {a : Nat → Q'}
    (ha : ∀ j, (0 : Q') ≤ a j) (k : Nat) :
    quarticCoeff a (k+2) ≤ a k + 6*a (k+2) + a (k+4) := by
  have hsum : (0 : Q') ≤ a (k+1) + a (k+3) :=
    Q'.zero_le_add _ _ (ha _) (ha _)
  have hneg : -(4*(a (k+1)+a (k+3))) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.neg_le_neg (Q'.mul_nonneg _ _ (by decide) hsum))
      (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
  have hdrop := Q'.add_le_add_left (6*a (k+2)) _ _ hneg
  have hdrop2 := Q'.add_le_add_right _ _ (a k) hdrop
  have hdrop3 := Q'.add_le_add_right _ _ (a (k+4)) hdrop2
  have hnormal : (((6*a (k+2)+0)+a k)+a (k+4)) ≈
      a k + 6*a (k+2) + a (k+4) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.const 6) (.var 1)) (.const 0)) (.var 0)) (.var 2))
      (.add (.add (.var 0) (.mul (.const 6) (.var 1))) (.var 2))
      (by decide) (fun | 0 => a k | 1 => a (k+2) | _ => a (k+4))
  exact Q'.le_trans' _ _ _ hdrop3 (Q'.le_of_eqv hnormal)

private theorem cutCoeff_dim_le_tail {w : Q'} (hw : (0 : Q') ≤ w)
    (K s j : Nat) (C : Q') (hcap : dimQ j ≤ C * dimQ s) :
    cutCoeff w K s * dimQ j ≤ C * tailTerm w 2 s := by
  have hsource := cutCoeff_le_raw hw K s
  have hfirst : cutCoeff w K s * dimQ j ≤ coeffW w s * dimQ j :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsource (dimQ_nonneg j)
  have hsecond : coeffW w s * dimQ j ≤ coeffW w s * (C * dimQ s) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcap (coeffW_nonneg hw s)
  have hpin : coeffW w s * (C * dimQ s) ≈ C * tailTerm w 2 s := by
    unfold coeffW dimQ tailTerm
    have hsquare : Q'.ofNat (s+1) * Q'.ofNat (s+1) ≈
        Q'.ofNat ((s+1)^2) := by
      rw [Nat.pow_succ, Nat.pow_one]
      change Q'.ofNat (s+1) * Q'.ofNat (s+1) ≈
        Q'.ofNat ((s+1)*(s+1))
      exact Q'.eqv_symm (ofNat_mul_eqv _ _)
    have hring : (Q'.ofNat (s+1) * qpow w (c4 s)) *
        (C * Q'.ofNat (s+1)) ≈
        C * ((Q'.ofNat (s+1) * Q'.ofNat (s+1)) * qpow w (c4 s)) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 0)))
        (.mul (.var 2) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
        (by decide) (fun | 0 => Q'.ofNat (s+1) | 1 => qpow w (c4 s) | _ => C)
    exact Q'.eqv_trans _ _ _ hring
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hsquare))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hpin))

private theorem high_dim_left (k : Nat) :
    dimQ (k+2) ≤ 3 * dimQ k := by
  unfold dimQ
  have hn : k+2+1 ≤ 3*(k+1) := by omega
  exact Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hn)
    (Q'.le_of_eqv (ofNat_mul_eqv 3 (k+1)))

private theorem high_dim_right (k : Nat) :
    dimQ (k+2) ≤ dimQ (k+4) := by
  unfold dimQ
  exact CReal.ofNat_le_ofNat (by omega)

private theorem high_left_term {w : Q'} (hw : (0 : Q') ≤ w)
    (K k : Nat) :
    cutCoeff w K k * dimQ (k+2) ≤ 3 * tailTerm w 2 k :=
  cutCoeff_dim_le_tail hw K k (k+2) 3 (high_dim_left k)

private theorem high_center_term {w : Q'} (hw : (0 : Q') ≤ w)
    (K k : Nat) :
    cutCoeff w K (k+2) * dimQ (k+2) ≤ tailTerm w 2 (k+2) := by
  have h := cutCoeff_dim_le_tail hw K (k+2) (k+2) 1
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem high_right_term {w : Q'} (hw : (0 : Q') ≤ w)
    (K k : Nat) :
    cutCoeff w K (k+4) * dimQ (k+2) ≤ tailTerm w 2 (k+4) := by
  have h := cutCoeff_dim_le_tail hw K (k+4) (k+2) 1
    (Q'.le_trans' _ _ _ (high_dim_right k)
      (Q'.ge_of_eqv (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

private def positiveCoeff (a : Nat → Q') (k : Nat) : Q' :=
  a k + 6*a (k+2) + a (k+4)

private theorem positiveCoeff_nonnegative {a : Nat → Q'}
    (ha : ∀ j, (0 : Q') ≤ a j) (k : Nat) :
    (0 : Q') ≤ positiveCoeff a k := by
  unfold positiveCoeff
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (ha k)
      (Q'.mul_nonneg _ _ (by decide) (ha (k+2))))
    (ha (k+4))

private theorem positiveCoeff_dim_bound {w : Q'} (hw : (0 : Q') ≤ w)
    (K k : Nat) :
    positiveCoeff (cutCoeff w K) k * dimQ (k+2) ≤
      3*tailTerm w 2 k + 6*tailTerm w 2 (k+2) +
        tailTerm w 2 (k+4) := by
  have hleft := high_left_term hw K k
  have hcenter := high_center_term hw K k
  have hright := high_right_term hw K k
  have hcenter6 : 6*(cutCoeff w K (k+2)*dimQ (k+2)) ≤
      6*tailTerm w 2 (k+2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcenter (by decide)
  have hsum :
      cutCoeff w K k*dimQ (k+2) +
        6*(cutCoeff w K (k+2)*dimQ (k+2)) +
          cutCoeff w K (k+4)*dimQ (k+2) ≤
      3*tailTerm w 2 k + 6*tailTerm w 2 (k+2) +
        tailTerm w 2 (k+4) :=
    Q'.add_le_add
      (Q'.add_le_add hleft hcenter6) hright
  have hpin : positiveCoeff (cutCoeff w K) k * dimQ (k+2) ≈
      cutCoeff w K k*dimQ (k+2) +
        6*(cutCoeff w K (k+2)*dimQ (k+2)) +
          cutCoeff w K (k+4)*dimQ (k+2) := by
    unfold positiveCoeff
    exact poly_identity_of_normal_eq
      (.mul (.add (.add (.var 0) (.mul (.const 6) (.var 1))) (.var 2)) (.var 3))
      (.add (.add (.mul (.var 0) (.var 3))
        (.mul (.const 6) (.mul (.var 1) (.var 3))))
        (.mul (.var 2) (.var 3)))
      (by decide)
      (fun | 0 => cutCoeff w K k | 1 => cutCoeff w K (k+2)
           | 2 => cutCoeff w K (k+4) | _ => dimQ (k+2))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hsum

private theorem high_response_term {w : Q'} (hw : (0 : Q') ≤ w)
    (K k : Nat) (Gamma : Nat → Q') (J : Q')
    (hGamma0 : ∀ j, (0 : Q') ≤ Gamma j)
    (hGammaCap : ∀ j, Gamma j ≤ dimQ j * J)
    (hJ : (0 : Q') ≤ J) :
    quarticCoeff (cutCoeff w K) (k+2) * Gamma (k+2) ≤
      (3*tailTerm w 2 k + 6*tailTerm w 2 (k+2) +
        tailTerm w 2 (k+4)) * J := by
  have ha : ∀ j, (0 : Q') ≤ cutCoeff w K j :=
    cutCoeff_nonnegative hw K
  have hdrop := quarticCoeff_upper ha k
  have hfirst : quarticCoeff (cutCoeff w K) (k+2) * Gamma (k+2) ≤
      positiveCoeff (cutCoeff w K) k * Gamma (k+2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdrop (hGamma0 _)
  have hsecond : positiveCoeff (cutCoeff w K) k * Gamma (k+2) ≤
      positiveCoeff (cutCoeff w K) k * (dimQ (k+2)*J) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (hGammaCap _) (positiveCoeff_nonnegative ha k)
  have hthird := Q'.mul_le_mul_of_nonneg_right _ _ _
    (positiveCoeff_dim_bound hw K k) hJ
  have hmul : positiveCoeff (cutCoeff w K) k * (dimQ (k+2)*J) ≈
      (positiveCoeff (cutCoeff w K) k * dimQ (k+2))*J :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmul) hthird))

private theorem finSum_nonnegative_local (f : Nat → Q')
    (hf : ∀ j, (0 : Q') ≤ f j) : ∀ N, (0 : Q') ≤ finSum f N
  | 0 => Q'.le_refl' 0
  | N+1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (finSum_nonnegative_local f hf N) (hf N)

private theorem shifted_tail_le_window {w : Q'} (hw : (0 : Q') ≤ w)
    (S N d : Nat) (hd : d ≤ 4) :
    finSum (fun t => tailTerm w 2 (S+(d+t))) N ≤
      dimensionTail w S (N+4) := by
  let f : Nat → Q' := fun t => tailTerm w 2 (S+t)
  have hf : ∀ t, (0 : Q') ≤ f t :=
    fun t => tailTerm_nonneg hw 2 (S+t)
  have hp := FiveHolonomyPerronCutoff.finSum_split f d N
  have hprefix := finSum_nonnegative_local f hf d
  have hfirst : finSum (fun t => f (d+t)) N ≤ finSum f (d+N) := by
    have hplus := Q'.add_le_self_of_nonneg
      (finSum (fun t => f (d+t)) N) (finSum f d) hprefix
    exact Q'.le_trans' _ _ _ hplus
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
        (Q'.le_of_eqv (Q'.eqv_symm hp)))
  have hsecond : finSum f (d+N) ≤ finSum f (N+4) :=
    finSum_monotone_of_nonneg f hf (d+N) (N+4) (by omega)
  exact Q'.le_trans' _ _ _ hfirst hsecond

private theorem finSum_three_scaled (A B C : Nat → Q') (J : Q') (N : Nat) :
    finSum (fun t => (3*A t + 6*B t + C t)*J) N ≈
      (3*finSum A N + 6*finSum B N + finSum C N)*J := by
  have hadd1 := finSum_add
    (fun t => 3*A t + 6*B t) C N
  have hadd2 := finSum_add
    (fun t => 3*A t) (fun t => 6*B t) N
  have h3 := Q'.eqv_symm (const_mul_finSum A 3 N)
  have h6 := Q'.eqv_symm (const_mul_finSum B 6 N)
  have hsum1 : finSum (fun t => 3*A t + 6*B t + C t) N ≈
      finSum (fun t => 3*A t) N + finSum (fun t => 6*B t) N +
        finSum C N :=
    Q'.eqv_trans _ _ _ hadd1
      (Q'.add_eqv_congr_right _ _ _ hadd2)
  have hsum2 : finSum (fun t => 3*A t) N +
        finSum (fun t => 6*B t) N + finSum C N ≈
      3*finSum A N + 6*finSum B N + finSum C N :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ h3)
        (Q'.add_eqv_congr_left _ _ _ h6))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (finSum_mul_const
      (fun t => 3*A t + 6*B t + C t) J N))
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ hsum1 hsum2))

private theorem high_response_window {w : Q'} (hw : (0 : Q') ≤ w)
    (S K N : Nat) (Gamma : Nat → Q') (J : Q')
    (hGamma0 : ∀ j, (0 : Q') ≤ Gamma j)
    (hGammaCap : ∀ j, Gamma j ≤ dimQ j * J)
    (hJ : (0 : Q') ≤ J) :
    finSum (fun t => quarticCoeff (cutCoeff w K) (S+t+2) *
      Gamma (S+t+2)) N ≤
      10 * dimensionTail w S (N+4) * J := by
  let T : Nat → Q' := fun d =>
    finSum (fun t => tailTerm w 2 (S+(d+t))) N
  have hsum : finSum (fun t => quarticCoeff (cutCoeff w K) (S+t+2) *
        Gamma (S+t+2)) N ≤
      finSum (fun t =>
        (3*tailTerm w 2 (S+t) +
          6*tailTerm w 2 (S+t+2) +
          tailTerm w 2 (S+t+4)) * J) N :=
    YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise _ _
      (fun t => high_response_term hw K (S+t) Gamma J
        hGamma0 hGammaCap hJ) N
  have h0 : T 0 ≤ dimensionTail w S (N+4) :=
    shifted_tail_le_window hw S N 0 (by decide)
  have h2 : T 2 ≤ dimensionTail w S (N+4) :=
    shifted_tail_le_window hw S N 2 (by decide)
  have h4 : T 4 ≤ dimensionTail w S (N+4) :=
    shifted_tail_le_window hw S N 4 (by decide)
  have hweighted : 3*T 0 + 6*T 2 + T 4 ≤
      10*dimensionTail w S (N+4) := by
    have h0' := Q'.mul_le_mul_of_nonneg_left _ _ _ h0 (by decide : (0:Q')≤3)
    have h2' := Q'.mul_le_mul_of_nonneg_left _ _ _ h2 (by decide : (0:Q')≤6)
    have hsum' := Q'.add_le_add (Q'.add_le_add h0' h2') h4
    have hpin : 3*dimensionTail w S (N+4) +
        6*dimensionTail w S (N+4) + dimensionTail w S (N+4) ≈
        10*dimensionTail w S (N+4) :=
      poly_identity_of_normal_eq
        (.add (.add (.mul (.const 3) (.var 0))
          (.mul (.const 6) (.var 0))) (.var 0))
        (.mul (.const 10) (.var 0)) (by decide)
        (fun _ => dimensionTail w S (N+4))
    exact Q'.le_trans' _ _ _ hsum' (Q'.le_of_eqv hpin)
  have hsumPin : finSum (fun t =>
        (3*tailTerm w 2 (S+t) +
          6*tailTerm w 2 (S+t+2) +
          tailTerm w 2 (S+t+4)) * J) N ≈
      (3*T 0 + 6*T 2 + T 4)*J := by
    let A : Nat → Q' := fun t => tailTerm w 2 (S+t)
    let B : Nat → Q' := fun t => tailTerm w 2 (S+(2+t))
    let C : Nat → Q' := fun t => tailTerm w 2 (S+(4+t))
    have hindex : ∀ t,
        S+t+2 = S+(2+t) ∧ S+t+4 = S+(4+t) := by
      intro t
      constructor <;> omega
    have hreindex : finSum (fun t =>
        (3*tailTerm w 2 (S+t) +
          6*tailTerm w 2 (S+t+2) +
          tailTerm w 2 (S+t+4)) * J) N ≈
        finSum (fun t => (3*A t + 6*B t + C t)*J) N :=
      finSum_eqv_congr _ _
        (fun t => by
          rw [(hindex t).1, (hindex t).2]
          exact Q'.eqv_refl _) N
    have hscaled : finSum (fun t => (3*A t + 6*B t + C t)*J) N ≈
        (3*T 0 + 6*T 2 + T 4)*J := by
      have hA : (fun t => tailTerm w 2 (S+(0+t))) = A := by
        funext t
        dsimp [A]
        rw [Nat.zero_add]
      have hT0 : T 0 = finSum A N := by
        change finSum (fun t => tailTerm w 2 (S+(0+t))) N = finSum A N
        rw [hA]
      have hT2 : T 2 = finSum B N := rfl
      have hT4 : T 4 = finSum C N := rfl
      rw [hT0, hT2, hT4]
      exact finSum_three_scaled A B C J N
    exact Q'.eqv_trans _ _ _ hreindex hscaled
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsumPin)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hweighted hJ))

/-- A finite high-output-spin tail of the exact zero-extended quartic heat
coefficients.  `Gamma` is a nonnegative character response bounded by the
dimension times the original uninserted source mass `J`; those two inputs
are intentionally kept explicit here.  The estimate does not assert either
input for a particular physical source. -/
theorem high_response_tail_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (S K N : Nat) (hS : 1 ≤ S)
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide))
    (Gamma : Nat → Q') (J : Q')
    (hGamma0 : ∀ j, (0 : Q') ≤ Gamma j)
    (hGammaCap : ∀ j, Gamma j ≤ dimQ j * J)
    (hJ : (0 : Q') ≤ J) :
    finSum (fun t => quarticCoeff (cutCoeff w K) (S+t+2) *
      Gamma (S+t+2)) N ≤
      80 * Q'.ofNat (S^3) * qpow w (S*S) * J := by
  have hwindow := high_response_window hw0 S K N Gamma J
    hGamma0 hGammaCap hJ
  have hblocks := dimensionTail_le_eight_blocks hw0 hw1 S hS hq (N+4)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hblocks
    (by decide : (0:Q')≤10)
  have hscaledJ := Q'.mul_le_mul_of_nonneg_right _ _ _ hscaled hJ
  have hpin : 10 * (8 * Q'.ofNat (S^3) * qpow w (S*S)) * J ≈
      80 * Q'.ofNat (S^3) * qpow w (S*S) * J :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 10)
        (.mul (.mul (.const 8) (.var 0)) (.var 1))) (.var 2))
      (.mul (.mul (.mul (.const 80) (.var 0)) (.var 1)) (.var 2))
      (by decide)
      (fun | 0 => Q'.ofNat (S^3) | 1 => qpow w (S*S) | _ => J)
  exact Q'.le_trans' _ _ _ hwindow
    (Q'.le_trans' _ _ _ hscaledJ (Q'.le_of_eqv hpin))

end YMGap.Continuum.SU2HeatQuarticTailComparison

#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.quarticCoeff_upper
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.cutCoeff_dim_le_tail
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_left_term
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_center_term
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_right_term
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_response_term
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.finSum_nonnegative_local
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.shifted_tail_le_window
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.finSum_three_scaled
#print axioms YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_response_window
#print axioms YMGap.Continuum.SU2HeatQuarticTailComparison.high_response_tail_bound
