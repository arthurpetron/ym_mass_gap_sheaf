/-
# Uniform head comparison for the original finite quartic coefficients

The exceptional spins and all interior bulk spins use one explicit budget.
The cutoff separation and nome guard are displayed, not supplied as a
physical scaling law. This is a finite coefficient and response estimate.
-/

import YMGap.Continuum.SU2HeatQuarticFiniteRegroup
import YMGap.Continuum.SU2HeatQuarticLowCoefficients
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2HeatQuarticHeadComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero coeffW_nonneg)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient
open YMGap.Continuum.SU2HeatQuarticLowCoefficients
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv

theorem relativeBudget_nonnegative {n h : Q'}
    (hn : (0 : Q') ≤ n) (hh : (0 : Q') ≤ h) :
    (0 : Q') ≤ relativeBudget n h := by
  have hn2 := Q'.mul_nonneg n n hn hn
  have hn4 := Q'.mul_nonneg _ _ hn2 hn2
  have hh2 := Q'.mul_nonneg h h hh hh
  have hh4 := Q'.mul_nonneg _ _ hh2 hh2
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hn4) hh4)
    (Q'.mul_nonneg _ _ (by decide) hh2)

theorem relativeBudget_mono {n N h : Q'}
    (hn : (0 : Q') ≤ n) (hnN : n ≤ N) (hh : (0 : Q') ≤ h) :
    relativeBudget n h ≤ relativeBudget N h := by
  have hN := Q'.le_trans' _ _ _ hn hnN
  have hn2 := Q'.mul_nonneg n n hn hn
  have hN2 := Q'.mul_nonneg N N hN hN
  have h2 := Q'.mul_le_mul_of_nonneg hnN hnN hN hn
  have h4 := Q'.mul_le_mul_of_nonneg h2 h2 hN2 hn2
  have hh2 := Q'.mul_nonneg h h hh hh
  have hh4 := Q'.mul_nonneg _ _ hh2 hh2
  exact Q'.add_le_add_right _ _ (296*(h*h))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') h4 (by decide)) hh4)

private theorem lower_half_guard {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L e : Nat) (he : e ≤ 4*L) (hh : (1 : Q') ≤ 2*w^(4*L)) :
    (1 : Q') ≤ 2*w^e := by
  have hp : w^(4*L) ≤ w^e := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (qpow_eqv_pow w (4*L)))
    (Q'.le_trans' _ _ _ (HeatKernelRGStep.qpow_antitone hw0 hw1 e (4*L) he)
      (Q'.le_of_eqv (qpow_eqv_pow w e)))
  exact Q'.le_trans' _ _ _ hh
    (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hp (by decide))

private theorem sixty_le_budget {n h : Q'}
    (hn : (0 : Q') ≤ n) (hh : (0 : Q') ≤ h) :
    60*RingNormaliser.qpow h 2 ≤ relativeBudget n h := by
  have hh2 := Q'.mul_nonneg h h hh hh
  have hp : RingNormaliser.qpow h 2 ≈ h*h :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv h)
  have hn2 := Q'.mul_nonneg n n hn hn
  have htail := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 32)
      (Q'.mul_nonneg _ _ hn2 hn2))
    (Q'.mul_nonneg _ _ hh2 hh2)
  have hlast : 296*(h*h) ≤ relativeBudget n h :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _))
      (Q'.add_le_add_right _ _ _ htail)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hp))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : (60 : Q') ≤ 296) hh2)
      hlast)

/-- ONE budget for every head output, with the actual cutoff coefficients.
The separation `L+1<=K` ensures both neighbours are retained. -/
theorem coefficient_head_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L K : Nat) (hL : 3 ≤ L) (hK : L+1 ≤ K)
    (hhalf : (1 : Q') ≤ 2*w^(4*L)) (j : Nat) (hj : j < L) :
    quarticCoeff (cutCoeff w K) j ≤
      relativeBudget (Q'.ofNat L) (1 + -w) * coeffW w j := by
  have hh := Q'.sub_nonneg_of_le hw1
  match j with
  | 0 =>
      have hz : quarticCoeff (cutCoeff w K) 0 = zeroCoeff w := by
        simp only [quarticCoeff, zeroCoeff, cutCoeff,
          if_pos (show 0 ≤ K by omega), if_pos (show 1 ≤ K by omega),
          if_pos (show 2 ≤ K by omega)]
      rw [hz, coeffW_zero]
      exact Q'.le_trans' _ _ _ (zeroCoeff_le_sixty hw0 hw1)
        (Q'.le_trans' _ _ _ (sixty_le_budget (Q'.ofNat_nonneg L) hh)
          (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  | 1 =>
      have hz : quarticCoeff (cutCoeff w K) 1 = oneCoeff w := by
        simp only [quarticCoeff, oneCoeff, cutCoeff,
          if_pos (show 0 ≤ K by omega), if_pos (show 1 ≤ K by omega),
          if_pos (show 2 ≤ K by omega), if_pos (show 3 ≤ K by omega)]
      rw [hz]
      have h2 : (2 : Q') ≤ Q'.ofNat L :=
        CReal.ofNat_le_ofNat (show 2 ≤ L by omega)
      exact Q'.le_trans' _ _ _
        (oneCoeff_le_relative hw0 hw1 (lower_half_guard hw0 hw1 L 4 (by omega) hhalf))
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (relativeBudget_mono (by decide) h2 hh) (coeffW_nonneg hw0 1))
  | k+2 =>
      rw [quarticCoeff_cut_interior w K k (by omega)]
      have hn : Q'.ofNat (k+3) ≤ Q'.ofNat L :=
        CReal.ofNat_le_ofNat (show k+3 ≤ L by omega)
      exact Q'.le_trans' _ _ _
        (quarticBulkCoeff_le_relative hw0 hw1 k
          (lower_half_guard hw0 hw1 L (4*k+8) (by omega) hhalf))
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (relativeBudget_mono (Q'.ofNat_nonneg _) hn hh) (coeffW_nonneg hw0 _))

private theorem sum_le_bounded (f g : Nat → Q') :
    ∀ N, (∀ j, j < N → f j ≤ g j) → finSum f N ≤ finSum g N
  | 0, _ => Q'.le_refl' _
  | N+1, h => Q'.add_le_add (sum_le_bounded f g N (fun j hj => h j (by omega)))
      (h N (by omega))

/-- The head is paid by the SAME complete heat response. Nonnegativity of
the responses is spectral and must be supplied by the actual kernel. -/
theorem head_response_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L K : Nat) (hL : 3 ≤ L) (hK : L+1 ≤ K)
    (hhalf : (1 : Q') ≤ 2*w^(4*L))
    (Gamma : Nat → Q') (hGamma : ∀ j, (0 : Q') ≤ Gamma j) :
    finSum (fun j => quarticCoeff (cutCoeff w K) j * Gamma j) L ≤
      relativeBudget (Q'.ofNat L) (1 + -w) *
        finSum (fun j => coeffW w j * Gamma j) (K+1) := by
  let C := relativeBudget (Q'.ofNat L) (1 + -w)
  have hC : (0 : Q') ≤ C := relativeBudget_nonnegative
    (Q'.ofNat_nonneg L) (Q'.sub_nonneg_of_le hw1)
  have hs := sum_le_bounded
    (fun j => quarticCoeff (cutCoeff w K) j * Gamma j)
    (fun j => C * (coeffW w j * Gamma j)) L (fun j hj =>
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (coefficient_head_bound hw0 hw1 L K hL hK hhalf j hj) (hGamma j))
        (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))
  have hpad := finSum_monotone_of_nonneg (fun j => coeffW w j * Gamma j)
    (fun j => Q'.mul_nonneg _ _ (coeffW_nonneg hw0 j) (hGamma j)) L (K+1) (by omega)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (const_mul_finSum _ C L))
      (Q'.mul_le_mul_of_nonneg_left _ _ C hpad hC))

#print axioms relativeBudget_nonnegative
#print axioms relativeBudget_mono
#print axioms coefficient_head_bound
#print axioms head_response_bound

end YMGap.Continuum.SU2HeatQuarticHeadComparison
