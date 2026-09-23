/-
# Cutoff-independent polynomial heat-prefix budgets

The quartic heat-prefix estimate extends uniformly to every fixed polynomial
degree `m`.  The budget is explicit and depends on the strict upper nome, but
not on the representation cutoff.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.SU2HeatPolynomialPrefixBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv

/-- Gain forcing `2^m` times the eventual ratio below one half. -/
def gainTarget (m : Nat) : Q' := HKConv.divPos 1 (Q'.ofNat (2 * 2^m))

def labelCutoff (W : Q') (m : Nat) : Nat := powBaseCutoff W (gainTarget m)

theorem gainTarget_positive (m : Nat) : (0 : Q') < gainTarget m :=
  HKConv.divPos_pos (by decide)

private theorem gain_scaled (m : Nat) :
    Q'.ofNat (2^m) * gainTarget m ≈ HalfPow.half := by
  let A := Q'.ofNat (2^m)
  let D := Q'.ofNat (2 * 2^m)
  have hDnum : 0 < D.num := by
    change (0 : Int) < Int.ofNat (2 * 2^m)
    exact Int.ofNat_lt.mpr (Nat.mul_pos (by decide) (Nat.two_pow_pos m))
  have hcancel : gainTarget m * D ≈ (1 : Q') := by
    exact HKConv.divPos_mul_eqv hDnum
  have hD : D ≈ 2 * A := by
    exact Q'.eqv_trans _ _ _ (ofNat_mul_eqv 2 (2^m)) (Q'.eqv_refl _)
  have hleft : 2 * (A * gainTarget m) ≈ 1 := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.var 1) (.mul (.const 2) (.var 0)))
        (by decide) (fun n => if n = 0 then A else gainTarget m))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hD)) hcancel)
  have hright : 2 * HalfPow.half ≈ (1 : Q') := by decide
  exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos 1)
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))

theorem ratio_le_half {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q'))
    (m : Nat) :
    Q'.ofNat (2^m) * qpow W (2*labelCutoff W m+3) ≤ HalfPow.half := by
  have hp := Q'.le_trans' _ _ _
    (qpow_antitone (Q'.le_of_lt hW0) (Q'.le_of_lt hW1)
      (labelCutoff W m) (2*labelCutoff W m+3) (by omega))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow W (labelCutoff W m)))
      (pow_base_le_cutoff hW0 hW1 (gainTarget_positive m)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (Q'.ofNat_nonneg _))
    (Q'.le_of_eqv (gain_scaled m))

theorem shifted_geometric {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q'))
    (m k : Nat) :
    tailTerm W m (labelCutoff W m+k) ≤
      tailTerm W m (labelCutoff W m)*HalfPow.half^k := by
  refine CharacterTail.geom_dom (fun i => tailTerm W m (labelCutoff W m+i))
    (tailTerm W m (labelCutoff W m)) HalfPow.half HalfPow.half_nonneg
    (Q'.le_refl' _) ?_ k
  intro j
  dsimp only
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _
    (tailTerm_ratio_gen (Q'.le_of_lt hW0) (Q'.le_of_lt hW1) m
      (labelCutoff W m) _ (by omega))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_le_half hW0 hW1 m)
      (tailTerm_nonneg (Q'.le_of_lt hW0) m _))

def tailBudget (W : Q') (m : Nat) : Q' :=
  geoTailBase (tailTerm W m (labelCutoff W m)) HalfPow.half 0

def prefixBudget (W : Q') (m : Nat) : Q' :=
  finSum (tailTerm W m) (labelCutoff W m) + tailBudget W m

theorem tailBudget_nonnegative {W : Q'} (hW0 : (0 : Q') < W) (m : Nat) :
    (0 : Q') ≤ tailBudget W m :=
  geoTailBase_nonneg (tailTerm_nonneg (Q'.le_of_lt hW0) m _) HalfPow.half_nonneg 0

theorem shifted_sum_bound {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q'))
    (m L : Nat) :
    finSum (fun i => tailTerm W m (labelCutoff W m+i)) L ≤ tailBudget W m :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ (shifted_geometric hW0 hW1 m) L)
    (by simpa only [Nat.zero_add, geoIncrBase] using
      (geoTailBase_series_le (tailTerm_nonneg (Q'.le_of_lt hW0) m (labelCutoff W m))
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0 L))

theorem prefix_bound {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q'))
    (m K : Nat) :
    finSum (tailTerm W m) K ≤ prefixBudget W m := by
  by_cases hK : K ≤ labelCutoff W m
  · exact Q'.le_trans' _ _ _
      (finSum_monotone_of_nonneg _ (tailTerm_nonneg (Q'.le_of_lt hW0) m) _ _ hK)
      (Q'.add_le_self_of_nonneg _ _ (tailBudget_nonnegative hW0 m))
  · have he : labelCutoff W m + (K-labelCutoff W m) = K := Nat.add_sub_of_le (by omega)
    have hs := finSum_split (tailTerm W m) (labelCutoff W m) (K-labelCutoff W m)
    rw [he] at hs
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
      (Q'.add_le_add_left _ _ _ (shifted_sum_bound hW0 hW1 m _))

theorem prefixBudget_nonnegative {W : Q'} (hW0 : (0 : Q') < W) (m : Nat) :
    (0 : Q') ≤ prefixBudget W m :=
  Q'.zero_le_add _ _
    (finSum_monotone_of_nonneg _ (tailTerm_nonneg (Q'.le_of_lt hW0) m)
      0 _ (Nat.zero_le _))
    (tailBudget_nonnegative hW0 m)

end YMGap.Continuum.SU2HeatPolynomialPrefixBound

#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.gainTarget
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.gainTarget_positive
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.labelCutoff
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.ratio_le_half
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.shifted_geometric
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.tailBudget
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.prefixBudget
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.tailBudget_nonnegative
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.shifted_sum_bound
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.prefix_bound
#print axioms YMGap.Continuum.SU2HeatPolynomialPrefixBound.prefixBudget_nonnegative
