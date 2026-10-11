/-
# Computed finite selected-entropy error budget

The all-occurrence count L and selected-occurrence count F remain separate.
For k=activeFactorCount(q)-1, the actual finite coefficient
256*(1-q)*(L+3*k*F) is bounded by the computed natural budget 256*L+768*k*F.
Its inverse-successor remainder is paid at an explicit q/L/F/epsilon rate.

Only 0<q<1 is needed; no active-block lower bound, density division,
logarithmic assumption or physical calibration enters. The zero-count case
is included without a positive-budget premise. This is finite error payment,
not a conditional logarithmic or source-relative response estimate.
-/

import YMGap.Continuum.RegularizedLogPolynomial
import YMGap.Continuum.SU2HeatJacobiActiveFactorCount
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.BF4SelectedEntropyBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.RegularizedLogPolynomial (modulus)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (rho : Nat → Q') : RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

/-- Computable budget with all-factor and selected-factor costs kept distinct. -/
def errorBudget (q : Q') (L F : Nat) : Nat :=
  256*L+768*(activeFactorCount q-1)*F

theorem errorBudget_ofNat (q : Q') (L F : Nat) :
    Q'.ofNat (errorBudget q L F) ≈
      256*Q'.ofNat L+768*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F :=
  tc (Q'.ofNat_add_eqv _ _)
    (Q'.add_eqv_congr' (ClusterCount.ofNat_mul_eqv 256 L)
      (tc (ClusterCount.ofNat_mul_eqv (768*(activeFactorCount q-1)) F)
        (Q'.mul_eqv_congr_right _ _ _ (ClusterCount.ofNat_mul_eqv 768 (activeFactorCount q-1)))))

theorem error_coefficient_nonnegative {q : Q'} (hq1 : q < (1 : Q')) (L F : Nat) :
    (0 : Q') ≤ (256*(1-q))*(Q'.ofNat L+
      3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F) :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (HKPos.one_sub_pos hq1)))
    (Q'.zero_le_add _ _ (ClusterCount.ofNat_nonneg L)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) (ClusterCount.ofNat_nonneg _))
        (ClusterCount.ofNat_nonneg F)))

/-- The original finite coefficient is below its actual natural budget.
No near-unit-nome or nonzero-count premise is needed. -/
theorem error_coefficient_le {q : Q'} (hq0 : (0 : Q') < q)
    (_hq1 : q < (1 : Q')) (L F : Nat) :
    (256*(1-q))*(Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F) ≤
      Q'.ofNat (errorBudget q L F) := by
  have hg1 : 1-q ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hq0)))
    (Q'.le_of_eqv (by decide : (1 : Q')+ -(0 : Q') ≈ 1))
  have hn : (0 : Q') ≤ Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F :=
    Q'.zero_le_add _ _ (ClusterCount.ofNat_nonneg L)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) (ClusterCount.ofNat_nonneg _))
        (ClusterCount.ofNat_nonneg F))
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (256 : Q')
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hg1 hn) (by decide)
  have hp : (256 : Q')*(1*(Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F)) ≈
      Q'.ofNat (errorBudget q L F) :=
    tc (qr (256*(1*(.var 0+3*.var 1*.var 2))) (256*.var 0+768*.var 1*.var 2)
      (by decide) (fun | 0 => Q'.ofNat L | 1 => Q'.ofNat (activeFactorCount q-1) | _ => Q'.ofNat F))
      (Q'.eqv_symm (errorBudget_ofNat q L F))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hp))

/-- Computed rate, retaining an entropy degree of at least one. -/
def errorRate (q : Q') (L F : Nat) (epsilon : Q') : Nat :=
  max 1 (modulus (epsilon*Q'.invSucc (errorBudget q L F)))

theorem errorRate_one_le (q : Q') (L F : Nat) (epsilon : Q') :
    1 ≤ errorRate q L F epsilon := Nat.le_max_left _ _

/-- The actual finite selected-entropy remainder is at most epsilon after
the computed rate. This includes L=F=0 and makes no positive-budget division. -/
theorem error_bound {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (L F : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (N : Nat)
    (hN : errorRate q L F epsilon ≤ N) :
    ((256*(1-q))*(Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F))*
      Q'.invSucc N ≤ epsilon := by
  let A := errorBudget q L F
  let delta := epsilon*Q'.invSucc A
  have hd : (0 : Q') < delta := Q'.mul_pos he (Q'.invSucc_pos A)
  have hNm : modulus delta ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hinv := Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hNm)
    (HalfPow.invSucc_den_le delta hd)
  have hA0 := ClusterCount.ofNat_nonneg A
  have hA1 : Q'.ofNat A*Q'.invSucc A ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (ClusterCount.ofNat_le_ofNat (Nat.le_succ A)) (Q'.invSucc_nonneg A))
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc A))
  have heps : Q'.ofNat A*delta ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qr (.var 0*(.var 1*.var 2)) (.var 1*(.var 0*.var 2))
      (by decide) (fun | 0 => Q'.ofNat A | 1 => epsilon | _ => Q'.invSucc A)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hA1 (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.mul_one_eqv epsilon)))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (error_coefficient_le hq0 hq1 L F) (Q'.invSucc_nonneg N))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hinv hA0) heps)

end YMGap.Continuum.BF4SelectedEntropyBudget

#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.errorBudget
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.errorBudget_ofNat
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.error_coefficient_nonnegative
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.error_coefficient_le
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.errorRate
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.errorRate_one_le
#print axioms YMGap.Continuum.BF4SelectedEntropyBudget.error_bound
