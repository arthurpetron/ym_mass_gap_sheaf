/-
# A bounded rational cap for the original cube fundamental interval

This file records a small explicit coefficient regime for the already-defined
original cube interval.  It supplies neither a nome-uniform estimate nor a
gain, response, or continuum conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
  (cubeFundamentalDelta)

def alphaCap : Q' := Q'.mkPos 1 512 (by decide)
def deltaCap : Q' := Q'.mkPos 1 32 (by decide)
def baseCap : Q' := Q'.mkPos 257 256 (by decide)

/-- The actual six-face fundamental delta is at most `1/32` whenever its
original first-character coefficient is at most `1/512`. -/
theorem cubeFundamentalDelta_le_cap (w : Q')
    (ha : (0 : Q') ≤ coeffW w 1) (hα : coeffW w 1 ≤ alphaCap) :
    cubeFundamentalDelta w ≤ deltaCap := by
  have hmul : 2 * coeffW w 1 ≤ 2 * alphaCap :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hα (by decide)
  have hbase0 : 1 + 2 * coeffW w 1 ≤ 1 + 2 * alphaCap :=
    Q'.add_le_add_left 1 _ _ hmul
  have hbase : 1 + 2 * coeffW w 1 ≤ baseCap :=
    Q'.le_trans' _ _ _ hbase0 (by decide)
  have htwononneg : (0 : Q') ≤ 2 * coeffW w 1 :=
    Q'.mul_nonneg _ _ (by decide) ha
  have hbaseNonneg : (0 : Q') ≤ 1 + 2 * coeffW w 1 :=
    Q'.zero_le_add _ _ (by decide) htwononneg
  have hpow : (1 + 2 * coeffW w 1)^6 ≤ baseCap^6 :=
    pow_le_pow_base _ _ hbaseNonneg hbase 6
  have hdiff : cubeFundamentalDelta w ≤ baseCap^6 - 1 := by
    unfold cubeFundamentalDelta
    exact Q'.add_le_add_right _ _ (-1) hpow
  exact Q'.le_trans' _ _ _ hdiff (by decide)

/-- The same coefficient cap implies the direct kernel smallness guard `2α≤1`. -/
theorem directKernelGuard_of_coeffW_cap (w : Q')
    (hα : coeffW w 1 ≤ alphaCap) :
    coeffW w 1 * 2 ≤ 1 := by
  have htwice : 2 * coeffW w 1 ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hα (by decide)) (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW w 1) 2)) htwice

/-- An explicit positive nome whose actual coefficient lies in the small-cap
regime; this only demonstrates that the finite guard is inhabited. -/
def smallNome : Q' := Q'.mkPos 1 16 (by decide)

theorem smallNome_pos : (0 : Q') < smallNome := by decide

theorem smallNome_coeff_eq :
    (coeffW smallNome 1).eqv (Q'.mkPos 1 2048 (by decide)) := by
  unfold smallNome coeffW YMGap.Continuum.RGTransport.dimQ
    YMGap.Continuum.RGTransport.c4 YMGap.Continuum.RGTransport.qpow
  decide

theorem smallNome_coeff_nonneg : (0 : Q') ≤ coeffW smallNome 1 := by
  exact Q'.le_trans' _ _ _ (by decide)
    (Q'.ge_of_eqv smallNome_coeff_eq)

theorem smallNome_coeff_le_cap : coeffW smallNome 1 ≤ alphaCap := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv smallNome_coeff_eq) (by decide)

theorem smallNome_delta_le_cap : cubeFundamentalDelta smallNome ≤ deltaCap :=
  cubeFundamentalDelta_le_cap smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap

theorem smallNome_directKernelGuard : coeffW smallNome 1 * 2 ≤ 1 :=
  directKernelGuard_of_coeffW_cap smallNome smallNome_coeff_le_cap

#print axioms alphaCap
#print axioms deltaCap
#print axioms baseCap
#print axioms cubeFundamentalDelta_le_cap
#print axioms directKernelGuard_of_coeffW_cap
#print axioms smallNome
#print axioms smallNome_pos
#print axioms smallNome_coeff_eq
#print axioms smallNome_coeff_nonneg
#print axioms smallNome_coeff_le_cap
#print axioms smallNome_delta_le_cap
#print axioms smallNome_directKernelGuard

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
