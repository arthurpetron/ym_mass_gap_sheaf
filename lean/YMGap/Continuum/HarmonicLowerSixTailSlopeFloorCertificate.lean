/-
# Exact lower-six next-slope-floor certificate

The generated integer polynomial is `2520 * L1NUM`.  Two homogeneous
tensor-Bernstein tables prove it nonnegative on the two projective charts
covering the production corridor.  All table signs and both substituted
polynomial identities are closed kernel computations.
-/

import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateBlocks
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateBlocks
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate

local infix:50 " ≈ " => Q'.eqv

private def twoVariableEnvironment (D N : Q') : Nat → Q'
  | 0 => D
  | 1 => N
  | _ => 0

/-- The transparent cleared integer polynomial `2520 * L1NUM`. -/
def lowerSixTailNextSlopeFloorCleared (D N : Q') : Q' :=
  RingNormaliser.eval (twoVariableEnvironment D N)
    lowerSixTailNextSlopeFloorClearedExpr

private theorem ringQpow_pos (x : Q') (hx : (0 : Q') < x) : ∀ n,
    (0 : Q') < RingNormaliser.qpow x n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n + 1 => Q'.mul_pos (ringQpow_pos x hx n) hx

private theorem chartA_blocks_physical_identity :
    fastNormalize lowerSixTailSlopeFloorChartABlockPhysicalSumExpr =
      fastNormalize lowerSixTailSlopeFloorChartAPhysicalExpr := by
  rfl

private theorem chartB_blocks_physical_identity :
    fastNormalize lowerSixTailSlopeFloorChartBBlockPhysicalSumExpr =
      fastNormalize lowerSixTailSlopeFloorChartBPhysicalExpr := by
  rfl

/-- Chart A certificate: `64 ≤ N` and `N² ≤ D ≤ 2N²`. -/
theorem lowerSixTailNextSlopeFloorCleared_nonnegative_chartA
    {D N : Q'}
    (hNpos : (0 : Q') < N)
    (h64 : Q'.ofNat 64 ≤ N)
    (hN2D : N * N ≤ D)
    (hD2N2 : D ≤ Q'.ofNat 2 * (N * N)) :
    (0 : Q') ≤ lowerSixTailNextSlopeFloorCleared D N := by
  let rho := twoVariableEnvironment D N
  have hcoordinates : ∀ i,
      (0 : Q') ≤ RingNormaliser.eval rho
        (lowerSixTailSlopeFloorChartASubstitution i) := by
    intro i
    rcases i with _ | i
    · change (0 : Q') ≤ Q'.ofInt 64
      decide
    · rcases i with _ | i
      · change (0 : Q') ≤ N + -(Q'.ofInt 64)
        exact Q'.sub_nonneg_of_le h64
      · rcases i with _ | i
        · change (0 : Q') ≤ D + -(N * N)
          exact Q'.sub_nonneg_of_le hN2D
        · rcases i with _ | i
          · change (0 : Q') ≤ Q'.ofInt 2 * (N * N) + -D
            exact Q'.sub_nonneg_of_le hD2N2
          · change (0 : Q') ≤ Q'.ofInt 0
            exact Q'.le_refl' 0
  have block_nonnegative
      (startRow : Nat) (rows : List (List Int))
      (physical : RingNormaliser.PolyExpr)
      (hrows : IntegerRowsNonnegative rows = true)
      (hidentity :
        fastNormalize
            (substitute lowerSixTailSlopeFloorChartASubstitution
              (homogeneousTensorBlockExpr 15 8 startRow rows)) =
          fastNormalize physical) :
      (0 : Q') ≤ RingNormaliser.eval rho physical :=
    physical_nonnegative_of_homogeneous_block_rows_certificate
      15 8 startRow rows rho lowerSixTailSlopeFloorChartASubstitution
      physical hcoordinates hrows hidentity
  have h0 := block_nonnegative 0
    lowerSixTailSlopeFloorChartABlock0Rows
    lowerSixTailSlopeFloorChartABlock0PhysicalExpr
    chartABlock0_coefficients_nonnegative chartABlock0_physical_identity
  have h1 := block_nonnegative 2
    lowerSixTailSlopeFloorChartABlock1Rows
    lowerSixTailSlopeFloorChartABlock1PhysicalExpr
    chartABlock1_coefficients_nonnegative chartABlock1_physical_identity
  have h2 := block_nonnegative 4
    lowerSixTailSlopeFloorChartABlock2Rows
    lowerSixTailSlopeFloorChartABlock2PhysicalExpr
    chartABlock2_coefficients_nonnegative chartABlock2_physical_identity
  have h3 := block_nonnegative 6
    lowerSixTailSlopeFloorChartABlock3Rows
    lowerSixTailSlopeFloorChartABlock3PhysicalExpr
    chartABlock3_coefficients_nonnegative chartABlock3_physical_identity
  have h4 := block_nonnegative 8
    lowerSixTailSlopeFloorChartABlock4Rows
    lowerSixTailSlopeFloorChartABlock4PhysicalExpr
    chartABlock4_coefficients_nonnegative chartABlock4_physical_identity
  have h5 := block_nonnegative 10
    lowerSixTailSlopeFloorChartABlock5Rows
    lowerSixTailSlopeFloorChartABlock5PhysicalExpr
    chartABlock5_coefficients_nonnegative chartABlock5_physical_identity
  have h6 := block_nonnegative 12
    lowerSixTailSlopeFloorChartABlock6Rows
    lowerSixTailSlopeFloorChartABlock6PhysicalExpr
    chartABlock6_coefficients_nonnegative chartABlock6_physical_identity
  have h7 := block_nonnegative 14
    lowerSixTailSlopeFloorChartABlock7Rows
    lowerSixTailSlopeFloorChartABlock7PhysicalExpr
    chartABlock7_coefficients_nonnegative chartABlock7_physical_identity
  have hblocks : (0 : Q') ≤ RingNormaliser.eval rho
      lowerSixTailSlopeFloorChartABlockPhysicalSumExpr := by
    change (0 : Q') ≤
      RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock0PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock1PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock2PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock3PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock4PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock5PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock6PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartABlock7PhysicalExpr +
        0)))))))
    exact Q'.zero_le_add _ _ h0
      (Q'.zero_le_add _ _ h1
      (Q'.zero_le_add _ _ h2
      (Q'.zero_le_add _ _ h3
      (Q'.zero_le_add _ _ h4
      (Q'.zero_le_add _ _ h5
      (Q'.zero_le_add _ _ h6
      (Q'.zero_le_add _ _ h7 (Q'.le_refl' 0))))))))
  have hphysical : (0 : Q') ≤ RingNormaliser.eval rho
      lowerSixTailSlopeFloorChartAPhysicalExpr :=
    Q'.le_trans' _ _ _ hblocks
      (Q'.le_of_eqv
        (eval_eqv_of_fastNormalize_eq _ _
          chartA_blocks_physical_identity rho))
  let C := Q'.ofInt lowerSixTailSlopeFloorChartAQuotient
  let NP := RingNormaliser.qpow N 15
  let L := lowerSixTailNextSlopeFloorCleared D N
  have hshape : (0 : Q') ≤ C * (NP * L) := by
    simpa [rho, twoVariableEnvironment, C, NP, L,
      lowerSixTailNextSlopeFloorCleared,
      lowerSixTailSlopeFloorChartAPhysicalExpr] using hphysical
  have hCpos : (0 : Q') < C := by
    dsimp only [C, lowerSixTailSlopeFloorChartAQuotient]
    decide
  have hCcancel : C * (0 : Q') ≤ C * (NP * L) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv C)) hshape
  have hinner : (0 : Q') ≤ NP * L :=
    Q'.le_of_mul_le_mul_left hCcancel hCpos
  have hNPpos : (0 : Q') < NP := by
    dsimp only [NP]
    exact ringQpow_pos N hNpos 15
  have hNPcancel : NP * (0 : Q') ≤ NP * L :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv NP)) hinner
  exact Q'.le_of_mul_le_mul_left hNPcancel hNPpos

/-- Chart B certificate: `91 ≤ N`, `N ≤ 2D`, and `D ≤ N²`. -/
theorem lowerSixTailNextSlopeFloorCleared_nonnegative_chartB
    {D N : Q'}
    (hNpos : (0 : Q') < N)
    (h91 : Q'.ofNat 91 ≤ N)
    (hN2D : N ≤ Q'.ofNat 2 * D)
    (hDN2 : D ≤ N * N)
    (hTwoNOnePos :
      (0 : Q') < Q'.ofNat 2 * N + -(1 : Q')) :
    (0 : Q') ≤ lowerSixTailNextSlopeFloorCleared D N := by
  let rho := twoVariableEnvironment D N
  have hN0 : (0 : Q') ≤ N := Q'.le_of_lt hNpos
  have hTwoN0 : (0 : Q') ≤ Q'.ofNat 2 * N :=
    Q'.mul_nonneg _ _ (by decide) hN0
  have hcoordinates : ∀ i,
      (0 : Q') ≤ RingNormaliser.eval rho
        (lowerSixTailSlopeFloorChartBSubstitution i) := by
    intro i
    rcases i with _ | i
    · change (0 : Q') ≤ Q'.ofInt 91
      decide
    · rcases i with _ | i
      · change (0 : Q') ≤ N + -(Q'.ofInt 91)
        exact Q'.sub_nonneg_of_le h91
      · rcases i with _ | i
        · change (0 : Q') ≤ N * (Q'.ofInt 2 * D + -N)
          exact Q'.mul_nonneg _ _ hN0 (Q'.sub_nonneg_of_le hN2D)
        · rcases i with _ | i
          · change (0 : Q') ≤
              (Q'.ofInt 2 * N) * (N * N + -D)
            exact Q'.mul_nonneg _ _ hTwoN0 (Q'.sub_nonneg_of_le hDN2)
          · change (0 : Q') ≤ Q'.ofInt 0
            exact Q'.le_refl' 0
  have block_nonnegative
      (startRow : Nat) (rows : List (List Int))
      (physical : RingNormaliser.PolyExpr)
      (hrows : IntegerRowsNonnegative rows = true)
      (hidentity :
        fastNormalize
            (substitute lowerSixTailSlopeFloorChartBSubstitution
              (homogeneousTensorBlockExpr 15 8 startRow rows)) =
          fastNormalize physical) :
      (0 : Q') ≤ RingNormaliser.eval rho physical :=
    physical_nonnegative_of_homogeneous_block_rows_certificate
      15 8 startRow rows rho lowerSixTailSlopeFloorChartBSubstitution
      physical hcoordinates hrows hidentity
  have h0 := block_nonnegative 0
    lowerSixTailSlopeFloorChartBBlock0Rows
    lowerSixTailSlopeFloorChartBBlock0PhysicalExpr
    chartBBlock0_coefficients_nonnegative chartBBlock0_physical_identity
  have h1 := block_nonnegative 2
    lowerSixTailSlopeFloorChartBBlock1Rows
    lowerSixTailSlopeFloorChartBBlock1PhysicalExpr
    chartBBlock1_coefficients_nonnegative chartBBlock1_physical_identity
  have h2 := block_nonnegative 4
    lowerSixTailSlopeFloorChartBBlock2Rows
    lowerSixTailSlopeFloorChartBBlock2PhysicalExpr
    chartBBlock2_coefficients_nonnegative chartBBlock2_physical_identity
  have h3 := block_nonnegative 6
    lowerSixTailSlopeFloorChartBBlock3Rows
    lowerSixTailSlopeFloorChartBBlock3PhysicalExpr
    chartBBlock3_coefficients_nonnegative chartBBlock3_physical_identity
  have h4 := block_nonnegative 8
    lowerSixTailSlopeFloorChartBBlock4Rows
    lowerSixTailSlopeFloorChartBBlock4PhysicalExpr
    chartBBlock4_coefficients_nonnegative chartBBlock4_physical_identity
  have h5 := block_nonnegative 10
    lowerSixTailSlopeFloorChartBBlock5Rows
    lowerSixTailSlopeFloorChartBBlock5PhysicalExpr
    chartBBlock5_coefficients_nonnegative chartBBlock5_physical_identity
  have h6 := block_nonnegative 12
    lowerSixTailSlopeFloorChartBBlock6Rows
    lowerSixTailSlopeFloorChartBBlock6PhysicalExpr
    chartBBlock6_coefficients_nonnegative chartBBlock6_physical_identity
  have h7 := block_nonnegative 14
    lowerSixTailSlopeFloorChartBBlock7Rows
    lowerSixTailSlopeFloorChartBBlock7PhysicalExpr
    chartBBlock7_coefficients_nonnegative chartBBlock7_physical_identity
  have hblocks : (0 : Q') ≤ RingNormaliser.eval rho
      lowerSixTailSlopeFloorChartBBlockPhysicalSumExpr := by
    change (0 : Q') ≤
      RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock0PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock1PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock2PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock3PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock4PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock5PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock6PhysicalExpr +
      (RingNormaliser.eval rho lowerSixTailSlopeFloorChartBBlock7PhysicalExpr +
        0)))))))
    exact Q'.zero_le_add _ _ h0
      (Q'.zero_le_add _ _ h1
      (Q'.zero_le_add _ _ h2
      (Q'.zero_le_add _ _ h3
      (Q'.zero_le_add _ _ h4
      (Q'.zero_le_add _ _ h5
      (Q'.zero_le_add _ _ h6
      (Q'.zero_le_add _ _ h7 (Q'.le_refl' 0))))))))
  have hphysical : (0 : Q') ≤ RingNormaliser.eval rho
      lowerSixTailSlopeFloorChartBPhysicalExpr :=
    Q'.le_trans' _ _ _ hblocks
      (Q'.le_of_eqv
        (eval_eqv_of_fastNormalize_eq _ _
          chartB_blocks_physical_identity rho))
  let C := Q'.ofInt lowerSixTailSlopeFloorChartBQuotient
  let NP := RingNormaliser.qpow N 15
  let TP := RingNormaliser.qpow (Q'.ofNat 2 * N + -(1 : Q')) 8
  let L := lowerSixTailNextSlopeFloorCleared D N
  have hshape : (0 : Q') ≤ C * (NP * (TP * L)) := by
    simpa [rho, twoVariableEnvironment, C, NP, TP, L,
      lowerSixTailNextSlopeFloorCleared,
      lowerSixTailSlopeFloorChartBPhysicalExpr] using hphysical
  have hCpos : (0 : Q') < C := by
    dsimp only [C, lowerSixTailSlopeFloorChartBQuotient]
    decide
  have hCcancel : C * (0 : Q') ≤ C * (NP * (TP * L)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv C)) hshape
  have hinner : (0 : Q') ≤ NP * (TP * L) :=
    Q'.le_of_mul_le_mul_left hCcancel hCpos
  have hNPpos : (0 : Q') < NP := by
    dsimp only [NP]
    exact ringQpow_pos N hNpos 15
  have hNPcancel : NP * (0 : Q') ≤ NP * (TP * L) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv NP)) hinner
  have htail : (0 : Q') ≤ TP * L :=
    Q'.le_of_mul_le_mul_left hNPcancel hNPpos
  have hTPpos : (0 : Q') < TP := by
    dsimp only [TP]
    exact ringQpow_pos _ hTwoNOnePos 8
  have hTPcancel : TP * (0 : Q') ≤ TP * L :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv TP)) htail
  exact Q'.le_of_mul_le_mul_left hTPcancel hTPpos

#print axioms lowerSixTailNextSlopeFloorCleared
#print axioms lowerSixTailNextSlopeFloorCleared_nonnegative_chartA
#print axioms lowerSixTailNextSlopeFloorCleared_nonnegative_chartB

end YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
