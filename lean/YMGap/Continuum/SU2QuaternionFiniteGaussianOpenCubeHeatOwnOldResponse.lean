/-
# Corrected heat-carrier OWN/OLD response

This leaf assembles the finite OLD-centered response coefficients from the
corrected heat-carrier connected values and OWN means.  The supplied OLD
center remains arbitrary: no relation between its `c2,c3,c4` fields and the
finite FREE OWN means is assumed.  In particular the surviving
`(-c3)*(-c3)` term is retained in `P6`.

The output is exact finite FREE bookkeeping and explicit Wick substitution.
It does not identify an ORIGINAL-law center, prove a neighboring-time sign,
control higher remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- Corrected OLD-centered fourth response coefficient. -/
def openCubeHeatCayleyTraceP4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime +
    (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage leftTime - oldCenter.c2) *
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- Corrected OLD-centered fifth response coefficient. -/
def openCubeHeatCayleyTraceP5
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c2) *
    (openCubeHeatCayleyTraceOwnA3Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c3) +
  (openCubeHeatCayleyTraceOwnA3Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c3) *
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- Corrected OLD-centered sixth response coefficient. -/
def openCubeHeatCayleyTraceP6
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  ((openCubeHeatCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime +
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
        (openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
    (openCubeHeatCayleyTraceOwnA3Mean
        timeBonds side sidePositive stage leftTime - oldCenter.c3) *
      (openCubeHeatCayleyTraceOwnA3Mean
        timeBonds side sidePositive stage rightTime - oldCenter.c3)) +
  (openCubeHeatCayleyTraceOwnA4Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c4) *
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

theorem openCubeHeatCayleyTraceP5_parity
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP5
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
          (-oldCenter.c3) +
        (-oldCenter.c3) *
          (openCubeHeatCayleyTraceOwnA2Mean
            timeBonds side sidePositive stage rightTime - oldCenter.c2) := by
  unfold openCubeHeatCayleyTraceP5
  have leftCubicResidual :
      openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeHeatCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage leftTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  have rightCubicResidual :
      openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeHeatCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ rightCubicResidual)
    (Q'.mul_eqv_congr_right _ _ _ leftCubicResidual)

theorem openCubeHeatCayleyTraceP6_parity
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      ((openCubeHeatCayleyTraceConnectedR6WickSum
            timeBonds side sidePositive stage leftTime rightTime +
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage leftTime - oldCenter.c2) *
            (openCubeHeatCayleyTraceOwnA4Mean
              timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
        (-oldCenter.c3) * (-oldCenter.c3)) +
      (openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c4) *
        (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2) := by
  unfold openCubeHeatCayleyTraceP6
  have leftCubicResidual :
      openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeHeatCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage leftTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  have rightCubicResidual :
      openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeHeatCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (mul_congr leftCubicResidual rightCubicResidual))
    (Q'.eqv_refl _)

/-- Complete explicit finite Wick form of corrected `P4`. -/
def openCubeHeatCayleyTraceP4CompleteWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceConnectedR4WickSum
      timeBonds side sidePositive stage leftTime rightTime +
    (openCubeHeatCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage leftTime - oldCenter.c2) *
      (openCubeHeatCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage rightTime - oldCenter.c2)

theorem openCubeHeatCayleyTraceP4_complete_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP4
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP4CompleteWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  have leftResidual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightResidual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage rightTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  unfold openCubeHeatCayleyTraceP4
    openCubeHeatCayleyTraceP4CompleteWickSum
  exact Q'.add_eqv_congr'
    (openCubeHeatCayleyTraceConnectedR4_wick
      timeBonds side sidePositive stage leftTime rightTime)
    (mul_congr leftResidual rightResidual)

/-- Complete explicit parity-normalized finite Wick form of corrected `P5`. -/
def openCubeHeatCayleyTraceP5CompleteWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  (openCubeHeatCayleyTraceOwnA2MeanGramSum
      timeBonds side sidePositive stage leftTime - oldCenter.c2) *
      (-oldCenter.c3) +
    (-oldCenter.c3) *
      (openCubeHeatCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage rightTime - oldCenter.c2)

theorem openCubeHeatCayleyTraceP5_complete_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP5
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP5CompleteWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  have hparity := openCubeHeatCayleyTraceP5_parity
    timeBonds side sidePositive stage leftTime rightTime oldCenter
  have leftResidual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightResidual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage rightTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hparity
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ leftResidual)
      (Q'.mul_eqv_congr_left _ _ _ rightResidual))

/-- Complete explicit parity-normalized finite Wick form of corrected `P6`. -/
def openCubeHeatCayleyTraceP6CompleteWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  ((openCubeHeatCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime +
      (openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
        (openCubeHeatCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
    (-oldCenter.c3) * (-oldCenter.c3)) +
  (openCubeHeatCayleyTraceOwnA4MeanWickSum
      timeBonds side sidePositive stage leftTime - oldCenter.c4) *
    (openCubeHeatCayleyTraceOwnA2MeanGramSum
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

theorem openCubeHeatCayleyTraceP6_complete_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6CompleteWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  have leftA2Residual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightA2Residual :
      openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2 ≈
        openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage rightTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  have leftA4Residual :
      openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c4 ≈
        openCubeHeatCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage leftTime - oldCenter.c4 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA4Mean_wick
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightA4Residual :
      openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c4 ≈
        openCubeHeatCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage rightTime - oldCenter.c4 :=
    Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceOwnA4Mean_wick
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (openCubeHeatCayleyTraceP6_parity
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (mul_congr leftA2Residual rightA4Residual))
        (Q'.eqv_refl _))
      (mul_congr leftA4Residual rightA2Residual))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse.openCubeHeatCayleyTraceP4_complete_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse.openCubeHeatCayleyTraceP5_complete_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse.openCubeHeatCayleyTraceP6_complete_wick
