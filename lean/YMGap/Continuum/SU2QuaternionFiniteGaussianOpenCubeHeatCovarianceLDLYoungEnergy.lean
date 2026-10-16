/-
# Young-energy control of the heat covariance LDL residual

The canonical heat covariance factor is unit-upper, so entrywise localization
leaves an ordering-dependent suffix.  Positivity gives a different reduction:
Young's inequality bounds every off-diagonal absolute residual coefficient by
the average of two diagonal residual energies.  Each diagonal energy is also
the exact stage-zero Heron covariance overshoot above the checked covariance
diagonal.

This replaces a potentially dense suffix estimate by two positive diagonal
quantities.  No cutoff-uniform bound for those quantities, ORIGINAL-law
comparison, continuum limit, Hamiltonian gap, or Clay theorem is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {Index : Type}
    (lower upper : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | item :: items, hypothesis =>
      Q'.add_le_add
        (hypothesis item List.mem_cons_self)
        (listQSum_mono_local lower upper items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

/-- Rational Young inequality in the normalization used by the diagonal
energy reduction: `|xy| <= (x^2+y^2)/2`. -/
private theorem abs_mul_le_half_square_sum (x y : Q') :
    Q'.abs (x * y) ≤
      half * ((x * x) + (y * y)) := by
  have hproduct := ExpNeg.abs_mul_le x y
  have hdouble :
      Q'.abs (x * y) + Q'.abs (x * y) ≤
        (x * x) + (y * y) := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hproduct hproduct) ?_
    refine Q'.le_trans' _ _ _
      (CRealAlg.amgm_two (Q'.abs x) (Q'.abs y)) ?_
    exact Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.abs_mul_self_eqv x)
        (Q'.abs_mul_self_eqv y))
  have hscaled :
      half *
          (Q'.abs (x * y) + Q'.abs (x * y)) ≤
        half * ((x * x) + (y * y)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdouble half_nonneg
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hscaled
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (half * Q'.abs (x * y) +
        half * Q'.abs (x * y)) _
      (Q'.mul_add_eqv
        half (Q'.abs (x * y)) (Q'.abs (x * y)))
      (ExpNeg.two_halves (Q'.abs (x * y))))

/-- Positive stage-zero diagonal residual energy of one LDL factor row. -/
def ldlFactorResidualDiagonalEnergy
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (row : Nat) : Q' :=
  listQSum
    (fun channel =>
      CReal.errAt (diagonal channel) 0 *
        (factor row channel * factor row channel))
    (List.range n)

/-- The stage-zero signed diagonal residual is definitionally the diagonal
energy. -/
theorem ldlFactorResidual_zero_diagonal_eq_energy
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (row : Nat) :
    ldlFactorResidual n factor diagonal 0 row row =
      ldlFactorResidualDiagonalEnergy n factor diagonal row :=
  rfl

/-- The diagonal energy is the corresponding absolute residual coefficient. -/
theorem ldlFactorResidualDiagonalEnergy_eq_coefficient
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (row : Nat) :
    ldlFactorResidualDiagonalEnergy n factor diagonal row ≈
      ldlFactorResidualCoefficient n factor diagonal row row := by
  unfold ldlFactorResidualDiagonalEnergy ldlFactorResidualCoefficient
  apply listQSum_congr_on
  intro channel _
  rw [ExpNeg.abs_of_nonneg
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (factor row channel))]
  exact Q'.eqv_refl _

/-- Every absolute residual coefficient is bounded by the average of the two
diagonal energies when all LDL pivots are positive. -/
theorem ldlFactorResidualCoefficient_le_diagonalEnergy_average
    {n left right : Nat} {factor : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true) :
    ldlFactorResidualCoefficient n factor diagonal left right ≤
      half *
        (ldlFactorResidualDiagonalEnergy n factor diagonal left +
          ldlFactorResidualDiagonalEnergy n factor diagonal right) := by
  unfold ldlFactorResidualCoefficient
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun channel =>
        CReal.errAt (diagonal channel) 0 *
          Q'.abs (factor left channel * factor right channel))
      (fun channel =>
        CReal.errAt (diagonal channel) 0 *
          (half *
            ((factor left channel * factor left channel) +
              (factor right channel * factor right channel))))
      (List.range n) ?_) ?_
  · intro channel hchannel
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (abs_mul_le_half_square_sum
        (factor left channel) (factor right channel))
      (CReal.errAt_nonneg (diagonal channel)
        (finiteLDLPositiveDiagonalCheck_pos hpositive
          (List.mem_range.mp hchannel)) 0)
  · apply Q'.le_of_eqv
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_on
        (fun channel =>
          CReal.errAt (diagonal channel) 0 *
            (half *
              ((factor left channel * factor left channel) +
                (factor right channel * factor right channel))))
        (fun channel =>
          half *
            ((CReal.errAt (diagonal channel) 0 *
                (factor left channel * factor left channel)) +
              (CReal.errAt (diagonal channel) 0 *
                (factor right channel * factor right channel))))
        (List.range n) (fun channel _ =>
          poly_identity_of_normal_eq
            (.mul (.var 0)
              (.mul (.var 1)
                (.add (.mul (.var 2) (.var 2))
                  (.mul (.var 3) (.var 3)))))
            (.mul (.var 1)
              (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
                (.mul (.var 0) (.mul (.var 3) (.var 3)))))
            (by decide) (fun
              | 0 => CReal.errAt (diagonal channel) 0
              | 1 => half
              | 2 => factor left channel
              | _ => factor right channel))) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_mul_left half
        (fun channel =>
          (CReal.errAt (diagonal channel) 0 *
              (factor left channel * factor left channel)) +
            (CReal.errAt (diagonal channel) 0 *
              (factor right channel * factor right channel)))
        (List.range n)) ?_
    exact Q'.mul_eqv_congr_left half _ _
      (listQSum_add
        (fun channel =>
          CReal.errAt (diagonal channel) 0 *
            (factor left channel * factor left channel))
        (fun channel =>
          CReal.errAt (diagonal channel) 0 *
            (factor right channel * factor right channel))
        (List.range n))

/-- Equivalent diagonal-coefficient form of the Young-energy bound. -/
theorem ldlFactorResidualCoefficient_le_diagonalCoefficient_average
    {n left right : Nat} {factor : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true) :
    ldlFactorResidualCoefficient n factor diagonal left right ≤
      half *
        (ldlFactorResidualCoefficient n factor diagonal left left +
          ldlFactorResidualCoefficient n factor diagonal right right) := by
  refine Q'.le_trans' _ _ _
    (ldlFactorResidualCoefficient_le_diagonalEnergy_average hpositive) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left half _ _
      (Q'.add_eqv_congr'
        (ldlFactorResidualDiagonalEnergy_eq_coefficient
          n factor diagonal left)
        (ldlFactorResidualDiagonalEnergy_eq_coefficient
          n factor diagonal right)))

/-- For checked LDL data, the diagonal energy is exactly the excess of the
stage-zero Heron factor covariance over the checked covariance diagonal. -/
theorem factorCovariance_heronLDLTransform_zero_diagonal
    {n row : Nat} {matrix factor : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix factor diagonal = true)
    (hrow : row < n) :
    factorCovariance n (heronLDLTransform factor diagonal 0) row row ≈
      matrix row row +
        ldlFactorResidualDiagonalEnergy n factor diagonal row := by
  change factorCovariance n
      (heronLDLTransform factor diagonal 0) row row ≈
    matrix row row + ldlFactorResidual n factor diagonal 0 row row
  exact factorCovariance_heronLDLTransform_checked hcheck hrow hrow

/-- Heat-covariance specialization: every residual coefficient is controlled
by the average of two exact diagonal stage-zero energies. -/
theorem combGaugeHeatFreeHistoryLDLResidualCoefficient_le_diagonalEnergy_average
    (timeBonds width left right : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width
    ldlFactorResidualCoefficient n data.lower data.diagonal left right ≤
      half *
        (ldlFactorResidualDiagonalEnergy n data.lower data.diagonal left +
          ldlFactorResidualDiagonalEnergy n data.lower data.diagonal right) := by
  dsimp only
  exact ldlFactorResidualCoefficient_le_diagonalEnergy_average
    (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
      timeBonds width)

/-- The heat diagonal energy is the exact stage-zero covariance overshoot. -/
theorem combGaugeHeatFreeHistoryHeron_zero_diagonal
    (timeBonds width row : Nat)
    (hrow : row <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width
    factorCovariance n
        (combGaugeHeatFreeHistoryHeronTransform timeBonds width 0)
        row row ≈
      combGaugeHeatFreeHistoryCovariance timeBonds width row row +
        ldlFactorResidualDiagonalEnergy n data.lower data.diagonal row := by
  dsimp only [combGaugeHeatFreeHistoryHeronTransform]
  exact factorCovariance_heronLDLTransform_zero_diagonal
    (combGaugeHeatFreeHistoryCovariancePositiveLDL_check timeBonds width)
    hrow

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy.ldlFactorResidualCoefficient_le_diagonalEnergy_average
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy.ldlFactorResidualCoefficient_le_diagonalCoefficient_average
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy.factorCovariance_heronLDLTransform_zero_diagonal
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy.combGaugeHeatFreeHistoryLDLResidualCoefficient_le_diagonalEnergy_average
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy.combGaugeHeatFreeHistoryHeron_zero_diagonal
