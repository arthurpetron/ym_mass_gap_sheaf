/-
# Unit-upper suffix structure of the heat covariance LDL residual

The canonical covariance factor is obtained by inverting the unit-lower
precision factor.  Its Gram factor is therefore `L⁻ᵀ`, which is unit-upper.
Consequently an entrywise Heron residual coefficient does not use an arbitrary
full range: every channel below `max(left,right)` vanishes exactly, while the
remaining coefficient is a suffix sum through the physical carrier cutoff.

This identifies the current obstruction honestly.  Source-row support has
already been reduced to four coordinates, but each surviving covariance-LDL
entry may retain an ordering-dependent suffix whose length grows with the
cutoff.  No uniform entry bound, cancellation, or mass-gap conclusion is
proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderSupport

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalUnitLowerInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eq_filter_of_zero_local
    {Index : Type} (value : Index → Q') (test : Index → Bool) :
    ∀ items : List Index,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | item :: items, hzero => by
      have htail : ∀ other, other ∈ items → test other = false →
          value other ≈ 0 := by
        intro other membership htest
        exact hzero other (List.mem_cons_of_mem item membership) htest
      cases htest : test item with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum value (items.filter test)) _
            (Q'.add_eqv_congr'
              (hzero item List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test items htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test items htail)

private theorem residualTerm_eqv_zero_of_left_zero
    (diagonal left right : Q') (hleft : left = 0) :
    CReal.errAt diagonal 0 * Q'.abs (left * right) ≈ 0 := by
  subst left
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _
        (ExpNeg.abs_eqv_congr (Q'.zero_mul_eqv right))
        (Q'.eqv_of_eq TrigAdd.abs_zero_eq)))
    (Q'.mul_zero_eqv _)

private theorem residualTerm_eqv_zero_of_right_zero
    (diagonal left right : Q') (hright : right = 0) :
    CReal.errAt diagonal 0 * Q'.abs (left * right) ≈ 0 := by
  subst right
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _
        (ExpNeg.abs_eqv_congr (Q'.mul_zero_eqv left))
        (Q'.eqv_of_eq TrigAdd.abs_zero_eq)))
    (Q'.mul_zero_eqv _)

/-- Suffix form of one LDL residual entry for a unit-upper factor. -/
def ldlFactorResidualSuffixCoefficient
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (left right : Nat) : Q' :=
  listQSum
    (fun channel =>
      CReal.errAt (diagonal channel) 0 *
        Q'.abs (factor left channel * factor right channel))
    ((List.range n).filter fun channel =>
      decide (Nat.max left right ≤ channel))

/-- For an in-range pair of rows in a unit-upper factor, the residual
coefficient is exactly the suffix starting at `max(left,right)`. -/
theorem ldlFactorResidualCoefficient_eq_suffix
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (left right : Nat) (hleft : left < n) (hright : right < n)
    (hupper : ∀ {row column : Nat}, row < n → column < n →
      column < row → factor row column = 0) :
    ldlFactorResidualCoefficient n factor diagonal left right ≈
      ldlFactorResidualSuffixCoefficient
        n factor diagonal left right := by
  unfold ldlFactorResidualCoefficient
    ldlFactorResidualSuffixCoefficient
  apply listQSum_eq_filter_of_zero_local
  intro channel hchannel htest
  have hchannelRange : channel < n := List.mem_range.mp hchannel
  have hbelow : channel < Nat.max left right := by
    exact Nat.lt_of_not_ge (of_decide_eq_false htest)
  have hside : channel < left ∨ channel < right := by
    by_cases hleftRight : left ≤ right
    · exact Or.inr (by
        simpa only [Nat.max_eq_right hleftRight] using hbelow)
    · have hrightLeft : right ≤ left := by omega
      exact Or.inl (by
        simpa only [Nat.max_eq_left hrightLeft] using hbelow)
  rcases hside with hleftSide | hrightSide
  · exact residualTerm_eqv_zero_of_left_zero
      (diagonal channel) (factor left channel) (factor right channel)
      (hupper hleft hchannelRange hleftSide)
  · exact residualTerm_eqv_zero_of_right_zero
      (diagonal channel) (factor left channel) (factor right channel)
      (hupper hright hchannelRange hrightSide)

/-- The canonical heat-covariance Gram factor is unit-upper: entries below
the diagonal vanish exactly. -/
theorem combGaugeHeatFreeHistoryCovariancePositiveLDL_lower_eq_zero_of_lt
    (timeBonds width row column : Nat)
    (hrow : row <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hcolumn : column <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hlt : column < row) :
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower row column = 0 := by
  unfold combGaugeHeatFreeHistoryCovariancePositiveLDL
    finiteMatrixInversePositiveLDLDataOfStrictPositive
    finiteMatrixInversePositiveLDLData
    finiteMatrixTranspose
  exact (positiveLDLLowerInverseData_isUnitLower
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_strictlyPositive
      timeBonds width)).2 hcolumn hrow hlt

/-- Each in-range heat-covariance residual entry is exactly its
ordering-dependent unit-upper suffix sum. -/
theorem combGaugeHeatFreeHistoryLDLResidualCoefficient_eq_suffix
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width
    ldlFactorResidualCoefficient n data.lower data.diagonal left right ≈
      ldlFactorResidualSuffixCoefficient
        n data.lower data.diagonal left right := by
  dsimp only
  exact ldlFactorResidualCoefficient_eq_suffix
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
    left right hleft hright
    (fun hrow hcolumn hlt =>
      combGaugeHeatFreeHistoryCovariancePositiveLDL_lower_eq_zero_of_lt
        timeBonds width _ _ hrow hcolumn hlt)

theorem ldlFactorResidualSuffixCoefficient_channel_mem
    {n left right channel : Nat}
    (hmembership : channel ∈
      (List.range n).filter (fun index =>
        decide (Nat.max left right ≤ index))) :
    Nat.max left right ≤ channel ∧ channel < n := by
  have hparts := List.mem_filter.mp hmembership
  exact ⟨of_decide_eq_true hparts.2, List.mem_range.mp hparts.1⟩

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix.ldlFactorResidualCoefficient_eq_suffix
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix.combGaugeHeatFreeHistoryCovariancePositiveLDL_lower_eq_zero_of_lt
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLSuffix.combGaugeHeatFreeHistoryLDLResidualCoefficient_eq_suffix
