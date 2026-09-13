/-
# Counting entropy is absorbed at the EXISTING small-nome pilot

The collar-adjusted per-face rate is multiplied by the proved degree-625
core count. This module checks that the combined rate is strictly below
one at the already-used w=1/1024 point. It is a coupling-specific scalar
certificate, not a beta-uniform assertion or a physical mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget
import YMGap.Continuum.FiniteSizeGeometricSum

namespace YMGap.Continuum.BF4ExactSlabSummableCoreRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget
open YMGap.Continuum.FiniteSizeGeometricSum

theorem existingNome_inversePower_bound :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    (inverseFaceFloor w hd)^48 ≤ (64 : Q') := by
  let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
  let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
  let r := inverseFaceFloor w hd
  have hr : (0 : Q') < r := inverseFaceFloor_pos w hd
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r 8 6))
    (Q'.le_trans' _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.pow_nonneg r (Q'.le_of_lt hr) 8) existingNome_eighthPower_bound 6)
      (Q'.le_of_eqv (by decide : Q'.eqv ((2 : Q')^6) 64)))

/-- Strictness of the COMBINED counting/collar/heat rate, at the stated pilot only. -/
theorem existingNome_entropyRate :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    (0 : Q') < entropyRate 625 (adjustedCoreRate w hd) ∧
      entropyRate 625 (adjustedCoreRate w hd) < (1 : Q') := by
  let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
  let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
  have hr : adjustedCoreRate w hd ≤ pairedHeatRate w * 64 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ existingNome_inversePower_bound (Q'.le_of_lt existingNome_rate.1)
  have hscalar : (625 : Q') * (pairedHeatRate w * 64) < (1 : Q') := by
    change (625 : Q') * (pairedHeatRate BF4ExactSlabPlaquetteSmallNomeCertificate.nome * 64) < (1 : Q')
    decide
  exact ⟨Q'.mul_pos (by decide : (0 : Q') < 625) existingNome_adjustedRate.1,
    Q'.lt_of_le_of_lt (Q'.mul_le_mul_of_nonneg_left _ _ _ hr (by decide : (0 : Q') ≤ 625)) hscalar⟩

end YMGap.Continuum.BF4ExactSlabSummableCoreRate

#print axioms YMGap.Continuum.BF4ExactSlabSummableCoreRate.existingNome_inversePower_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummableCoreRate.existingNome_entropyRate
