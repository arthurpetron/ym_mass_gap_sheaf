/-
# Monotonicity of the guarded original Wilson rate

All statements here are finite rational order facts.  They compare the
already-defined nome-dependent heat and collar rates; they do not assert a
uniform rate, a continuum limit, or a physical calibration.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap

namespace YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound (pairedHeatRate pairedHeatRate_nonnegative)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)

theorem heatRatio_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) :
    heatRatio u ≤ heatRatio v := by
  unfold heatRatio
  have hp : qpow u 3 ≤ qpow v 3 := qpow_mono hu0 huv 3
  have hleft : 2 * qpow u 3 ≤ 2 * qpow v 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hp (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ 16 hleft (by decide)

theorem heatRemainderBound_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) :
    heatRemainderBound u ≤ heatRemainderBound v := by
  have hp : qpow u 3 ≤ qpow v 3 := qpow_mono hu0 huv 3
  have hscaled : (128 : Q') * qpow u 3 ≤ 128 * qpow v 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 128 hp (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (heatRemainderBound_eq u))
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv (heatRemainderBound_eq v)))

private theorem pairedRate_mono {d e : Q'} (hd0 : (0 : Q') ≤ d)
    (hde : d ≤ e) (he0 : (0 : Q') ≤ e) :
    d + d + d*d ≤ e + e + e*e := by
  have hprod₁ : d*d ≤ e*d := Q'.mul_le_mul_of_nonneg_right _ _ _ hde hd0
  have hprod₂ : e*d ≤ e*e := Q'.mul_le_mul_of_nonneg_left _ _ _ hde he0
  have hprod : d*d ≤ e*e := Q'.le_trans' _ _ _ hprod₁ hprod₂
  exact Q'.add_le_add (Q'.add_le_add hde hde) hprod

theorem pairedHeatRate_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) :
    pairedHeatRate u ≤ pairedHeatRate v := by
  have hde := heatRemainderBound_mono hu0 huv
  have hd0 := heatRemainderBound_nonnegative hu0
  have he0 := heatRemainderBound_nonnegative (Q'.le_trans' _ _ _ hu0 huv)
  exact pairedRate_mono hd0 hde he0

theorem inverseFaceFloor_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1) :
    inverseFaceFloor u hdu ≤ inverseFaceFloor v hdv := by
  have hdelta := heatRemainderBound_mono hu0 huv
  have hden : 1 + -heatRemainderBound v ≤ 1 + -heatRemainderBound u :=
    Q'.add_le_add (Q'.le_refl' 1) (Q'.neg_le_neg hdelta)
  unfold inverseFaceFloor
  exact ArtanhMonotone.recipPos_antitone _ _ (HKPos.one_sub_pos hdv)
    (HKPos.one_sub_pos hdu) hden

theorem adjustedCoreRate_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1) :
    adjustedCoreRate u hdu ≤ adjustedCoreRate v hdv := by
  have hp := pairedHeatRate_mono hu0 huv
  have hpv0 := pairedHeatRate_nonnegative (Q'.le_trans' _ _ _ hu0 huv)
  have hi := inverseFaceFloor_mono hu0 huv hdu hdv
  have hiu0 := Q'.le_of_lt (inverseFaceFloor_pos u hdu)
  have hipow := YMGap.Constructive.CRealLog.pow_le_pow_base _ _ hiu0 hi 48
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hp
    (Q'.pow_nonneg _ hiu0 48)
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hipow hpv0
  exact Q'.le_trans' _ _ _ hfirst hsecond

theorem timeRate_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1) :
    timeRate u hdu ≤ timeRate v hdv := by
  unfold timeRate entropyRate
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 625)
    (adjustedCoreRate_mono hu0 huv hdu hdv) (by decide)

theorem twoStepRate_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1) :
    twoStepRate u hdu ≤ twoStepRate v hdv := by
  have ht := timeRate_mono hu0 huv hdu hdv
  have htu0 : (0 : Q') ≤ timeRate u hdu := by
    unfold timeRate entropyRate
    exact Q'.mul_nonneg _ _ (by decide) (adjustedCoreRate_nonnegative hu0 hdu)
  have htv0 : (0 : Q') ≤ timeRate v hdv := by
    unfold timeRate entropyRate
    exact Q'.mul_nonneg _ _ (by decide)
      (adjustedCoreRate_nonnegative (Q'.le_trans' _ _ _ hu0 huv) hdv)
  unfold twoStepRate
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ht htu0)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ ht htv0)

#print axioms heatRatio_mono
#print axioms heatRemainderBound_mono
#print axioms pairedHeatRate_mono
#print axioms inverseFaceFloor_mono
#print axioms adjustedCoreRate_mono
#print axioms timeRate_mono
#print axioms twoStepRate_mono

end YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity
