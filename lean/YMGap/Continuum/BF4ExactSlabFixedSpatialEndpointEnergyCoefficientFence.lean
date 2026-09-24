/-
# Scalar fence for the computed endpoint energy coefficient

This concerns only the explicit coefficient produced by the endpoint channel
argument.  It is not a lower bound on the actual energy and is not a physical
counterexample.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound
import YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2HeatProductFirstMomentFloor
open YMGap.Continuum.JacobiShiftedRelativeSlope
open YMGap.Continuum.JacobiHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound
open YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor

local infix:50 " ≈ " => Q'.eqv

private theorem budget_ge_Cstar {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : HKConv.Cstar w ≤ budget w := by
  have hseries := prefix_le_budget hw0 hw1 1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
    change HKConv.Cstar w ≈ finSum (rate w) 1
    unfold finSum rate HKConvGen.geoIncrBase
    have hterm : (0 : Q') + HKConv.Cstar w * 1 ≈ HKConv.Cstar w :=
      Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) (Q'.mul_one_eqv _)
    exact Q'.eqv_symm hterm)) hseries

private theorem q_le_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b ≤ a := by
  change ¬ a.num * (b.den : Int) ≤ b.num * (a.den : Int) at h
  change b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  omega

private theorem endpointCap_ge_thirtyTwo_budget {w : Q'}
    (hw0 : (0 : Q') < w) :
    (32 : Q') * budget w ≤ endpointRelativeCap w := by
  have hb0 := budget_nonnegative hw0
  have hr4096 : (0 : Q') ≤ relativeCap w 4096 :=
    Q'.le_of_lt (relativeCap_positive hw0 (by decide))
  have hfirst : (32 : Q') * budget w ≤ relativeCap w 32 := by
    change (32 : Q') * budget w ≤ (32 : Q') * budget w + 1
    exact Q'.add_le_self_of_nonneg _ _ Q'.zero_le_one
  have hsecond : relativeCap w 32 ≤ endpointRelativeCap w := by
    change relativeCap w 32 ≤
      6 * relativeCap w 4096 + relativeCap w 32
    have h := Q'.add_le_self_of_nonneg (relativeCap w 32)
      (6 * relativeCap w 4096) (Q'.mul_nonneg _ _ (by decide) hr4096)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.add_comm_eqv (relativeCap w 32) (6 * relativeCap w 4096)))
  exact Q'.le_trans' _ _ _ hfirst hsecond

private theorem endpointExponent_gap_square_ge_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hhalf : (HalfPow.half : Q') ≤ w) :
    (1 : Q') ≤ Q'.ofNat (endpointChannelFloorExponent w) *
      (((1 : Q') - w) * ((1 : Q') - w)) := by
  let eps := (1 : Q') - w
  let C := endpointRelativeCap w
  let M := endpointChannelFloorExponent w
  have heps : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hC1 : (1 : Q') ≤ C := by
    have hb0 := budget_nonnegative hw0
    have hrel : (1 : Q') ≤ relativeCap w 32 := by
      change (1 : Q') ≤ (32 : Q') * budget w + 1
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv 1)))
        (Q'.add_le_add_right 0 (32*budget w) 1
          (Q'.mul_nonneg _ _ (by decide) hb0))
    exact Q'.le_trans' _ _ _ hrel (by
      change relativeCap w 32 ≤
        6 * relativeCap w 4096 + relativeCap w 32
      have h := Q'.add_le_self_of_nonneg (relativeCap w 32)
        (6 * relativeCap w 4096) (Q'.mul_nonneg _ _ (by decide)
          (Q'.le_of_lt (relativeCap_positive hw0 (by decide))))
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
        (Q'.add_comm_eqv (relativeCap w 32) (6 * relativeCap w 4096))))
  have htwo : (1 : Q') ≤ HKPos.two w := by
    unfold HKPos.two
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hhalf (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q') ≈ 2*HalfPow.half))
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (by
        exact poly_identity_of_normal_eq
          (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
          (by decide) (fun _ => w))))
  have hCe : (32 : Q') ≤ C*(eps*eps) := by
    have hb := budget_ge_Cstar hw0 hw1
    have hcb := endpointCap_ge_thirtyTwo_budget hw0
    have hstar := HKConv.Cstar_bound hw1
    have hscale1 := Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') htwo (by decide)
    have hscale2 := Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') hstar (by decide)
    have hscale3 := Q'.mul_le_mul_of_nonneg_right _ _ (eps*eps)
      (Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') hb (by decide))
      (Q'.mul_nonneg _ _ heps heps)
    have hscale4 := Q'.mul_le_mul_of_nonneg_right _ _ (eps*eps) hcb
      (Q'.mul_nonneg _ _ heps heps)
    exact Q'.le_trans' _ _ _ hscale1
      (Q'.le_trans' _ _ _ hscale2
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.const 32) (.mul (.var 0) (.mul (.var 1) (.var 1))))
          (.mul (.mul (.const 32) (.var 0)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => HKConv.Cstar w | _ => eps)))
          (Q'.le_trans' _ _ _ hscale3 hscale4)))
  have hC2e : (32 : Q') ≤ (C*C)*(eps*eps) := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ C hCe (Q'.le_trans' _ _ _ Q'.zero_le_one hC1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (32 : Q')).symm)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') hC1 (by decide))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv 32 C))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
            (by decide) (fun | 0 => C | _ => eps))))))
  have hM := endpointChannelFloorExponent_sufficient w
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (eps*eps) hM
    (Q'.mul_nonneg _ _ heps heps)
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 48*32)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (48 : Q') hC2e (by decide))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _).symm) hscaled))

/-- The computed exponent is so large that its nome power is no larger than
the nome gap, for every strict nome. -/
theorem endpointFloorPower_le_gap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    RGTransport.qpow w (endpointChannelFloorExponent w) ≤ (1 : Q') - w := by
  let eps := (1 : Q') - w
  let M := endpointChannelFloorExponent w
  have hw0' := Q'.le_of_lt hw0
  have hw1' := Q'.le_of_lt hw1
  have heps : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le hw1'
  by_cases hhalf : (HalfPow.half : Q') ≤ w
  · have hMe := endpointExponent_gap_square_ge_one hw0 hw1 hhalf
    have hMpos := endpointChannelFloorExponent_positive w
    have hMs : M - 1 + 1 = M := by omega
    have hcorr0 := one_add_gap_mul_qpow_succ_le_one hw0' hw1' (M-1)
    rw [hMs] at hcorr0
    have hcorr := hcorr0
    have hcoef : (1 : Q') ≤ eps*((1 : Q')+Q'.ofNat M*eps) := by
      have hadd := Q'.add_le_self_of_nonneg
        (Q'.ofNat M*(eps*eps)) eps heps
      exact Q'.le_trans' _ _ _ hMe
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 1))
          (.mul (.var 1) (.add (.const 1) (.mul (.var 0) (.var 1))))
          (by decide) (fun | 0 => Q'.ofNat M | _ => eps))))
    have hp0 := RGTransport.qpow_nonneg w hw0' M
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hp0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _).symm)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ eps hcorr heps)
            (Q'.le_of_eqv (Q'.mul_one_eqv eps)))))
  · have hwle : w ≤ HalfPow.half := by
      exact q_le_of_not_le hhalf
    have h1M : 1 ≤ M := by
      unfold M
      exact endpointChannelFloorExponent_positive w
    have hpow : RGTransport.qpow w M ≤ w :=
      Q'.le_trans' _ _ _
        (qpow_antitone_exponent hw0' hw1' h1M)
        (by change RGTransport.qpow w 1 ≤ w; exact Q'.le_of_eqv (Q'.one_mul_eqv w))
    have hwgap : w ≤ eps := by
      have hzero : (0 : Q') ≤ HalfPow.half - w := Q'.sub_nonneg_of_le hwle
      have hadd := Q'.add_le_add_left HalfPow.half 0 (HalfPow.half-w) hzero
      rw [Q'.add_zero'] at hadd
      exact Q'.le_trans' _ _ _ hwle
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by
            unfold eps
            exact Q'.eqv_trans _ _ _
              (Q'.add_assoc_eqv HalfPow.half HalfPow.half (-w)).symm
              (Q'.add_eqv_congr_right _ _ (-w)
                (by decide : (HalfPow.half + HalfPow.half) ≈ (1 : Q'))))))
    exact Q'.le_trans' _ _ _ hpow hwgap

/-- The energy coefficient is at least sixty-four times the computed floor. -/
theorem sixtyFour_endpointHeatFloor_le_coefficient {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (64 : Q') * endpointChannelHeatFloor w ≤ endpointEnergyPartitionCoefficient w := by
  have h := endpointFloorPower_le_gap hw0 hw1
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q') h (by decide)
  have hpin : (64 : Q') * endpointChannelHeatFloor w ≈
      (32 : Q') * RGTransport.qpow w (endpointChannelFloorExponent w) := by
    unfold endpointChannelHeatFloor
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (64 : Q') HalfPow.half
        (RGTransport.qpow w (endpointChannelFloorExponent w))).symm
      (Q'.mul_eqv_congr_right _ _ _
        (by decide : (64 : Q') * HalfPow.half ≈ (32 : Q')))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hs (by
      unfold endpointEnergyPartitionCoefficient
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
            (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))))))

/-- Any multiplicative normalization of this computed coefficient has loss at
least `32`; this is only a fence on the certificate. -/
theorem normalizedCoefficient_ge_thirtyTwo {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hdelta : endpointEnergyPartitionCoefficient w ≤
      (2 : Q') * endpointChannelHeatFloor w * delta) :
    (32 : Q') ≤ delta := by
  have hfloor := sixtyFour_endpointHeatFloor_le_coefficient hw0 hw1
  have h := Q'.le_trans' _ _ _ hfloor hdelta
  have hrho := endpointChannelHeatFloor_positive hw0
  apply Q'.le_of_mul_le_mul_left (c := (2 : Q') * endpointChannelHeatFloor w)
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.const 32))
      (.mul (.const 64) (.var 0)) (by decide)
      (fun _ => endpointChannelHeatFloor w))) h
  · exact Q'.mul_pos (by decide) hrho

#print axioms endpointFloorPower_le_gap
#print axioms sixtyFour_endpointHeatFloor_le_coefficient
#print axioms normalizedCoefficient_ge_thirtyTwo

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence
