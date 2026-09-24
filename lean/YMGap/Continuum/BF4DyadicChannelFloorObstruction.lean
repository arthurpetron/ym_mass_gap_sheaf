/-
# Numerical obstruction for the proposed growing-loop channel floor

This file studies only the number obtained by iterating the already-computed
one-plaquette first-moment exponent.  It does NOT construct a growing-loop
partition floor.  The quadratic `A` remainder in the signed geometric budget
already costs at least 1920 relative to this proposed normalizer.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.SU2HeatProductFirstMomentFloor

namespace YMGap.Continuum.BF4DyadicChannelFloorObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
  (endpointChannelFloorExponent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence
  (endpointFloorPower_le_gap)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.SU2HeatProductFirstMomentFloor
  (qpow_antitone_exponent)

/-- Candidate normalization obtained by paying the existing local exponent
once per four-link perimeter unit. No comparison with a partition is asserted. -/
def loopFloor (w : Q') (L : Nat) : Q' :=
  HalfPow.half * RGTransport.qpow w
    (L * endpointChannelFloorExponent w)

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < RGTransport.qpow w n
  | 0 => by exact (by decide : (0 : Q') < 1)
  | n + 1 => Q'.mul_pos (qpow_positive hw n) hw

/-- The proposed loop floor is positive at every strict positive nome. -/
theorem loopFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (L : Nat) :
    (0 : Q') < loopFloor w L :=
  Q'.mul_pos (by decide) (qpow_positive hw0 _)

/-- Iterating the already-degenerate endpoint power makes the proposed floor
no larger than half the square of the loop heat deficit, once `L >= 2`. -/
theorem loopFloor_le_half_loopDefect_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (L : Nat) (hL : 2 ≤ L) :
    loopFloor w L ≤ HalfPow.half *
      (((1 : Q') - RGTransport.qpow w L) *
        ((1 : Q') - RGTransport.qpow w L)) := by
  let M := endpointChannelFloorExponent w
  let p := RGTransport.qpow w M
  let eps := (1 : Q') - w
  let delta := (1 : Q') - RGTransport.qpow w L
  have hw0' := Q'.le_of_lt hw0
  have hw1' := Q'.le_of_lt hw1
  have hp0 : (0 : Q') ≤ p := RGTransport.qpow_nonneg w hw0' M
  have heps0 : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le hw1'
  have heps1 : eps ≤ (1 : Q') := by
    have hn := Q'.neg_le_neg hw0'
    have h := Q'.add_le_add_left 1 (-w) 0 hn
    rw [Q'.add_zero'] at h
    exact h
  have hp : p ≤ eps := endpointFloorPower_le_gap hw0 hw1
  have hpL : RGTransport.qpow p L ≤ RGTransport.qpow eps L :=
    qpow_mono hp0 hp L
  have heL : RGTransport.qpow eps L ≤ RGTransport.qpow eps 2 :=
    qpow_antitone_exponent heps0 heps1 hL
  have hpoww : RGTransport.qpow w L ≤ w :=
    Q'.le_trans' _ _ _
      (qpow_antitone_exponent hw0' hw1' (by omega : 1 ≤ L))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))
  have hepsdelta : eps ≤ delta := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 (-w) (-(RGTransport.qpow w L))
        (Q'.neg_le_neg hpoww))
      (Q'.le_of_eqv (Q'.eqv_refl _))
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_trans' _ _ _ heps0 hepsdelta
  have hsquare : eps * eps ≤ delta * delta :=
    Q'.mul_le_mul_of_nonneg hepsdelta hepsdelta hdelta0 heps0
  have hiter : RGTransport.qpow w (L*M) ≤ delta*delta := by
    have hpin : Q'.eqv (RGTransport.qpow w (L*M)) (RGTransport.qpow p L) := by
      rw [Nat.mul_comm L M]
      exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow w M L)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ hpL
        (Q'.le_trans' _ _ _ heL
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv
            (Q'.mul_eqv_congr_right _ _ eps (Q'.one_mul_eqv eps))) hsquare)))
  exact Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hiter (by decide)

/-- The existing quadratic coefficient dominates 1920 copies of the proposed
floor.  This is a statement about certificate numbers only. -/
theorem nineteenTwenty_loopFloor_le_quadraticBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (L : Nat) (hL : 2 ≤ L) :
    (1920 : Q') * loopFloor w L ≤
      (960 : Q') * (((1 : Q') - RGTransport.qpow w L) *
        ((1 : Q') - RGTransport.qpow w L)) := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (1920 : Q')
    (loopFloor_le_half_loopDefect_square hw0 hw1 L hL) (by decide)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (1920 : Q') HalfPow.half
      (((1 : Q') - RGTransport.qpow w L) *
        ((1 : Q') - RGTransport.qpow w L))).symm
    (Q'.mul_eqv_congr_right _ _ _
      (by decide : Q'.eqv ((1920 : Q') * HalfPow.half) (960 : Q')))))

/-- Any coefficient paying the quadratic budget through this positive proposed
floor is at least 1920.  This does not lower-bound the physical energy. -/
theorem coefficient_ge_nineteenTwenty {w C : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (L : Nat) (hL : 2 ≤ L)
    (hpay : (960 : Q') * (((1 : Q') - RGTransport.qpow w L) *
        ((1 : Q') - RGTransport.qpow w L)) ≤ C * loopFloor w L) :
    (1920 : Q') ≤ C := by
  have hchain := Q'.le_trans' _ _ _
    (nineteenTwenty_loopFloor_le_quadraticBudget hw0 hw1 L hL) hpay
  have hcomm : loopFloor w L * (1920 : Q') ≤ loopFloor w L * C :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _).symm)
      (Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact Q'.le_of_mul_le_mul_left hcomm (loopFloor_positive hw0 L)

theorem side_succ_ge_two (scale : Nat) : 2 ≤ side (scale + 1) := by
  unfold side
  rw [Nat.pow_succ]
  have h : 0 < 2 ^ scale := Nat.pow_pos (by decide : 0 < 2)
  omega

/-- Actual dyadic-side specialization of the numerical obstruction. -/
theorem dyadic_coefficient_ge_nineteenTwenty {w C : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat)
    (hpay : (960 : Q') *
        (((1 : Q') - RGTransport.qpow w (side (scale+1))) *
          ((1 : Q') - RGTransport.qpow w (side (scale+1)))) ≤
      C * loopFloor w (side (scale+1))) :
    (1920 : Q') ≤ C :=
  coefficient_ge_nineteenTwenty hw0 hw1 _ (side_succ_ge_two scale) hpay

#print axioms loopFloor
#print axioms loopFloor_positive
#print axioms loopFloor_le_half_loopDefect_square
#print axioms nineteenTwenty_loopFloor_le_quadraticBudget
#print axioms coefficient_ge_nineteenTwenty
#print axioms side_succ_ge_two
#print axioms dyadic_coefficient_ge_nineteenTwenty

end YMGap.Continuum.BF4DyadicChannelFloorObstruction
