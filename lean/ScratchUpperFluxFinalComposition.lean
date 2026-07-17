import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment

namespace ScratchUpperFluxFinalComposition

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem upper_final_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "upper_final_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               upper_final_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

example (k : Nat) :
    lowerSixModeWeight k (growingAnchor k + 1) ≤
      lowerSixModeWeight k 1 * qpow HalfPow.half (8 * (k + 2) + 8) := by
  exact lowerSixUpperEndpointWeight_le_first_dyadic k

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem lowerSixDiscreteHermiteFluxPoly_eqv_congr
    {D D' N N' : Q'} (hD : D ≈ D') (hN : N ≈ N') :
    lowerSixDiscreteHermiteFluxPoly D N ≈
      lowerSixDiscreteHermiteFluxPoly D' N' := by
  unfold lowerSixDiscreteHermiteFluxPoly
  repeat' first
    | apply Q'.add_eqv_congr'
    | apply Q'.neg_eqv_congr
    | apply Q'.mul_eqv_congr'
    | apply RingNormaliser.qpow_eqv_congr
    | exact hD
    | exact hN
    | exact Q'.eqv_refl _

private theorem upperEndpoint_cast_eqv (k : Nat) :
    Q'.ofNat (growingAnchor k + 1) ≈
      Q'.ofNat 2 * Q'.ofNat (k + 2) + (1 : Q') := by
  unfold growingAnchor
  refine Q'.eqv_trans _
    (Q'.ofNat (2 * (k + 2)) + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.ofNat_add_eqv (2 * (k + 2)) 1
  · exact Q'.add_eqv_congr'
      (HeatKernelRGStep.ofNat_mul_eqv 2 (k + 2)) (by decide)

/-- Independent scratch composition of the production polynomial and dyadic
lemmas: the adverse upper endpoint costs at most twelve first-mode mass
units. -/
theorem negative_four_upperFlux_le_firstMass (k : Nat) :
    -(Q'.ofNat 4 *
        lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≤
      Q'.ofNat 12 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 *
          lowerSixModeWeight k 1) := by
  let D := Q'.ofNat (k + 2)
  let W := lowerSixModeWeight k (growingAnchor k + 1)
  let W1 := lowerSixModeWeight k 1
  let H := qpow HalfPow.half (8 * (k + 2) + 8)
  let J := lowerSixDiscreteHermiteFluxPoly D
    (Q'.ofNat 2 * D + (1 : Q'))
  let C7 := Q'.ofNat 183488 * RingNormaliser.qpow D 7
  have hD1 : (1 : Q') ≤ D := by
    dsimp only [D]
    exact CReal.ofNat_le_ofNat (by omega)
  have hD0 : (0 : Q') ≤ D :=
    Q'.le_trans' _ _ _ (by decide) hD1
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W]
    exact lowerSixModeWeight_nonnegative k _
  have hW10 : (0 : Q') ≤ W1 := by
    dsimp only [W1]
    exact lowerSixModeWeight_nonnegative k 1
  have hC70 : (0 : Q') ≤ C7 := by
    dsimp only [C7]
    exact Q'.mul_nonneg _ _ (by decide)
      (ringQpow_nonnegative hD0 7)
  have hJ : -J ≤ C7 := by
    dsimp only [J, C7]
    exact negative_endpointFluxPoly_le_degreeSeven hD1
  have hweighted0 := Q'.mul_le_mul_of_nonneg_left _ _ W hJ hW0
  have hweighted : W * (-J) ≤ C7 * (W1 * H) := by
    have hcomm : W * C7 ≈ C7 * W := Q'.mul_comm_eqv _ _
    have hendpoint := lowerSixUpperEndpointWeight_le_first_dyadic k
    have hendpointScaled := Q'.mul_le_mul_of_nonneg_left _ _ C7
      hendpoint hC70
    dsimp only [W, W1, H] at hendpointScaled
    exact Q'.le_trans' _ _ _ hweighted0
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hendpointScaled)
  have hfour := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4)
    hweighted (by decide)
  have hDsplit : RingNormaliser.qpow D 7 ≈
      RingNormaliser.qpow D 3 * RingNormaliser.qpow D 4 := by
    have h := HeatKernelRGStep.qpow_add D 3 4
    simpa using h
  have hright : Q'.ofNat 4 * (C7 * (W1 * H)) ≈
      (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W1)) *
        ((Q'.ofNat 183488 * RingNormaliser.qpow D 4) * H) := by
    dsimp only [C7]
    refine Q'.eqv_trans _
      (Q'.ofNat 4 *
        ((Q'.ofNat 183488 *
          (RingNormaliser.qpow D 3 * RingNormaliser.qpow D 4)) *
            (W1 * H))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hDsplit))
    · upper_final_ring
  have hdegree := degreeFour_dyadicFlux_le_three
    (D := k + 2) (by omega : 1 ≤ k + 2)
  have hfront0 : (0 : Q') ≤
      Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W1) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ringQpow_nonnegative hD0 3) hW10)
  have hdegreeScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W1)) hdegree hfront0
  have hfinal :
      (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W1)) * Q'.ofNat 3 ≈
        Q'.ofNat 12 * (RingNormaliser.qpow D 3 * W1) := by
    upper_final_ring
  have hcanonical : Q'.ofNat 4 * (W * (-J)) ≤
      Q'.ofNat 12 * (RingNormaliser.qpow D 3 * W1) :=
    Q'.le_trans' _ _ _ hfour
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.le_trans' _ _ _ hdegreeScaled (Q'.le_of_eqv hfinal)))
  have hpoly := lowerSixDiscreteHermiteFluxPoly_eqv_congr
    (Q'.eqv_refl D) (upperEndpoint_cast_eqv k)
  have hflux :
      lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1) ≈
        W * J := by
    unfold lowerSixDiscreteHermiteFluxNumerator
    dsimp only [W, J, D]
    exact Q'.mul_eqv_congr_left _ _ _ hpoly
  have hneg :
      -(Q'.ofNat 4 *
          lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≈
        Q'.ofNat 4 * (W * (-J)) := by
    refine Q'.eqv_trans _ (-(Q'.ofNat 4 * (W * J))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hflux)
    · upper_final_ring
  dsimp only [D, W1] at hcanonical ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) hcanonical

#print axioms negative_four_upperFlux_le_firstMass

end ScratchUpperFluxFinalComposition
