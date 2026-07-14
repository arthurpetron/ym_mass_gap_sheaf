/-
Direct payment of the remote first-Hermite flux by two old masses.

At the physical endpoint `N = 2D+1`, the weight-free flux has degree seven,
whereas the squared harmonic weight contributes at least `8D+8` exact
dyadic blocks after the first mode is extracted.  The polynomial-times-
dyadic envelope is decreasing already from `D=1`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem upper_flux_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "upper_flux_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               upper_flux_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private theorem polyEval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha) ?_
      exact Q'.mul_eqv_congr_left _ _ _ ihb
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private def pDiscreteHermiteFlux : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let N3 := .pow N 3
  let N4 := .pow N 4
  let N5 := .pow N 5
  let N6 := .pow N 6
  let N7 := .pow N 7
  .add (.add (.add (.add (.add (.add (.add (.add (.add
    (.mul (.mul (.const 192) N) D4)
    (.mul (.mul (.const 384) N3) D3))
    (.neg (.mul (.mul (.const 6) N) D3)))
    (.neg (.mul (.mul (.const 384) N5) D2)))
    (.mul (.mul (.const 576) N4) D2))
    (.mul (.mul (.const 184) N3) D2))
    (.mul (.mul (.const 224) N5) D))
    (.neg (.mul (.const 256) N7)))
    (.mul (.const 576) N6))
    (.mul (.const 3) D3)

private theorem lowerSixDiscreteHermiteFluxPoly_eqv_congr_N
    (D : Q') {N N' : Q'} (hN : N ≈ N') :
    lowerSixDiscreteHermiteFluxPoly D N ≈
      lowerSixDiscreteHermiteFluxPoly D N' := by
  let rho : Nat → Q' := fun | 0 => D | _ => N
  let sigma : Nat → Q' := fun | 0 => D | _ => N'
  simpa only [pDiscreteHermiteFlux, lowerSixDiscreteHermiteFluxPoly,
    RingNormaliser.eval, rho, sigma,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 6 = Q'.ofNat 6 from rfl,
    show Q'.ofInt 184 = Q'.ofNat 184 from rfl,
    show Q'.ofInt 192 = Q'.ofNat 192 from rfl,
    show Q'.ofInt 224 = Q'.ofNat 224 from rfl,
    show Q'.ofInt 256 = Q'.ofNat 256 from rfl,
    show Q'.ofInt 384 = Q'.ofNat 384 from rfl,
    show Q'.ofInt 576 = Q'.ofNat 576 from rfl] using
    (polyEval_eqv_congr pDiscreteHermiteFlux (rho := rho) (sigma := sigma)
      (by
        intro i
        rcases i with _ | i
        · exact Q'.eqv_refl _
        · exact hN))

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem ringQpow_succ_mono_of_one_le
    {D : Q'} (hD : (1 : Q') ≤ D) (m : Nat) :
    RingNormaliser.qpow D m ≤ RingNormaliser.qpow D (m + 1) := by
  let P := RingNormaliser.qpow D m
  have hP0 : (0 : Q') ≤ P :=
    ringQpow_nonnegative (Q'.le_trans' _ _ _ (by decide) hD) m
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ P hD hP0
  have hstart : P ≤ P * (1 : Q') :=
    Q'.ge_of_eqv (Q'.mul_one_eqv P)
  change P ≤ P * D
  exact Q'.le_trans' _ _ _ hstart hmul

private theorem ofNat_pow_eqv_ringQpow (D : Nat) : ∀ m,
    Q'.ofNat (D ^ m) ≈ RingNormaliser.qpow (Q'.ofNat D) m
  | 0 => by
      simpa only [Nat.pow_zero, RingNormaliser.qpow_zero] using
        (show Q'.ofNat 1 ≈ (1 : Q') by decide)
  | m + 1 => by
      rw [Nat.pow_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (D ^ m) * Q'.ofNat D) _
        (HeatKernelRGStep.ofNat_mul_eqv (D ^ m) D) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (ofNat_pow_eqv_ringQpow D m)

private def pEndpointFluxSub : PE :=
  let D : PE := .var 0
  let N : PE := .add (.mul (.const 2) D) (.const 1)
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let N3 := .pow N 3
  let N4 := .pow N 4
  let N5 := .pow N 5
  let N6 := .pow N 6
  let N7 := .pow N 7
  .add (.add (.add (.add (.add (.add (.add (.add (.add
    (.mul (.mul (.const 192) N) D4)
    (.mul (.mul (.const 384) N3) D3))
    (.neg (.mul (.mul (.const 6) N) D3)))
    (.neg (.mul (.mul (.const 384) N5) D2)))
    (.mul (.mul (.const 576) N4) D2))
    (.mul (.mul (.const 184) N3) D2))
    (.mul (.mul (.const 224) N5) D))
    (.neg (.mul (.const 256) N7)))
    (.mul (.const 576) N6))
    (.mul (.const 3) D3)

private def pEndpointFluxExpanded : PE :=
  let D : PE := .var 0
  .add (.add (.add (.add (.add (.add (.add
    (.neg (.mul (.const 45056) (.pow D 7)))
    (.neg (.mul (.const 89088) (.pow D 6))))
    (.neg (.mul (.const 49344) (.pow D 5))))
    (.mul (.const 15956) (.pow D 4)))
    (.mul (.const 31693) (.pow D 3)))
    (.mul (.const 15672) (.pow D 2)))
    (.mul (.const 3552) D))
    (.const 320)

private theorem pEndpointFluxExpanded_normal :
    RingNormaliser.normalize pEndpointFluxSub =
      RingNormaliser.normalize pEndpointFluxExpanded := by decide

private def endpointFluxExpandedQ (D : Q') : Q' :=
  -(Q'.ofNat 45056 * RingNormaliser.qpow D 7) +
  -(Q'.ofNat 89088 * RingNormaliser.qpow D 6) +
  -(Q'.ofNat 49344 * RingNormaliser.qpow D 5) +
  Q'.ofNat 15956 * RingNormaliser.qpow D 4 +
  Q'.ofNat 31693 * RingNormaliser.qpow D 3 +
  Q'.ofNat 15672 * RingNormaliser.qpow D 2 +
  Q'.ofNat 3552 * D + Q'.ofNat 320

private def endpointFluxPositiveQ (D : Q') : Q' :=
  (Q'.ofNat 45056 * RingNormaliser.qpow D 7 +
    Q'.ofNat 89088 * RingNormaliser.qpow D 6) +
    Q'.ofNat 49344 * RingNormaliser.qpow D 5

private def endpointFluxLowerQ (D : Q') : Q' :=
  Q'.ofNat 15956 * RingNormaliser.qpow D 4 +
  Q'.ofNat 31693 * RingNormaliser.qpow D 3 +
  Q'.ofNat 15672 * RingNormaliser.qpow D 2 +
  Q'.ofNat 3552 * D + Q'.ofNat 320

private theorem endpointFlux_substitution_algebra (D : Q') :
    lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat 2 * D + (1 : Q')) ≈
      endpointFluxExpandedQ D := by
  simpa only [pEndpointFluxSub, pEndpointFluxExpanded,
    endpointFluxExpandedQ, lowerSixDiscreteHermiteFluxPoly,
    RingNormaliser.eval,
    show Q'.ofInt 1 = Q'.ofNat 1 from rfl,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 6 = Q'.ofNat 6 from rfl,
    show Q'.ofInt 184 = Q'.ofNat 184 from rfl,
    show Q'.ofInt 192 = Q'.ofNat 192 from rfl,
    show Q'.ofInt 224 = Q'.ofNat 224 from rfl,
    show Q'.ofInt 256 = Q'.ofNat 256 from rfl,
    show Q'.ofInt 320 = Q'.ofNat 320 from rfl,
    show Q'.ofInt 384 = Q'.ofNat 384 from rfl,
    show Q'.ofInt 576 = Q'.ofNat 576 from rfl,
    show Q'.ofInt 3552 = Q'.ofNat 3552 from rfl,
    show Q'.ofInt 15672 = Q'.ofNat 15672 from rfl,
    show Q'.ofInt 15956 = Q'.ofNat 15956 from rfl,
    show Q'.ofInt 31693 = Q'.ofNat 31693 from rfl,
    show Q'.ofInt 45056 = Q'.ofNat 45056 from rfl,
    show Q'.ofInt 49344 = Q'.ofNat 49344 from rfl,
    show Q'.ofInt 89088 = Q'.ofNat 89088 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      pEndpointFluxSub pEndpointFluxExpanded
      pEndpointFluxExpanded_normal (fun _ => D))

private def pEndpointNegL : PE :=
  .neg pEndpointFluxExpanded

private def pEndpointNegR : PE :=
  let D : PE := .var 0
  let P := .add (.add
    (.mul (.const 45056) (.pow D 7))
    (.mul (.const 89088) (.pow D 6)))
    (.mul (.const 49344) (.pow D 5))
  let N := .add (.add (.add (.add
    (.mul (.const 15956) (.pow D 4))
    (.mul (.const 31693) (.pow D 3)))
    (.mul (.const 15672) (.pow D 2)))
    (.mul (.const 3552) D))
    (.const 320)
  .add P (.neg N)

private theorem pEndpointNeg_normal :
    RingNormaliser.normalize pEndpointNegL =
      RingNormaliser.normalize pEndpointNegR := by decide

private theorem endpointFlux_negative_algebra (D : Q') :
    -(endpointFluxExpandedQ D) ≈
      endpointFluxPositiveQ D + -(endpointFluxLowerQ D) := by
  simpa [pEndpointNegL, pEndpointNegR, pEndpointFluxExpanded,
    endpointFluxExpandedQ, endpointFluxPositiveQ, endpointFluxLowerQ,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pEndpointNegL pEndpointNegR pEndpointNeg_normal (fun _ => D))

/-- Exact degree-seven envelope for the negative remote flux polynomial. -/
theorem negative_endpointFluxPoly_le_degreeSeven
    {D : Q'} (hD : (1 : Q') ≤ D) :
    -lowerSixDiscreteHermiteFluxPoly D
        (Q'.ofNat 2 * D + (1 : Q')) ≤
      Q'.ofNat 183488 * RingNormaliser.qpow D 7 := by
  have hD0 : (0 : Q') ≤ D := Q'.le_trans' _ _ _ (by decide) hD
  let P := endpointFluxPositiveQ D
  let N := endpointFluxLowerQ D
  have hN0 : (0 : Q') ≤ N := by
    dsimp only [N, endpointFluxLowerQ]
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (by decide)
              (ringQpow_nonnegative hD0 4))
            (Q'.mul_nonneg _ _ (by decide)
              (ringQpow_nonnegative hD0 3)))
          (Q'.mul_nonneg _ _ (by decide)
            (ringQpow_nonnegative hD0 2)))
        (Q'.mul_nonneg _ _ (by decide) hD0))
      (by decide)
  have hdrop : P + -N ≤ P := by
    have hn := Q'.nonpos_neg_of_nonneg hN0
    have hadd := Q'.add_le_add_left P _ _ hn
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv P))
  have hsub := endpointFlux_substitution_algebra D
  have hnegsub :
      -lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat 2 * D + (1 : Q')) ≈
        P + -N := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hsub) ?_
    dsimp only [P, N]
    exact endpointFlux_negative_algebra D
  have h56 := ringQpow_succ_mono_of_one_le hD 5
  have h67 := ringQpow_succ_mono_of_one_le hD 6
  have h56' : RingNormaliser.qpow D 5 ≤ RingNormaliser.qpow D 6 := by
    simpa using h56
  have h67' : RingNormaliser.qpow D 6 ≤ RingNormaliser.qpow D 7 := by
    simpa using h67
  have h57 := Q'.le_trans' _ _ _ h56' h67'
  have h6scaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 89088)
    h67' (by decide)
  have h5scaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 49344)
    h57 (by decide)
  have hadd1 := Q'.add_le_add_left
    (Q'.ofNat 45056 * RingNormaliser.qpow D 7) _ _ h6scaled
  have hadd2 := Q'.add_le_add_right _ _
    (Q'.ofNat 49344 * RingNormaliser.qpow D 5) hadd1
  have hadd3 := Q'.add_le_add_left
    ((Q'.ofNat 45056 * RingNormaliser.qpow D 7) +
      Q'.ofNat 89088 * RingNormaliser.qpow D 7) _ _ h5scaled
  have hP : P ≤ Q'.ofNat 183488 * RingNormaliser.qpow D 7 := by
    change endpointFluxPositiveQ D ≤ _
    exact Q'.le_trans' _ _ _ hadd2
      (Q'.le_trans' _ _ _ hadd3 (Q'.le_of_eqv (by
        let X := RingNormaliser.qpow D 7
        have hfirst :
            (Q'.ofNat 45056 * X + Q'.ofNat 89088 * X) +
                Q'.ofNat 49344 * X ≈
              ((Q'.ofNat 45056 + Q'.ofNat 89088) * X) +
                Q'.ofNat 49344 * X :=
          Q'.add_eqv_congr_right _ _ _
            (Q'.eqv_symm (Q'.add_mul_eqv _ _ X))
        have hsecond :
            ((Q'.ofNat 45056 + Q'.ofNat 89088) * X) +
                Q'.ofNat 49344 * X ≈
              ((Q'.ofNat 45056 + Q'.ofNat 89088) +
                Q'.ofNat 49344) * X :=
          Q'.eqv_symm (Q'.add_mul_eqv _ _ X)
        have hconst :
            (Q'.ofNat 45056 + Q'.ofNat 89088) + Q'.ofNat 49344 ≈
              Q'.ofNat 183488 := by decide
        exact Q'.eqv_trans _ _ _ hfirst
          (Q'.eqv_trans _ _ _ hsecond
            (Q'.mul_eqv_congr_right _ _ X hconst)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnegsub)
    (Q'.le_trans' _ _ _ hdrop hP)

private theorem growingAnchor_endpoint_cast (k : Nat) :
    Q'.ofNat (growingAnchor k + 1) ≈
      Q'.ofNat 2 * Q'.ofNat (k + 2) + (1 : Q') := by
  unfold growingAnchor
  refine Q'.eqv_trans _
    (Q'.ofNat (2 * (k + 2)) + Q'.ofNat 1) _
    (Q'.ofNat_add_eqv (2 * (k + 2)) 1) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (HeatKernelRGStep.ofNat_mul_eqv 2 (k + 2))

/-- The same degree-seven envelope at the actual old-scale remote endpoint. -/
private theorem negative_actual_endpointFluxPoly_le_degreeSeven (k : Nat) :
    -lowerSixDiscreteHermiteFluxPoly (Q'.ofNat (k + 2))
        (Q'.ofNat (growingAnchor k + 1)) ≤
      Q'.ofNat 183488 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 7 := by
  let D := Q'.ofNat (k + 2)
  have hD : (1 : Q') ≤ D := by
    dsimp only [D]
    exact CReal.ofNat_le_ofNat (by omega : 1 ≤ k + 2)
  have hpoly := negative_endpointFluxPoly_le_degreeSeven hD
  have hendpoint := lowerSixDiscreteHermiteFluxPoly_eqv_congr_N D
    (growingAnchor_endpoint_cast k)
  have hneg :
      -lowerSixDiscreteHermiteFluxPoly D
          (Q'.ofNat (growingAnchor k + 1)) ≈
        -lowerSixDiscreteHermiteFluxPoly D
          (Q'.ofNat 2 * D + (1 : Q')) :=
    Q'.neg_eqv_congr _ _ hendpoint
  dsimp only [D] at hneg hpoly ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) hpoly

private def dyadicFluxEnvelope (D : Nat) : Q' :=
  Q'.ofNat (183488 * D ^ 4) *
    qpow HalfPow.half (8 * D + 8)

private theorem dyadicFluxEnvelope_step
    {D : Nat} (hD : 1 ≤ D) :
    dyadicFluxEnvelope (D + 1) ≤ dyadicFluxEnvelope D := by
  have hbase : D + 1 ≤ 2 * D := by omega
  have hpow : (D + 1) ^ 4 ≤ (2 * D) ^ 4 :=
    Nat.pow_le_pow_left hbase 4
  have hpow16 : (D + 1) ^ 4 ≤ 16 * D ^ 4 := by
    simpa [Nat.mul_pow] using hpow
  have hnat : 183488 * (D + 1) ^ 4 ≤
      16 * (183488 * D ^ 4) := by
    have h := Nat.mul_le_mul_left 183488 hpow16
    omega
  have hcast := CReal.ofNat_le_ofNat hnat
  let A := Q'.ofNat (183488 * D ^ 4)
  let H := qpow HalfPow.half (8 * D + 8)
  let E := qpow HalfPow.half 8
  have hH0 : (0 : Q') ≤ H := qpow_nonneg _ HalfPow.half_nonneg _
  have hE0 : (0 : Q') ≤ E := qpow_nonneg _ HalfPow.half_nonneg _
  have hHE0 : (0 : Q') ≤ H * E := Q'.mul_nonneg _ _ hH0 hE0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (H * E) hcast hHE0
  have hexp : 8 * (D + 1) + 8 = (8 * D + 8) + 8 := by omega
  have hsplit : qpow HalfPow.half (8 * (D + 1) + 8) ≈ H * E := by
    rw [hexp]
    dsimp only [H, E]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hleft : dyadicFluxEnvelope (D + 1) ≈
      Q'.ofNat (183488 * (D + 1) ^ 4) * (H * E) := by
    unfold dyadicFluxEnvelope
    exact Q'.mul_eqv_congr_left _ _ _ hsplit
  have hcastRight : Q'.ofNat (16 * (183488 * D ^ 4)) ≈
      Q'.ofNat 16 * A := by
    dsimp only [A]
    exact HeatKernelRGStep.ofNat_mul_eqv 16 (183488 * D ^ 4)
  have hmid :
      Q'.ofNat (16 * (183488 * D ^ 4)) * (H * E) ≈
        A * (H * (Q'.ofNat 16 * E)) := by
    refine Q'.eqv_trans _ ((Q'.ofNat 16 * A) * (H * E)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hcastRight
    · upper_flux_ring
  have h16E : Q'.ofNat 16 * E ≤ (1 : Q') := by
    dsimp only [E, HalfPow.half, qpow]
    decide
  have hHscaled := Q'.mul_le_mul_of_nonneg_left _ _ H h16E hH0
  have hAscaled := Q'.mul_le_mul_of_nonneg_left _ _ A hHscaled
    (HeatKernelRGStep.zero_le_ofNat _)
  have hright : A * (H * (1 : Q')) ≈ dyadicFluxEnvelope D := by
    unfold dyadicFluxEnvelope
    dsimp only [A, H]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmid)
        (Q'.le_trans' _ _ _ hAscaled (Q'.le_of_eqv hright))))

private theorem dyadicFluxEnvelope_antitone
    (D t : Nat) (hD : 1 ≤ D) :
    dyadicFluxEnvelope (D + t) ≤ dyadicFluxEnvelope D := by
  induction t with
  | zero =>
      rw [Nat.add_zero]
      exact Q'.le_refl' _
  | succ t ih =>
      rw [Nat.add_succ]
      exact Q'.le_trans' _ _ _
        (dyadicFluxEnvelope_step (show 1 ≤ D + t by omega)) ih

theorem degreeFour_dyadicFlux_le_three
    {D : Nat} (hD : 1 ≤ D) :
    Q'.ofNat 183488 * RingNormaliser.qpow (Q'.ofNat D) 4 *
        qpow HalfPow.half (8 * D + 8) ≤ Q'.ofNat 3 := by
  have hanti := dyadicFluxEnvelope_antitone 1 (D - 1) (by decide)
  have hidx : 1 + (D - 1) = D := by omega
  rw [hidx] at hanti
  have hone : dyadicFluxEnvelope 1 ≤ Q'.ofNat 3 := by
    unfold dyadicFluxEnvelope HalfPow.half qpow
    decide
  have hbound := Q'.le_trans' _ _ _ hanti hone
  have hleft :
      Q'.ofNat 183488 * RingNormaliser.qpow (Q'.ofNat D) 4 *
          qpow HalfPow.half (8 * D + 8) ≈
        dyadicFluxEnvelope D := by
    unfold dyadicFluxEnvelope
    have hcoef :
        Q'.ofNat 183488 * RingNormaliser.qpow (Q'.ofNat D) 4 ≈
          Q'.ofNat (183488 * D ^ 4) := by
      refine Q'.eqv_trans _
        (Q'.ofNat 183488 * Q'.ofNat (D ^ 4)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (ofNat_pow_eqv_ringQpow D 4))
      · exact Q'.eqv_symm
          (HeatKernelRGStep.ofNat_mul_eqv 183488 (D ^ 4))
    exact Q'.mul_eqv_congr_right _ _ _ hcoef
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hbound

private theorem squaredBase_qpow_eqv_double (w : Q') (m : Nat) :
    qpow (w * w) m ≈ qpow w (m + m) := by
  exact Q'.eqv_trans _ _ _
    (FusionQuotientCollapse.qpow_mul_self w m)
    (Q'.eqv_symm (HeatKernelRGStep.qpow_add w m m))

/-- After extracting the first old-scale mode, the remote endpoint retains
at least `8D+8` exact dyadic harmonic blocks. -/
theorem lowerSixUpperEndpointWeight_le_first_dyadic (k : Nat) :
    lowerSixModeWeight k (growingAnchor k + 1) ≤
      lowerSixModeWeight k 1 *
        qpow HalfPow.half (8 * (k + 2) + 8) := by
  let D := k + 2
  let n := growingAnchor k + 1
  let r := n * n - 1
  let L := 8 * D + 8
  let w := harmW k
  let sigma := w * w
  let W1 := lowerSixModeWeight k 1
  let R := qpow sigma r
  let H := qpow HalfPow.half L
  have hnpos : 0 < n := by
    dsimp only [n]
    unfold growingAnchor
    omega
  have hexp : 1 + r = n * n := by
    have hsquarepos : 0 < n * n := Nat.mul_pos hnpos hnpos
    dsimp only [r]
    omega
  have hsplit0 := HeatKernelRGStep.qpow_add sigma 1 r
  rw [hexp] at hsplit0
  have hsplit : lowerSixModeWeight k n ≈ W1 * R := by
    unfold lowerSixModeWeight
    dsimp only [W1, R, sigma, w, n]
    exact hsplit0
  have hdouble := squaredBase_qpow_eqv_double w r
  have hindex : r + r = D * L := by
    have hn : n = 2 * D + 1 := by
      dsimp only [n, D]
      unfold growingAnchor
      rfl
    have hsquare : (2 * D + 1) * (2 * D + 1) =
        4 * (D * D) + 4 * D + 1 := by
      have hquad : (2 * D) * (2 * D) = 4 * (D * D) := by ac_rfl
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, hquad]
      omega
    have hr : r = 4 * (D * D) + 4 * D := by
      dsimp only [r]
      rw [hn, hsquare]
      omega
    rw [hr]
    rw [show L = 8 * D + 8 from rfl]
    have hac : 8 * (D * D) = D * (8 * D) := by ac_rfl
    calc
      (4 * (D * D) + 4 * D) + (4 * (D * D) + 4 * D) =
          8 * (D * D) + 8 * D := by omega
      _ = D * (8 * D) + D * 8 := by
        rw [hac, Nat.mul_comm 8 D]
      _ = D * (8 * D + 8) := by
        exact (Nat.mul_add D (8 * D) 8).symm
  rw [hindex] at hdouble
  have hiter := HeatKernelRGStep.qpow_qpow w D L
  have hratio : R ≈ qpow (qpow w D) L := by
    dsimp only [R, sigma]
    exact Q'.eqv_trans _ _ _ hdouble (Q'.eqv_symm hiter)
  have hblock : qpow w D ≤ HalfPow.half := by
    dsimp only [w, D]
    exact harmonic_block_power_le_half k
  have hbase0 : (0 : Q') ≤ qpow w D :=
    qpow_nonneg _ (by
      dsimp only [w]
      exact harmW_nonneg k) _
  have hmono := HeatKernelGap.qpow_mono hbase0 hblock L
  have hRH : R ≤ H :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hratio) hmono
  have hW10 : (0 : Q') ≤ W1 := by
    dsimp only [W1]
    exact lowerSixModeWeight_nonnegative k 1
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ W1 hRH hW10
  dsimp only [n, W1, R, H, L] at hsplit hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hmul

private theorem lowerSixFirstWeight_le_HermiteWeightSum (k : Nat) :
    lowerSixModeWeight k 1 ≤ lowerSixHermiteWeightSum k := by
  let f : Nat → Q' := fun j => lowerSixModeWeight k (j + 1)
  have hmono : finSum f 1 ≤ finSum f (growingAnchor k) :=
    finSum_monotone_of_nonneg f
      (fun j => lowerSixModeWeight_nonnegative k (j + 1))
      1 (growingAnchor k) (by
        unfold growingAnchor
        omega)
  have hone : lowerSixModeWeight k 1 ≈ finSum f 1 := by
    change lowerSixModeWeight k 1 ≈
      (0 : Q') + lowerSixModeWeight k 1
    exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  unfold lowerSixHermiteWeightSum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hone) hmono

private theorem lowerSixFirstMass_le_HermiteMass (k : Nat) :
    (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
        lowerSixModeWeight k 1 ≤
      lowerSixHermiteMassSum k := by
  let C := Q'.ofNat 6 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hD0 : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC0 : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD0 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C
    (lowerSixFirstWeight_le_HermiteWeightSum k) hC0
  have hmass := lowerSixHermiteMassSum_eqv_scaledWeightSum k
  dsimp only [C] at hscaled
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_symm hmass))

private def pUpperWeightedL : PE :=
  let D : PE := .var 0
  let W : PE := .var 1
  let H : PE := .var 2
  .mul
    (.mul (.const 4) (.mul (.const 183488) (.pow D 7)))
    (.mul W H)

private def pUpperWeightedR : PE :=
  let D : PE := .var 0
  let W : PE := .var 1
  let H : PE := .var 2
  .mul
    (.mul (.const 4) (.mul (.pow D 3) W))
    (.mul (.mul (.const 183488) (.pow D 4)) H)

private theorem pUpperWeighted_normal :
    RingNormaliser.normalize pUpperWeightedL =
      RingNormaliser.normalize pUpperWeightedR := by decide

private theorem upper_weighted_algebra (D W H : Q') :
    (Q'.ofNat 4 *
        (Q'.ofNat 183488 * RingNormaliser.qpow D 7)) * (W * H) ≈
      (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W)) *
        ((Q'.ofNat 183488 * RingNormaliser.qpow D 4) * H) := by
  let rho : Nat → Q' := fun
    | 0 => D
    | 1 => W
    | _ => H
  simpa [pUpperWeightedL, pUpperWeightedR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pUpperWeightedL pUpperWeightedR pUpperWeighted_normal rho)

private def pUpperWeightedFinalL : PE :=
  let D : PE := .var 0
  let W : PE := .var 1
  .mul (.mul (.const 4) (.mul (.pow D 3) W)) (.const 3)

private def pUpperWeightedFinalR : PE :=
  let D : PE := .var 0
  let W : PE := .var 1
  .mul (.const 12) (.mul (.pow D 3) W)

private theorem pUpperWeightedFinal_normal :
    RingNormaliser.normalize pUpperWeightedFinalL =
      RingNormaliser.normalize pUpperWeightedFinalR := by decide

private theorem upper_weighted_final_algebra (D W : Q') :
    (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W)) * Q'.ofNat 3 ≈
      Q'.ofNat 12 * (RingNormaliser.qpow D 3 * W) := by
  simpa [pUpperWeightedFinalL, pUpperWeightedFinalR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pUpperWeightedFinalL pUpperWeightedFinalR
      pUpperWeightedFinal_normal (fun | 0 => D | _ => W))

/-- The exponentially remote first Hermite flux is paid by two copies of
the old-scale positive Hermite mass.  No large-scale hypothesis is needed. -/
theorem lowerSixFirstUpperFlux_le_two_HermiteMass (k : Nat) :
    -(Q'.ofNat 4 *
        lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≤
      Q'.ofNat 2 * lowerSixHermiteMassSum k := by
  let D := Q'.ofNat (k + 2)
  let Wn := lowerSixModeWeight k (growingAnchor k + 1)
  let W1 := lowerSixModeWeight k 1
  let H := qpow HalfPow.half (8 * (k + 2) + 8)
  let P := lowerSixDiscreteHermiteFluxPoly D
    (Q'.ofNat (growingAnchor k + 1))
  let K := Q'.ofNat 183488
  let M := lowerSixHermiteMassSum k
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hWn0 : (0 : Q') ≤ Wn := by
    dsimp only [Wn]
    exact lowerSixModeWeight_nonnegative k _
  have hW10 : (0 : Q') ≤ W1 := by
    dsimp only [W1]
    exact lowerSixModeWeight_nonnegative k 1
  have hpoly : -P ≤ K * RingNormaliser.qpow D 7 := by
    dsimp only [P, K, D]
    exact negative_actual_endpointFluxPoly_le_degreeSeven k
  have hfourWn0 : (0 : Q') ≤ Q'.ofNat 4 * Wn :=
    Q'.mul_nonneg _ _ (by decide) hWn0
  have hpolyScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 4 * Wn) hpoly hfourWn0
  have hfluxFactor :
      -(Q'.ofNat 4 * (Wn * P)) ≈
        (Q'.ofNat 4 * Wn) * (-P) := by
    upper_flux_ring
  have hpolyReorder :
      (Q'.ofNat 4 * Wn) *
          (K * RingNormaliser.qpow D 7) ≈
        (Q'.ofNat 4 * (K * RingNormaliser.qpow D 7)) * Wn := by
    upper_flux_ring
  have hpolyPaid :
      -(Q'.ofNat 4 * (Wn * P)) ≤
        (Q'.ofNat 4 * (K * RingNormaliser.qpow D 7)) * Wn :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hfluxFactor)
      (Q'.le_trans' _ _ _ hpolyScaled (Q'.le_of_eqv hpolyReorder))
  have hweight : Wn ≤ W1 * H := by
    dsimp only [Wn, W1, H]
    exact lowerSixUpperEndpointWeight_le_first_dyadic k
  have hD7nonneg : (0 : Q') ≤ RingNormaliser.qpow D 7 :=
    ringQpow_nonnegative hD0 7
  have hweightScale0 :
      (0 : Q') ≤ Q'.ofNat 4 * (K * RingNormaliser.qpow D 7) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (by decide) hD7nonneg)
  have hweightScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 4 * (K * RingNormaliser.qpow D 7))
    hweight hweightScale0
  have halgebra := upper_weighted_algebra D W1 H
  have henv :
      (K * RingNormaliser.qpow D 4) * H ≤ Q'.ofNat 3 := by
    dsimp only [K, D, H]
    exact degreeFour_dyadicFlux_le_three (show 1 ≤ k + 2 by omega)
  have hD3W0 : (0 : Q') ≤ RingNormaliser.qpow D 3 * W1 :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hD0 3) hW10
  have henvScale0 :
      (0 : Q') ≤ Q'.ofNat 4 *
        (RingNormaliser.qpow D 3 * W1) :=
    Q'.mul_nonneg _ _ (by decide) hD3W0
  have henvScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 4 * (RingNormaliser.qpow D 3 * W1))
    henv henvScale0
  have hfinalAlg := upper_weighted_final_algebra D W1
  have htoFirstMass :
      (Q'.ofNat 4 * (K * RingNormaliser.qpow D 7)) * (W1 * H) ≤
        Q'.ofNat 12 * (RingNormaliser.qpow D 3 * W1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv halgebra)
      (Q'.le_trans' _ _ _ henvScaled (Q'.le_of_eqv hfinalAlg))
  have hfirstMass :
      (Q'.ofNat 6 * RingNormaliser.qpow D 3) * W1 ≤ M := by
    dsimp only [D, W1, M]
    exact lowerSixFirstMass_le_HermiteMass k
  have htwoMass := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hfirstMass (by decide)
  have hmassAlg :
      Q'.ofNat 12 * (RingNormaliser.qpow D 3 * W1) ≈
        Q'.ofNat 2 *
          ((Q'.ofNat 6 * RingNormaliser.qpow D 3) * W1) := by
    upper_flux_ring
  have hstart :
      -(Q'.ofNat 4 *
          lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≈
        -(Q'.ofNat 4 * (Wn * P)) := by
    unfold lowerSixDiscreteHermiteFluxNumerator
    dsimp only [Wn, P, D]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _ hpolyPaid
      (Q'.le_trans' _ _ _ hweightScaled
        (Q'.le_trans' _ _ _ htoFirstMass
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmassAlg) htwoMass))))

/-- Closed large-scale cubic-debt reserve residual: the former remote-flux
input is discharged by `lowerSixFirstUpperFlux_le_two_HermiteMass`. -/
theorem lowerSixCubicDebtMassReserveResidual_nonnegative_large_closed
    {k : Nat} (hk : 8189 ≤ k) :
    (0 : Q') ≤ lowerSixCubicDebtMassReserveResidual k := by
  exact lowerSixCubicDebtMassReserveResidual_nonnegative_large hk
    (lowerSixFirstUpperFlux_le_two_HermiteMass k)

/-- Production composition with only the signed finite-`D` Hermite
remainder payment left as an input. -/
theorem lowerSixQuadraticPayment_large_of_remainder
    {k : Nat} (hk : 8189 ≤ k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  exact lowerSixQuadraticPayment_large_of_remainder_and_upperFlux hk
    hremainder (lowerSixFirstUpperFlux_le_two_HermiteMass k)

#print axioms negative_endpointFluxPoly_le_degreeSeven
#print axioms degreeFour_dyadicFlux_le_three
#print axioms lowerSixUpperEndpointWeight_le_first_dyadic
#print axioms lowerSixFirstUpperFlux_le_two_HermiteMass
#print axioms lowerSixCubicDebtMassReserveResidual_nonnegative_large_closed
#print axioms lowerSixQuadraticPayment_large_of_remainder

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment
