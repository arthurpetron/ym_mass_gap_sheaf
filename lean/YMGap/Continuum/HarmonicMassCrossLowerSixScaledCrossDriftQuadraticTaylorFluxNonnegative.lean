/-
Term structure for the nonnegativity of the cleared lower-six Taylor flux.

Pointwise positivity is false even after adding the positive Hermite mass.
This file factors those cells through their old Gaussian weight, exposing a
short-step bracket suitable for a summed Abel/Gaussian-moment estimate, and
separately isolates the exact endpoint/low-flux cancellation.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem flux_nonnegative_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "flux_nonnegative_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               flux_nonnegative_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_add, Int.natCast_mul,
               Int.natCast_one, Int.natCast_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pMassNetL : PE :=
  let M : PE := .var 0
  let A : PE := .var 1
  let W : PE := .var 2
  let C : PE := .var 3
  let S : PE := .var 4
  let Jp : PE := .var 5
  let Jn : PE := .var 6
  .add M
    (.add
      (.add (.mul A (.mul W C))
        (.neg (.add (.mul (.mul W S) Jp) (.neg (.mul W Jn)))))
      (.neg M))

private def pMassNetR : PE :=
  let A : PE := .var 1
  let W : PE := .var 2
  let C : PE := .var 3
  let S : PE := .var 4
  let Jp : PE := .var 5
  let Jn : PE := .var 6
  .mul W (.add (.mul A C) (.neg (.add (.mul S Jp) (.neg Jn))))

private theorem pMassNet_normal :
    RingNormaliser.normalize pMassNetL =
      RingNormaliser.normalize pMassNetR := by decide

private theorem massNet_algebra (M A W C S Jp Jn : Q') :
    M + (A * (W * C) + -((W * S) * Jp + -(W * Jn)) + -M) ≈
      W * (A * C + -(S * Jp + -Jn)) := by
  simpa [pMassNetL, pMassNetR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pMassNetL pMassNetR pMassNet_normal
      (fun | 0 => M | 1 => A | 2 => W | 3 => C | 4 => S |
        5 => Jp | _ => Jn))

/-- Weight-free short-step bracket for one Hermite mass-plus-remainder cell. -/
def lowerSixHermiteNetBracket (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  Q'.ofNat 48 * RingNormaliser.qpow D 4 *
      lowerSixQuadraticTaylorCarrier k n +
    -(step * J (n + 1) + -J n)

private theorem lowerSixModeWeight_succ_eqv (k n : Nat) :
    lowerSixModeWeight k (n + 1) ≈
      lowerSixModeWeight k n *
        qpow (harmW k * harmW k) (2 * n + 1) := by
  have hexp : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  unfold lowerSixModeWeight
  rw [hexp]
  exact HeatKernelRGStep.qpow_add
    (harmW k * harmW k) (n * n) (2 * n + 1)

/-- Exact removal of the large square exponent from a mass-plus-remainder
cell.  The prefactor is the positive old Gaussian weight. -/
theorem lowerSixMass_add_remainder_eqv_weight_mul_netBracket (k n : Nat) :
    lowerSixDiscreteHermiteMassNumerator k n +
        lowerSixDiscreteHermiteRemainder k n ≈
      lowerSixModeWeight k n * lowerSixHermiteNetBracket k n := by
  let D := Q'.ofNat (k + 2)
  let W := lowerSixModeWeight k n
  let Ws := lowerSixModeWeight k (n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let Jn := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n)
  let Jp := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))
  let C := lowerSixQuadraticTaylorCarrier k n
  let A := Q'.ofNat 48 * RingNormaliser.qpow D 4
  let M := Q'.ofNat 6 * RingNormaliser.qpow D 3 * W
  have hw : Ws ≈ W * step := by
    dsimp only [Ws, W, step]
    exact lowerSixModeWeight_succ_eqv k n
  have hflux : Ws * Jp + -(W * Jn) ≈
      (W * step) * Jp + -(W * Jn) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hw)
  have hneg : -(Ws * Jp + -(W * Jn)) ≈
      -((W * step) * Jp + -(W * Jn)) :=
    Q'.neg_eqv_congr _ _ hflux
  unfold lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteRemainder lowerSixQuadraticTaylorWeightedTerm
    lowerSixDiscreteHermiteFluxNumerator lowerSixHermiteNetBracket
  change M + (A * (W * C) + -(Ws * Jp + -(W * Jn)) + -M) ≈
    W * (A * C + -(step * Jp + -Jn))
  refine Q'.eqv_trans _
    (M + (A * (W * C) +
      -((W * step) * Jp + -(W * Jn)) + -M)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _ hneg))
  · exact massNet_algebra M A W C step Jp Jn

/-- Exact fence: positive mass does not make the finite-D remainder
pointwise nonnegative.  The remaining proof must estimate a sum. -/
theorem lowerSixMass_plus_remainder_pointwise_nonnegative_fails_k247_n20 :
    ¬ ((0 : Q') ≤
      lowerSixDiscreteHermiteMassNumerator 247 20 +
        lowerSixDiscreteHermiteRemainder 247 20) := by
  unfold lowerSixDiscreteHermiteRemainder
    lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteFluxNumerator lowerSixDiscreteHermiteFluxPoly
    lowerSixQuadraticTaylorWeightedTerm lowerSixQuadraticTaylorCarrier
    lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixDriftExcess lowerSixModeWeight lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope driftDen harmW harmU
    oneSub unit RingNormaliser.qpow qpow
  decide

/-! ## The augmented endpoint pays the lower flux endpoint -/

def lowerSixEndpointFluxTailNat (D : Nat) : Nat :=
  381 * (D * D * D) + 376 * (D * D) + 224 * D + 320

def lowerSixEndpointFluxTail (D : Q') : Q' :=
  Q'.ofNat 381 * RingNormaliser.qpow D 3 +
    Q'.ofNat 376 * RingNormaliser.qpow D 2 +
    Q'.ofNat 224 * D + Q'.ofNat 320

/-- Weight-free difference between the cleared endpoint augmentation and
the lower Hermite-flux endpoint. -/
def lowerSixEndpointFluxCore (k : Nat) : Q' :=
  lowerSixQuadraticTaylorClearingScale k *
      (Q'.ofNat 4 *
        (Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k 1 +
          -Q'.ofNat (k + 2))) +
    -lowerSixDiscreteHermiteFluxPoly
      (Q'.ofNat (k + 2)) (Q'.ofNat 1)

theorem lowerSixEndpoint_add_lowerFlux_eqv_weight_mul_core (k : Nat) :
    lowerSixQuadraticTaylorClearingScale k *
          lowerSixQuadraticTaylorEndpointAugmentation k +
        -lowerSixDiscreteHermiteFluxNumerator k 1 ≈
      lowerSixModeWeight k 1 * lowerSixEndpointFluxCore k := by
  unfold lowerSixQuadraticTaylorEndpointAugmentation
    lowerSixDiscreteHermiteFluxNumerator lowerSixEndpointFluxCore
  flux_nonnegative_ring

private def pEndpointCoreL : PE :=
  let D : PE := .var 0
  let E : PE := .var 1
  let D2 : PE := .pow D 2
  let D3 : PE := .pow D 3
  let D4 : PE := .pow D 4
  let J : PE :=
    .add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.add
                      (.mul (.const 192) D4)
                      (.mul (.const 384) D3))
                    (.neg (.mul (.const 6) D3)))
                  (.neg (.mul (.const 384) D2)))
                (.mul (.const 576) D2))
              (.mul (.const 184) D2))
            (.mul (.const 224) D))
          (.neg (.const 256)))
        (.const 576))
      (.mul (.const 3) D3)
  .add
    (.mul (.mul (.const 48) D4)
      (.mul (.const 4)
        (.add
          (.mul (.add D (.const 1)) (.add (.const 1) E))
          (.neg D))))
    (.neg J)

private def pEndpointCoreR : PE :=
  let D : PE := .var 0
  let E : PE := .var 1
  let D2 : PE := .pow D 2
  let D3 : PE := .pow D 3
  let D4 : PE := .pow D 4
  .add
    (.mul (.mul (.mul (.const 192) D4) (.add D (.const 1))) E)
    (.neg
      (.add
        (.add
          (.add (.mul (.const 381) D3) (.mul (.const 376) D2))
          (.mul (.const 224) D))
        (.const 320)))

private theorem pEndpointCore_normal :
    RingNormaliser.normalize pEndpointCoreL =
      RingNormaliser.normalize pEndpointCoreR := by decide

private theorem endpointCore_algebra (D E : Q') :
    (Q'.ofNat 48 * RingNormaliser.qpow D 4) *
          (Q'.ofNat 4 *
            ((D + 1) * ((1 : Q') + E) + -D)) +
        -lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat 1) ≈
      Q'.ofNat 192 * RingNormaliser.qpow D 4 * (D + 1) * E +
        -lowerSixEndpointFluxTail D := by
  simpa [pEndpointCoreL, pEndpointCoreR,
    lowerSixDiscreteHermiteFluxPoly, lowerSixEndpointFluxTail,
    RingNormaliser.eval, RingNormaliser.qpow] using
    (RingNormaliser.poly_identity_of_normal_eq
      pEndpointCoreL pEndpointCoreR pEndpointCore_normal
      (fun | 0 => D | _ => E))

/-- Exact cancellation of the leading `192 D^4` endpoint flux. -/
theorem lowerSixEndpointFluxCore_eqv_excess_minus_tail (k : Nat) :
    lowerSixEndpointFluxCore k ≈
      Q'.ofNat 192 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (Q'.ofNat (k + 2) + 1) * lowerSixDriftExcess k +
        -lowerSixEndpointFluxTail (Q'.ofNat (k + 2)) := by
  let D := Q'.ofNat (k + 2)
  let E := lowerSixDriftExcess k
  have hfactor : lowerSixQuadraticTaylorFactor k 1 ≈ (1 : Q') + E := by
    unfold lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
      lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    dsimp only [E]
    simp only [lowerSixQuadraticCoeff]
    flux_nonnegative_ring
  have hkp3 : Q'.ofNat (k + 3) ≈ D + 1 := by
    have hnat : k + 3 = (k + 2) + 1 := by omega
    rw [hnat]
    refine Q'.eqv_trans _ (Q'.ofNat (k + 2) + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (by decide)
  have hprod : Q'.ofNat (k + 3) *
      lowerSixQuadraticTaylorFactor k 1 ≈
        (D + 1) * ((1 : Q') + E) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hkp3)
      (Q'.mul_eqv_congr_left _ _ _ hfactor)
  have hinside : Q'.ofNat (k + 3) *
        lowerSixQuadraticTaylorFactor k 1 + -Q'.ofNat (k + 2) ≈
      (D + 1) * ((1 : Q') + E) + -D :=
    Q'.add_eqv_congr_right _ _ _ hprod
  unfold lowerSixEndpointFluxCore lowerSixQuadraticTaylorClearingScale
  dsimp only [D, E] at hinside ⊢
  refine Q'.eqv_trans _
    ((Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) *
        (Q'.ofNat 4 *
          ((Q'.ofNat (k + 2) + 1) *
              ((1 : Q') + lowerSixDriftExcess k) +
            -Q'.ofNat (k + 2))) +
      -lowerSixDiscreteHermiteFluxPoly
        (Q'.ofNat (k + 2)) (Q'.ofNat 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hinside))
  · exact endpointCore_algebra
      (Q'.ofNat (k + 2)) (lowerSixDriftExcess k)

private theorem endpoint_ofNat_mul_unit_eqv_one (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem endpoint_ofNat_two_eqv_one_add_one :
    Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide

/-- The exact drift excess is at least `2/D²`, with `D=k+2`. -/
theorem lowerSix_two_le_square_mul_driftExcess (k : Nat) :
    Q'.ofNat 2 ≤
      Q'.ofNat ((k + 2) * (k + 2)) * lowerSixDriftExcess k := by
  let DD := (k + 2) * (k + 2)
  let DDq := Q'.ofNat DD
  let u := unit (driftDen k) (driftDen_pos k)
  have hDD : 0 < DD := by
    dsimp only [DD]
    exact Nat.mul_pos (by omega) (by omega)
  have hden : driftDen k ≤ DD := by
    unfold driftDen
    dsimp only [DD]
    omega
  have hu : unit DD hDD ≤ u := by
    dsimp only [u]
    exact unit_antitone (driftDen_pos k) hDD hden
  have hDDq0 : (0 : Q') ≤ DDq := HeatKernelRGStep.zero_le_ofNat _
  have hmul : DDq * unit DD hDD ≤ DDq * u :=
    Q'.mul_le_mul_of_nonneg_left _ _ DDq hu hDDq0
  have hone : (1 : Q') ≤ DDq * u :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (endpoint_ofNat_mul_unit_eqv_one DD hDD)) hmul
  have hone_add : (1 : Q') + 1 ≤ DDq * u + DDq * u := by
    have hleft := Q'.add_le_add_left (1 : Q') 1 (DDq * u) hone
    have hright := Q'.add_le_add_right 1 (DDq * u) (DDq * u) hone
    exact Q'.le_trans' _ _ _ hleft hright
  have htwo_add : Q'.ofNat 2 ≤ DDq * u + DDq * u :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv endpoint_ofNat_two_eqv_one_add_one) hone_add
  have htwo_mul : Q'.ofNat 2 ≤ DDq * (u + u) :=
    Q'.le_trans' _ _ _ htwo_add
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv DDq u u)))
  have huu : (0 : Q') ≤ u * u :=
    Q'.mul_nonneg _ _ (unit_nonneg _ _) (unit_nonneg _ _)
  have hsum : u + u ≤ (u + u) + u * u :=
    Q'.add_le_self_of_nonneg _ _ huu
  have hscaled : DDq * (u + u) ≤ DDq * ((u + u) + u * u) :=
    Q'.mul_le_mul_of_nonneg_left _ _ DDq hsum hDDq0
  unfold lowerSixDriftExcess
  dsimp only [DD, DDq, u] at htwo_mul hscaled ⊢
  exact Q'.le_trans' _ _ _ htwo_mul hscaled

theorem lowerSixEndpointFluxTail_ofNat_eqv (D : Nat) :
    lowerSixEndpointFluxTail (Q'.ofNat D) ≈
      Q'.ofNat (lowerSixEndpointFluxTailNat D) := by
  let Dq := Q'.ofNat D
  have hp2 : RingNormaliser.qpow Dq 2 ≈ Q'.ofNat (D * D) := by
    refine Q'.eqv_trans _ (Dq * Dq) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ Dq (Q'.one_mul_eqv Dq)
    · exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv D D)
  have hp3 : RingNormaliser.qpow Dq 3 ≈ Q'.ofNat (D * D * D) := by
    refine Q'.eqv_trans _ (Q'.ofNat (D * D) * Dq) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ Dq hp2
    · exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (D * D) D)
  have h381 : Q'.ofNat 381 * RingNormaliser.qpow Dq 3 ≈
      Q'.ofNat (381 * (D * D * D)) := by
    refine Q'.eqv_trans _ (Q'.ofNat 381 * Q'.ofNat (D * D * D)) _
      (Q'.mul_eqv_congr_left _ _ _ hp3) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 381 (D * D * D))
  have h376 : Q'.ofNat 376 * RingNormaliser.qpow Dq 2 ≈
      Q'.ofNat (376 * (D * D)) := by
    refine Q'.eqv_trans _ (Q'.ofNat 376 * Q'.ofNat (D * D)) _
      (Q'.mul_eqv_congr_left _ _ _ hp2) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 376 (D * D))
  have h224 : Q'.ofNat 224 * Dq ≈ Q'.ofNat (224 * D) :=
    Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 224 D)
  unfold lowerSixEndpointFluxTail lowerSixEndpointFluxTailNat
  dsimp only [Dq] at h381 h376 h224
  refine Q'.eqv_trans _
    ((Q'.ofNat (381 * (D * D * D)) +
        Q'.ofNat (376 * (D * D))) +
      Q'.ofNat (224 * D) + Q'.ofNat 320) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' h381 h376) h224)
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (Q'.ofNat (381 * (D * D * D) + 376 * (D * D)) +
        Q'.ofNat (224 * D) + Q'.ofNat 320) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.ofNat_add_eqv _ _)))
    · refine Q'.eqv_trans _
        (Q'.ofNat
            (381 * (D * D * D) + 376 * (D * D) + 224 * D) +
          Q'.ofNat 320) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))
      · exact Q'.eqv_symm (Q'.ofNat_add_eqv _ _)

private theorem endpoint_tailNat_le_leadingNat
    {k : Nat} (hk : 247 ≤ k) :
    lowerSixEndpointFluxTailNat (k + 2) ≤
      384 * ((k + 2) * (k + 2)) * ((k + 2) + 1) := by
  let D := k + 2
  have hD : 249 ≤ D := by dsimp only [D]; omega
  have h224 : 224 * D ≤ D * D := by
    have hm := Nat.mul_le_mul_right D (show 224 ≤ D by omega)
    simpa [Nat.mul_comm] using hm
  have h249sq : 249 * 249 ≤ D * D :=
    Nat.mul_le_mul hD hD
  have h320 : 320 ≤ D * D :=
    Nat.le_trans (by decide : 320 ≤ 249 * 249) h249sq
  have hsmall : 224 * D + 320 ≤ 2 * (D * D) := by omega
  have hmain :
      381 * (D * D * D) + 376 * (D * D) + 224 * D + 320 ≤
        384 * (D * D * D) + 384 * (D * D) := by omega
  have hrhs :
      384 * (D * D) * (D + 1) =
        384 * (D * D * D) + 384 * (D * D) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  unfold lowerSixEndpointFluxTailNat
  dsimp only [D] at hmain hrhs ⊢
  rw [hrhs]
  exact hmain

private theorem endpoint_qpow4_eqv_ofNat_square_square (D : Nat) :
    RingNormaliser.qpow (Q'.ofNat D) 4 ≈
      Q'.ofNat (D * D) * Q'.ofNat (D * D) := by
  let Dq := Q'.ofNat D
  have hp2 : RingNormaliser.qpow Dq 2 ≈ Q'.ofNat (D * D) := by
    refine Q'.eqv_trans _ (Dq * Dq) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ Dq (Q'.one_mul_eqv Dq)
    · exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv D D)
  have hp22 := RingNormaliser.qpow_add Dq 2 2
  dsimp only [Dq] at hp2 hp22 ⊢
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (Q'.ofNat D) 2 *
      RingNormaliser.qpow (Q'.ofNat D) 2) _ hp22 ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (D * D) * RingNormaliser.qpow (Q'.ofNat D) 2) _
    (Q'.mul_eqv_congr_right _ _ _ hp2) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hp2

private def pEndpointLeadingRearrangeL : PE :=
  .mul
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.var 3))

private def pEndpointLeadingRearrangeR : PE :=
  .mul
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
    (.var 3)

private theorem pEndpointLeadingRearrange_normal :
    RingNormaliser.normalize pEndpointLeadingRearrangeL =
      RingNormaliser.normalize pEndpointLeadingRearrangeR := by decide

private theorem endpointLeading_rearrange (A B C E : Q') :
    ((A * B) * C) * (B * E) ≈ ((A * (B * B)) * C) * E := by
  simpa [pEndpointLeadingRearrangeL, pEndpointLeadingRearrangeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pEndpointLeadingRearrangeL pEndpointLeadingRearrangeR
      pEndpointLeadingRearrange_normal
      (fun | 0 => A | 1 => B | 2 => C | _ => E))

private theorem endpoint_leading_lower
    (k : Nat) :
    Q'.ofNat
        (384 * ((k + 2) * (k + 2)) * ((k + 2) + 1)) ≤
      Q'.ofNat 192 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        (Q'.ofNat (k + 2) + 1) * lowerSixDriftExcess k := by
  let DD := (k + 2) * (k + 2)
  let D := Q'.ofNat (k + 2)
  let Dp := D + 1
  let B := Q'.ofNat 192 * Q'.ofNat DD * Dp
  have htwo := lowerSix_two_le_square_mul_driftExcess k
  have hB0 : (0 : Q') ≤ B := by
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (HeatKernelRGStep.zero_le_ofNat _))
      (HeatKernelRGStep.zero_le_ofNat _)
  have hmul : B * Q'.ofNat 2 ≤
      B * (Q'.ofNat DD * lowerSixDriftExcess k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ B htwo hB0
  have hleft : B * Q'.ofNat 2 ≈
      Q'.ofNat
        (384 * ((k + 2) * (k + 2)) * ((k + 2) + 1)) := by
    have hDp : Dp ≈ Q'.ofNat ((k + 2) + 1) := by
      dsimp only [Dp, D]
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.ofNat_add_eqv (k + 2) 1)
        (Q'.add_eqv_congr_left _ _ _ (by decide)))
    have h192 : Q'.ofNat 192 * Q'.ofNat DD ≈
        Q'.ofNat (192 * DD) :=
      Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 192 DD)
    have hstep1 : B ≈
        Q'.ofNat ((192 * DD) * ((k + 2) + 1)) := by
      dsimp only [B]
      refine Q'.eqv_trans _
        (Q'.ofNat (192 * DD) * Dp) _
        (Q'.mul_eqv_congr_right _ _ _ h192) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (192 * DD) * Q'.ofNat ((k + 2) + 1)) _
        (Q'.mul_eqv_congr_left _ _ _ hDp) ?_
      exact Q'.eqv_symm
        (HeatKernelRGStep.ofNat_mul_eqv (192 * DD) ((k + 2) + 1))
    refine Q'.eqv_trans _
      (Q'.ofNat ((192 * DD) * ((k + 2) + 1)) * Q'.ofNat 2) _
      (Q'.mul_eqv_congr_right _ _ _ hstep1) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (((192 * DD) * ((k + 2) + 1)) * 2)) _
      (Q'.eqv_symm
        (HeatKernelRGStep.ofNat_mul_eqv
          ((192 * DD) * ((k + 2) + 1)) 2)) ?_
    have hnat : ((192 * DD) * ((k + 2) + 1)) * 2 =
        384 * DD * ((k + 2) + 1) := by
      calc
        ((192 * DD) * ((k + 2) + 1)) * 2 =
            (192 * 2) * DD * ((k + 2) + 1) := by ac_rfl
        _ = 384 * DD * ((k + 2) + 1) := by
          rw [show 192 * 2 = 384 by decide]
    rw [hnat]
    exact Q'.eqv_refl _
  have hright : B * (Q'.ofNat DD * lowerSixDriftExcess k) ≈
      Q'.ofNat 192 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        (Q'.ofNat (k + 2) + 1) * lowerSixDriftExcess k := by
    have hr := endpointLeading_rearrange
      (Q'.ofNat 192) (Q'.ofNat DD) Dp (lowerSixDriftExcess k)
    have hp4 := endpoint_qpow4_eqv_ofNat_square_square (k + 2)
    dsimp only [DD, Dp, D] at hp4 hr ⊢
    refine Q'.eqv_trans _ _ _ hr ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hp4)))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hmul)
    (Q'.le_of_eqv hright)

theorem lowerSixEndpointFluxCore_nonnegative
    {k : Nat} (hk : 247 ≤ k) :
    (0 : Q') ≤ lowerSixEndpointFluxCore k := by
  let T := lowerSixEndpointFluxTail (Q'.ofNat (k + 2))
  let L := Q'.ofNat 192 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
    (Q'.ofNat (k + 2) + 1) * lowerSixDriftExcess k
  have htailEq := lowerSixEndpointFluxTail_ofNat_eqv (k + 2)
  have htailNat := endpoint_tailNat_le_leadingNat hk
  have hlower := endpoint_leading_lower k
  have htailCast : Q'.ofNat (lowerSixEndpointFluxTailNat (k + 2)) ≤
      Q'.ofNat
        (384 * ((k + 2) * (k + 2)) * ((k + 2) + 1)) :=
    Q'.ofNat_le_ofNat htailNat
  have hTL : T ≤ L := by
    dsimp only [T, L]
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv htailEq) htailCast) hlower
  have hsub : (0 : Q') ≤ L + -T := Q'.sub_nonneg_of_le hTL
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixEndpointFluxCore_eqv_excess_minus_tail k)))

/-- The endpoint augmentation pays the entire adverse lower flux endpoint. -/
theorem lowerSixEndpoint_add_lowerFlux_nonnegative
    {k : Nat} (hk : 247 ≤ k) :
    (0 : Q') ≤
      lowerSixQuadraticTaylorClearingScale k *
          lowerSixQuadraticTaylorEndpointAugmentation k +
        -lowerSixDiscreteHermiteFluxNumerator k 1 := by
  have hw : (0 : Q') ≤ lowerSixModeWeight k 1 := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hc := lowerSixEndpointFluxCore_nonnegative hk
  have hprod : (0 : Q') ≤
      lowerSixModeWeight k 1 * lowerSixEndpointFluxCore k :=
    Q'.mul_nonneg _ _ hw hc
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (lowerSixEndpoint_add_lowerFlux_eqv_weight_mul_core k)))

#print axioms lowerSixMass_add_remainder_eqv_weight_mul_netBracket
#print axioms lowerSixMass_plus_remainder_pointwise_nonnegative_fails_k247_n20
#print axioms lowerSixEndpoint_add_lowerFlux_eqv_weight_mul_core
#print axioms lowerSixEndpointFluxCore_eqv_excess_minus_tail
#print axioms lowerSix_two_le_square_mul_driftExcess
#print axioms lowerSixEndpointFluxTail_ofNat_eqv
#print axioms lowerSixEndpointFluxCore_nonnegative
#print axioms lowerSixEndpoint_add_lowerFlux_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
