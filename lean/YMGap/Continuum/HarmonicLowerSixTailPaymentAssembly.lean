/-
Assembly of the certified lower-six Hermite tail payment.

The exact square-root head is nonnegative.  On its complementary suffix the
second Hermite flux is the boundary term selected by the joint endpoint
certificate, while the Gaussian block estimates pay a uniform bulk error.
This file first identifies those independently constructed coordinates and
then packages the finite telescoping/payment argument without changing the
production remainder.
-/

import YMGap.Continuum.HarmonicLowerSixExactHead
import YMGap.Continuum.HarmonicLowerSixJointEndpointPayment

namespace YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicLowerSixExactHead
open YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric
open YMGap.Continuum.HarmonicLowerSixJointEndpointPayment
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- The weight-free second flux respects rational mode equivalence. -/
theorem lowerSixHermiteSecondFluxPoly_eqv_congr_mode
    (D : Q') {N M : Q'} (hNM : N ≈ M) :
    lowerSixHermiteSecondFluxPoly D N ≈
      lowerSixHermiteSecondFluxPoly D M := by
  have h3 := RingNormaliser.qpow_eqv_congr hNM 3
  have h5 := RingNormaliser.qpow_eqv_congr hNM 5
  have h7 := RingNormaliser.qpow_eqv_congr hNM 7
  have h9 := RingNormaliser.qpow_eqv_congr hNM 9
  unfold lowerSixHermiteSecondFluxPoly
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_left _ _ _ hNM)))
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_left _ _ _ h3))))
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ h5)))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ h7))))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ h9))

/-- The positive polynomial in the joint endpoint certificate is exactly the
negative of the weight-free second Hermite flux at the first unresolved mode. -/
theorem lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux (k : Nat) :
    lowerSixJointEndpointPositivePoly k ≈
      -lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
        (Q'.ofNat (thetaWindowLeft k + 1)) := by
  have hendpoint :=
    YMGap.Continuum.HarmonicLowerSixJointEndpointPayment.lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux k
  have hmode : Q'.ofNat (thetaWindowLeft k) + (1 : Q') ≈
      Q'.ofNat (thetaWindowLeft k + 1) := by
    exact Q'.eqv_trans _
      (Q'.ofNat (thetaWindowLeft k) + Q'.ofNat 1) _
      (Q'.add_eqv_congr_left _ _ _ (by decide))
      (Q'.eqv_symm (Q'.ofNat_add_eqv (thetaWindowLeft k) 1))
  have hflux := lowerSixHermiteSecondFluxPoly_eqv_congr_mode
    (Q'.ofNat (k + 2)) hmode
  exact Q'.eqv_trans _ _ _ hendpoint
    (Q'.neg_eqv_congr _ _ hflux)

/-- Weighted form of the endpoint identification. -/
theorem lowerSixModeWeight_mul_endpointPositivePoly_eqv_neg_secondFluxNumerator
    (k : Nat) :
    lowerSixModeWeight k (thetaWindowLeft k + 1) *
        lowerSixJointEndpointPositivePoly k ≈
      -lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1) := by
  let W := lowerSixModeWeight k (thetaWindowLeft k + 1)
  let P := lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
    (Q'.ofNat (thetaWindowLeft k + 1))
  have hendpoint := lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux k
  have hmul : W * lowerSixJointEndpointPositivePoly k ≈ W * (-P) :=
    Q'.mul_eqv_congr_left _ _ _ hendpoint
  unfold lowerSixHermiteSecondFluxNumerator
  dsimp only [W, P] at hmul ⊢
  exact Q'.eqv_trans _ _ _ hmul (Q'.mul_neg_eqv _ _)

/-- In particular the endpoint polynomial is nonnegative; this is derived
from the global sum-of-squares sign theorem for the second flux. -/
theorem lowerSixJointEndpointPositivePoly_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixJointEndpointPositivePoly k := by
  have hflux := lowerSixHermiteSecondFluxPoly_nonpositive
    (D := Q'.ofNat (k + 2))
    (N := Q'.ofNat (thetaWindowLeft k + 1))
    (HeatKernelRGStep.zero_le_ofNat _)
    (HeatKernelRGStep.zero_le_ofNat _)
  have hneg : (0 : Q') ≤
      -lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
        (Q'.ofNat (thetaWindowLeft k + 1)) :=
    Q'.nonneg_neg_of_nonpos hflux
  exact Q'.le_trans' _ _ _ hneg
    (Q'.ge_of_eqv (lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux k))

private abbrev PositivePE := RingNormaliser.PolyExpr

private def pTailOneSubSquareL : PositivePE :=
  let u : PositivePE := .var 0
  let w : PositivePE := .add (.const 1) (.neg u)
  .add (.const 1) (.neg (.mul w w))

private def pTailOneSubSquareR : PositivePE :=
  let u : PositivePE := .var 0
  let w : PositivePE := .add (.const 1) (.neg u)
  .mul u (.add (.const 1) w)

private theorem pTailOneSubSquare_normal :
    RingNormaliser.normalize pTailOneSubSquareL =
      RingNormaliser.normalize pTailOneSubSquareR := by
  decide

private theorem tail_one_sub_harmW_square_eqv (k : Nat) :
    (1 : Q') + -(harmW k * harmW k) ≈
      harmU k * ((1 : Q') + harmW k) := by
  unfold harmW oneSub
  simpa [pTailOneSubSquareL, pTailOneSubSquareR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTailOneSubSquareL pTailOneSubSquareR pTailOneSubSquare_normal
      (fun _ => harmU k))

theorem lowerSixHarmonicSquareDefect_pos (k : Nat) :
    (0 : Q') < (1 : Q') + -(harmW k * harmW k) := by
  have honePlus : (0 : Q') < (1 : Q') + harmW k :=
    Q'.pos_add_nonneg (by decide) (harmW_nonneg k)
  have hproduct : (0 : Q') < harmU k * ((1 : Q') + harmW k) :=
    Q'.mul_pos (harmU_pos k) honePlus
  exact HeatKernelRGStep.lt_of_lt_of_le hproduct
    (Q'.ge_of_eqv (tail_one_sub_harmW_square_eqv k))

theorem lowerSixJointBlockFactor_pos (k : Nat) :
    (0 : Q') < lowerSixJointBlockFactor k := by
  have hwidth : (0 : Q') <
      Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) :=
    Q'.ofNat_succ_pos (2 * (thetaWindowLeft k + 1))
  have hinner : (0 : Q') <
      Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
        ((1 : Q') + -(harmW k * harmW k)) :=
    Q'.mul_pos hwidth (lowerSixHarmonicSquareDefect_pos k)
  unfold lowerSixJointBlockFactor
  exact Q'.mul_pos (by
    unfold fourFifths
    decide) hinner

theorem lowerSixJointSecondClearingScale_pos (k : Nat) :
    (0 : Q') < lowerSixJointSecondClearingScale k := by
  have hD : (0 : Q') < Q'.ofNat (k + 2) :=
    Q'.ofNat_succ_pos (k + 1)
  unfold lowerSixJointSecondClearingScale
  exact Q'.mul_pos (by decide)
    (BondMovingScaledNorm.qpow_pos hD 2)

private theorem tailRingQpow_nonnegative {a : Q'}
    (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (tailRingQpow_nonnegative ha m) ha

private def pTailSwapOuterL : PositivePE :=
  .mul (.var 0) (.mul (.var 1) (.var 2))

private def pTailSwapOuterR : PositivePE :=
  .mul (.var 1) (.mul (.var 0) (.var 2))

private theorem pTailSwapOuter_normal :
    RingNormaliser.normalize pTailSwapOuterL =
      RingNormaliser.normalize pTailSwapOuterR := by
  decide

private theorem tailSwapOuter (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  simpa [pTailSwapOuterL, pTailSwapOuterR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTailSwapOuterL pTailSwapOuterR pTailSwapOuter_normal
      (fun | 0 => a | 1 => b | _ => c))

private def pTailReorderBulkL : PositivePE :=
  .mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))

private def pTailReorderBulkR : PositivePE :=
  .mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))

private theorem pTailReorderBulk_normal :
    RingNormaliser.normalize pTailReorderBulkL =
      RingNormaliser.normalize pTailReorderBulkR := by
  decide

private theorem tailReorderBulk (a b c d : Q') :
    a * (b * (c * d)) ≈ (b * c) * (a * d) := by
  simpa [pTailReorderBulkL, pTailReorderBulkR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTailReorderBulkL pTailReorderBulkR pTailReorderBulk_normal
      (fun | 0 => a | 1 => b | 2 => c | _ => d))

/-! ## Finite second-flux summation -/

/-- The exact pointwise inequality still requiring the analytic second-flux
certificate.  All quantities are production quantities; this is not a new
free input type. -/
def LowerSixTailSecondFluxLocalBound (k n : Nat) : Prop :=
  lowerSixJointSecondClearingScale k *
      -(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n) ≤
    (lowerSixHermiteSecondFluxNumerator k (n + 1) +
        -lowerSixHermiteSecondFluxNumerator k n) +
      (Q'.ofNat 15630 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) *
        lowerSixModeWeight k n

private abbrev PE := RingNormaliser.PolyExpr

private def pTailForwardStepL : PE :=
  .add (.add (.var 0) (.neg (.var 1)))
    (.add (.var 2) (.neg (.var 0)))

private def pTailForwardStepR : PE :=
  .add (.var 2) (.neg (.var 1))

private theorem pTailForwardStep_normal :
    RingNormaliser.normalize pTailForwardStepL =
      RingNormaliser.normalize pTailForwardStepR := by
  decide

private theorem tailForwardStep (x a b : Q') :
    (x + -a) + (b + -x) ≈ b + -a := by
  simpa [pTailForwardStepL, pTailForwardStepR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTailForwardStepL pTailForwardStepR pTailForwardStep_normal
      (fun | 0 => x | 1 => a | _ => b))

private theorem finSum_forwardDifferenceFrom
    (F : Nat → Q') (K : Nat) : ∀ M,
    finSum (fun j => F (K + j + 1) + -F (K + j)) M ≈
      F (K + M) + -F K
  | 0 => Q'.eqv_symm (Q'.add_neg_self_eqv (F K))
  | M + 1 => by
      rw [finSum_succ]
      have ih := finSum_forwardDifferenceFrom F K M
      refine Q'.eqv_trans _
        ((F (K + M) + -F K) +
          (F (K + M + 1) + -F (K + M))) _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact tailForwardStep _ _ _

private theorem finSum_neg_four_mul (f : Nat → Q') (M : Nat) :
    finSum (fun j => -(Q'.ofNat 4 * f j)) M ≈
      -(Q'.ofNat 4 * finSum f M) := by
  have hterm : ∀ j,
      -(Q'.ofNat 4 * f j) ≈ (-Q'.ofNat 4) * f j := by
    intro j
    exact Q'.eqv_symm (Q'.neg_mul_eqv (Q'.ofNat 4) (f j))
  have hsum := RationalTail.finSum_eqv_congr
    (fun j => -(Q'.ofNat 4 * f j))
    (fun j => (-Q'.ofNat 4) * f j) hterm M
  have hpull := Q'.eqv_symm
    (RationalTail.const_mul_finSum f (-Q'.ofNat 4) M)
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _ hpull
      (Q'.neg_mul_eqv (Q'.ofNat 4) (finSum f M)))

private theorem finSum_secondFluxDebt_eqv
    (k K M : Nat) :
    finSum
        (fun j => lowerSixJointSecondClearingScale k *
          -(Q'.ofNat 4 *
            lowerSixDiscreteHermiteRemainder k (K + j))) M ≈
      lowerSixJointSecondClearingScale k *
        -(Q'.ofNat 4 *
          finSum (fun j =>
            lowerSixDiscreteHermiteRemainder k (K + j)) M) := by
  let f := fun j => lowerSixDiscreteHermiteRemainder k (K + j)
  have hpull := Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun j => -(Q'.ofNat 4 * f j))
      (lowerSixJointSecondClearingScale k) M)
  have hneg := finSum_neg_four_mul f M
  dsimp only [f] at hpull hneg ⊢
  exact Q'.eqv_trans _ _ _ hpull
    (Q'.mul_eqv_congr_left _ _ _ hneg)

/-- Summing the pointwise second-flux inequality leaves only the first
unresolved endpoint and a Gaussian-weight bulk term. -/
theorem lowerSixTailSecondFluxBulkBound_of_pointwise
    {k : Nat} (hk : 8189 ≤ k)
    (hlocal : ∀ n,
      thetaWindowLeft k + 1 ≤ n → n ≤ growingAnchor k →
      LowerSixTailSecondFluxLocalBound k n) :
    let K := thetaWindowLeft k + 1
    let M := growingAnchor k - thetaWindowLeft k
    let C := Q'.ofNat 15630 *
      RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
    lowerSixJointSecondClearingScale k *
        -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k) ≤
      lowerSixModeWeight k K * lowerSixJointEndpointPositivePoly k +
        C * finSum (fun j => lowerSixModeWeight k (K + j)) M := by
  let K := thetaWindowLeft k + 1
  let M := growingAnchor k - thetaWindowLeft k
  let T := lowerSixJointSecondClearingScale k
  let C := Q'.ofNat 15630 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let R := fun j => lowerSixDiscreteHermiteRemainder k (K + j)
  let G := fun n => lowerSixHermiteSecondFluxNumerator k n
  let W := fun j => lowerSixModeWeight k (K + j)
  let dG := fun j => G (K + j + 1) + -G (K + j)
  have hKM : K + M = growingAnchor k + 1 := by
    dsimp only [K, M]
    have hleft : thetaWindowLeft k ≤ growingAnchor k := by
      have hc := thetaWindowCenter_le_harmonicDen
        (k := k) (show 38 ≤ k by omega)
      unfold thetaWindowLeft growingAnchor
      have hdiv := Nat.div_le_self (thetaWindowCenter k) 2
      omega
    omega
  have hsum : finSum (fun j => T * -(Q'.ofNat 4 * R j)) M ≤
      finSum (fun j => dG j + C * W j) M := by
    apply YMGap.Constructive.finSum_le_lt
    intro j hj
    dsimp only [T, R, dG, G, W, C]
    apply hlocal
    · dsimp only [K]
      omega
    · omega
  have hleft : finSum (fun j => T * -(Q'.ofNat 4 * R j)) M ≈
      T * -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k) := by
    have hdebt := finSum_secondFluxDebt_eqv k K M
    have hindex :
        finSum (fun j => lowerSixDiscreteHermiteRemainder k (K + j)) M ≈
          lowerSixHermiteRemainderTailSum k := by
      unfold lowerSixHermiteRemainderTailSum
      apply RationalTail.finSum_eqv_congr
      intro j
      dsimp only [K, M]
      rw [show thetaWindowLeft k + 1 + j =
        thetaWindowLeft k + j + 1 by omega]
      exact Q'.eqv_refl _
    have hscaled :
        T * -(Q'.ofNat 4 *
              finSum (fun j =>
                lowerSixDiscreteHermiteRemainder k (K + j)) M) ≈
          T * -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ hindex))
    unfold lowerSixHermiteRemainderTailSum
    dsimp only [T, R, K, M] at hdebt hscaled ⊢
    exact Q'.eqv_trans _ _ _ hdebt hscaled
  have hsplit : finSum (fun j => dG j + C * W j) M ≈
      finSum dG M + C * finSum W M := by
    exact Q'.eqv_trans _ _ _ (RationalTail.finSum_add dG (fun j => C * W j) M)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (RationalTail.const_mul_finSum W C M)))
  have htel : finSum dG M ≈ G (K + M) + -G K := by
    dsimp only [dG, G]
    exact finSum_forwardDifferenceFrom
      (fun n => lowerSixHermiteSecondFluxNumerator k n) K M
  have hend : G (K + M) ≤ (0 : Q') := by
    dsimp only [G]
    exact lowerSixHermiteSecondFluxNumerator_nonpositive k (K + M)
  have hendDrop : G (K + M) + -G K ≤ -G K := by
    have h := Q'.add_le_add_right (G (K + M)) 0 (-G K) hend
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-G K))))
  have hendpoint : -G K ≈
      lowerSixModeWeight k K * lowerSixJointEndpointPositivePoly k := by
    dsimp only [G, K]
    exact Q'.eqv_symm
      (lowerSixModeWeight_mul_endpointPositivePoly_eqv_neg_secondFluxNumerator k)
  have hright : finSum (fun j => dG j + C * W j) M ≤
      lowerSixModeWeight k K * lowerSixJointEndpointPositivePoly k +
        C * finSum W M := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    have hflux : finSum dG M ≤ -G K :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv htel) hendDrop
    have hadd := Q'.add_le_add_right (finSum dG M) (-G K)
      (C * finSum W M) hflux
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_right _ _ _ hendpoint))
  dsimp only [T, C, W, K, M] at hleft hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum hright)

/-! ## Paying the Gaussian bulk with the first square-root block -/

/-- The square-root-block tail and the sharp first-block Bernoulli estimate
turn the endpoint-plus-Gaussian expression into the exact joint endpoint
block.  No measured constant enters: `15630`, `4/5`, and `128/127` are the
exact coefficients already derived by the polynomial and geometric
certificates. -/
theorem lowerSixTailEndpointAndGaussianBulk_scaled_le_endpointBlock
    {k : Nat} (hk : 8189 ≤ k) :
    let K := thetaWindowLeft k + 1
    let M := growingAnchor k - thetaWindowLeft k
    let a := lowerSixJointBlockFactor k
    let C := Q'.ofNat 15630 *
      RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
    a *
        (lowerSixModeWeight k K * lowerSixJointEndpointPositivePoly k +
          C * finSum (fun j => lowerSixModeWeight k (K + j)) M) ≤
      lowerSixModeWeight k K * lowerSixJointEndpointBlock k := by
  let K := thetaWindowLeft k + 1
  let M := growingAnchor k - thetaWindowLeft k
  let a := lowerSixJointBlockFactor k
  let C := Q'.ofNat 15630 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let W := lowerSixModeWeight k K
  let J := lowerSixJointEndpointPositivePoly k
  let L := lowerSixBlockClosure
  let B0 := lowerSixGaussianTailBlock k 0
  let Tail := finSum (fun j => lowerSixModeWeight k (K + j)) M
  have ha0 : (0 : Q') ≤ a :=
    Q'.le_of_lt (lowerSixJointBlockFactor_pos k)
  have hD0 : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC0 : (0 : Q') ≤ C := by
    dsimp only [C]
    exact Q'.mul_nonneg _ _ (by decide)
      (tailRingQpow_nonnegative hD0 4)
  have hL0 : (0 : Q') ≤ L := by
    dsimp only [L, lowerSixBlockClosure, HalfPow.half]
    decide
  have hCL0 : (0 : Q') ≤ C * L :=
    Q'.mul_nonneg _ _ hC0 hL0
  have htail : Tail ≤ L * B0 := by
    have hraw := lowerSixWeightTail_le_squareRootBlock
      (k := k) (show 247 ≤ k by omega) M
    have hindex : Tail ≈
        finSum
          (fun j => lowerSixModeWeight k
            (thetaWindowLeft k + j + 1)) M := by
      dsimp only [Tail, K]
      apply RationalTail.finSum_eqv_congr
      intro j
      rw [show thetaWindowLeft k + 1 + j =
        thetaWindowLeft k + j + 1 by omega]
      exact Q'.eqv_refl _
    dsimp only [L, B0] at hraw ⊢
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hindex) hraw
  have htailC : C * Tail ≤ C * (L * B0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ C htail hC0
  have htailAC : a * (C * Tail) ≤ a * (C * (L * B0)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ a htailC ha0
  have hfirstBlock : a * B0 ≤ W := by
    dsimp only [a, B0, W, K]
    exact lowerSixGaussianFirstBlock_cleared
      (k := k) (show 247 ≤ k by omega)
  have hblockScaled : (C * L) * (a * B0) ≤ (C * L) * W :=
    Q'.mul_le_mul_of_nonneg_left _ _ (C * L) hfirstBlock hCL0
  have hbulkLeft : a * (C * (L * B0)) ≈ (C * L) * (a * B0) := by
    exact tailReorderBulk _ _ _ _
  have hbulkRight : (C * L) * W ≈ W * (C * L) :=
    Q'.mul_comm_eqv _ _
  have hbulkCore : a * (C * (L * B0)) ≤ W * (C * L) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hbulkLeft)
      (Q'.le_trans' _ _ _ hblockScaled (Q'.le_of_eqv hbulkRight))
  have hbulk : a * (C * Tail) ≤ W * (C * L) :=
    Q'.le_trans' _ _ _ htailAC hbulkCore
  have hendpoint : a * (W * J) ≤ W * (a * J) :=
    Q'.le_of_eqv (tailSwapOuter _ _ _)
  have hadd : a * (W * J) + a * (C * Tail) ≤
      W * (a * J) + W * (C * L) :=
    Q'.add_le_add hendpoint hbulk
  have hleft : a * (W * J + C * Tail) ≈
      a * (W * J) + a * (C * Tail) :=
    Q'.mul_add_eqv _ _ _
  have hright : W * (a * J + C * L) ≈
      W * (a * J) + W * (C * L) :=
    Q'.mul_add_eqv _ _ _
  have hresult : a * (W * J + C * Tail) ≤ W * (a * J + C * L) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hright))
  dsimp only [a, C, W, J, L, Tail, K, M] at hresult ⊢
  unfold lowerSixJointEndpointBlock
  exact hresult

/-- Once the local second-flux inequality is available, the complete
endpoint/tail machinery pays the production Hermite tail by the exact linear
head reserve. -/
theorem lowerSixHermiteRemainderTailPayment_of_pointwise
    {k : Nat} (hk : 8189 ≤ k)
    (hlocal : ∀ n,
      thetaWindowLeft k + 1 ≤ n → n ≤ growingAnchor k →
      LowerSixTailSecondFluxLocalBound k n) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k := by
  let K := thetaWindowLeft k + 1
  let M := growingAnchor k - thetaWindowLeft k
  let a := lowerSixJointBlockFactor k
  let T := lowerSixJointSecondClearingScale k
  let C := Q'.ofNat 15630 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let debt := -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k)
  let H := lowerSixHermiteLinearHeadMassFloor k
  let endpoint :=
    lowerSixModeWeight k K * lowerSixJointEndpointPositivePoly k +
      C * finSum (fun j => lowerSixModeWeight k (K + j)) M
  have hbulk : T * debt ≤ endpoint := by
    dsimp only [T, debt, endpoint, K, M, C]
    exact lowerSixTailSecondFluxBulkBound_of_pointwise hk hlocal
  have ha0 : (0 : Q') ≤ a :=
    Q'.le_of_lt (lowerSixJointBlockFactor_pos k)
  have hscaled : a * (T * debt) ≤ a * endpoint :=
    Q'.mul_le_mul_of_nonneg_left _ _ a hbulk ha0
  have hblock : a * endpoint ≤
      lowerSixModeWeight k K * lowerSixJointEndpointBlock k := by
    dsimp only [a, endpoint, K, M, C]
    exact lowerSixTailEndpointAndGaussianBulk_scaled_le_endpointBlock hk
  have hreserve : lowerSixModeWeight k K *
        lowerSixJointEndpointBlock k ≤ lowerSixJointReservePolynomial k := by
    dsimp only [K]
    exact lowerSixJointEndpointBlock_weight_le_reserve_large hk
  have hfactor : a * T * H ≈ lowerSixJointReservePolynomial k := by
    dsimp only [a, T, H]
    exact lowerSixJointBlockPayment_eqv_reserve k
  have hpaid : a * (T * debt) ≤ a * T * H :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ hblock
        (Q'.le_trans' _ _ _ hreserve (Q'.ge_of_eqv hfactor)))
  have hleft : a * (T * debt) ≈ (a * T) * debt := by
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hright : a * T * H ≈ (a * T) * H :=
    Q'.eqv_refl _
  have hcancel : (a * T) * debt ≤ (a * T) * H :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hpaid (Q'.le_of_eqv hright))
  have hpositive : (0 : Q') < a * T :=
    Q'.mul_pos (lowerSixJointBlockFactor_pos k)
      (lowerSixJointSecondClearingScale_pos k)
  have hresult : debt ≤ H :=
    Q'.le_of_mul_le_mul_left hcancel hpositive
  dsimp only [debt, H] at hresult ⊢
  exact hresult

/-- The certified nonnegative head upgrades the tail payment to the complete
production remainder sum. -/
theorem lowerSixFullRemainderPayment_of_pointwise
    {k : Nat} (hk : 8189 ≤ k)
    (hlocal : ∀ n,
      thetaWindowLeft k + 1 ≤ n → n ≤ growingAnchor k →
      LowerSixTailSecondFluxLocalBound k n) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k :=
  lowerSixFullRemainderPayment_of_tailPayment hk
    (lowerSixHermiteRemainderTailPayment_of_pointwise hk hlocal)

#print axioms lowerSixHermiteSecondFluxPoly_eqv_congr_mode
#print axioms lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux
#print axioms lowerSixModeWeight_mul_endpointPositivePoly_eqv_neg_secondFluxNumerator
#print axioms lowerSixJointEndpointPositivePoly_nonnegative
#print axioms lowerSixHarmonicSquareDefect_pos
#print axioms lowerSixJointBlockFactor_pos
#print axioms lowerSixJointSecondClearingScale_pos
#print axioms lowerSixTailSecondFluxBulkBound_of_pointwise
#print axioms lowerSixTailEndpointAndGaussianBulk_scaled_le_endpointBlock
#print axioms lowerSixHermiteRemainderTailPayment_of_pointwise
#print axioms lowerSixFullRemainderPayment_of_pointwise

end YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
