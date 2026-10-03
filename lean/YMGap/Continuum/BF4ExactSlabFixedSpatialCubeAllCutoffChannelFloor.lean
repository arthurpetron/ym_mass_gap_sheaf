/-
# Original centered cube channel and square floors at every later cutoff

At the fixed nome 1/16, the actual action-prefix error is paid BEFORE
the exact face kinetic factor w^12. The center is arbitrary with |c|<=1/4;
no replacement of the original OWN mean or centered eigenpin occurs.
The resulting original weighted square has a quantitative positive floor.
No signed gain, temporal limit, or scaling-family assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeWeight bentObservable bentObservable_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement (first_face_square_haar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome smallNome_coeff_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
  (cubeInterval cubeDifferenceInterval cubeHalfCertificate actionDifferenceCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
  (testedActionRemainder tested_centered_cutoff_decomposition)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport
  (centeredBentMessage centeredOriginalSquare centeredSquare_cube_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (bentObservableInterval)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left SquareBound)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
local notation "quarter" => Q'.mkPos 1 4 (by decide)
local notation "eighth" => Q'.mkPos 1 8 (by decide)
local notation "sixteenth" => Q'.mkPos 1 16 (by decide)
local notation "half" => HalfPow.half
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep cubeWeight centeredBentMessage centeredOriginalSquare

private def firstInterval : Interval N firstFaceTrace 2 :=
  (sharpCharacterInterval (SquareBound.scalar
    (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01))
    (plaquette_unit 2 N (Nat.le_refl _) ((0,0,0,0),.p01))) 1).changeCap (by decide)

private def difference (K : Nat) : RatPoly :=
  polyAdd (cubeWeight smallNome K) (polySmul (-1) (cubeWeight smallNome 1))

private def differenceInterval (K : Nat) (hK : 1 ≤ K) : Interval N (difference K) actionDifferenceCap :=
  Interval.ofCoeff
    (supported_add (cubeInterval K hK).support
      (polySmul_supported (cubeInterval 1 (by decide)).support (-1)))
    ((RatPolyCoeffEqv.refl _).add (neg_smul _).symm)
    (cubeDifferenceInterval K hK)

private theorem remainder_expand (K : Nat) (c : Q') :
    testedActionRemainder smallNome K c ≈
      quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (difference K)) -
        c*quaternionHaar N (polyMul firstFaceTrace (difference K)) := by
  have hc := (RatPolyCoeffEqv.polyMul_smul_right (-c) firstFaceTrace polyOne).trans
    ((RatPolyCoeffEqv.mul_one firstFaceTrace).smul (-c))
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul firstFaceTrace (polyAdd bentObservable (polySmul (-c) polyOne))) (difference K))
      (polyAdd (polyMul (polyMul firstFaceTrace bentObservable) (difference K))
        (polySmul (-c) (polyMul firstFaceTrace (difference K)))) := by
    refine ((RatPolyCoeffEqv.mul_add_right firstFaceTrace bentObservable
      (polySmul (-c) polyOne)).mul_right (difference K)).trans ?_
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add ((hc.mul_right (difference K)).trans
      (RatPolyCoeffEqv.polyMul_smul_left (-c) firstFaceTrace (difference K)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (quaternionHaar_polySmul N (-c) _))
        (poly_identity_of_normal_eq (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (by decide)
          (fun
            | 0 => quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (difference K))
            | 1 => c
            | _ => quaternionHaar N (polyMul firstFaceTrace (difference K))))))

/-- The actual signed action remainder, with BOTH endpoint tests retained. -/
theorem testedActionRemainder_abs_le (K : Nat) (hK : 1 ≤ K) (c : Q')
    (hc : Q'.abs c ≤ quarter) :
    Q'.abs (testedActionRemainder smallNome K c) ≤
      (Q'.mkPos 9 2 (by decide))*actionDifferenceCap := by
  let M := quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (difference K))
  let B := quaternionHaar N (polyMul firstFaceTrace (difference K))
  have hM : Q'.abs M ≤ (2*2)*actionDifferenceCap :=
    ((firstInterval.mul bentObservableInterval).mul (differenceInterval K hK)).haar_bound
  have hB : Q'.abs B ≤ 2*actionDifferenceCap :=
    (firstInterval.mul (differenceInterval K hK)).haar_bound
  have hmul : Q'.abs (c*B) ≤ quarter*(2*actionDifferenceCap) :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le c B)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs B) hc (Q'.abs_nonneg B))
        (Q'.mul_le_mul_of_nonneg_left _ _ quarter hB (by decide)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (remainder_expand K c)))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le M (-(c*B)))
      (Q'.le_trans' _ _ _ (Q'.add_le_add hM
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' (c*B))) hmul)) (by decide)))

private def lowChannel (c : Q') : Q' :=
  (coeffW smallNome 1*half + qpow (coeffW smallNome 1) 5*eighth) -
    c*(coeffW smallNome 1 + qpow (coeffW smallNome 1) 5*sixteenth)

private theorem lowChannel_lower (c : Q') (hc : Q'.abs c ≤ quarter) :
    coeffW smallNome 1*quarter ≤ lowChannel c := by
  have hc' := Q'.le_trans' _ _ _ (Q'.le_abs_self c) hc
  have hv : (0 : Q') ≤ coeffW smallNome 1 + qpow (coeffW smallNome 1) 5*sixteenth := by decide
  have hmono := Q'.add_le_add_left
    (coeffW smallNome 1*half + qpow (coeffW smallNome 1) 5*eighth) _ _
    (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_right _ _ _ hc' hv))
  exact Q'.le_trans' _ _ _ (by decide : coeffW smallNome 1*quarter ≤ lowChannel quarter) hmono

/-- Literal original tested centered-message floor, uniformly in K>=1. -/
theorem tested_centered_channel_lower (K : Nat) (hK : 1 ≤ K) (c : Q')
    (hc : Q'.abs c ≤ quarter) :
    qpow smallNome 12*(coeffW smallNome 1*eighth) ≤
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) := by
  let e := (Q'.mkPos 9 2 (by decide))*actionDifferenceCap
  let R := testedActionRemainder smallNome K c
  have hn : -R ≤ e := Q'.le_trans' _ _ _ (Q'.neg_le_abs R) (testedActionRemainder_abs_le K hK c hc)
  have hr : -e ≤ R := Q'.le_trans' _ _ _ (Q'.neg_le_neg hn) (Q'.le_of_eqv (Q'.neg_neg_eqv R))
  have hbase := Q'.add_le_add (lowChannel_lower c hc) hr
  have hcore : coeffW smallNome 1*eighth ≤ lowChannel c+R :=
    Q'.le_trans' _ _ _ (by decide : coeffW smallNome 1*eighth ≤ coeffW smallNome 1*quarter + -e) hbase
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (qpow smallNome 12) hcore (by decide)
  have hpin : quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) ≈
      qpow smallNome 12*(lowChannel c+R) := by
    unfold centeredBentMessage
    exact tested_centered_cutoff_decomposition smallNome K hK c
  exact Q'.le_trans' _ _ _ hmul
    (Q'.ge_of_eqv hpin)

private theorem message_supported (K : Nat) (c : Q') :
    SupportedQuaternionBlocks N (centeredBentMessage smallNome K c) := by
  unfold centeredBentMessage
  exact supported_add (transferStep_supported smallNome K 2 bentObservable_supported)
    (polySmul_supported (transferStep_supported smallNome K 2 (supported_one N)) (-c))

private theorem projection_square_le_raw (K : Nat) (c : Q') :
    quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) *
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) ≤
      quaternionHaar N (polyMul (centeredBentMessage smallNome K c) (centeredBentMessage smallNome K c)) := by
  have h := weighted_cauchySchwarz N polyOne firstFaceTrace (centeredBentMessage smallNome K c)
    (Certificate.one N) firstInterval.support (message_supported K c)
  have hx : weightedPair N polyOne firstFaceTrace (centeredBentMessage smallNome K c) ≈
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hy : weightedPair N polyOne firstFaceTrace firstFaceTrace ≈ 1 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)) first_face_square_haar
  have hz : weightedPair N polyOne (centeredBentMessage smallNome K c) (centeredBentMessage smallNome K c) ≈
      quaternionHaar N (polyMul (centeredBentMessage smallNome K c) (centeredBentMessage smallNome K c)) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx) (Q'.mul_eqv_congr_left _ _ _ hx)
  have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hy)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- Original interacting square dominates HALF the original tested projection squared. -/
theorem centeredSquare_projection_lower (K : Nat) (hK : 1 ≤ K) (c : Q') :
    half*(quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c)) *
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c))) ≤
      centeredOriginalSquare smallNome K c := by
  let b := centeredBentMessage smallNome K c
  have hraw := Q'.mul_le_mul_of_nonneg_left _ _ half (projection_square_le_raw K c) HalfPow.half_nonneg
  have hfloor := haar_order (cubeHalfCertificate K hK) (Certificate.square b (message_supported K c))
  have hcap : quaternionHaar N (polyMul (cap half) (polyMul b b)) ≈
      half*quaternionHaar N (polyMul b b) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (cap_mul_left half _))
      (quaternionHaar_polySmul N half _)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcap)
    (Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv (centeredSquare_cube_pin smallNome K c))))

/-- Positive quantitative C2 floor for the SAME arbitrary capped center. -/
theorem centeredSquare_channel_lower (K : Nat) (hK : 1 ≤ K) (c : Q')
    (hc : Q'.abs c ≤ quarter) :
    let z := qpow smallNome 12*(coeffW smallNome 1*eighth)
    half*(z*z) ≤ centeredOriginalSquare smallNome K c := by
  dsimp only
  let z := qpow smallNome 12*(coeffW smallNome 1*eighth)
  let p := quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage smallNome K c))
  have hz : (0 : Q') ≤ z := by decide
  have hzp : z ≤ p := tested_centered_channel_lower K hK c hc
  have hp : (0 : Q') ≤ p := Q'.le_trans' _ _ _ hz hzp
  have hsq : z*z ≤ p*p := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ z hzp hz)
    (Q'.mul_le_mul_of_nonneg_right _ _ p hzp hp)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ half hsq HalfPow.half_nonneg)
    (centeredSquare_projection_lower K hK c)

#print axioms testedActionRemainder_abs_le
#print axioms tested_centered_channel_lower
#print axioms centeredSquare_projection_lower
#print axioms centeredSquare_channel_lower

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor
