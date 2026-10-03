/-
# A relative ORIGINAL OWN-centered signed gain at EVERY guarded cutoff

At the fixed nome 1/16, width two and terminal depth zero, the actual gain
is at least one quarter of its SAME filtered square. Both the positive
square floor and the complete original Young cost are constructed uniformly
in cutoff. The center is the EXISTING original odd-law mean.

This removes the cutoff-one restriction from the finite signed-gain pilot.
It does not control growing spatial loops, terminal-depth limits, changing
coupling/width families, completed survival or the continuum Clay target.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean
import YMGap.Continuum.QuaternionHaarSignedInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeWeight bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome baseCap deltaCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval (cubeInterval cubeCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval (cubeVacuumInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (bentObservableInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor (centeredSquare_channel_lower)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean
  (originalOddMean originalOddMean_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (commutatorGain)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSignedInterval
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
local notation "quarter" => Q'.mkPos 1 4 (by decide)
local notation "eighth" => Q'.mkPos 1 8 (by decide)
local notation "half" => HalfPow.half
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep cubeWeight centeredOriginalYoungCost
  centeredOriginalSquare centeredOriginalGain

private def vacuumInterval (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    Interval N (transferStep smallNome K 2 polyOne) (1+deltaCap) :=
  Interval.ofCoeff (transferStep_supported smallNome K 2 (supported_one N))
    (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.const 1) (.add (.var 0) (.neg (.const 1)))) (by decide)
      (fun _ => transferStep smallNome K 2 polyOne))
    ((Interval.one N).add (cubeVacuumInterval K hK hhead))

private def centerInterval (c : Q') (hc : Q'.abs c ≤ quarter) :
    Interval N (polyAdd bentObservable (polySmul (-c) polyOne)) (2+quarter) := by
  let C := YMGap.Continuum.QuaternionHaarSignedInterval.Interval.smul_abs (-c)
    (Interval.one N)
  have hcap : Q'.abs (-c)*1 ≤ quarter :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.abs_neg' c))) hc
  exact bentObservableInterval.add (C.weaken hcap)

/-- The complete original endpoint cost is bounded, with all shared action
factors and the actual U=T_K1 retained. No bare variance is substituted. -/
theorem centeredYoungCost_le_128 (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (c : Q') (hc : Q'.abs c ≤ quarter) :
    centeredOriginalYoungCost smallNome K c ≤ 128 := by
  let U := vacuumInterval K hK hhead
  let F := centerInterval c hc
  let R := (cubeInterval K hK).mul ((U.mul F).mul (U.mul F))
  have h : Q'.abs (quaternionHaar N
      (polyMul (cubeWeight smallNome K)
        (polyMul (centeredOriginalEndpoint smallNome K c) (centeredOriginalEndpoint smallNome K c)))) ≤
      baseCap^6 * (((1+deltaCap)*(2+quarter))*((1+deltaCap)*(2+quarter))) := R.haar_bound
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (youngCost_cube_pin smallNome K c))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ h (by decide)))

/-- A genuine relative SIGNED gain producer, on the SAME original filtered
norm. The reference factor is the original six-link multiplier w^18. -/
theorem centeredGain_relative_lower (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (c : Q') (hc : Q'.abs c ≤ quarter) :
    quarter*centeredOriginalSquare smallNome K c ≤
      centeredOriginalGain smallNome K c (qpow smallNome 18) := by
  let a := qpow smallNome 18
  let S := centeredOriginalSquare smallNome K c
  let Q := centeredOriginalYoungCost smallNome K c
  let G := centeredOriginalGain smallNome K c a
  let z := qpow smallNome 12*(coeffW smallNome 1*eighth)
  have hS : half*(z*z) ≤ S := centeredSquare_channel_lower K hK c hc
  have hQ : (a*a)*Q ≤ half*S :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (a*a)
      (centeredYoungCost_le_128 K hK hhead c hc) (SumOfSquares.q_mul_self_nonneg a))
      (Q'.le_trans' _ _ _ (by decide : (a*a)*128 ≤ half*(half*(z*z)))
        (Q'.mul_le_mul_of_nonneg_left _ _ half hS HalfPow.half_nonneg))
  have hidentity : half*S ≈ S+ -(half*S) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.var 0)
        (.add (.add (.var 0) (.var 0)) (.neg (.var 0)))
        (by decide) (fun _ => half*S))
      (Q'.add_eqv_congr' (ExpNeg.two_halves S) (Q'.eqv_refl _))
  have hhalf : half*S ≤ 2*G :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left S _ _ (Q'.neg_le_neg hQ))
        (gain_young_lower smallNome K c a (cubeCertificate K hK)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ half hhalf HalfPow.half_nonneg
  have hl : half*(half*S) ≈ quarter*S :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ S (by decide : half*half ≈ quarter))
  have hr : half*(2*G) ≈ G :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ G (by decide : half*2 ≈ 1))
        (Q'.one_mul_eqv G))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hr))

def finiteGainFloor : Q' :=
  let z := qpow smallNome 12*(coeffW smallNome 1*eighth)
  quarter*(half*(z*z))

theorem finiteGainFloor_positive : (0 : Q') < finiteGainFloor := by decide

/-- Actual existing OWN odd center, all original guarded cutoffs, and SAME
filtered-square comparison; no new centered observable or gain is used. -/
theorem originalOwnGain_relative_lower (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) :
    quarter*centeredOriginalSquare smallNome K (originalOddMean K hK hhead) ≤
      commutatorGain smallNome K 2 0 bentObservable (originalOddMean K hK hhead)
        (qpow smallNome 18) :=
  Q'.le_trans' _ _ _
    (centeredGain_relative_lower K hK hhead _ (originalOddMean_abs_le K hK hhead))
    (Q'.ge_of_eqv (original_commutator_gain_pin smallNome K _ _))

theorem originalOwnGain_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) :
    finiteGainFloor ≤ commutatorGain smallNome K 2 0 bentObservable
      (originalOddMean K hK hhead) (qpow smallNome 18) :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ quarter
    (centeredSquare_channel_lower K hK _ (originalOddMean_abs_le K hK hhead)) (by decide))
    (originalOwnGain_relative_lower K hK hhead)

theorem originalOwnGain_positive (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) :
    (0 : Q') < commutatorGain smallNome K 2 0 bentObservable
      (originalOddMean K hK hhead) (qpow smallNome 18) :=
  HeatKernelRGStep.lt_of_lt_of_le finiteGainFloor_positive (originalOwnGain_floor K hK hhead)

/-- An explicit inhabited family satisfies BOTH original guards; the
unbounded cutoff parameter does not stand for spatial/spacing control. -/
def guardedCutoff : Nat := max 1 (headCutoff smallNome)

theorem guarded_originalOwnGain_positive (extra : Nat) :
    let K := guardedCutoff+extra
    (0 : Q') < commutatorGain smallNome K 2 0 bentObservable
      (originalOddMean K (by change 1 ≤ max 1 (headCutoff smallNome)+extra; omega)
        (by change headCutoff smallNome ≤ max 1 (headCutoff smallNome)+extra; omega))
      (qpow smallNome 18) :=
  originalOwnGain_positive _ (by unfold guardedCutoff; omega) (by unfold guardedCutoff; omega)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.centeredYoungCost_le_128
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.centeredGain_relative_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.finiteGainFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.originalOwnGain_relative_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.originalOwnGain_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.originalOwnGain_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.guarded_originalOwnGain_positive
