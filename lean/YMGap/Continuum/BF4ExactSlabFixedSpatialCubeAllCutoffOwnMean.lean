/-
# The original odd cube mean at every guarded cutoff

At the fixed positive nome 1/16, both the actual six-face action remainder
and the literal original vacuum remainder have cap 1/32. Their shared-variable
product gives the original odd background cap 65/1024. The original odd
partition is at least 959/1024 and its bent numerator has absolute value at
most 130/1024. This bounds the EXISTING OWN mean by 1/4 at every cutoff
satisfying both K>=1 and its original head guard. No raw message locality,
substitute cube center, gain sign, or changing-family claim is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul quaternionHaar_append)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval (cubeInterval cubeRemainderInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval
  (cubeVacuumInterval cubeVacuumRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome smallNome_pos deltaCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall
  (backgroundCap partitionFloor numeratorCap meanCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (bentObservableInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (bent_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean mean_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv
local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
attribute [local irreducible] baseLinks cubeWeight cubeTransfer bentObservable transferStep weightedMass
  terminalMessage cubeInterval cubeRemainderInterval cubeVacuumInterval
  YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight
  YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight

/-- The literal original odd partition at width two and terminal depth zero. -/
def oddPartition (K : Nat) : Q' :=
  weightedMass smallNome K 2 (transferStep smallNome K 2 polyOne)

/-- The original bent numerator retains exactly the same original vacuum. -/
def oddNumerator (K : Nat) : Q' :=
  weightedMass smallNome K 2 (polyMul bentObservable (transferStep smallNome K 2 polyOne))

def cubeOddBackground (K : Nat) : RatPoly :=
  polyMul (cubeWeight smallNome K) (transferStep smallNome K 2 polyOne)

def cubeOddBackgroundRemainder (K : Nat) : RatPoly :=
  polyAdd (cubeOddBackground K) (polyNeg polyOne)

attribute [local irreducible] cubeOddBackground cubeOddBackgroundRemainder

private theorem cubeWeight_supported (K : Nat) :
    SupportedQuaternionBlocks N (cubeWeight smallNome K) := by
  unfold cubeWeight
  exact heatProduct_supported smallNome K 2 cubeFaces

private theorem neg_one_supported : SupportedQuaternionBlocks N (polyNeg polyOne) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one N source hs

private theorem background_supported (K : Nat) :
    SupportedQuaternionBlocks N (cubeOddBackground K) := by
  unfold cubeOddBackground
  exact supported_polyMul (cubeWeight_supported K)
    (transferStep_supported smallNome K 2 (supported_one N))

/-- Both signs retain all six action factors and the literal original T1. -/
def cubeOddBackgroundInterval (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) :
    Interval N (cubeOddBackgroundRemainder K) backgroundCap := by
  let v : RatPoly := polyAdd (cubeWeight smallNome K) (polyNeg polyOne)
  let u : RatPoly := polyAdd (transferStep smallNome K 2 polyOne) (polyNeg polyOne)
  have V : Interval N v deltaCap := cubeRemainderInterval K hK
  have U : Interval N u deltaCap := by
    simpa only [cubeVacuumRemainder] using (cubeVacuumInterval K hK hhead)
  have hr : Interval N (polyAdd (polyAdd v u) (polyMul v u))
      ((deltaCap + deltaCap) + deltaCap * deltaCap) := (V.add U).add (V.mul U)
  have hs : SupportedQuaternionBlocks N (cubeOddBackgroundRemainder K) := by
    unfold cubeOddBackgroundRemainder cubeOddBackground
    exact supported_add
      (supported_polyMul (cubeInterval K hK).support
        (transferStep_supported smallNome K 2 (supported_one N))) neg_one_supported
  have hp : RatPolyCoeffEqv (cubeOddBackgroundRemainder K)
      (polyAdd (polyAdd (polyAdd (cubeWeight smallNome K) (polyNeg polyOne))
        (polyAdd (transferStep smallNome K 2 polyOne) (polyNeg polyOne)))
        (polyMul (polyAdd (cubeWeight smallNome K) (polyNeg polyOne))
          (polyAdd (transferStep smallNome K 2 polyOne) (polyNeg polyOne)))) := by
    unfold cubeOddBackgroundRemainder cubeOddBackground
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.const 1)))
      (.add (.add (.add (.var 0) (.neg (.const 1))) (.add (.var 1) (.neg (.const 1))))
        (.mul (.add (.var 0) (.neg (.const 1))) (.add (.var 1) (.neg (.const 1)))))
      (by decide) (fun | 0 => cubeWeight smallNome K | _ => transferStep smallNome K 2 polyOne)
  have hcert : Interval N (cubeOddBackgroundRemainder K)
      ((deltaCap + deltaCap) + deltaCap * deltaCap) := Interval.ofCoeff hs hp hr
  exact hcert.changeCap (by decide)

theorem oddPartition_background_pin (K : Nat) :
    oddPartition K ≈ H (cubeOddBackground K) := by
  unfold cubeOddBackground
  have h := (original_seven_bent_moments_cube smallNome K).1
  change weightedMass smallNome K 2 (polyMul polyOne (transferStep smallNome K 2 polyOne)) ≈
    H (polyMul (cubeWeight smallNome K) (polyMul polyOne (cubeTransfer smallNome K polyOne))) at h
  have hleft := weightedMass_congr smallNome K 2
    (RatPolyCoeffEqv.one_mul (transferStep smallNome K 2 polyOne))
  have hright := haar_of_coeff (blocks := N) ((RatPolyCoeffEqv.refl (cubeWeight smallNome K)).mul
    (RatPolyCoeffEqv.one_mul (cubeTransfer smallNome K polyOne)))
  have ht := original_vacuum_message_cube smallNome K (cubeWeight smallNome K) (cubeWeight_supported K)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ hright (Q'.eqv_symm ht)))

theorem oddNumerator_background_pin (K : Nat) :
    oddNumerator K ≈ H (polyMul (cubeOddBackground K) bentObservable) := by
  have h := (original_seven_bent_moments_cube smallNome K).2.1
  change weightedMass smallNome K 2 (polyMul bentObservable (transferStep smallNome K 2 polyOne)) ≈
    H (polyMul (cubeWeight smallNome K) (polyMul bentObservable (cubeTransfer smallNome K polyOne))) at h
  have ht := original_vacuum_message_cube smallNome K (polyMul (cubeWeight smallNome K) bentObservable)
    (supported_polyMul (cubeWeight_supported K) bentObservable_supported)
  have hs := haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_assoc (cubeWeight smallNome K)
    bentObservable (cubeTransfer smallNome K polyOne))
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (cubeWeight smallNome K) bentObservable) (transferStep smallNome K 2 polyOne))
      (polyMul (cubeOddBackground K) bentObservable) := by
    unfold cubeOddBackground
    exact (RatPolyCoeffEqv.mul_assoc _ _ _).trans
      (((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.mul_comm _ _)).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm ht) (haar_of_coeff (blocks := N) hr)))

attribute [local irreducible] oddPartition oddNumerator

private theorem haar_one : H polyOne ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem background_remainder_haar (K : Nat) :
    H (cubeOddBackgroundRemainder K) + 1 ≈ H (cubeOddBackground K) := by
  have hp : RatPolyCoeffEqv
      (polyAdd (cubeOddBackgroundRemainder K) polyOne) (cubeOddBackground K) := by
    unfold cubeOddBackgroundRemainder
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.const 1))) (.const 1)) (.var 0)
      (by decide) (fun _ => cubeOddBackground K)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm haar_one))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _)) (haar_of_coeff (blocks := N) hp))

private theorem background_bent_remainder_haar (K : Nat) :
    H (polyMul (cubeOddBackgroundRemainder K) bentObservable) ≈
      H (polyMul (cubeOddBackground K) bentObservable) := by
  have hp : RatPolyCoeffEqv
      (polyAdd (polyMul (cubeOddBackgroundRemainder K) bentObservable) bentObservable)
      (polyMul (cubeOddBackground K) bentObservable) := by
    unfold cubeOddBackgroundRemainder
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.neg (.const 1))) (.var 1)) (.var 1))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => cubeOddBackground K | _ => bentObservable)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _).symm)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm bent_haar_zero))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _)) (haar_of_coeff (blocks := N) hp)))

/-- A lower bound on the SAME original odd partition. -/
theorem oddPartition_floor (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    partitionFloor ≤ oddPartition K := by
  have hab := (cubeOddBackgroundInterval K hK hhead).haar_bound
  have hl : -backgroundCap ≤ H (cubeOddBackgroundRemainder K) :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hab))
      (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  have he : H (cubeOddBackgroundRemainder K) + 1 ≈ oddPartition K :=
    Q'.eqv_trans _ _ _ (background_remainder_haar K)
      (Q'.eqv_symm (oddPartition_background_pin K))
  exact Q'.le_trans' _ _ _ (by decide : partitionFloor ≤ -backgroundCap + 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ 1 hl) (Q'.le_of_eqv he))

theorem oddPartition_positive (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    (0 : Q') < oddPartition K :=
  HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < partitionFloor)
    (oddPartition_floor K hK hhead)

theorem oddNumerator_abs_le (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    Q'.abs (oddNumerator K) ≤ numeratorCap := by
  have h := ((cubeOddBackgroundInterval K hK hhead).mul bentObservableInterval).haar_bound
  have hp : H (polyMul (cubeOddBackgroundRemainder K) bentObservable) ≈ oddNumerator K :=
    Q'.eqv_trans _ _ _ (background_bent_remainder_haar K)
      (Q'.eqv_symm (oddNumerator_background_pin K))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hp))
    (Q'.le_trans' _ _ _ h (by decide))

/-- The original edge-law mean has its OWN numerator and partition. -/
theorem mean_odd_ratio_pin (K : Nat) (hhead : headCutoff smallNome ≤ K)
    (hZ : (0 : Q') < oddPartition K) :
    mean smallNome_pos (by decide) K 2 hhead 0 bentObservable ≈
      oddNumerator K * Q'.recipPos (oddPartition K) hZ := by
  have hzero : terminalMessage smallNome K 2 0 = polyOne := by
    unfold terminalMessage
    rfl
  have hone : terminalMessage smallNome K 2 1 = transferStep smallNome K 2 polyOne := by
    simpa only [hzero] using (terminalMessage_next smallNome K 2 0).symm
  have ht0 : RatPolyCoeffEqv (terminalMessage smallNome K 2 0) polyOne := by
    rw [hzero]
    exact RatPolyCoeffEqv.refl _
  have ht1 : RatPolyCoeffEqv (terminalMessage smallNome K 2 1) (transferStep smallNome K 2 polyOne) := by
    rw [hone]
    exact RatPolyCoeffEqv.refl _
  have hn : weightedMass smallNome K 2
      (polyMul (polyMul (terminalMessage smallNome K 2 1) bentObservable) (terminalMessage smallNome K 2 0)) ≈
      oddNumerator K := by
    unfold oddNumerator
    exact weightedMass_congr smallNome K 2
      ((((ht1.mul (RatPolyCoeffEqv.refl bentObservable)).mul ht0).trans
        (RatPolyCoeffEqv.mul_one (polyMul (transferStep smallNome K 2 polyOne) bentObservable))).trans
        (RatPolyCoeffEqv.mul_comm (transferStep smallNome K 2 polyOne) bentObservable))
  have hz : weightedMass smallNome K 2
      (polyMul (terminalMessage smallNome K 2 1) (terminalMessage smallNome K 2 0)) ≈
      oddPartition K := by
    unfold oddPartition
    exact weightedMass_congr smallNome K 2
      ((ht1.mul ht0).trans (RatPolyCoeffEqv.mul_one (transferStep smallNome K 2 polyOne)))
  have hm : middleRatio smallNome_pos (by decide) K 2 hhead 1 0 bentObservable ≈
      oddNumerator K * Q'.recipPos (oddPartition K) hZ := by
    unfold middleRatio massRatio
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _ _ hZ hz))
  exact Q'.eqv_trans _ _ _ (mean_pin smallNome_pos (by decide) K 2 hhead 0 bentObservable_supported) hm

/-- Exactly the existing OWN mean; the extra prefix guard records the
constructed finite bound's domain, not a replacement centering rule. -/
def originalOddMean (K : Nat) (_hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) : Q' :=
  mean smallNome_pos (by decide) K 2 hhead 0 bentObservable

theorem originalOddMean_pin (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    originalOddMean K hK hhead ≈
      Q'.divPos (oddNumerator K) (oddPartition K) (oddPartition_positive K hK hhead) :=
  mean_odd_ratio_pin K hhead (oddPartition_positive K hK hhead)

attribute [local irreducible] originalOddMean

theorem originalOddMean_bounds (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    -meanCap ≤ originalOddMean K hK hhead ∧ originalOddMean K hK hhead ≤ meanCap := by
  have hN := oddNumerator_abs_le K hK hhead
  have hZ := oddPartition_floor K hK hhead
  have hupper : oddNumerator K ≤ meanCap * oddPartition K :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ hN (Q'.le_trans' _ _ _
        (by decide : numeratorCap ≤ meanCap * partitionFloor)
        (Q'.mul_le_mul_of_nonneg_left _ _ meanCap hZ (by decide))))
  have hlower : -meanCap * oddPartition K ≤ oddNumerator K := by
    have hneg : -(oddNumerator K) ≤ meanCap * oddPartition K :=
      Q'.le_trans' _ _ _ (Q'.neg_le_abs _)
        (Q'.le_trans' _ _ _ hN (Q'.le_trans' _ _ _
          (by decide : numeratorCap ≤ meanCap * partitionFloor)
          (Q'.mul_le_mul_of_nonneg_left _ _ meanCap hZ (by decide))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv _ _))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg hneg) (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  have hp := originalOddMean_pin K hK hhead
  exact ⟨Q'.le_trans' _ _ _
      (Q'.le_divPos_of_mul_le _ _ (oddPartition_positive K hK hhead) hlower) (Q'.ge_of_eqv hp),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.divPos_le_of_le_mul _ _ (oddPartition_positive K hK hhead) hupper)⟩

theorem originalOddMean_abs_le (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    Q'.abs (originalOddMean K hK hhead) ≤ meanCap :=
  Q'.abs_le (originalOddMean_bounds K hK hhead).1 (originalOddMean_bounds K hK hhead).2

theorem existingMean_abs_le (K : Nat) (hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) :
    Q'.abs (mean smallNome_pos (by decide) K 2 hhead 0 bentObservable) ≤ meanCap := by
  have h := originalOddMean_abs_le K hK hhead
  unfold originalOddMean at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.cubeOddBackground
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.cubeOddBackgroundInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddPartition_background_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddNumerator_background_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.oddNumerator_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.mean_odd_ratio_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.originalOddMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.originalOddMean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.originalOddMean_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.originalOddMean_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.existingMean_abs_le
