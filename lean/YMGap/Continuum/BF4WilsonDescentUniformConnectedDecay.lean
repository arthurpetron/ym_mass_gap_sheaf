/-
# A fixed temporal decay rate on the original Wilson connected scalar

The sharper descent count is evaluated on the SAME separated Wilson probes
and selected original action. All old small-nome guards remain explicit,
but the spatial/temporal rate is now the constant 1/4 throughout that region.
The actual probe/collar amplitude still depends on the nome and expression.
No physical spacing identification or continuum conclusion is made here.
-/
import YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay

namespace YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
  (oldGuardBudget comparisonCoreRate comparison_guard)
open YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance
open YMGap.Continuum.BF4ExactSlabDescentCoreCount (countPrefactor)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount (totalProbeSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay
  (sizeLoss probeLinkCount connectedScalar_selected_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftFace shiftLink)
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay (shifted_root_distance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist natDist)

local infix:50 " ≈ " => Q'.eqv

def timeRate : Q' := entropyRate 96 comparisonCoreRate
def twoStepRate : Q' := timeRate*timeRate
theorem timeRate_positive : (0 : Q') < timeRate := by decide
theorem timeRate_lt_one : timeRate < (1 : Q') := by decide
theorem twoStepRate_positive : (0 : Q') < twoStepRate := by decide
theorem twoStepRate_lt_one : twoStepRate < (1 : Q') := by decide
theorem twoStepRate_eq : twoStepRate ≈ Q'.mkPos 1 16 (by decide) := by decide

def decayAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (base R : Nat) (x y : IntrinsicExpression base) : Q' :=
  let c := intrinsicCap x
  let d := intrinsicCap y
  (((c*d+c*d)*probePrefactor w hd (probeLinkCount base R+probeLinkCount base R)) *
    Q'.ofNat (2^(sizeLoss base R)*96^(sizeLoss base R))) *
    Q'.recipPos (1 + -timeRate) (HKPos.one_sub_pos timeRate_lt_one)

theorem decayAmplitude_nonnegative (w : Q') (hd : heatRemainderBound w < 1)
    (base R : Nat) (x y : IntrinsicExpression base) : (0 : Q') ≤ decayAmplitude w hd base R x y := by
  have hc := Q'.mul_nonneg _ _ (intrinsicCap_nonnegative x) (intrinsicCap_nonnegative y)
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hc hc)
      (probePrefactor_nonnegative w hd _)) (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem root_distance (space start gap : Nat) :
    linfDist (shiftFace space (start+gap) originFace) (shiftFace space start originFace) = gap := by
  have h := shifted_root_distance space gap 0 start
  simpa only [Nat.add_comm, Nat.zero_add, natDist, Nat.sub_zero, Nat.zero_sub, Nat.add_zero] using h

private theorem budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    (base r R n t : Nat) (x y : IntrinsicExpression base) :
    oldGuardBudget
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n)) (probeBoxSize_pos base R))
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t) (probeBoxSize_pos base R))
      w hd (intrinsicCap x) (intrinsicCap y) ≈
        decayAmplitude w hd base R x y * timeRate^(R+n+1-sizeLoss base R) := by
  have h := oldGuardBudget_factor
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n)) (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t) (probeBoxSize_pos base R))
    w hd (intrinsicCap x) (intrinsicCap y)
  unfold countPrefactor totalProbeSize at h
  rw [shiftedBoxProbe_size, shiftedBoxProbe_size, shiftedBoxProbe_root, shiftedBoxProbe_root,
    root_distance, List.length_append, shiftedBoxLinks_length, shiftedBoxLinks_length] at h
  exact h

/-- The actual original Wilson time lag, with a fixed rate but an explicit
nome-dependent amplitude. Cutoff, volume and buffer do not enter that amplitude. -/
theorem connectedScalar_uniform_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r R n t stage : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    Q'.abs (connectedScalar hw0 hw1 (R+n) r stage t x (advance n y)) ≤
      decayAmplitude w hd base R x y * timeRate^(R+n+1-sizeLoss base R) := by
  have h := finite_covariance_distance_bound hw0 hw1 hsmall hd hs
    (chartExtent base r (R+n) t) (chartIds base r (R+n) t) (chartIds_nodup base r (R+n) t)
    (fun _ hi => chartIds_physical hi)
    (upperProbe base r R n t x) (lowerProbe base r R n t y) (intrinsicCap x) (intrinsicCap y)
    (upperProbe_interval base r R n t x hx) (lowerProbe_interval base r R n t y hy)
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t+(R+n))))
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t)))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n)) (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t) (probeBoxSize_pos base R))
    (upperProbe_local base r R n t x hx) (lowerProbe_local base r R n t y hy) stage
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (connectedScalar_selected_pin hw0 hw1 base r R n t stage x y hx hy)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (budget_pin w hd base r R n t x y)))

end YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay

#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.timeRate
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.twoStepRate
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.timeRate_positive
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.timeRate_lt_one
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.twoStepRate_positive
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.twoStepRate_lt_one
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.twoStepRate_eq
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.decayAmplitude
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.decayAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay.connectedScalar_uniform_bound
