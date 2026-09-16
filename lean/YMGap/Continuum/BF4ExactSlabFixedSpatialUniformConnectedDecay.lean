/-
# Uniform temporal decay of the actual selected-chain connected scalar

The reflected joint insertion and its two unit marginals are pinned to
the same original selected-action covariance. Separate fixed-size boxes
contain the literal upper and lower probes, without enclosing their gap.
The original positive partition square cancels in the existing
selected-action estimate, without separately bounding moments or
introducing a reciprocal ceiling.

The explicit amplitude depends on the nome, original base and observation
radius, and the original signed coefficient/spin lists. It is independent
of spatial margin, heat cutoff, boundary-time buffer and physical lag.
The exponent retains its natural-subtraction support loss. No spatial
limit, completed strict form estimate or continuum gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
import YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (unitSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime unit physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
  (paddedWidth recenter recenter_time)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl (spanCap chartProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftFace shiftLink)
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay (shifted_root_distance)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount (totalProbeSize countPrefactor)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist natDist)

local infix:50 " ≈ " => Q'.eqv

/-- Twice the actual connected box support size: 2*6*N^4. -/
def sizeLoss (base R : Nat) : Nat :=
  let N := probeBoxSize base R
  (N*N*N*N)*6 + (N*N*N*N)*6

/-- Literal boundary-link occurrence count of each fixed box, including fringe. -/
def probeLinkCount (base R : Nat) : Nat :=
  let N := probeBoxSize base R
  (N*N*N*N)*24

/-- The regulator- and lag-independent amplitude for these original presentations. -/
def decayAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base R : Nat) (x y : PhysicalSpan base) : Q' :=
  let c := spanCap x.val
  let d := spanCap y.val
  (((c*d+c*d)*probePrefactor w hd (probeLinkCount base R+probeLinkCount base R)) *
    Q'.ofNat (2^(sizeLoss base R)*625^(sizeLoss base R))) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

theorem decayAmplitude_nonnegative (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base R : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    (0 : Q') ≤ decayAmplitude w hd hs base R x y := by
  have hc := (upperProbe_interval base 0 R 0 0 x hx).nonnegative
  have he := (lowerProbe_interval base 0 R 0 0 y hy).nonnegative
  have hce := Q'.mul_nonneg _ _ hc he
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hce hce) (probePrefactor_nonnegative w hd _))
      (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem placedSpan_unit (extent start : Nat) :
    RatPolyCoeffEqv (placedSpan extent start unitSpan) polyOne := by
  change RatPolyCoeffEqv (polyAdd (polySmul 1 polyOne) polyZero) polyOne
  exact ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero polyOne)

private theorem upperProbe_unit (base r R n t : Nat) :
    RatPolyCoeffEqv (upperProbe base r R n t (unit base)) polyOne :=
  placedSpan_unit _ _

private theorem lowerProbe_unit (base r R n t : Nat) :
    RatPolyCoeffEqv (lowerProbe base r R n t (unit base)) polyOne :=
  placedSpan_unit _ _

private theorem chartProbe_left_unit (base r R n t : Nat) (x : PhysicalSpan base)
    (hx : radius x.val ≤ R) :
    RatPolyCoeffEqv (chartProbe base r (R+n) t x (unit base))
      (upperProbe base r R n t x) := by
  have h := chartProbe_separated base r R n t x (unit base) hx
  rw [physicalTime_unit] at h
  rw [h]
  exact ((RatPolyCoeffEqv.refl _).mul (lowerProbe_unit base r R n t)).trans
    (RatPolyCoeffEqv.mul_one _)

private theorem chartProbe_right_unit (base r R n t : Nat) (y : PhysicalSpan base) :
    RatPolyCoeffEqv (chartProbe base r (R+n) t (unit base) (physicalTime n y))
      (lowerProbe base r R n t y) := by
  rw [chartProbe_separated base r R n t (unit base) y (Nat.zero_le R)]
  exact ((upperProbe_unit base r R n t).mul (RatPolyCoeffEqv.refl _)).trans
    (RatPolyCoeffEqv.one_mul _)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- The actual joint moment and both actual marginals have the SAME selected
chain and cutoff partition. No full-slab action is substituted. -/
theorem connectedScalar_selected_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base r R n t stage : Nat) (x y : PhysicalSpan base) (hx : radius x.val ≤ R) :
    connectedScalar hw0 hw1 (paddedWidth base r) stage (R+n)
        (recenter r x) (physicalTime n (recenter r y)) t ≈
      finiteCovariance w hw0 hw1 (chartExtent base r (R+n) t)
        (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
        (upperProbe base r R n t x) (lowerProbe base r R n t y) stage := by
  unfold connectedScalar finiteCovariance
  apply Q'.add_eqv_congr'
  · rw [← recenter_time r n y]
    change finiteValue w hw0 hw1 (chartExtent base r (R+n) t)
        (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
        (chartProbe base r (R+n) t x (physicalTime n y)) stage ≈ _
    rw [chartProbe_separated base r R n t x y hx]
    exact Q'.eqv_refl _
  · apply Q'.neg_eqv_congr
    apply qmul
    · change finiteValue w hw0 hw1 (chartExtent base r (R+n) t)
          (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
          (chartProbe base r (R+n) t x (unit base)) stage ≈ _
      exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
        (chartProbe_left_unit base r R n t x hx) stage
    · rw [← recenter_time r n y]
      change finiteValue w hw0 hw1 (chartExtent base r (R+n) t)
          (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
          (chartProbe base r (R+n) t (unit base) (physicalTime n y)) stage ≈ _
      exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
        (chartProbe_right_unit base r R n t y) stage

private theorem root_distance (space start gap : Nat) :
    linfDist (shiftFace space (start+gap) originFace) (shiftFace space start originFace) = gap := by
  have h := shifted_root_distance space gap 0 start
  simpa only [Nat.add_comm, Nat.zero_add, natDist, Nat.sub_zero, Nat.zero_sub, Nat.add_zero] using h

private theorem budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r R n t : Nat) (x y : PhysicalSpan base) :
    distanceBudget
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
        (probeBoxSize_pos base R))
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
        (probeBoxSize_pos base R)) w hd hs (spanCap x.val) (spanCap y.val) ≈
      decayAmplitude w hd hs base R x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(R+n+1-sizeLoss base R) := by
  have h := distanceBudget_factor
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
      (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
      (probeBoxSize_pos base R)) w hd hs (spanCap x.val) (spanCap y.val)
  unfold countPrefactor totalProbeSize at h
  rw [shiftedBoxProbe_size, shiftedBoxProbe_size, shiftedBoxProbe_root, shiftedBoxProbe_root,
    root_distance, List.length_append, shiftedBoxLinks_length, shiftedBoxLinks_length] at h
  exact h

/-- A strict small-nome temporal rate with regulator-independent amplitude,
on the actual finite selected-chain connected scalar. Initial overlapping
supports are included by natural subtraction in the exponent. -/
theorem connectedScalar_uniform_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r R n t stage : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    Q'.abs (connectedScalar hw0 hw1 (paddedWidth base r) stage (R+n)
      (recenter r x) (physicalTime n (recenter r y)) t) ≤
      decayAmplitude w hd hs base R x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(R+n+1-sizeLoss base R) := by
  have h := finite_covariance_distance_bound hw0 hw1 hsmall hd hs
    (chartExtent base r (R+n) t) (chartIds base r (R+n) t) (chartIds_nodup base r (R+n) t)
    (fun _ hi => chartIds_physical hi)
    (upperProbe base r R n t x) (lowerProbe base r R n t y) (spanCap x.val) (spanCap y.val)
    (upperProbe_interval base r R n t x hx) (lowerProbe_interval base r R n t y hy)
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t+(R+n))))
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t)))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
      (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
      (probeBoxSize_pos base R))
    (upperProbe_local base r R n t x hx) (lowerProbe_local base r R n t y hy) stage
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (connectedScalar_selected_pin hw0 hw1 base r R n t stage x y hx)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (budget_pin w hd hs base r R n t x y)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.sizeLoss
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.probeLinkCount
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.decayAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.decayAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.connectedScalar_selected_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay.connectedScalar_uniform_bound
