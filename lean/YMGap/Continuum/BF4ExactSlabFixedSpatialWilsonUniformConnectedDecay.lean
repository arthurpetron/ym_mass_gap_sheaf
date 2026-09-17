/-
# Regulator-uniform decay of the actual finite Wilson connected scalar

The literal reflected joint insertion and both unit marginals are pinned
to ONE covariance for the SAME selected original action and heat cutoff.
Two separately placed fixed-size boxes contain the actual Wilson probes;
the intervening time gap is not put inside either support box. The existing
signed covariance estimate cancels the SAME original partition square.

The computed amplitude depends on the nome, base, observation radius and
the actual signed Wilson expressions. It is independent of spatial margin,
heat stage, boundary-time buffer and physical time lag. The exponent retains
the explicit natural-subtraction support loss. This finite bound alone is
not a limiting OS norm estimate, a strict operator bound or a physical mass
calibration; the original small-nome guards remain explicit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
import YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison (chartInsertion chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator
  (chartPairing connectedScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
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
open YMGap.Continuum.SepLatticeZ4Linf (linfDist natDist)

local infix:50 " ≈ " => Q'.eqv

/-- Twice the actual connected box support size, with no time-lag factor. -/
def sizeLoss (base R : Nat) : Nat :=
  let N := probeBoxSize base R
  (N*N*N*N)*6 + (N*N*N*N)*6

/-- Boundary-link occurrence count of each fixed box, including its fringe. -/
def probeLinkCount (base R : Nat) : Nat :=
  let N := probeBoxSize base R
  (N*N*N*N)*24

/-- The original-expression amplitude contains no regulator or time lag. -/
def decayAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base R : Nat) (x y : IntrinsicExpression base) : Q' :=
  let c := intrinsicCap x
  let d := intrinsicCap y
  (((c*d+c*d)*probePrefactor w hd (probeLinkCount base R+probeLinkCount base R)) *
    Q'.ofNat (2^(sizeLoss base R)*625^(sizeLoss base R))) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

theorem decayAmplitude_nonnegative (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base R : Nat) (x y : IntrinsicExpression base) :
    (0 : Q') ≤ decayAmplitude w hd hs base R x y := by
  have hcd := Q'.mul_nonneg _ _ (intrinsicCap_nonnegative x) (intrinsicCap_nonnegative y)
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hcd hcd) (probePrefactor_nonnegative w hd _))
      (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem upperProbe_unit (base r R n t : Nat) :
    upperProbe base r R n t (unit base) = polyOne := rfl

private theorem lowerProbe_unit (base r R n t : Nat) :
    lowerProbe base r R n t (unit base) = polyOne := rfl

private theorem chartInsertion_left_unit (base r R n t : Nat)
    (x : IntrinsicExpression base) (hx : x.radius ≤ R) :
    RatPolyCoeffEqv
      (chartInsertion r (R+n) t
        (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit base))))
      (upperProbe base r R n t x) := by
  have hp : chartInsertion r (R+n) t
        (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit base))) =
      polyMul (upperProbe base r R n t x) (lowerProbe base r R n t (unit base)) := by
    simpa only [chart_advance_unit, chart_unit] using
      chartInsertion_separated base r R n t x (unit base) hx (Nat.zero_le R)
  rw [hp, lowerProbe_unit]
  exact RatPolyCoeffEqv.mul_one _

private theorem chartInsertion_right_unit (base r R n t : Nat)
    (y : IntrinsicExpression base) (hy : y.radius ≤ R) :
    RatPolyCoeffEqv
      (chartInsertion r (R+n) t
        (.mul (mirror (R+n) (chart (R+n) (unit base))) (chart (R+n) (advance n y))))
      (lowerProbe base r R n t y) := by
  rw [chartInsertion_separated base r R n t (unit base) y (Nat.zero_le R) hy,
    upperProbe_unit]
  exact RatPolyCoeffEqv.one_mul _

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Joint and marginal moments retain exactly one selected action and partition.
The advanced unit is identified by its literal chart, not its radius tag. -/
theorem connectedScalar_selected_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base r R n t stage : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    connectedScalar hw0 hw1 (R+n) r stage t x (advance n y) ≈
      finiteCovariance w hw0 hw1 (chartExtent base r (R+n) t)
        (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
        (upperProbe base r R n t x) (lowerProbe base r R n t y) stage := by
  unfold connectedScalar finiteCovariance
  apply Q'.add_eqv_congr'
  · change finiteValue w hw0 hw1 (chartExtent base r (R+n) t)
        (chartIds base r (R+n) t) (fun _ hi => chartIds_physical hi)
        (chartInsertion r (R+n) t
          (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y)))) stage ≈ _
    rw [chartInsertion_separated base r R n t x y hx hy]
    exact Q'.eqv_refl _
  · apply Q'.neg_eqv_congr
    apply qmul
    · exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
        (chartInsertion_left_unit base r R n t x hx) stage
    · exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
        (chartInsertion_right_unit base r R n t y hy) stage

private theorem root_distance (space start gap : Nat) :
    linfDist (shiftFace space (start+gap) originFace) (shiftFace space start originFace) = gap := by
  have h := shifted_root_distance space gap 0 start
  simpa only [Nat.add_comm, Nat.zero_add, natDist, Nat.sub_zero, Nat.zero_sub, Nat.add_zero] using h

private theorem budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r R n t : Nat) (x y : IntrinsicExpression base) :
    distanceBudget
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
        (probeBoxSize_pos base R))
      (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
        (probeBoxSize_pos base R)) w hd hs (intrinsicCap x) (intrinsicCap y) ≈
      decayAmplitude w hd hs base R x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(R+n+1-sizeLoss base R) := by
  have h := distanceBudget_factor
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
      (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
      (probeBoxSize_pos base R)) w hd hs (intrinsicCap x) (intrinsicCap y)
  unfold countPrefactor totalProbeSize at h
  rw [shiftedBoxProbe_size, shiftedBoxProbe_size, shiftedBoxProbe_root, shiftedBoxProbe_root,
    root_distance, List.length_append, shiftedBoxLinks_length, shiftedBoxLinks_length] at h
  exact h

/-- Uniform in all three finite regulators and physical lag, not in nome,
base or expression. Natural subtraction also covers overlapping supports. -/
theorem connectedScalar_uniform_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r R n t stage : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    Q'.abs (connectedScalar hw0 hw1 (R+n) r stage t x (advance n y)) ≤
      decayAmplitude w hd hs base R x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(R+n+1-sizeLoss base R) := by
  have h := finite_covariance_distance_bound hw0 hw1 hsmall hd hs
    (chartExtent base r (R+n) t) (chartIds base r (R+n) t) (chartIds_nodup base r (R+n) t)
    (fun _ hi => chartIds_physical hi)
    (upperProbe base r R n t x) (lowerProbe base r R n t y) (intrinsicCap x) (intrinsicCap y)
    (upperProbe_interval base r R n t x hx) (lowerProbe_interval base r R n t y hy)
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t+(R+n))))
    ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t)))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t+(R+n))
      (probeBoxSize_pos base R))
    (shiftedBoxProbe (probeBoxSize base R) (r+1) (paddedWidth base r+1+t)
      (probeBoxSize_pos base R))
    (upperProbe_local base r R n t x hx) (lowerProbe_local base r R n t y hy) stage
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr
      (connectedScalar_selected_pin hw0 hw1 base r R n t stage x y hx hy)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (budget_pin w hd hs base r R n t x y)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.sizeLoss
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.probeLinkCount
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.decayAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.decayAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.connectedScalar_selected_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.connectedScalar_uniform_bound
