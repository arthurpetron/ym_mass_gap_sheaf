/-
# Original cube odd-background and bent-observable intervals

The background is literally Vcube*(original T1). Expanding its remainder
as (Vcube-1)+(T1-1)+(Vcube-1)*(T1-1) retains all shared coordinates.
The bent trace has its exact dimension-two interval from the original
six-link Haar-unit word. These are finite polynomial certificates, not
an interacting mean, gain sign, cutoff-limit or scaling conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarWordDifference (word_supported word_unit)
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks cubeWeight transferStep

/-- The original odd background retains the literal original vacuum message. -/
def cubeOddBackground (w : Q') : RatPoly :=
  polyMul (cubeWeight w 1) (transferStep w 1 2 polyOne)

def cubeOddBackgroundRemainder (w : Q') : RatPoly :=
  polyAdd (cubeOddBackground w) (polyNeg polyOne)

/-- The computed shared-variable product remainder cap. -/
def cubeOddBackgroundCap (w : Q') : Q' :=
  cubeFundamentalDelta w + cubeFundamentalDelta w +
    cubeFundamentalDelta w * cubeFundamentalDelta w

private theorem neg_one_supported : SupportedQuaternionBlocks N (polyNeg polyOne) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one N source hs

private theorem background_supported (w : Q') : SupportedQuaternionBlocks N (cubeOddBackground w) := by
  have hv : SupportedQuaternionBlocks N (cubeWeight w 1) := by
    unfold cubeWeight
    exact heatProduct_supported w 1 2 cubeFaces
  exact supported_polyMul hv (transferStep_supported w 1 2 (supported_one N))

private theorem remainder_pin (w : Q') :
    RatPolyCoeffEqv (cubeOddBackgroundRemainder w)
      (polyAdd (polyAdd (cubeFundamentalRemainder w) (cubeVacuumRemainder w))
        (polyMul (cubeFundamentalRemainder w) (cubeVacuumRemainder w))) := by
  change RatPolyCoeffEqv
    (polyAdd (polyMul (cubeWeight w 1) (transferStep w 1 2 polyOne)) (polyNeg polyOne))
    (polyAdd
      (polyAdd (polyAdd (cubeWeight w 1) (polyNeg polyOne))
        (polyAdd (transferStep w 1 2 polyOne) (polyNeg polyOne)))
      (polyMul (polyAdd (cubeWeight w 1) (polyNeg polyOne))
        (polyAdd (transferStep w 1 2 polyOne) (polyNeg polyOne))))
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.const 1)))
    (.add (.add (.add (.var 0) (.neg (.const 1))) (.add (.var 1) (.neg (.const 1))))
      (.mul (.add (.var 0) (.neg (.const 1))) (.add (.var 1) (.neg (.const 1)))))
    (by decide) (fun | 0 => cubeWeight w 1 | _ => transferStep w 1 2 polyOne)

/-- Both signs, with the SAME original U and all shared action links retained. -/
def cubeOddBackgroundInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1 * 2 ≤ 1) :
    Interval N (cubeOddBackgroundRemainder w) (cubeOddBackgroundCap w) := by
  let V := cubeFundamentalInterval w ha
  let U := cubeVacuumInterval w ha hcap
  exact Interval.ofCoeff (supported_add (background_supported w) neg_one_supported)
    (remainder_pin w) ((V.add U).add (V.mul U))

private theorem bent_edge_member (e : OrientedBF4Link) (he : e ∈ bentEdges) : e.link ∈ cubeLinks := by
  simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem bent_index_lt (e : OrientedBF4Link) (he : e ∈ bentEdges) :
    (baseLinks 2).idxOf e.link < N :=
  List.idxOf_lt_length_of_mem (cubeLinks_in_carrier e.link (bent_edge_member e he))

private theorem bent_word_supported :
    Supported N (wordAt (fun e => (baseLinks 2).idxOf e.link) bentEdges) := by
  apply word_supported
  intro e he
  have hi := bent_index_lt e he
  cases e.reverse
  · exact Supported.coordinate hi
  · exact (Supported.coordinate hi).conj

private theorem bent_word_unit :
    HaarCarrierEqv N
      (polyQuaternionNorm (wordAt (fun e => (baseLinks 2).idxOf e.link) bentEdges)) polyOne := by
  apply word_unit
  intro e he
  have hi := bent_index_lt e he
  cases e.reverse
  · exact haarNorm_coordinate hi
  · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (haarNorm_coordinate hi)

/-- The literal bent fundamental trace has the sharp cap two, from its
actual ordered Haar-unit word. Bare centering or source independence is not assumed. -/
def bentObservableInterval : Interval N bentObservable 2 :=
  Interval.changeCap (by decide)
    (sharpCharacterInterval (SquareBound.scalar bent_word_supported bent_word_unit) 1)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.cubeOddBackground
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.cubeOddBackgroundRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.cubeOddBackgroundCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.cubeOddBackgroundInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.bentObservableInterval
