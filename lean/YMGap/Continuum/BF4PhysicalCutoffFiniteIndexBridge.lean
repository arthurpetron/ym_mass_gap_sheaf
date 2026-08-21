/-
# Exact finite-index presentation of the physical BF4 cutoff carrier

The physical Markov construction sums over the literal positive-row carrier,
whereas exact rational matrix certificates use indices `0, ..., n-1`.  This
module totalizes the genuine carrier by `List.getD` and proves exact identities
for its stationary mean, weighted diagonal form, and reflected joint
quadratic.  The fallback state is never read by an in-range matrix sum.

This is an identification layer only.  It constructs no spectral estimate,
cofinal cutoff family, thermodynamic limit, continuum theory, or Clay result.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4WeightedJointPerronPerturbation
import YMGap.Continuum.FiniteListIndexQuadraticBridge
import YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

namespace YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Dimension of the literal positive-row physical carrier. -/
def centralPhysicalFiniteCarrierSize
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Nat :=
  (centralPositiveHalfStates w hw K half).length

/-- Totalized lookup in the genuine positive-row physical carrier. -/
def centralPhysicalFiniteStateAt
    (w : Q') (hw : (0 : Q') ≤ w) (K half index : Nat) :
    EdgeLabelling :=
  finiteListStateAt
    (centralPositiveHalfStates w hw K half)
    zeroEdgeLabelling index

/-- Indexed stationary weight on the genuine carrier. -/
def centralPhysicalFiniteWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K half index : Nat) : Q' :=
  centralPhysicalRowMarginal w hw K half
    (centralPhysicalFiniteStateAt w hw K half index)

/-- Indexed normalized reflected joint matrix on the genuine carrier. -/
def centralPhysicalFiniteKernel
    (w : Q') (hw : (0 : Q') ≤ w) (K half row column : Nat) : Q' :=
  centralNormalizedPhysicalReflectedKernel w hw K half
    (centralPhysicalFiniteStateAt w hw K half row)
    (centralPhysicalFiniteStateAt w hw K half column)

/-- An actual physical observable read as a totalized finite coefficient
vector. -/
def centralPhysicalFiniteCoefficient
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') (index : Nat) : Q' :=
  observable (centralPhysicalFiniteStateAt w hw K half index)

/-- The indexed weighted mean is exactly the physical stationary mean. -/
theorem centralPhysicalFiniteWeightedMean_eqv_stationaryMean
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw K half)
        (centralPhysicalFiniteWeight w hw K half)
        (centralPhysicalFiniteCoefficient w hw K half observable) ≈
      centralPhysicalStationaryMean w hw K half observable := by
  let states := centralPositiveHalfStates w hw K half
  let stateAt := finiteListStateAt states zeroEdgeLabelling
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        centralPhysicalRowMarginal w hw K half (stateAt index) *
          observable (stateAt index))
      (List.range states.length)) _ ?_ ?_
  · unfold finiteWeightedMean centralPhysicalFiniteCarrierSize
      centralPhysicalFiniteWeight centralPhysicalFiniteCoefficient
      centralPhysicalFiniteStateAt
    apply listQSum_congr_on
    intro index _hindex
    exact Q'.mul_comm_eqv _ _
  · unfold centralPhysicalStationaryMean
    exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states zeroEdgeLabelling
        (fun state =>
          centralPhysicalRowMarginal w hw K half state *
            observable state))

/-- The indexed diagonal quadratic is exactly the physical weighted norm. -/
theorem centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    finiteDiagonalQuadratic
        (centralPhysicalFiniteCarrierSize w hw K half)
        (centralPhysicalFiniteWeight w hw K half)
        (centralPhysicalFiniteCoefficient w hw K half observable) ≈
      centralPhysicalWeightedInner
        w hw K half observable observable := by
  let states := centralPositiveHalfStates w hw K half
  let stateAt := finiteListStateAt states zeroEdgeLabelling
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        centralPhysicalRowMarginal w hw K half (stateAt index) *
          (observable (stateAt index) * observable (stateAt index)))
      (List.range states.length)) _ ?_ ?_
  · unfold finiteDiagonalQuadratic centralPhysicalFiniteCarrierSize
      centralPhysicalFiniteWeight centralPhysicalFiniteCoefficient
      centralPhysicalFiniteStateAt
    apply listQSum_congr_on
    intro index _hindex
    exact Q'.mul_comm_eqv _ _
  · unfold centralPhysicalWeightedInner
    exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states zeroEdgeLabelling
        (fun state =>
          centralPhysicalRowMarginal w hw K half state *
            (observable state * observable state)))

/-- The indexed matrix quadratic is exactly the normalized physical reflected
joint quadratic. -/
theorem centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    finiteMatrixQuadratic
        (centralPhysicalFiniteCarrierSize w hw K half)
        (centralPhysicalFiniteKernel w hw K half)
        (centralPhysicalFiniteCoefficient w hw K half observable) ≈
      centralPhysicalJointQuadratic w hw K half observable := by
  unfold finiteMatrixQuadratic centralPhysicalFiniteCarrierSize
    centralPhysicalFiniteKernel centralPhysicalFiniteCoefficient
    centralPhysicalFiniteStateAt centralPhysicalJointQuadratic
    finiteJointQuadratic
  exact finiteIndexDoubleSum_eqv_listQSum
    (centralPositiveHalfStates w hw K half)
    zeroEdgeLabelling
    (fun left right =>
      (observable left * observable right) *
        centralNormalizedPhysicalReflectedKernel
          w hw K half left right)

/-- Exact physical centering transports to exact finite weighted centering. -/
theorem centralPhysicalFiniteCoefficient_centered
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {observable : EdgeLabelling → Q'}
    (hcenter : CentralPhysicalMeanZero w hw K half observable) :
    finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw K half)
        (centralPhysicalFiniteWeight w hw K half)
        (centralPhysicalFiniteCoefficient w hw K half observable) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
      w hw K half observable)
    hcenter

end YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteWeightedMean_eqv_stationaryMean
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteCoefficient_centered
