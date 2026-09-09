/-
# Three-event raw-cross form of each connected Gibbs row

The source-resolved connected raw cross still hides its structure inside an
arbitrary-observable numerator.  This module expands that numerator exactly
into the joint, root, and target face cylinders.  Each cylinder contributes
one signed cross between its conditional recoupling-row raw mass and its
coarse physical raw mass.

The resulting numerator keeps the three signs and the two centered moment
coefficients intact.  It therefore exposes literal cylinder weights without
forcing a triangle inequality.  A relative bound on the combined signed
event-cross numerator compiles to the preceding row-cross calibration and
hence to the normalized centered remainder.

No smallness estimate is asserted.  The blocked target moment and coarse
root moment remain normalized coefficients; clearing those final partition
factors is the next algebraic step.

Constructive contract: finite rational sums and exact distributive algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawCross

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawEventCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawCross
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem distributeThree_mul_local
    (first second third factor : Q') :
    (first + (second + third)) * factor ≈
      first * factor + (second * factor + third * factor) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv first (second + third) factor)
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_mul_eqv second third factor))

private theorem additiveThreeCross_regroup_local
    (rowJoint rowRoot rowTarget coarseJoint coarseRoot coarseTarget : Q') :
    (rowJoint + (rowRoot + rowTarget)) +
        -(coarseJoint + (coarseRoot + coarseTarget)) ≈
      (rowJoint + -coarseJoint) +
        ((rowRoot + -coarseRoot) + (rowTarget + -coarseTarget)) := by
  ring_qeqv

private theorem coefficientCylinderCross_local
    (row coarse coefficient rowPartition coarsePartition : Q') :
    (row * coefficient) * coarsePartition +
        -((coarse * coefficient) * rowPartition) ≈
      coefficient *
        (row * coarsePartition + -(coarse * rowPartition)) := by
  ring_qeqv

private theorem negativeCylinderCross_local
    (row coarse rowPartition coarsePartition : Q') :
    (row * (-1)) * coarsePartition +
        -((coarse * (-1)) * rowPartition) ≈
      -(row * coarsePartition + -(coarse * rowPartition)) := by
  let cross := row * coarsePartition + -(coarse * rowPartition)
  refine Q'.eqv_trans _ ((-1 : Q') * cross) _ ?_ ?_
  · simpa only [cross] using
      (coefficientCylinderCross_local row coarse (-1)
        rowPartition coarsePartition)
  exact Q'.eqv_trans _ (-(1 * cross)) _
    (Q'.neg_mul_eqv 1 cross)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv cross))

private theorem observableNumerator_add_local
    {A : Type} (mass : A → Q') (items : List A)
    (left right : A → Q') :
    listQSum (fun item => mass item * (left item + right item)) items ≈
      listQSum (fun item => mass item * left item) items +
        listQSum (fun item => mass item * right item) items := by
  refine Q'.eqv_trans _
    (listQSum
      (fun item =>
        mass item * left item + mass item * right item)
      items) _ ?_ ?_
  · apply listQSum_congr
    intro item
    exact Q'.mul_add_eqv (mass item) (left item) (right item)
  exact listQSum_add
    (fun item => mass item * left item)
    (fun item => mass item * right item) items

private theorem observableNumerator_weightedCylinder_eqv_local
    (mass : EdgeLabelling → Q') (items : List EdgeLabelling)
    (event : EdgeLabelling → Bool) (coefficient : Q') :
    listQSum
        (fun state =>
          mass state * weightedCylinderObservable event coefficient state)
        items ≈
      finiteEventMass mass items event * coefficient := by
  unfold weightedCylinderObservable finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then mass state else 0) * coefficient)
      items) _ ?_ ?_
  · apply listQSum_congr
    intro state
    cases hevent : event state
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ 0 _
        (Q'.mul_zero_eqv (mass state))
        (Q'.eqv_symm (Q'.zero_mul_eqv coefficient))
    · simp only [if_true]
      exact Q'.eqv_refl _
  exact listQSum_mul_right
    (fun state => if event state then mass state else 0)
    coefficient items

private theorem wholeSlabRecouplingRawObservableNumerator_add
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (left right : EdgeLabelling → Q') :
    wholeSlabRecouplingRawObservableNumerator source
        (fun state => left state + right state) ≈
      wholeSlabRecouplingRawObservableNumerator source left +
        wholeSlabRecouplingRawObservableNumerator source right := by
  unfold wholeSlabRecouplingRawObservableNumerator
  exact observableNumerator_add_local
    (wholeSlabRecouplingRawWeight S source.fineState)
    S.coarse.physicalLabellings left right

private theorem physicalObservableNumerator_add
    (D : SlabPhysicalData) (left right : EdgeLabelling → Q') :
    physicalObservableNumerator D (fun state => left state + right state) ≈
      physicalObservableNumerator D left +
        physicalObservableNumerator D right := by
  unfold physicalObservableNumerator
  exact observableNumerator_add_local
    D.physicalTerm D.physicalLabellings left right

private theorem physicalObservableNumerator_indicator_eqv_eventMass
    (D : SlabPhysicalData) (event : EdgeLabelling → Bool) :
    physicalObservableNumerator D
        (weightedCylinderObservable event 1) ≈
      finiteEventMass D.physicalTerm D.physicalLabellings event := by
  unfold physicalObservableNumerator
  exact Q'.eqv_trans _ _ _
    (observableNumerator_weightedCylinder_eqv_local
      D.physicalTerm D.physicalLabellings event 1)
    (Q'.mul_one_eqv _)

theorem wholeSlabRecouplingRawObservableNumerator_weightedCylinder_eqv
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (event : EdgeLabelling → Bool) (coefficient : Q') :
    wholeSlabRecouplingRawObservableNumerator source
        (weightedCylinderObservable event coefficient) ≈
      wholeSlabRecouplingRawCylinderMass source event * coefficient := by
  unfold wholeSlabRecouplingRawObservableNumerator
    wholeSlabRecouplingRawCylinderMass
  exact observableNumerator_weightedCylinder_eqv_local
    (wholeSlabRecouplingRawWeight S source.fineState)
    S.coarse.physicalLabellings event coefficient

theorem physicalObservableNumerator_weightedCylinder_eqv
    (D : SlabPhysicalData) (event : EdgeLabelling → Bool)
    (coefficient : Q') :
    physicalObservableNumerator D
        (weightedCylinderObservable event coefficient) ≈
      physicalEventNumerator D event * coefficient := by
  refine Q'.eqv_trans _
    (finiteEventMass D.physicalTerm D.physicalLabellings event * coefficient)
    _ ?_ ?_
  · unfold physicalObservableNumerator
    exact observableNumerator_weightedCylinder_eqv_local
      D.physicalTerm D.physicalLabellings event coefficient
  exact Q'.mul_eqv_congr_right _ _ coefficient
    (Q'.eqv_symm
      (physicalObservableNumerator_indicator_eqv_eventMass D event))

/-! ## 1. Expand the connected observable into three cylinder numerators -/

theorem wholeSlabRecouplingRawConnectedObservableNumerator_eqv_threeEvents
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) :
    wholeSlabRecouplingRawObservableNumerator source
        (connectedRemainderObservable K M) ≈
      wholeSlabRecouplingRawCylinderMass source
          (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget) * (-1) +
        (wholeSlabRecouplingRawCylinderMass source
            (slabPhysicalFacePositiveB M.coarseRoot) *
              blockedFaceMoment K M.coarseTarget +
          wholeSlabRecouplingRawCylinderMass source
            (slabPhysicalFacePositiveB M.coarseTarget) *
              coarseFaceMoment K M.coarseRoot) := by
  let pairObservable := weightedCylinderObservable
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget) (-1)
  let rootObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseRoot)
    (blockedFaceMoment K M.coarseTarget)
  let targetObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseTarget)
    (coarseFaceMoment K M.coarseRoot)
  refine Q'.eqv_trans _
    (wholeSlabRecouplingRawObservableNumerator source pairObservable +
      (wholeSlabRecouplingRawObservableNumerator source rootObservable +
        wholeSlabRecouplingRawObservableNumerator source targetObservable))
    _ ?_ ?_
  · unfold connectedRemainderObservable pairObservable rootObservable
      targetObservable
    exact Q'.eqv_trans _ _ _
      (wholeSlabRecouplingRawObservableNumerator_add source _ _)
      (Q'.add_eqv_congr_left _ _ _
        (wholeSlabRecouplingRawObservableNumerator_add source _ _))
  exact Q'.add_eqv_congr'
    (wholeSlabRecouplingRawObservableNumerator_weightedCylinder_eqv
      source _ (-1))
    (Q'.add_eqv_congr'
      (wholeSlabRecouplingRawObservableNumerator_weightedCylinder_eqv
        source _ (blockedFaceMoment K M.coarseTarget))
      (wholeSlabRecouplingRawObservableNumerator_weightedCylinder_eqv
        source _ (coarseFaceMoment K M.coarseRoot)))

theorem coarsePhysicalConnectedObservableNumerator_eqv_threeEvents
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    physicalObservableNumerator S.coarse
        (connectedRemainderObservable K M) ≈
      physicalEventNumerator S.coarse
          (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget) * (-1) +
        (physicalEventNumerator S.coarse
            (slabPhysicalFacePositiveB M.coarseRoot) *
              blockedFaceMoment K M.coarseTarget +
          physicalEventNumerator S.coarse
            (slabPhysicalFacePositiveB M.coarseTarget) *
              coarseFaceMoment K M.coarseRoot) := by
  let pairObservable := weightedCylinderObservable
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget) (-1)
  let rootObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseRoot)
    (blockedFaceMoment K M.coarseTarget)
  let targetObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseTarget)
    (coarseFaceMoment K M.coarseRoot)
  refine Q'.eqv_trans _
    (physicalObservableNumerator S.coarse pairObservable +
      (physicalObservableNumerator S.coarse rootObservable +
        physicalObservableNumerator S.coarse targetObservable))
    _ ?_ ?_
  · unfold connectedRemainderObservable pairObservable rootObservable
      targetObservable
    exact Q'.eqv_trans _ _ _
      (physicalObservableNumerator_add S.coarse _ _)
      (Q'.add_eqv_congr_left _ _ _
        (physicalObservableNumerator_add S.coarse _ _))
  exact Q'.add_eqv_congr'
    (physicalObservableNumerator_weightedCylinder_eqv
      S.coarse _ (-1))
    (Q'.add_eqv_congr'
      (physicalObservableNumerator_weightedCylinder_eqv
        S.coarse _ (blockedFaceMoment K M.coarseTarget))
      (physicalObservableNumerator_weightedCylinder_eqv
        S.coarse _ (coarseFaceMoment K M.coarseRoot)))

/-! ## 2. One signed cross for each literal cylinder -/

/-- Raw row-versus-coarse cross numerator of one Boolean cylinder. -/
def wholeSlabRecouplingRawCylinderCrossNumerator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  wholeSlabRecouplingRawCylinderMass source event *
      S.coarse.physicalPartition +
    -(physicalEventNumerator S.coarse event *
      wholeSlabRecouplingPartition source)

/-- The connected arbitrary-observable cross, expanded as one signed
combination of the three literal cylinder crosses. -/
def wholeSlabRecouplingConnectedRawEventCrossNumerator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) : Q' :=
  -(wholeSlabRecouplingRawCylinderCrossNumerator source
      (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)) +
    (blockedFaceMoment K M.coarseTarget *
        wholeSlabRecouplingRawCylinderCrossNumerator source
          (slabPhysicalFacePositiveB M.coarseRoot) +
      coarseFaceMoment K M.coarseRoot *
        wholeSlabRecouplingRawCylinderCrossNumerator source
          (slabPhysicalFacePositiveB M.coarseTarget))

theorem wholeSlabRecouplingConnectedRawCrossNumerator_eqv_threeEventCross
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) :
    wholeSlabRecouplingRawObservableCrossNumerator source
        (connectedRemainderObservable K M) ≈
      wholeSlabRecouplingConnectedRawEventCrossNumerator source K M := by
  let rowJoint := wholeSlabRecouplingRawCylinderMass source
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
  let rowRoot := wholeSlabRecouplingRawCylinderMass source
    (slabPhysicalFacePositiveB M.coarseRoot)
  let rowTarget := wholeSlabRecouplingRawCylinderMass source
    (slabPhysicalFacePositiveB M.coarseTarget)
  let coarseJoint := physicalEventNumerator S.coarse
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
  let coarseRoot := physicalEventNumerator S.coarse
    (slabPhysicalFacePositiveB M.coarseRoot)
  let coarseTarget := physicalEventNumerator S.coarse
    (slabPhysicalFacePositiveB M.coarseTarget)
  let blockedCoefficient := blockedFaceMoment K M.coarseTarget
  let coarseCoefficient := coarseFaceMoment K M.coarseRoot
  let rowPartition := wholeSlabRecouplingPartition source
  let coarsePartition := S.coarse.physicalPartition
  refine Q'.eqv_trans _
    (((rowJoint * (-1)) * coarsePartition +
        ((rowRoot * blockedCoefficient) * coarsePartition +
          (rowTarget * coarseCoefficient) * coarsePartition)) +
      -((coarseJoint * (-1)) * rowPartition +
        ((coarseRoot * blockedCoefficient) * rowPartition +
          (coarseTarget * coarseCoefficient) * rowPartition))) _ ?_ ?_
  · unfold wholeSlabRecouplingRawObservableCrossNumerator
    refine Q'.eqv_trans _
      ((rowJoint * (-1) +
          (rowRoot * blockedCoefficient + rowTarget * coarseCoefficient)) *
          coarsePartition +
        -((coarseJoint * (-1) +
          (coarseRoot * blockedCoefficient +
            coarseTarget * coarseCoefficient)) * rowPartition)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ coarsePartition
          (by
            simpa only [rowJoint, rowRoot, rowTarget, blockedCoefficient,
              coarseCoefficient] using
              wholeSlabRecouplingRawConnectedObservableNumerator_eqv_threeEvents
                source K M))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ rowPartition
            (by
              simpa only [coarseJoint, coarseRoot, coarseTarget,
                blockedCoefficient, coarseCoefficient] using
                coarsePhysicalConnectedObservableNumerator_eqv_threeEvents
                  K M)))
    exact Q'.add_eqv_congr'
      (distributeThree_mul_local
        (rowJoint * (-1)) (rowRoot * blockedCoefficient)
        (rowTarget * coarseCoefficient) coarsePartition)
      (Q'.neg_eqv_congr _ _
        (distributeThree_mul_local
          (coarseJoint * (-1)) (coarseRoot * blockedCoefficient)
          (coarseTarget * coarseCoefficient) rowPartition))
  refine Q'.eqv_trans _
    (((rowJoint * (-1)) * coarsePartition +
        -((coarseJoint * (-1)) * rowPartition)) +
      (((rowRoot * blockedCoefficient) * coarsePartition +
          -((coarseRoot * blockedCoefficient) * rowPartition)) +
        ((rowTarget * coarseCoefficient) * coarsePartition +
          -((coarseTarget * coarseCoefficient) * rowPartition)))) _ ?_ ?_
  · exact additiveThreeCross_regroup_local
      ((rowJoint * (-1)) * coarsePartition)
      ((rowRoot * blockedCoefficient) * coarsePartition)
      ((rowTarget * coarseCoefficient) * coarsePartition)
      ((coarseJoint * (-1)) * rowPartition)
      ((coarseRoot * blockedCoefficient) * rowPartition)
      ((coarseTarget * coarseCoefficient) * rowPartition)
  simpa only [wholeSlabRecouplingConnectedRawEventCrossNumerator,
      wholeSlabRecouplingRawCylinderCrossNumerator, rowJoint, rowRoot,
      rowTarget, coarseJoint, coarseRoot, coarseTarget, blockedCoefficient,
      coarseCoefficient, rowPartition, coarsePartition] using
    (Q'.add_eqv_congr'
      (negativeCylinderCross_local rowJoint coarseJoint
        rowPartition coarsePartition)
      (Q'.add_eqv_congr'
        (coefficientCylinderCross_local rowRoot coarseRoot
          blockedCoefficient rowPartition coarsePartition)
        (coefficientCylinderCross_local rowTarget coarseTarget
          coarseCoefficient rowPartition coarsePartition)))

/-! ## 3. Positive physical specialization and calibration -/

def positivePhysicalConnectedRawEventCrossNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) : Q' :=
  wholeSlabRecouplingConnectedRawEventCrossNumerator
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    (physicalKernel S hfineCutoff hcoarseCoupling) M

theorem positivePhysicalConnectedRawCrossNumerator_eqv_threeEventCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawCrossNumerator
        S hfineCutoff hcoarseCoupling source hsource hpositive M ≈
      positivePhysicalConnectedRawEventCrossNumerator
        S hfineCutoff hcoarseCoupling source hsource hpositive M := by
  unfold positivePhysicalConnectedRawCrossNumerator
    positivePhysicalConnectedRawEventCrossNumerator
  exact wholeSlabRecouplingConnectedRawCrossNumerator_eqv_threeEventCross
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    (physicalKernel S hfineCutoff hcoarseCoupling) M

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hnumerator

theorem positivePhysicalConnectedRawRowAction_eqv_threeEventCross_divPos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawRowAction
        S hfineCutoff hcoarseCoupling source hsource hpositive M ≈
      Q'.divPos
        (positivePhysicalConnectedRawEventCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M)
        (positivePhysicalConnectedRawCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive)
        (positivePhysicalConnectedRawCrossDenominator_pos
          S hfineCutoff hcoarseCoupling source hsource hpositive) := by
  exact Q'.eqv_trans _ _ _
    (positivePhysicalConnectedRawRowAction_eqv_rawCross_divPos
      S hfineCutoff hcoarseCoupling source hsource hpositive M)
    (divPos_eqv_congr_numerator_local
      (positivePhysicalConnectedRawCrossDenominator_pos
        S hfineCutoff hcoarseCoupling source hsource hpositive)
      (positivePhysicalConnectedRawCrossNumerator_eqv_threeEventCross
        S hfineCutoff hcoarseCoupling source hsource hpositive M))

/-- Division-free pointwise premise on the combined signed joint/root/target
event-cross numerator. -/
def PositivePhysicalConnectedRawEventCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  ∀ source (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source),
    Q'.abs
        (positivePhysicalConnectedRawEventCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M) ≤
      (kernelCeiling * (g * g)) *
        positivePhysicalConnectedRawCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive

theorem positivePhysicalConnectedRawCrossCalibration_of_threeEventCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hevents : PositivePhysicalConnectedRawEventCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    PositivePhysicalConnectedRawCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold PositivePhysicalConnectedRawCrossCalibration
  intro source hsource hpositive
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positivePhysicalConnectedRawCrossNumerator_eqv_threeEventCross
          S hfineCutoff hcoarseCoupling source hsource hpositive M))) ?_
  unfold PositivePhysicalConnectedRawEventCrossCalibration at hevents
  exact hevents source hsource hpositive

theorem coarseGibbsRefreshConnectedRemainderCalibration_of_threeEventCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hevents : PositivePhysicalConnectedRawEventCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawCross
    S hfineCutoff hcoarseCoupling M g kernelCeiling
    (positivePhysicalConnectedRawCrossCalibration_of_threeEventCross
      S hfineCutoff hcoarseCoupling M g kernelCeiling hevents)

#print axioms wholeSlabRecouplingRawObservableNumerator_weightedCylinder_eqv
#print axioms physicalObservableNumerator_weightedCylinder_eqv
#print axioms wholeSlabRecouplingRawConnectedObservableNumerator_eqv_threeEvents
#print axioms coarsePhysicalConnectedObservableNumerator_eqv_threeEvents
#print axioms wholeSlabRecouplingRawCylinderCrossNumerator
#print axioms wholeSlabRecouplingConnectedRawEventCrossNumerator
#print axioms wholeSlabRecouplingConnectedRawCrossNumerator_eqv_threeEventCross
#print axioms positivePhysicalConnectedRawEventCrossNumerator
#print axioms positivePhysicalConnectedRawCrossNumerator_eqv_threeEventCross
#print axioms positivePhysicalConnectedRawRowAction_eqv_threeEventCross_divPos
#print axioms PositivePhysicalConnectedRawEventCrossCalibration
#print axioms positivePhysicalConnectedRawCrossCalibration_of_threeEventCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_threeEventCross

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawEventCross
