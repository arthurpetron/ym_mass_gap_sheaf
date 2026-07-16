/-
# Outward fine/coarse character-numerator adapter

The source law is the outward coarse-query law at the derived block coupling
`2 * beta^4`; the target law is the outward fine-query law at `beta`.  This
module expands their exact event numerators into finite sums of local
heat-kernel character products times exact link-fusion multiplicities.  The
physical retune cross-difference is thereby identified with one literal
rational expression.  Bounding that expression remains an explicit theorem
obligation; it is not assumed or hidden in a retuned definition.
-/

import YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
import YMGap.Continuum.Z4ThreeBlockPatternRetuneCharacterCrossRatio
import YMGap.Continuum.Z4UnitCubeBareCouplingShift

namespace YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneCharacterCrossRatio
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio
open YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The two concrete physical laws and their positive cells -/

def outwardFineSubsupportLaw
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeSubsupportLaw fineCoupling
    (Q'.le_of_lt hfine) 1 6 outwardFineQueries

def outwardActivityMatchedCoarseSubsupportLaw
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeSubsupportLaw
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
    1 6 outwardCoarseQueries

theorem outwardFineSubsupportLaw_patternMass_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ∀ pattern, (0 : Q') < threeBlockPatternMass
      (outwardFineSubsupportLaw fineCoupling hfine) pattern := by
  unfold outwardFineSubsupportLaw
  intro pattern
  obtain ⟨left, ⟨shared, right⟩⟩ := pattern
  have hall := outwardAllEightFinePatternMasses_pos fineCoupling hfine
  cases left with
  | false =>
      cases shared with
      | false =>
          cases right with
          | false => exact hall.1
          | true => exact hall.2.2.2.1
      | true =>
          cases right with
          | false => exact hall.2.2.1
          | true => exact hall.2.2.2.2.2.2.1
  | true =>
      cases shared with
      | false =>
          cases right with
          | false => exact hall.2.1
          | true => exact hall.2.2.2.2.2.1
      | true =>
          cases right with
          | false => exact hall.2.2.2.2.1
          | true => exact hall.2.2.2.2.2.2.2

theorem outwardActivityMatchedCoarseSubsupportLaw_patternMass_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ∀ pattern, (0 : Q') < threeBlockPatternMass
      (outwardActivityMatchedCoarseSubsupportLaw
        fineCoupling hfine) pattern := by
  intro pattern
  simpa [outwardActivityMatchedCoarseSubsupportLaw,
    outwardCoarseSubsupportLaw] using
    (outwardCoarseSubsupportLaw_patternMass_pos
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_pos hfine) pattern)

/-! ## 2. Literal local character/fusion blocks -/

def outwardCutoffOnePhysicalStates : List EdgeLabelling :=
  boundedEdgeLabellings 1 (List.range (plaquetteEdgeCount 6))

/-- Product of the cutoff-one heat-kernel character coefficient attached to
each finite-box plaquette. -/
def outwardCutoffOneCharacterFaceBlock
    (coupling : Q') (physical : EdgeLabelling) : Q' :=
  parametricKPhysicalFaceFactor coupling 1 6 physical

/-- Product of the exact local SU(2) invariant/fusion-path cardinalities at
all finite-box links. -/
def outwardCutoffOneFusionMultiplicityBlock
    (physical : EdgeLabelling) : Q' :=
  explicitLinkMultiplicityProduct 1 6 physical
    (enumerate (distinctBoxLinks 6))

def outwardCutoffOneCharacterFusionBlock
    (coupling : Q') (physical : EdgeLabelling) : Q' :=
  outwardCutoffOneCharacterFaceBlock coupling physical *
    outwardCutoffOneFusionMultiplicityBlock physical

theorem parametricKPhysicalTerm_eq_outwardCharacterFusionBlock
    (coupling : Q') (physical : EdgeLabelling) :
    parametricKPhysicalTerm coupling 1 6 physical =
      outwardCutoffOneCharacterFusionBlock coupling physical := by
  rfl

def outwardPhysicalPatternMask
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (physical : EdgeLabelling) : Bool :=
  decide (physicalComponentSubsupportPattern 6 queries physical = pattern)

theorem normalizedPhysicalPatternEvent_eq_outwardMask
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (physical : EdgeLabelling) :
    threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling 1 6 queries) pattern physical =
      outwardPhysicalPatternMask queries pattern physical := by
  unfold threeBlockPatternEvent outwardPhysicalPatternMask
  rw [normalizedPhysicalThreeSubsupportPattern_eq]

def outwardPatternCharacterFusionTerm
    (coupling : Q') (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (physical : EdgeLabelling) : Q' :=
  if outwardPhysicalPatternMask queries pattern physical then
    outwardCutoffOneCharacterFusionBlock coupling physical
  else 0

def outwardPatternCharacterFusionNumerator
    (coupling : Q') (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) : Q' :=
  listQSum
    (outwardPatternCharacterFusionTerm coupling queries pattern)
    outwardCutoffOnePhysicalStates

def outwardCharacterFusionPartition (coupling : Q') : Q' :=
  listQSum (outwardCutoffOneCharacterFusionBlock coupling)
    outwardCutoffOnePhysicalStates

theorem parametricKEventNumerator_eq_outwardCharacterFusionNumerator
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) :
    parametricKEventNumerator coupling 1 6
        (threeBlockPatternEvent
          (normalizedPhysicalThreeSubsupportLaw
            coupling hcoupling 1 6 queries) pattern) ≈
      outwardPatternCharacterFusionNumerator
        coupling queries pattern := by
  unfold parametricKEventNumerator
    outwardPatternCharacterFusionNumerator
    outwardCutoffOnePhysicalStates
  apply listQSum_congr_on
  intro physical _
  unfold parametricKEventTerm outwardPatternCharacterFusionTerm
  rw [normalizedPhysicalPatternEvent_eq_outwardMask]
  cases hmask : outwardPhysicalPatternMask queries pattern physical
  · simp only [Bool.false_eq_true, if_false]
    exact Q'.eqv_refl 0
  · simp only [if_true]
    exact Q'.eqv_of_eq
      (parametricKPhysicalTerm_eq_outwardCharacterFusionBlock
        coupling physical)

theorem parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
    (coupling : Q') :
    parametricKPhysicalPartition coupling 1 6 =
      outwardCharacterFusionPartition coupling := by
  rfl

/-! ## 3. Exact concrete cross-difference -/

def outwardCoarsePatternCharacterFusionNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardPatternCharacterFusionNumerator
    (unitCubeBlockCoupling fineCoupling) outwardCoarseQueries pattern

def outwardFinePatternCharacterFusionNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardPatternCharacterFusionNumerator
    fineCoupling outwardFineQueries pattern

def outwardCoarseCharacterFusionPartition
    (fineCoupling : Q') : Q' :=
  outwardCharacterFusionPartition (unitCubeBlockCoupling fineCoupling)

def outwardFineCharacterFusionPartition
    (fineCoupling : Q') : Q' :=
  outwardCharacterFusionPartition fineCoupling

/-- The literal physical numerator cross-difference: coarse event numerator
times fine partition, minus fine event numerator times coarse partition. -/
def outwardFineCoarseLocalCharacterCrossDifference
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCoarsePatternCharacterFusionNumerator fineCoupling pattern *
      outwardFineCharacterFusionPartition fineCoupling +
    -(outwardFinePatternCharacterFusionNumerator fineCoupling pattern *
      outwardCoarseCharacterFusionPartition fineCoupling)

def outwardFineCoarseLocalCharacterDenominator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardFinePatternCharacterFusionNumerator fineCoupling pattern *
    outwardCoarseCharacterFusionPartition fineCoupling

def outwardCoarseSubsupportQuotientRepresentation
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockPatternQuotientRepresentation
      (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine) :=
  normalizedPhysicalThreeSubsupportQuotientRepresentation
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
    1 6 outwardCoarseQueries

def outwardFineSubsupportQuotientRepresentation
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockPatternQuotientRepresentation
      (outwardFineSubsupportLaw fineCoupling hfine) :=
  normalizedPhysicalThreeSubsupportQuotientRepresentation
    fineCoupling (Q'.le_of_lt hfine) 1 6 outwardFineQueries

def outwardFineCoarsePhysicalNumeratorCrossDifference
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) : Q' :=
  parametricKEventNumerator (unitCubeBlockCoupling fineCoupling) 1 6
        (threeBlockPatternEvent
          (outwardActivityMatchedCoarseSubsupportLaw
            fineCoupling hfine) pattern) *
      parametricKPhysicalPartition fineCoupling 1 6 +
    -(parametricKEventNumerator fineCoupling 1 6
          (threeBlockPatternEvent
            (outwardFineSubsupportLaw fineCoupling hfine) pattern) *
        parametricKPhysicalPartition
          (unitCubeBlockCoupling fineCoupling) 1 6)

theorem outwardFineCoarsePhysicalNumeratorCrossDifference_eq_localCharacterFusion
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    outwardFineCoarsePhysicalNumeratorCrossDifference
        fineCoupling hfine pattern ≈
      outwardFineCoarseLocalCharacterCrossDifference
        fineCoupling pattern := by
  unfold outwardFineCoarsePhysicalNumeratorCrossDifference
    outwardActivityMatchedCoarseSubsupportLaw
    outwardFineSubsupportLaw
    outwardFineCoarseLocalCharacterCrossDifference
    outwardCoarsePatternCharacterFusionNumerator
    outwardFinePatternCharacterFusionNumerator
    outwardCoarseCharacterFusionPartition
    outwardFineCharacterFusionPartition
  have hcoarseNumerator :=
    parametricKEventNumerator_eq_outwardCharacterFusionNumerator
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
      outwardCoarseQueries pattern
  have hfineNumerator :=
    parametricKEventNumerator_eq_outwardCharacterFusionNumerator
      fineCoupling (Q'.le_of_lt hfine) outwardFineQueries pattern
  have hcoarsePartition :
      parametricKPhysicalPartition
          (unitCubeBlockCoupling fineCoupling) 1 6 ≈
        outwardCharacterFusionPartition
          (unitCubeBlockCoupling fineCoupling) :=
    Q'.eqv_of_eq
      (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition _)
  have hfinePartition :
      parametricKPhysicalPartition fineCoupling 1 6 ≈
        outwardCharacterFusionPartition fineCoupling :=
    Q'.eqv_of_eq
      (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition _)
  exact Q'.add_eqv_congr'
    (mul_eqv_congr hcoarseNumerator hfinePartition)
    (Q'.neg_eqv_congr _ _
      (mul_eqv_congr hfineNumerator hcoarsePartition))

def outwardFineCoarsePhysicalDenominator
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) : Q' :=
  parametricKEventNumerator fineCoupling 1 6
      (threeBlockPatternEvent
        (outwardFineSubsupportLaw fineCoupling hfine) pattern) *
    parametricKPhysicalPartition
      (unitCubeBlockCoupling fineCoupling) 1 6

theorem outwardFineCoarsePhysicalDenominator_eq_localCharacterFusion
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    outwardFineCoarsePhysicalDenominator fineCoupling hfine pattern ≈
      outwardFineCoarseLocalCharacterDenominator
        fineCoupling pattern := by
  unfold outwardFineCoarsePhysicalDenominator
    outwardFineSubsupportLaw
    outwardFineCoarseLocalCharacterDenominator
    outwardFinePatternCharacterFusionNumerator
    outwardCoarseCharacterFusionPartition
  exact mul_eqv_congr
    (parametricKEventNumerator_eq_outwardCharacterFusionNumerator
      fineCoupling (Q'.le_of_lt hfine) outwardFineQueries pattern)
    (Q'.eqv_of_eq
      (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition _))

theorem outwardFinePhysicalEventNumerator_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < parametricKEventNumerator fineCoupling 1 6
      (threeBlockPatternEvent
        (outwardFineSubsupportLaw fineCoupling hfine) pattern) := by
  have hpattern := outwardFineSubsupportLaw_patternMass_pos
    fineCoupling hfine pattern
  unfold outwardFineSubsupportLaw at hpattern ⊢
  have hratio :=
    normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      fineCoupling (Q'.le_of_lt hfine) 1 6 outwardFineQueries pattern
  have hquot : (0 : Q') <
      Q'.divPos
        (parametricKEventNumerator fineCoupling 1 6
          (threeBlockPatternEvent
            (normalizedPhysicalThreeSubsupportLaw fineCoupling
              (Q'.le_of_lt hfine) 1 6 outwardFineQueries) pattern))
        (parametricKPhysicalPartition fineCoupling 1 6)
        (couplingKPhysicalPartition_pos
          (Q'.le_of_lt hfine) 1 6) :=
    Q'.pos_of_lt_of_le hpattern (Q'.le_of_eqv hratio)
  have hproduct : (0 : Q') <
      Q'.divPos
          (parametricKEventNumerator fineCoupling 1 6
            (threeBlockPatternEvent
              (normalizedPhysicalThreeSubsupportLaw fineCoupling
                (Q'.le_of_lt hfine) 1 6 outwardFineQueries) pattern))
          (parametricKPhysicalPartition fineCoupling 1 6)
          (couplingKPhysicalPartition_pos
            (Q'.le_of_lt hfine) 1 6) *
        parametricKPhysicalPartition fineCoupling 1 6 :=
    Q'.mul_pos hquot
      (couplingKPhysicalPartition_pos (Q'.le_of_lt hfine) 1 6)
  exact Q'.pos_of_lt_of_le hproduct
    (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _))

theorem outwardFineCoarsePhysicalDenominator_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < outwardFineCoarsePhysicalDenominator
      fineCoupling hfine pattern := by
  unfold outwardFineCoarsePhysicalDenominator
  exact Q'.mul_pos
    (outwardFinePhysicalEventNumerator_pos fineCoupling hfine pattern)
    (couplingKPhysicalPartition_pos
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6)

theorem outwardFineCoarseLocalCharacterDenominator_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < outwardFineCoarseLocalCharacterDenominator
      fineCoupling pattern := by
  exact Q'.pos_of_lt_of_le
    (outwardFineCoarsePhysicalDenominator_pos
      fineCoupling hfine pattern)
    (Q'.le_of_eqv
      (outwardFineCoarsePhysicalDenominator_eq_localCharacterFusion
        fineCoupling hfine pattern))

/-! ## 4. The exact remaining eight-cell inequality -/

/-- This is the remaining nontrivial estimate, stated entirely in terms of
derived finite character/fusion sums. -/
def OutwardFineCoarseLocalCrossDifferenceBound
    (fineCoupling bound : Q') : Prop :=
  ∀ pattern,
    absQ (outwardFineCoarseLocalCharacterCrossDifference
        fineCoupling pattern) ≤
      bound * outwardFineCoarseLocalCharacterDenominator
        fineCoupling pattern

theorem outwardFineCoarsePhysicalCrossDifference_le_of_local
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (bound : Q') (pattern : ThreeBlockPattern)
    (hcross : OutwardFineCoarseLocalCrossDifferenceBound
      fineCoupling bound) :
    absQ (outwardFineCoarsePhysicalNumeratorCrossDifference
      fineCoupling hfine pattern) ≤
      bound * outwardFineCoarsePhysicalDenominator
        fineCoupling hfine pattern := by
  have hlocal := hcross pattern
  have hdiff :=
    outwardFineCoarsePhysicalNumeratorCrossDifference_eq_localCharacterFusion
      fineCoupling hfine pattern
  have hdenominator :=
    outwardFineCoarsePhysicalDenominator_eq_localCharacterFusion
      fineCoupling hfine pattern
  have habs := absQ_eqv_congr hdiff
  have hscaledDenominator := Q'.mul_eqv_congr_left bound _ _ hdenominator
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv habs) hlocal)
    (Q'.ge_of_eqv hscaledDenominator)

#print axioms outwardFineSubsupportLaw_patternMass_pos
#print axioms outwardActivityMatchedCoarseSubsupportLaw_patternMass_pos
#print axioms parametricKPhysicalTerm_eq_outwardCharacterFusionBlock
#print axioms normalizedPhysicalPatternEvent_eq_outwardMask
#print axioms parametricKEventNumerator_eq_outwardCharacterFusionNumerator
#print axioms parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
#print axioms outwardFineCoarsePhysicalNumeratorCrossDifference_eq_localCharacterFusion
#print axioms outwardFineCoarseLocalCharacterDenominator_pos
#print axioms outwardFineCoarsePhysicalCrossDifference_le_of_local

end YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter
