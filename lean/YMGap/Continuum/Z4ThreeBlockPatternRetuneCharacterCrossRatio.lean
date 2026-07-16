/-
# Character cross-ratios for the exact three-block retune

Normalized physical pattern masses are exact event-numerator / partition
quotients.  Consequently each retune ratio is the cross-ratio

  (source event numerator * target partition) /
  (target event numerator * source partition).

This module proves that identity constructively and exposes the division-free
cross-difference whose bound controls the derived eight-cell defect.  No such
physical cross-difference estimate is assumed here.
-/

import YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope

namespace YMGap.Continuum.Z4ThreeBlockPatternRetuneCharacterCrossRatio

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Abstract exact quotient representations -/

structure ThreeBlockPatternQuotientRepresentation {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) where
  numerator : ThreeBlockPattern → Q'
  partition : Q'
  partition_pos : (0 : Q') < partition
  pattern_mass_eqv : ∀ pattern,
    threeBlockPatternMass law pattern ≈
      Q'.divPos (numerator pattern) partition partition_pos

theorem representedPatternMass_mul_partition
    {State : Type} {law : ThreeBlockOverlapFiniteLaw State}
    (representation : ThreeBlockPatternQuotientRepresentation law)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass law pattern * representation.partition ≈
      representation.numerator pattern := by
  refine Q'.eqv_trans _
    (Q'.divPos (representation.numerator pattern)
        representation.partition representation.partition_pos *
      representation.partition) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (representation.pattern_mass_eqv pattern)
  exact Q'.divPos_mul_eqv _ _ _

theorem representedNumerator_pos_of_patternMass_pos
    {State : Type} {law : ThreeBlockOverlapFiniteLaw State}
    (representation : ThreeBlockPatternQuotientRepresentation law)
    (pattern : ThreeBlockPattern)
    (hpattern : (0 : Q') < threeBlockPatternMass law pattern) :
    (0 : Q') < representation.numerator pattern := by
  have hquot : (0 : Q') <
      Q'.divPos (representation.numerator pattern)
        representation.partition representation.partition_pos :=
    Q'.pos_of_lt_of_le hpattern
      (Q'.le_of_eqv (representation.pattern_mass_eqv pattern))
  have hproduct : (0 : Q') <
      Q'.divPos (representation.numerator pattern)
          representation.partition representation.partition_pos *
        representation.partition :=
    Q'.mul_pos hquot representation.partition_pos
  exact Q'.pos_of_lt_of_le hproduct
    (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _))

/-! ## 2. Exact retune cross-product and cross-ratio -/

theorem patternRetuneRatio_mul_characterDenominator
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (sourceRep : ThreeBlockPatternQuotientRepresentation sourceLaw)
    (targetRep : ThreeBlockPatternQuotientRepresentation targetLaw)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern *
        (targetRep.numerator pattern * sourceRep.partition) ≈
      sourceRep.numerator pattern * targetRep.partition := by
  let ratio := patternRetuneRatio sourceLaw targetLaw htargetPos pattern
  let sourceMass := threeBlockPatternMass sourceLaw pattern
  let targetMass := threeBlockPatternMass targetLaw pattern
  refine Q'.eqv_trans _
    (ratio *
      ((targetMass * targetRep.partition) * sourceRep.partition)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left ratio _ _
      (Q'.mul_eqv_congr_right _ _ sourceRep.partition
        (Q'.eqv_symm
          (representedPatternMass_mul_partition targetRep pattern)))
  refine Q'.eqv_trans _
    (ratio *
      (targetMass * (targetRep.partition * sourceRep.partition))) _
    (Q'.mul_eqv_congr_left ratio _ _
      (Q'.mul_assoc_eqv targetMass targetRep.partition
        sourceRep.partition)) ?_
  refine Q'.eqv_trans _
    ((ratio * targetMass) *
      (targetRep.partition * sourceRep.partition)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv ratio targetMass
        (targetRep.partition * sourceRep.partition))) ?_
  refine Q'.eqv_trans _
    (sourceMass * (targetRep.partition * sourceRep.partition)) _
    (Q'.mul_eqv_congr_right _ _ _
      (patternRetuneRatio_mul_targetPatternMass
        sourceLaw targetLaw htargetPos pattern)) ?_
  refine Q'.eqv_trans _
    (sourceMass * (sourceRep.partition * targetRep.partition)) _
    (Q'.mul_eqv_congr_left sourceMass _ _
      (Q'.mul_comm_eqv targetRep.partition sourceRep.partition)) ?_
  refine Q'.eqv_trans _
    ((sourceMass * sourceRep.partition) * targetRep.partition) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv sourceMass sourceRep.partition
        targetRep.partition)) ?_
  exact Q'.mul_eqv_congr_right _ _ targetRep.partition
    (representedPatternMass_mul_partition sourceRep pattern)

theorem characterDenominator_pos
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (sourceRep : ThreeBlockPatternQuotientRepresentation sourceLaw)
    (targetRep : ThreeBlockPatternQuotientRepresentation targetLaw)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < targetRep.numerator pattern * sourceRep.partition := by
  exact Q'.mul_pos
    (representedNumerator_pos_of_patternMass_pos targetRep pattern
      (htargetPos pattern))
    sourceRep.partition_pos

theorem patternRetuneRatio_eqv_characterCrossRatio
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (sourceRep : ThreeBlockPatternQuotientRepresentation sourceLaw)
    (targetRep : ThreeBlockPatternQuotientRepresentation targetLaw)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≈
      Q'.divPos
        (sourceRep.numerator pattern * targetRep.partition)
        (targetRep.numerator pattern * sourceRep.partition)
        (characterDenominator_pos sourceLaw targetLaw sourceRep targetRep
          htargetPos pattern) := by
  let denominator := targetRep.numerator pattern * sourceRep.partition
  let numerator := sourceRep.numerator pattern * targetRep.partition
  apply Q'.mul_left_cancel_of_pos
    (characterDenominator_pos sourceLaw targetLaw sourceRep targetRep
      htargetPos pattern)
  refine Q'.eqv_trans _
    (patternRetuneRatio sourceLaw targetLaw htargetPos pattern *
      denominator) _
    (Q'.mul_comm_eqv denominator
      (patternRetuneRatio sourceLaw targetLaw htargetPos pattern)) ?_
  refine Q'.eqv_trans _ numerator _
    (patternRetuneRatio_mul_characterDenominator
      sourceLaw targetLaw sourceRep targetRep htargetPos pattern) ?_
  refine Q'.eqv_trans _
    (Q'.divPos numerator denominator
        (characterDenominator_pos sourceLaw targetLaw sourceRep targetRep
          htargetPos pattern) * denominator) _
    (Q'.eqv_symm (Q'.divPos_mul_eqv _ _ _)) ?_
  exact Q'.mul_comm_eqv _ _

/-! ## 3. Division-free character cross-difference control -/

theorem patternRetuneRelativeError_le_of_characterCrossDiff
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (sourceRep : ThreeBlockPatternQuotientRepresentation sourceLaw)
    (targetRep : ThreeBlockPatternQuotientRepresentation targetLaw)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) (bound : Q')
    (hcross :
      absQ
          (sourceRep.numerator pattern * targetRep.partition +
            -(targetRep.numerator pattern * sourceRep.partition)) ≤
        bound *
          (targetRep.numerator pattern * sourceRep.partition)) :
    patternRetuneRelativeError sourceLaw targetLaw htargetPos pattern ≤
      bound := by
  let denominator := targetRep.numerator pattern * sourceRep.partition
  let numerator := sourceRep.numerator pattern * targetRep.partition
  have hratio := patternRetuneRatio_eqv_characterCrossRatio
    sourceLaw targetLaw sourceRep targetRep htargetPos pattern
  have harg :
      patternRetuneRatio sourceLaw targetLaw htargetPos pattern +
          -(1 : Q') ≈
        Q'.divPos numerator denominator
            (characterDenominator_pos sourceLaw targetLaw sourceRep targetRep
              htargetPos pattern) +
          -(1 : Q') :=
    Q'.add_eqv_congr_right _ _ _ hratio
  unfold patternRetuneRelativeError
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (absQ_eqv_congr harg)) ?_
  exact absQ_divPos_sub_one_le
    (characterDenominator_pos sourceLaw targetLaw sourceRep targetRep
      htargetPos pattern) hcross

theorem threeBlockPatternRetuneDefect_le_of_characterCrossDiff
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (sourceRep : ThreeBlockPatternQuotientRepresentation sourceLaw)
    (targetRep : ThreeBlockPatternQuotientRepresentation targetLaw)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (bound : Q')
    (hcross : ∀ pattern,
      absQ
          (sourceRep.numerator pattern * targetRep.partition +
            -(targetRep.numerator pattern * sourceRep.partition)) ≤
        bound *
          (targetRep.numerator pattern * sourceRep.partition)) :
    threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos ≤
      bound := by
  unfold threeBlockPatternRetuneDefect
  apply qMax8_le_of_bounds
  all_goals
    apply patternRetuneRelativeError_le_of_characterCrossDiff
      sourceLaw targetLaw sourceRep targetRep htargetPos
    exact hcross _

/-! ## 4. The actual normalized physical character representation -/

def normalizedPhysicalThreeSubsupportQuotientRepresentation
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    ThreeBlockPatternQuotientRepresentation
      (normalizedPhysicalThreeSubsupportLaw
        coupling hcoupling cutoff volume queries) where
  numerator := fun pattern =>
    parametricKEventNumerator coupling cutoff volume
      (threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries) pattern)
  partition := parametricKPhysicalPartition coupling cutoff volume
  partition_pos := couplingKPhysicalPartition_pos
    hcoupling cutoff volume
  pattern_mass_eqv :=
    normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      coupling hcoupling cutoff volume queries

#print axioms representedPatternMass_mul_partition
#print axioms representedNumerator_pos_of_patternMass_pos
#print axioms patternRetuneRatio_mul_characterDenominator
#print axioms characterDenominator_pos
#print axioms patternRetuneRatio_eqv_characterCrossRatio
#print axioms patternRetuneRelativeError_le_of_characterCrossDiff
#print axioms threeBlockPatternRetuneDefect_le_of_characterCrossDiff
#print axioms normalizedPhysicalThreeSubsupportQuotientRepresentation

end YMGap.Continuum.Z4ThreeBlockPatternRetuneCharacterCrossRatio
