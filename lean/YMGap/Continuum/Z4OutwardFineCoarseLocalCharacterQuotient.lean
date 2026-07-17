/-
# Local character quotients for the outward fine/coarse comparison

The normalized physical laws already have exact event-numerator / partition
representations.  This module transports those representations across the
checked character/fusion identities from the outward adapter.  The resulting
quotients expose the literal local cross-difference directly to the generic
three-block retune-defect theorem, without unfolding the large physical
configuration structures.

No cross-difference estimate is postulated here: the final theorem takes the
explicit eight-cell local estimate as its hypothesis.
-/

import YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter

namespace YMGap.Continuum.Z4OutwardFineCoarseLocalCharacterQuotient

set_option maxRecDepth 8000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneCharacterCrossRatio
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

/-! ## 1. Constructive transport of quotient representations -/

def transportThreeBlockPatternQuotientRepresentation
    {State : Type} {law : ThreeBlockOverlapFiniteLaw State}
    (representation : ThreeBlockPatternQuotientRepresentation law)
    (numerator : ThreeBlockPattern → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (numerator_eqv : ∀ pattern,
      representation.numerator pattern ≈ numerator pattern)
    (partition_eqv : representation.partition ≈ partition) :
    ThreeBlockPatternQuotientRepresentation law where
  numerator := numerator
  partition := partition
  partition_pos := partition_pos
  pattern_mass_eqv := fun pattern =>
    Q'.eqv_trans _ _ _
      (representation.pattern_mass_eqv pattern)
      (divPos_eqv_congr_local
        representation.partition_pos partition_pos
        (numerator_eqv pattern) partition_eqv)

/-! ## 2. Exact local numerator and partition certificates -/

theorem outwardFineCharacterFusionPartition_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < outwardFineCharacterFusionPartition fineCoupling := by
  have hphysical := couplingKPhysicalPartition_pos
    (Q'.le_of_lt hfine) 1 6
  exact Q'.pos_of_lt_of_le hphysical
    (Q'.le_of_eqv
      (Q'.eqv_of_eq
        (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
          fineCoupling)))

theorem outwardCoarseCharacterFusionPartition_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < outwardCoarseCharacterFusionPartition fineCoupling := by
  have hphysical := couplingKPhysicalPartition_pos
    (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6
  exact Q'.pos_of_lt_of_le hphysical
    (Q'.le_of_eqv
      (Q'.eqv_of_eq
        (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
          (unitCubeBlockCoupling fineCoupling))))

theorem outwardFinePatternMass_eqv_localCharacterQuotient
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (outwardFineSubsupportLaw fineCoupling hfine) pattern ≈
      Q'.divPos
        (outwardFinePatternCharacterFusionNumerator
          fineCoupling pattern)
        (outwardFineCharacterFusionPartition fineCoupling)
        (outwardFineCharacterFusionPartition_pos fineCoupling hfine) := by
  unfold outwardFineSubsupportLaw
  refine Q'.eqv_trans _
    (Q'.divPos
      (parametricKEventNumerator fineCoupling 1 6
        (threeBlockPatternEvent
          (normalizedPhysicalThreeSubsupportLaw fineCoupling
            (Q'.le_of_lt hfine) 1 6 outwardFineQueries) pattern))
      (parametricKPhysicalPartition fineCoupling 1 6)
      (couplingKPhysicalPartition_pos (Q'.le_of_lt hfine) 1 6)) _ ?_ ?_
  · exact normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      fineCoupling (Q'.le_of_lt hfine) 1 6 outwardFineQueries pattern
  · exact divPos_eqv_congr_local
      (couplingKPhysicalPartition_pos (Q'.le_of_lt hfine) 1 6)
      (outwardFineCharacterFusionPartition_pos fineCoupling hfine)
      (parametricKEventNumerator_eq_outwardCharacterFusionNumerator
        fineCoupling (Q'.le_of_lt hfine) outwardFineQueries pattern)
      (Q'.eqv_of_eq
        (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
          fineCoupling))

theorem outwardCoarsePatternMass_eqv_localCharacterQuotient
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (outwardActivityMatchedCoarseSubsupportLaw
          fineCoupling hfine) pattern ≈
      Q'.divPos
        (outwardCoarsePatternCharacterFusionNumerator
          fineCoupling pattern)
        (outwardCoarseCharacterFusionPartition fineCoupling)
        (outwardCoarseCharacterFusionPartition_pos
          fineCoupling hfine) := by
  unfold outwardActivityMatchedCoarseSubsupportLaw
  refine Q'.eqv_trans _
    (Q'.divPos
      (parametricKEventNumerator (unitCubeBlockCoupling fineCoupling) 1 6
        (threeBlockPatternEvent
          (normalizedPhysicalThreeSubsupportLaw
            (unitCubeBlockCoupling fineCoupling)
            (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
            1 6 outwardCoarseQueries) pattern))
      (parametricKPhysicalPartition
        (unitCubeBlockCoupling fineCoupling) 1 6)
      (couplingKPhysicalPartition_pos
        (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6)) _ ?_ ?_
  · exact normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
      1 6 outwardCoarseQueries pattern
  · exact divPos_eqv_congr_local
      (couplingKPhysicalPartition_pos
        (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6)
      (outwardCoarseCharacterFusionPartition_pos fineCoupling hfine)
      (parametricKEventNumerator_eq_outwardCharacterFusionNumerator
        (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
        outwardCoarseQueries pattern)
      (Q'.eqv_of_eq
        (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
          (unitCubeBlockCoupling fineCoupling)))

/-! ## 3. Small literal character/fusion quotient representations -/

def outwardFineLocalCharacterQuotientRepresentation
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockPatternQuotientRepresentation
      (outwardFineSubsupportLaw fineCoupling hfine) :=
  { numerator := outwardFinePatternCharacterFusionNumerator fineCoupling
    partition := outwardFineCharacterFusionPartition fineCoupling
    partition_pos :=
      outwardFineCharacterFusionPartition_pos fineCoupling hfine
    pattern_mass_eqv :=
      outwardFinePatternMass_eqv_localCharacterQuotient
        fineCoupling hfine }

def outwardCoarseLocalCharacterQuotientRepresentation
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeBlockPatternQuotientRepresentation
      (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine) :=
  { numerator := outwardCoarsePatternCharacterFusionNumerator fineCoupling
    partition := outwardCoarseCharacterFusionPartition fineCoupling
    partition_pos :=
      outwardCoarseCharacterFusionPartition_pos fineCoupling hfine
    pattern_mass_eqv :=
      outwardCoarsePatternMass_eqv_localCharacterQuotient
        fineCoupling hfine }

/-! ## 4. Direct transfer of the exact residual to the retune defect -/

theorem outwardFineCoarseRetuneDefect_le_of_localCharacterCrossDifference
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (bound : Q')
    (hcross : OutwardFineCoarseLocalCrossDifferenceBound
      fineCoupling bound) :
    threeBlockPatternRetuneDefect
        (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw_patternMass_pos fineCoupling hfine) ≤
      bound := by
  apply threeBlockPatternRetuneDefect_le_of_characterCrossDiff
    (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine)
    (outwardFineSubsupportLaw fineCoupling hfine)
    (outwardCoarseLocalCharacterQuotientRepresentation
      fineCoupling hfine)
    (outwardFineLocalCharacterQuotientRepresentation
      fineCoupling hfine)
    (outwardFineSubsupportLaw_patternMass_pos fineCoupling hfine)
    bound
  intro pattern
  simpa only [outwardCoarseLocalCharacterQuotientRepresentation,
    outwardFineLocalCharacterQuotientRepresentation,
    outwardFineCoarseLocalCharacterCrossDifference,
    outwardFineCoarseLocalCharacterDenominator] using hcross pattern

#print axioms transportThreeBlockPatternQuotientRepresentation
#print axioms outwardFineCharacterFusionPartition_pos
#print axioms outwardCoarseCharacterFusionPartition_pos
#print axioms outwardFinePatternMass_eqv_localCharacterQuotient
#print axioms outwardCoarsePatternMass_eqv_localCharacterQuotient
#print axioms outwardFineLocalCharacterQuotientRepresentation
#print axioms outwardCoarseLocalCharacterQuotientRepresentation
#print axioms outwardFineCoarseRetuneDefect_le_of_localCharacterCrossDifference

end YMGap.Continuum.Z4OutwardFineCoarseLocalCharacterQuotient
