/-
# Compatible support-gas form of the outward fine/coarse residual

At cutoff one, direct physical-state enumeration has one Boolean label for
every plaquette of the volume-six box.  The exact support-fibre bijection
already reindexes that list into compatible families of connected surfaces.
This module applies the reindexing to all eight outward pattern numerators
and to both partitions, and transports the literal character cross-difference
to a support-gas cross-difference on which polymer estimates can operate.

The support-gas estimate itself remains an explicit obligation.
-/

import YMGap.Continuum.Z4OutwardFineCoarseLocalEightCells
import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge

namespace YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter
open YMGap.Continuum.Z4OutwardFineCoarseLocalCharacterQuotient
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The same three-bit event on compatible surface families -/

def outwardComponentSubsupportFamilyPattern
    (queries : ComponentSubsupportQueryTriple)
    (family : List (List Nat)) : ThreeBlockPattern :=
  (familyContainsComponentSubsupportB
      (componentSubsupportQueryLeft queries) family,
    familyContainsComponentSubsupportB
      (componentSubsupportQueryShared queries) family,
    familyContainsComponentSubsupportB
      (componentSubsupportQueryRight queries) family)

def outwardComponentSubsupportFamilyPatternEvent
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) : List (List Nat) → Bool :=
  fun family => decide
    (outwardComponentSubsupportFamilyPattern queries family = pattern)

theorem normalizedPhysicalPatternEvent_eq_liftedFamilyPatternEvent
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling 1 6 queries) pattern =
      cutoffOneLiftedFamilyEvent 6
        (outwardComponentSubsupportFamilyPatternEvent queries pattern) := by
  funext physical
  unfold threeBlockPatternEvent
  rw [normalizedPhysicalThreeSubsupportPattern_eq]
  rfl

/-! ## 2. Exact numerator and partition reindexing -/

def outwardCompatibleSupportPatternNumerator
    (coupling : Q') (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
    coupling 1 6
    (outwardComponentSubsupportFamilyPatternEvent queries pattern)

def outwardCompatibleSupportPartition (coupling : Q') : Q' :=
  couplingParametricKCompatibleSupportGasPartition coupling 1 6

theorem outwardPatternCharacterFusionNumerator_eqv_compatibleSupport
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) :
    outwardPatternCharacterFusionNumerator
        coupling queries pattern ≈
      outwardCompatibleSupportPatternNumerator
        coupling queries pattern := by
  have hphysical :=
    parametricKEventNumerator_eq_outwardCharacterFusionNumerator
      coupling hcoupling queries pattern
  rw [normalizedPhysicalPatternEvent_eq_liftedFamilyPatternEvent
    coupling hcoupling queries pattern] at hphysical
  unfold outwardCompatibleSupportPatternNumerator
  exact Q'.eqv_trans _
    (parametricKEventNumerator coupling 1 6
      (cutoffOneLiftedFamilyEvent 6
        (outwardComponentSubsupportFamilyPatternEvent queries pattern))) _
    (Q'.eqv_symm hphysical)
    (couplingParametricKEventNumerator_eqv_compatibleEventNumerator
      hcoupling 1 6
      (outwardComponentSubsupportFamilyPatternEvent queries pattern))

theorem outwardCharacterFusionPartition_eqv_compatibleSupport
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) :
    outwardCharacterFusionPartition coupling ≈
      outwardCompatibleSupportPartition coupling := by
  unfold outwardCompatibleSupportPartition
  exact Q'.eqv_trans _
    (parametricKPhysicalPartition coupling 1 6) _
    (Q'.eqv_symm
      (Q'.eqv_of_eq
        (parametricKPhysicalPartition_eq_outwardCharacterFusionPartition
          coupling)))
    (couplingParametricKPhysicalPartition_eqv_compatibleSupportGas
      hcoupling 1 6)

/-! ## 3. The literal compatible support-gas cross-difference -/

def outwardCoarseCompatibleSupportPatternNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCompatibleSupportPatternNumerator
    (unitCubeBlockCoupling fineCoupling) outwardCoarseQueries pattern

def outwardFineCompatibleSupportPatternNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCompatibleSupportPatternNumerator
    fineCoupling outwardFineQueries pattern

def outwardCoarseCompatibleSupportPartition
    (fineCoupling : Q') : Q' :=
  outwardCompatibleSupportPartition
    (unitCubeBlockCoupling fineCoupling)

def outwardFineCompatibleSupportPartition
    (fineCoupling : Q') : Q' :=
  outwardCompatibleSupportPartition fineCoupling

def outwardFineCoarseCompatibleSupportCrossDifference
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCoarseCompatibleSupportPatternNumerator
        fineCoupling pattern *
      outwardFineCompatibleSupportPartition fineCoupling +
    -(outwardFineCompatibleSupportPatternNumerator
          fineCoupling pattern *
        outwardCoarseCompatibleSupportPartition fineCoupling)

def outwardFineCoarseCompatibleSupportDenominator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardFineCompatibleSupportPatternNumerator fineCoupling pattern *
    outwardCoarseCompatibleSupportPartition fineCoupling

theorem outwardFineCoarseLocalCrossDifference_eqv_compatibleSupport
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    outwardFineCoarseLocalCharacterCrossDifference
        fineCoupling pattern ≈
      outwardFineCoarseCompatibleSupportCrossDifference
        fineCoupling pattern := by
  unfold outwardFineCoarseLocalCharacterCrossDifference
    outwardFineCoarseCompatibleSupportCrossDifference
    outwardCoarsePatternCharacterFusionNumerator
    outwardFinePatternCharacterFusionNumerator
    outwardCoarseCharacterFusionPartition
    outwardFineCharacterFusionPartition
    outwardCoarseCompatibleSupportPatternNumerator
    outwardFineCompatibleSupportPatternNumerator
    outwardCoarseCompatibleSupportPartition
    outwardFineCompatibleSupportPartition
  exact Q'.add_eqv_congr'
    (mul_eqv_congr
      (outwardPatternCharacterFusionNumerator_eqv_compatibleSupport
        (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
        outwardCoarseQueries pattern)
      (outwardCharacterFusionPartition_eqv_compatibleSupport
        fineCoupling (Q'.le_of_lt hfine)))
    (Q'.neg_eqv_congr _ _
      (mul_eqv_congr
        (outwardPatternCharacterFusionNumerator_eqv_compatibleSupport
          fineCoupling (Q'.le_of_lt hfine)
          outwardFineQueries pattern)
        (outwardCharacterFusionPartition_eqv_compatibleSupport
          (unitCubeBlockCoupling fineCoupling)
          (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)))))

theorem outwardFineCoarseLocalDenominator_eqv_compatibleSupport
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    outwardFineCoarseLocalCharacterDenominator
        fineCoupling pattern ≈
      outwardFineCoarseCompatibleSupportDenominator
        fineCoupling pattern := by
  unfold outwardFineCoarseLocalCharacterDenominator
    outwardFineCoarseCompatibleSupportDenominator
    outwardFinePatternCharacterFusionNumerator
    outwardCoarseCharacterFusionPartition
    outwardFineCompatibleSupportPatternNumerator
    outwardCoarseCompatibleSupportPartition
  exact mul_eqv_congr
    (outwardPatternCharacterFusionNumerator_eqv_compatibleSupport
      fineCoupling (Q'.le_of_lt hfine) outwardFineQueries pattern)
    (outwardCharacterFusionPartition_eqv_compatibleSupport
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)))

theorem outwardFineCoarseCompatibleSupportDenominator_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < outwardFineCoarseCompatibleSupportDenominator
      fineCoupling pattern := by
  exact Q'.pos_of_lt_of_le
    (outwardFineCoarseLocalCharacterDenominator_pos
      fineCoupling hfine pattern)
    (Q'.le_of_eqv
      (outwardFineCoarseLocalDenominator_eqv_compatibleSupport
        fineCoupling hfine pattern))

/-! ## 4. The support-gas residual and its transfer to the physical defect -/

def OutwardFineCoarseCompatibleSupportCrossDifferenceBound
    (fineCoupling bound : Q') : Prop :=
  ∀ pattern,
    absQ (outwardFineCoarseCompatibleSupportCrossDifference
        fineCoupling pattern) ≤
      bound * outwardFineCoarseCompatibleSupportDenominator
        fineCoupling pattern

theorem outwardFineCoarseLocalCrossDifferenceBound_of_compatibleSupport
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (bound : Q')
    (hcross : OutwardFineCoarseCompatibleSupportCrossDifferenceBound
      fineCoupling bound) :
    OutwardFineCoarseLocalCrossDifferenceBound
      fineCoupling bound := by
  intro pattern
  have hsupport := hcross pattern
  have hdiff :=
    outwardFineCoarseLocalCrossDifference_eqv_compatibleSupport
      fineCoupling hfine pattern
  have hdenominator :=
    outwardFineCoarseLocalDenominator_eqv_compatibleSupport
      fineCoupling hfine pattern
  have habs := absQ_eqv_congr hdiff
  have hscaledDenominator :=
    Q'.mul_eqv_congr_left bound _ _ hdenominator
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv habs) hsupport)
    (Q'.ge_of_eqv hscaledDenominator)

theorem outwardFineCoarseRetuneDefect_le_of_compatibleSupport
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (bound : Q')
    (hcross : OutwardFineCoarseCompatibleSupportCrossDifferenceBound
      fineCoupling bound) :
    threeBlockPatternRetuneDefect
        (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw_patternMass_pos fineCoupling hfine) ≤
      bound :=
  outwardFineCoarseRetuneDefect_le_of_localCharacterCrossDifference
    fineCoupling hfine bound
    (outwardFineCoarseLocalCrossDifferenceBound_of_compatibleSupport
      fineCoupling hfine bound hcross)

#print axioms normalizedPhysicalPatternEvent_eq_liftedFamilyPatternEvent
#print axioms outwardPatternCharacterFusionNumerator_eqv_compatibleSupport
#print axioms outwardCharacterFusionPartition_eqv_compatibleSupport
#print axioms outwardFineCoarseLocalCrossDifference_eqv_compatibleSupport
#print axioms outwardFineCoarseLocalDenominator_eqv_compatibleSupport
#print axioms outwardFineCoarseCompatibleSupportDenominator_pos
#print axioms outwardFineCoarseLocalCrossDifferenceBound_of_compatibleSupport
#print axioms outwardFineCoarseRetuneDefect_le_of_compatibleSupport

end YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
