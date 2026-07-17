/-
# Coupling drift versus query-geometry drift

The compatible support-gas cross-difference mixes two distinct effects.  We
insert the coarse query evaluated at the fine coupling as an exact middle
term.  This splits the residual into

* coupling drift with the query held fixed, and
* coarse/fine query-geometry drift with the coupling held fixed.

The split and its relative triangle bound are division-free exact-rational
identities.  Neither component estimate is assumed here.
-/

import YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference

namespace YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem add_sub_cancel_middle (a middle c : Q') :
    a + -c ≈ (a + -middle) + (middle + -c) := by
  have hright :
      (a + -middle) + (middle + -c) ≈ a + -c := by
    refine Q'.eqv_trans _
      (a + ((-middle) + (middle + -c))) _
      (Q'.add_assoc_eqv a (-middle) (middle + -c)) ?_
    refine Q'.add_eqv_congr_left a _ _ ?_
    refine Q'.eqv_trans _ (((-middle) + middle) + -c) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle (-c))) ?_
    refine Q'.eqv_trans _ (0 + -c) _
      (Q'.add_eqv_congr_right ((-middle) + middle) 0 (-c)
        (Q'.neg_add_self_eqv middle)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-c))
  exact Q'.eqv_symm hright

def outwardFineCouplingCoarseQueryNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCompatibleSupportPatternNumerator
    fineCoupling outwardCoarseQueries pattern

/-- Change `β` to `2 β^4`, holding the coarse pattern event fixed. -/
def outwardFineCoarseSupportCouplingCrossDifference
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCoarseCompatibleSupportPatternNumerator
        fineCoupling pattern *
      outwardFineCompatibleSupportPartition fineCoupling +
    -(outwardFineCouplingCoarseQueryNumerator fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling)

/-- Change the coarse query triple to the fine query triple at fixed `β`. -/
def outwardFineCoarseSupportGeometryCrossDifference
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardFineCouplingCoarseQueryNumerator fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling +
    -(outwardFineCompatibleSupportPatternNumerator
        fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling)

theorem outwardFineCoarseCompatibleSupportCrossDifference_split
    (fineCoupling : Q') (pattern : ThreeBlockPattern) :
    outwardFineCoarseCompatibleSupportCrossDifference
        fineCoupling pattern ≈
      outwardFineCoarseSupportCouplingCrossDifference
          fineCoupling pattern +
        outwardFineCoarseSupportGeometryCrossDifference
          fineCoupling pattern := by
  unfold outwardFineCoarseCompatibleSupportCrossDifference
    outwardFineCoarseSupportCouplingCrossDifference
    outwardFineCoarseSupportGeometryCrossDifference
  exact add_sub_cancel_middle
    (outwardCoarseCompatibleSupportPatternNumerator
        fineCoupling pattern *
      outwardFineCompatibleSupportPartition fineCoupling)
    (outwardFineCouplingCoarseQueryNumerator fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling)
    (outwardFineCompatibleSupportPatternNumerator fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling)

def OutwardFineCoarseSupportCouplingCrossDifferenceBound
    (fineCoupling bound : Q') : Prop :=
  ∀ pattern,
    absQ (outwardFineCoarseSupportCouplingCrossDifference
        fineCoupling pattern) ≤
      bound * outwardFineCoarseCompatibleSupportDenominator
        fineCoupling pattern

def OutwardFineCoarseSupportGeometryCrossDifferenceBound
    (fineCoupling bound : Q') : Prop :=
  ∀ pattern,
    absQ (outwardFineCoarseSupportGeometryCrossDifference
        fineCoupling pattern) ≤
      bound * outwardFineCoarseCompatibleSupportDenominator
        fineCoupling pattern

theorem outwardFineCoarseCompatibleSupportCrossDifferenceBound_of_split
    (fineCoupling couplingBound geometryBound : Q')
    (hcoupling : OutwardFineCoarseSupportCouplingCrossDifferenceBound
      fineCoupling couplingBound)
    (hgeometry : OutwardFineCoarseSupportGeometryCrossDifferenceBound
      fineCoupling geometryBound) :
    OutwardFineCoarseCompatibleSupportCrossDifferenceBound
      fineCoupling (couplingBound + geometryBound) := by
  intro pattern
  let denominator :=
    outwardFineCoarseCompatibleSupportDenominator fineCoupling pattern
  have hsplit :=
    outwardFineCoarseCompatibleSupportCrossDifference_split
      fineCoupling pattern
  have habs := absQ_eqv_congr hsplit
  have htriangle := absQ_add_le
    (outwardFineCoarseSupportCouplingCrossDifference fineCoupling pattern)
    (outwardFineCoarseSupportGeometryCrossDifference fineCoupling pattern)
  have hsum := Q'.add_le_add
    (hcoupling pattern) (hgeometry pattern)
  have hdistribute :
      couplingBound * denominator + geometryBound * denominator ≈
        (couplingBound + geometryBound) * denominator :=
    Q'.eqv_symm
      (Q'.add_mul_eqv couplingBound geometryBound denominator)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv habs) htriangle)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hdistribute))

theorem outwardFineCoarseRetuneDefect_le_of_supportErrorSplit
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (couplingBound geometryBound : Q')
    (hcoupling : OutwardFineCoarseSupportCouplingCrossDifferenceBound
      fineCoupling couplingBound)
    (hgeometry : OutwardFineCoarseSupportGeometryCrossDifferenceBound
      fineCoupling geometryBound) :
    threeBlockPatternRetuneDefect
        (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw_patternMass_pos fineCoupling hfine) ≤
      couplingBound + geometryBound :=
  outwardFineCoarseRetuneDefect_le_of_compatibleSupport
    fineCoupling hfine (couplingBound + geometryBound)
    (outwardFineCoarseCompatibleSupportCrossDifferenceBound_of_split
      fineCoupling couplingBound geometryBound hcoupling hgeometry)

#print axioms outwardFineCoarseCompatibleSupportCrossDifference_split
#print axioms outwardFineCoarseCompatibleSupportCrossDifferenceBound_of_split
#print axioms outwardFineCoarseRetuneDefect_le_of_supportErrorSplit

end YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit
