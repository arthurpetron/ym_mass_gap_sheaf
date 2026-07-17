/-
# A positive six-face witness for outward query disagreement

The elementary closed cube immediately outside the positive x face is in the
production fine-query `100` cell, but it contains none of the three production
coarse query faces.  Hence its singleton compatible family lies in the exact
fine/coarse disagreement event for pattern `100`.  Its complete derived
fundamental activity is a lower bound for that spin-summed event numerator at
every nonnegative coupling, and is strictly positive at every positive
coupling.

This is a finite local obstruction fence.  It does not by itself quantify the
disagreement relative to the full fine-pattern numerator.
-/

import YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
import YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor

namespace YMGap.Continuum.Z4OutwardChildQueryDisagreementWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. The same closed cube is coarse-pattern `000` -/

theorem outwardXQueryFace_not_mem_smallLift :
    outwardXQueryFace ∉ outwardXFineSmallLiftSurface := by
  simp [outwardXQueryFace, outwardXFineSmallLiftSurface,
    outwardXFineSmallLiftOffset, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, doubleAxisOffset, xAxisOffset,
    zeroAxisOffset, cubeFace]

theorem outwardXFineSmallLift_coarseX_false :
    physicalComponentSubsupportEvent 6 outwardXQuery
        (componentLabel outwardXFineSmallLiftRoot) = false := by
  exact componentLabel_subsupportEvent_false
    outwardXFineSmallLiftRoot_mem_canonical
    (coarseFaceQuerySupport_not_subset_geometricRoot
      zeroAxisOffset (Or.inl rfl) .rightYZ
      outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      outwardXQueryFace_not_mem_smallLift)

theorem outwardXFineSmallLift_coarseXFamilyEvent_false :
    familyContainsComponentSubsupportB outwardXQuery
      [outwardXFineSmallLiftRoot] = false := by
  have hx : componentContainsSubsupportB outwardXQuery
      outwardXFineSmallLiftRoot = false := by
    rw [← componentLabel_subsupportEvent_eq_componentContains
      outwardXFineSmallLiftRoot_mem_canonical]
    exact outwardXFineSmallLift_coarseX_false
  unfold familyContainsComponentSubsupportB
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  exact hx

/-! ## 2. Exact disagreement membership -/

theorem outwardPattern100Event_false_of_left_false
    (left shared right : List Nat)
    (family : List (List Nat))
    (hleft : familyContainsComponentSubsupportB left family = false) :
    outwardComponentSubsupportFamilyPatternEvent (left, shared, right)
      (true, false, false) family = false := by
  unfold outwardComponentSubsupportFamilyPatternEvent
    outwardComponentSubsupportFamilyPattern componentSubsupportQueryLeft
    componentSubsupportQueryShared componentSubsupportQueryRight
  rw [hleft]
  rfl

theorem outwardCoarseQueries_eq_explicit :
    outwardCoarseQueries =
      (outwardXQuery, outwardYQuery, outwardZQuery) := by
  unfold outwardCoarseQueries
  exact Eq.refl _

theorem outwardXFineSmallLift_coarsePattern100Event_false :
    outwardComponentSubsupportFamilyPatternEvent outwardCoarseQueries
        (true, false, false) [outwardXFineSmallLiftRoot] = false := by
  rw [outwardCoarseQueries_eq_explicit]
  exact outwardPattern100Event_false_of_left_false
    outwardXQuery outwardYQuery outwardZQuery
    [outwardXFineSmallLiftRoot]
    outwardXFineSmallLift_coarseXFamilyEvent_false

theorem supportEventDisagreement_true_of_false_true {A : Type}
    (first second : A → Bool) (item : A)
    (hfirst : first item = false) (hsecond : second item = true) :
    supportEventDisagreement first second item = true := by
  unfold supportEventDisagreement
  rw [hfirst, hsecond]
  rfl

theorem outwardXFineSmallLift_pattern100_disagreement_true :
    supportEventDisagreement
        (outwardComponentSubsupportFamilyPatternEvent
          outwardCoarseQueries (true, false, false))
        (outwardComponentSubsupportFamilyPatternEvent
          outwardFineQueries (true, false, false))
        [outwardXFineSmallLiftRoot] = true := by
  exact supportEventDisagreement_true_of_false_true
    (outwardComponentSubsupportFamilyPatternEvent
      outwardCoarseQueries (true, false, false))
    (outwardComponentSubsupportFamilyPatternEvent
      outwardFineQueries (true, false, false))
    [outwardXFineSmallLiftRoot]
    outwardXFineSmallLift_coarsePattern100Event_false
    outwardXFineSmallLift_familyPatternEvent_100

theorem outwardXFineSmallLift_singleton_mem_pattern100_disagreement :
    [outwardXFineSmallLiftRoot] ∈
      (canonicalCompatibleAmbientFamilies 6).filter
        (supportEventDisagreement
          (outwardComponentSubsupportFamilyPatternEvent
            outwardCoarseQueries (true, false, false))
          (outwardComponentSubsupportFamilyPatternEvent
            outwardFineQueries (true, false, false))) :=
  List.mem_filter.mpr
    ⟨outwardXFineSmallLift_singleton_mem_compatible,
      outwardXFineSmallLift_pattern100_disagreement_true⟩

/-! ## 3. Positive derived contribution to the spin-summed numerator -/

theorem outwardXFineSmallLift_activity_le_pattern100_disagreementNumerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling) :
    canonicalSurfaceActivity coupling 6 outwardXFineSmallLiftRoot ≤
      outwardFineCoarseGeometryDisagreementNumerator coupling
        (true, false, false) := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  have hrootSupport :=
    canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      hcoupling (cutoff := 1) (n := 6) (by decide) hsupport
  have hsupportFamily :
      couplingParametricKSupportActivity coupling 1 6
          outwardXFineSmallLiftRoot ≤
        couplingParametricKSupportFamilyActivity coupling 1 6
          [outwardXFineSmallLiftRoot] := by
    exact Q'.ge_of_eqv
      (Q'.mul_one_eqv
        (couplingParametricKSupportActivity coupling 1 6
          outwardXFineSmallLiftRoot))
  have hmember := listQSum_member_le
    (couplingParametricKSupportFamilyActivity coupling 1 6)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling 1 6)
    ((canonicalCompatibleAmbientFamilies 6).filter
      (supportEventDisagreement
        (outwardComponentSubsupportFamilyPatternEvent
          outwardCoarseQueries (true, false, false))
        (outwardComponentSubsupportFamilyPatternEvent
          outwardFineQueries (true, false, false))))
    outwardXFineSmallLift_singleton_mem_pattern100_disagreement
  unfold outwardFineCoarseGeometryDisagreementNumerator
    couplingParametricKCompatibleSupportEventNumerator
  exact Q'.le_trans' _ _ _ hrootSupport
    (Q'.le_trans' _ _ _ hsupportFamily hmember)

theorem outwardFineCoarseGeometryDisagreementNumerator_pattern100_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < outwardFineCoarseGeometryDisagreementNumerator coupling
      (true, false, false) :=
  Q'.pos_of_lt_of_le
    (outwardXFineSmallLiftRoot_activity_pos hcoupling)
    (outwardXFineSmallLift_activity_le_pattern100_disagreementNumerator
      (Q'.le_of_lt hcoupling))

#print axioms outwardXFineSmallLift_coarsePattern100Event_false
#print axioms outwardXFineSmallLift_pattern100_disagreement_true
#print axioms outwardXFineSmallLift_activity_le_pattern100_disagreementNumerator
#print axioms outwardFineCoarseGeometryDisagreementNumerator_pattern100_pos

end YMGap.Continuum.Z4OutwardChildQueryDisagreementWitness
