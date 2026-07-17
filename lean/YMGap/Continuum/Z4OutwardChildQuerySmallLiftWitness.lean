/-
# A six-face witness in the outward fine-query `100` cell

The production fine observable probes only one distinguished dyadic child
of each outward coarse face.  The elementary cube immediately outside the
positive x face contains the x child and neither the y nor z child.  This
module records that exact truth-table row and shows that its singleton
canonical family contributes its complete derived activity to the `100`
event numerator.
-/

import YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
import YMGap.Continuum.Z4AxisCubeSixFaceActivity
import YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
import YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries

namespace YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact old-query truth table -/

theorem outwardXFineSmallLift_oldFinePattern_100 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXFineSmallLiftRoot) =
      (true, false, false) := by
  have hx : ∀ id, id ∈ outwardXFineQuery →
      id ∈ outwardXFineSmallLiftRoot := by
    rw [outwardXFineQuery_eq_geometric]
    exact fineFaceQuerySupport_subset_geometricRoot
      zeroAxisOffset .rightYZ .origin outwardXFineSmallLiftSurface
      (by simpa [outwardXFineQueryFace, outwardXFineRootProbeFace] using
        outwardXFineRootProbeFace_mem_smallLift)
  have hy : ¬ (∀ id, id ∈ outwardYFineQuery →
      id ∈ outwardXFineSmallLiftRoot) := by
    rw [outwardYFineQuery_eq_geometric]
    exact fineFaceQuerySupport_not_subset_geometricRoot
      zeroAxisOffset (Or.inl rfl) .backXZ .origin
      outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      (by simpa [outwardYFineQueryFace, outwardYFineRootProbeFace] using
        outwardYFineRootProbeFace_not_mem_smallLift)
  have hz : ¬ (∀ id, id ∈ outwardZFineQuery →
      id ∈ outwardXFineSmallLiftRoot) := by
    rw [outwardZFineQuery_eq_geometric]
    exact fineFaceQuerySupport_not_subset_geometricRoot
      zeroAxisOffset (Or.inl rfl) .topXY .origin
      outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      (by simpa [outwardZFineQueryFace, outwardZFineRootProbeFace] using
        outwardZFineRootProbeFace_not_mem_smallLift)
  apply outwardFinePattern_eq_of_events
  · exact componentLabel_subsupportEvent_true
      outwardXFineSmallLiftRoot_mem_canonical hx
  · exact componentLabel_subsupportEvent_false
      outwardXFineSmallLiftRoot_mem_canonical hy
  · exact componentLabel_subsupportEvent_false
      outwardXFineSmallLiftRoot_mem_canonical hz

theorem outwardXFineSmallLift_familyPattern_100 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [outwardXFineSmallLiftRoot] = (true, false, false) := by
  have hpattern := outwardXFineSmallLift_oldFinePattern_100
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    outwardXFineSmallLiftRoot_mem_canonical] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem outwardXFineSmallLift_familyPatternEvent_100 :
    outwardComponentSubsupportFamilyPatternEvent outwardFineQueries
        (true, false, false) [outwardXFineSmallLiftRoot] = true := by
  unfold outwardComponentSubsupportFamilyPatternEvent
  exact decide_eq_true outwardXFineSmallLift_familyPattern_100

/-! ## 2. The witness has strictly positive derived activity -/

theorem outwardXFineSmallLiftSurface_nodup :
    outwardXFineSmallLiftSurface.Nodup := by
  unfold outwardXFineSmallLiftSurface axisCubeSurface
  exact nodup_map_of_injOn
    (axisShiftPlaquette outwardXFineSmallLiftOffset)
    unitCubeSurface unitCubeSurface_nodup
    (fun _ _ _ _ heq =>
      axisShiftPlaquette_injective outwardXFineSmallLiftOffset heq)

theorem outwardXFineSmallLiftSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXFineSmallLiftSurface := by
  unfold outwardXFineSmallLiftSurface axisCubeSurface
  exact axisShift_evenFaceIncidence outwardXFineSmallLiftOffset
    unitCubeSurface_evenFaceIncidence

private theorem evenFaceIncidence_of_sameSupport_local
    {left right : List Z4Plaq}
    (hsame : sameSupport (L := z4Chain.toLattice) left right)
    (hleftNodup : left.Nodup) (hrightNodup : right.Nodup)
    (hrightClosed : EvenFaceIncidence right) :
    EvenFaceIncidence left := by
  intro link
  have hfiltered := geometricIncidentPlaquettes_sameSupport hsame link
  have hlength := sameSupport_length_eq_of_nodup hfiltered
    (List.filter_sublist.nodup hleftNodup)
    (List.filter_sublist.nodup hrightNodup)
  have hcount : faceIncidenceCount link left =
      faceIncidenceCount link right :=
    Eq.trans
      (geometricIncidentPlaquettes_length_eq_faceIncidenceCount
        left link).symm
      (Eq.trans hlength
        (geometricIncidentPlaquettes_length_eq_faceIncidenceCount
          right link))
  rw [hcount]
  exact hrightClosed link

theorem outwardXFineSmallLiftRoot_evenFaceIncidence :
    EvenFaceIncidence
      (geometricPolymer 6 outwardXFineSmallLiftRoot) := by
  apply evenFaceIncidence_of_sameSupport_local
    (geometricSupportIds_sameSupport
      outwardXFineSmallLiftSurface_subset_box_six)
  · exact geometricPolymer_nodup
      (canonicalSurfacePolymer_mem_faceSupports
        outwardXFineSmallLiftRoot_mem_canonical)
  · exact outwardXFineSmallLiftSurface_nodup
  · exact outwardXFineSmallLiftSurface_evenFaceIncidence

/-- The numerical root and its six-face geometric certificate have exactly
the same incidence count at every physical link, not merely the same parity. -/
theorem outwardXFineSmallLiftRoot_faceIncidenceCount_eq_surface
    (link : Z4Link) :
    faceIncidenceCount link
        (geometricPolymer 6 outwardXFineSmallLiftRoot) =
      faceIncidenceCount link outwardXFineSmallLiftSurface := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  have hsame := geometricSupportIds_sameSupport
    outwardXFineSmallLiftSurface_subset_box_six
  have hfiltered := geometricIncidentPlaquettes_sameSupport hsame link
  have hlength := sameSupport_length_eq_of_nodup hfiltered
    (List.filter_sublist.nodup (geometricPolymer_nodup hsupport))
    (List.filter_sublist.nodup outwardXFineSmallLiftSurface_nodup)
  exact Eq.trans
    (geometricIncidentPlaquettes_length_eq_faceIncidenceCount
      (geometricPolymer 6 outwardXFineSmallLiftRoot) link).symm
    (Eq.trans hlength
      (geometricIncidentPlaquettes_length_eq_faceIncidenceCount
        outwardXFineSmallLiftSurface link))

theorem outwardXFineSmallLiftRoot_length :
    outwardXFineSmallLiftRoot.length = 6 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  have hsame := geometricSupportIds_sameSupport
    outwardXFineSmallLiftSurface_subset_box_six
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricPolymer_nodup hsupport)
    outwardXFineSmallLiftSurface_nodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans outwardXFineSmallLiftSurface_length

theorem outwardXFineSmallLiftRoot_incidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 6
      (componentLabel outwardXFineSmallLiftRoot)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 outwardXFineSmallLiftRoot) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  have hsame := geometricSupportIds_sameSupport
    outwardXFineSmallLiftSurface_subset_box_six
  have hsurfaceTouched :
      link ∈ geometricTouchedLinks outwardXFineSmallLiftSurface :=
    touchedSurface_of_sameSupport hsupport hsame hlink
  rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount,
    outwardXFineSmallLiftRoot_faceIncidenceCount_eq_surface,
    ← geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
  unfold outwardXFineSmallLiftSurface
  exact axisCubeSurface_incidentPlaquettes_length_eq_two
    outwardXFineSmallLiftOffset hsurfaceTouched

/-- The complete cutoff-one Haar activity of the outward small lift is the
sixth power of the derived fundamental heat-kernel coefficient. -/
theorem outwardXFineSmallLiftRoot_activity_eqv_pow_six
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 outwardXFineSmallLiftRoot ≈
      (BondMovingStep.coeffW coupling 1) ^ 6 := by
  exact canonicalSurfaceActivity_eqv_pow_six_of_incidence_two coupling
    (canonicalSurfacePolymer_mem_faceSupports
      outwardXFineSmallLiftRoot_mem_canonical)
    outwardXFineSmallLiftRoot_length
    outwardXFineSmallLiftRoot_incidentPlaquettes_length_eq_two

theorem outwardXFineSmallLiftRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXFineSmallLiftRoot := by
  exact canonicalSurfaceActivity_pos_of_evenIncidence hcoupling
    (canonicalSurfacePolymer_mem_faceSupports
      outwardXFineSmallLiftRoot_mem_canonical)
    outwardXFineSmallLiftRoot_evenFaceIncidence

/-! ## 3. Exact singleton contribution to the canonical event numerator -/

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | _ :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type} :
    ∀ (ambient : List A) (item : A), item ∈ ambient →
      [item] ∈ sublists ambient
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rw [sublists_cons']
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _
          (singleton_mem_sublists_of_mem_local tail item htail)

theorem outwardXFineSmallLift_singleton_mem_compatible :
    [outwardXFineSmallLiftRoot] ∈
      canonicalCompatibleAmbientFamilies 6 := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers 6) outwardXFineSmallLiftRoot
      outwardXFineSmallLiftRoot_mem_canonical, rfl⟩

/- The nonnegative-coupling version avoids any hidden sign assumption in the
single-family lower bound. -/
theorem outwardXFineSmallLift_activity_le_pattern100_numerator_of_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling) :
    canonicalSurfaceActivity coupling 6 outwardXFineSmallLiftRoot ≤
      canonicalPolymerEventNumerator coupling 6
        (canonicalSurfacePolymers 6)
        (outwardComponentSubsupportFamilyPatternEvent
          outwardFineQueries (true, false, false)) := by
  have htarget : [outwardXFineSmallLiftRoot] ∈
      (canonicalCompatibleAmbientFamilies 6).filter
        (outwardComponentSubsupportFamilyPatternEvent
          outwardFineQueries (true, false, false)) :=
    List.mem_filter.mpr
      ⟨outwardXFineSmallLift_singleton_mem_compatible,
        outwardXFineSmallLift_familyPatternEvent_100⟩
  have hmember := listQSum_member_le
    (familyWeight (canonicalSurfaceActivity coupling 6))
    (familyWeight_nonnegative _
      (canonicalSurfaceActivity_nonnegative hcoupling 6))
    ((canonicalCompatibleAmbientFamilies 6).filter
      (outwardComponentSubsupportFamilyPatternEvent
        outwardFineQueries (true, false, false))) htarget
  unfold canonicalPolymerEventNumerator eventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv
      (canonicalSurfaceActivity coupling 6
        outwardXFineSmallLiftRoot))) hmember

#print axioms outwardXFineSmallLift_oldFinePattern_100
#print axioms outwardXFineSmallLift_familyPattern_100
#print axioms outwardXFineSmallLiftRoot_activity_pos
#print axioms outwardXFineSmallLiftRoot_faceIncidenceCount_eq_surface
#print axioms outwardXFineSmallLiftRoot_length
#print axioms outwardXFineSmallLiftRoot_incidentPlaquettes_length_eq_two
#print axioms outwardXFineSmallLiftRoot_activity_eqv_pow_six
#print axioms outwardXFineSmallLift_activity_le_pattern100_numerator_of_nonnegative

end YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
