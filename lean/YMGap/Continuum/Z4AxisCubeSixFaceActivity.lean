/-
# Exact cutoff-one activity of a translated unit-cube boundary

Every positive-coordinate translate of the six-face unit cube has exactly two
incident excited plaquettes at each touched link.  Hence every cutoff-one Haar
multiplicity is one and the complete canonical activity is the sixth power of
the fundamental face coefficient.  This supplies exact, rather than visual,
weight matching for signed cube-path cancellations.
-/

import YMGap.Continuum.Z4CanonicalPinnedLayerQuadraticScaling
import YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier

namespace YMGap.Continuum.Z4AxisCubeSixFaceActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

theorem axisCubeSurface_incidentPlaquettes_length_eq_two
    (offset : AxisOffset) {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks (axisCubeSurface offset)) :
    (geometricIncidentPlaquettes (axisCubeSurface offset) link).length = 2 := by
  obtain ⟨shiftedPlaquette, hshiftedPlaquette, hshiftedLink⟩ :=
    mem_geometricTouchedLinks.mp hlink
  unfold axisCubeSurface at hshiftedPlaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, rfl⟩ :=
    List.mem_map.mp hshiftedPlaquette
  rw [edgesOf_axisShiftPlaquette] at hshiftedLink
  obtain ⟨sourceLink, hsourceLink, rfl⟩ :=
    List.mem_map.mp hshiftedLink
  have hsourceTouched :
      sourceLink ∈ geometricTouchedLinks unitCubeSurface :=
    mem_geometricTouchedLinks.mpr
      ⟨sourcePlaquette, hsourcePlaquette, hsourceLink⟩
  rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount,
    ← occurrenceCount_flatMap_edgesOf]
  unfold axisCubeSurface
  rw [flatMap_edgesOf_axisShiftPlaquette,
    occurrenceCount_axisShiftLink_image,
    occurrenceCount_flatMap_edgesOf,
    ← geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
  exact unitCube_geometricIncidentPlaquettes_length_eq_two hsourceTouched

theorem axisCubeSurface_nodup (offset : AxisOffset) :
    (axisCubeSurface offset).Nodup := by
  unfold axisCubeSurface
  exact nodup_map_of_injOn
    (axisShiftPlaquette offset) unitCubeSurface unitCubeSurface_nodup
    (fun _ _ _ _ heq => axisShiftPlaquette_injective offset heq)

theorem axisCubeSurface_length (offset : AxisOffset) :
    (axisCubeSurface offset).length = 6 := by
  simp [axisCubeSurface, unitCubeSurface]

theorem touchedSurface_of_sameSupport
    {n : Nat} {root : List Nat} {surface : List Z4Plaq}
    (hsupport : root ∈ cutoffOneFaceSupports n)
    (hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n root) surface)
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks n (componentLabel root)) :
    link ∈ geometricTouchedLinks surface := by
  have hrootTouched : link ∈ geometricTouchedLinks
      (geometricPolymer n root) :=
    (mem_touchedPhysicalLinks_iff_geometric hsupport link).mp hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hrootTouched
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette, hsame.1 plaquette hplaquette, hboundary⟩

/-! ## Exact activity from the local two-face certificate -/

theorem geometricLinkMultiplicityFactor_eq_one_of_incidence_two
    {n : Nat} {support : List Nat} {link : Z4Link}
    (hincidence :
      (geometricIncidentPlaquettes (geometricPolymer n support) link).length = 2) :
    geometricLinkMultiplicityFactor
      (geometricPolymer n support) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [hincidence]
  rfl

private theorem geometricLinkMultiplicityProduct_eqv_one_on_of_incidence_two
    {n : Nat} {support : List Nat}
    (hincidence : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    ∀ links : List Z4Link,
      (∀ link, link ∈ links →
        link ∈ touchedPhysicalLinks n (componentLabel support)) →
      geometricLinkMultiplicityProduct
        (geometricPolymer n support) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer n support) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer n support) rest) ≈ 1
      rw [geometricLinkMultiplicityFactor_eq_one_of_incidence_two
        (hincidence (hsubset link List.mem_cons_self))]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (geometricLinkMultiplicityProduct_eqv_one_on_of_incidence_two
            hincidence rest (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem explicitLinkMultiplicityProduct_eqv_one_of_incidence_two
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hincidence : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    explicitLinkMultiplicityProduct 1 n (componentLabel support)
      (touchedIndexedLinks n (componentLabel support)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric hsupport)
    (geometricLinkMultiplicityProduct_eqv_one_on_of_incidence_two
      hincidence _ (fun _ hlink => hlink))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Every cutoff-one closed surface whose touched links have two incident
faces has activity determined solely by its number of faces. -/
theorem canonicalSurfaceActivity_eqv_pow_length_of_incidence_two
    (coupling : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hincidence : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    canonicalSurfaceActivity coupling n support ≈
      (coeffW coupling 1) ^ support.length := by
  have hface :=
    parametricPhysicalFaceFactor_componentLabel_eqv_pow coupling hsupport
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor coupling n
      (componentLabel support) *
    explicitLinkMultiplicityProduct 1 n (componentLabel support)
      (touchedIndexedLinks n (componentLabel support))) ≈
      (coeffW coupling 1) ^ support.length
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ support.length * 1) _
    (qmul_congr_local hface
      (explicitLinkMultiplicityProduct_eqv_one_of_incidence_two
        hsupport hincidence))
    (Q'.mul_one_eqv _)

/-- A support whose six faces meet every touched link in exactly two faces has
the exact cutoff-one Haar activity of a unit-cube boundary.  The statement is
abstract in the support list, so concrete roots only need supply their small
geometric incidence certificate. -/
theorem canonicalSurfaceActivity_eqv_pow_six_of_incidence_two
    (coupling : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hlength : support.length = 6)
    (hincidence : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    canonicalSurfaceActivity coupling n support ≈
      (coeffW coupling 1) ^ 6 := by
  have hface :=
    parametricPhysicalFaceFactor_componentLabel_eqv_pow coupling hsupport
  rw [hlength] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor coupling n
      (componentLabel support) *
    explicitLinkMultiplicityProduct 1 n (componentLabel support)
      (touchedIndexedLinks n (componentLabel support))) ≈
      (coeffW coupling 1) ^ 6
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6 * 1) _
    (qmul_congr_local hface
      (explicitLinkMultiplicityProduct_eqv_one_of_incidence_two
        hsupport hincidence))
    (Q'.mul_one_eqv _)

/-! ## Instantiation for the encoded translated cube root -/

theorem axisCoarseRoot_length_eq_six
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    (axisCoarseRoot offset).length = 6 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    (axisCoarseRoot_mem_canonical offset hoffset)
  have hlength := sameSupport_length_eq_of_nodup
    (axisCoarseRoot_sameSupport offset hoffset)
    (geometricPolymer_nodup hsupport)
    (axisCubeSurface_nodup offset)
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans (axisCubeSurface_length offset)

theorem axisCoarseRoot_incidentPlaquettes_length_eq_two
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 6
      (componentLabel (axisCoarseRoot offset))) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 (axisCoarseRoot offset)) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    (axisCoarseRoot_mem_canonical offset hoffset)
  have hsame := axisCoarseRoot_sameSupport offset hoffset
  have hsurfaceTouched :
      link ∈ geometricTouchedLinks (axisCubeSurface offset) :=
    touchedSurface_of_sameSupport hsupport hsame hlink
  have hincidentSame := geometricIncidentPlaquettes_sameSupport hsame link
  have hlength := sameSupport_length_eq_of_nodup hincidentSame
    (geometricIncidentPlaquettes_nodup hsupport link)
    (by
      unfold geometricIncidentPlaquettes
      exact List.filter_sublist.nodup (axisCubeSurface_nodup offset))
  exact hlength.trans
    (axisCubeSurface_incidentPlaquettes_length_eq_two offset hsurfaceTouched)

theorem axisCoarseRoot_canonicalSurfaceActivity_eqv_pow_six
    (coupling : Q') (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    canonicalSurfaceActivity coupling 6 (axisCoarseRoot offset) ≈
      (coeffW coupling 1) ^ 6 := by
  exact canonicalSurfaceActivity_eqv_pow_six_of_incidence_two coupling
    (canonicalSurfacePolymer_mem_faceSupports
      (axisCoarseRoot_mem_canonical offset hoffset))
    (axisCoarseRoot_length_eq_six offset hoffset)
    (axisCoarseRoot_incidentPlaquettes_length_eq_two offset hoffset)

#print axioms axisCubeSurface_incidentPlaquettes_length_eq_two
#print axioms touchedSurface_of_sameSupport
#print axioms explicitLinkMultiplicityProduct_eqv_one_of_incidence_two
#print axioms canonicalSurfaceActivity_eqv_pow_length_of_incidence_two
#print axioms canonicalSurfaceActivity_eqv_pow_six_of_incidence_two
#print axioms axisCoarseRoot_length_eq_six
#print axioms axisCoarseRoot_incidentPlaquettes_length_eq_two
#print axioms axisCoarseRoot_canonicalSurfaceActivity_eqv_pow_six

end YMGap.Continuum.Z4AxisCubeSixFaceActivity
