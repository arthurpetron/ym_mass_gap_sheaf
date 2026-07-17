/-
# Exact equal activity of the four seven-cube cycle carriers

The four canonical roots have 28 excited faces, one four-valent touched link,
and only bivalent remaining links.  Hence their complete cutoff-one singleton
family activities are all exactly `coeffW^28 * 2`.
-/

import YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots

namespace YMGap.Continuum.Z4OutwardSevenCubeCycleActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair
open YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SingleFourIncidenceActivity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem root_surface_incidence_length_eq
    {root : List Nat} {surface : List Z4Plaq}
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 root) surface)
    (hsurfaceNodup : surface.Nodup) (link : Z4Link) :
    (geometricIncidentPlaquettes (geometricPolymer 6 root) link).length =
      (geometricIncidentPlaquettes surface link).length := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hroot
  have hincidentSame := geometricIncidentPlaquettes_sameSupport hsame link
  exact sameSupport_length_eq_of_nodup hincidentSame
    (geometricIncidentPlaquettes_nodup hsupport link)
    (List.filter_sublist.nodup hsurfaceNodup)

private theorem root_touched_of_surface_touched
    {root : List Nat} {surface : List Z4Plaq}
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 root) surface)
    {link : Z4Link} (hlink : link ∈ geometricTouchedLinks surface) :
    link ∈ touchedPhysicalLinks 6 (componentLabel root) := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hroot
  rw [mem_touchedPhysicalLinks_iff_geometric hsupport link]
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hlink
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette, hsame.2 plaquette hplaquette, hedge⟩

#print axioms root_surface_incidence_length_eq
#print axioms root_touched_of_surface_touched

/-! ## 1. Root-level incidence certificates -/

theorem sevenCube011To100Root_fourLink_mem_touched :
    sevenCube011To100FourLink ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube011To100Root) :=
  root_touched_of_surface_touched sevenCube011To100Root_mem_canonical
    sevenCube011To100Root_sameSupport
    sevenCubeCycle_fourLinks_mem_touched.1

theorem sevenCube100To000Root_fourLink_mem_touched :
    sevenCube100To000FourLink ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube100To000Root) :=
  root_touched_of_surface_touched sevenCube100To000Root_mem_canonical
    sevenCube100To000Root_sameSupport
    sevenCubeCycle_fourLinks_mem_touched.2.1

theorem sevenCube000To111Root_fourLink_mem_touched :
    sevenCube000To111FourLink ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube000To111Root) :=
  root_touched_of_surface_touched sevenCube000To111Root_mem_canonical
    sevenCube000To111Root_sameSupport
    sevenCubeCycle_fourLinks_mem_touched.2.2.1

theorem sevenCube111To011Root_fourLink_mem_touched :
    sevenCube111To011FourLink ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube111To011Root) :=
  root_touched_of_surface_touched sevenCube111To011Root_mem_canonical
    sevenCube111To011Root_sameSupport
    sevenCubeCycle_fourLinks_mem_touched.2.2.2

#print axioms sevenCube011To100Root_fourLink_mem_touched
#print axioms sevenCube100To000Root_fourLink_mem_touched
#print axioms sevenCube000To111Root_fourLink_mem_touched
#print axioms sevenCube111To011Root_fourLink_mem_touched

theorem sevenCube011To100Root_four_incidence :
    (geometricIncidentPlaquettes (geometricPolymer 6 sevenCube011To100Root)
      sevenCube011To100FourLink).length = 4 :=
  (root_surface_incidence_length_eq sevenCube011To100Root_mem_canonical
    sevenCube011To100Root_sameSupport sevenCubeCycleSurface_nodups.1
    sevenCube011To100FourLink).trans sevenCube011To100_four_incidence

theorem sevenCube100To000Root_four_incidence :
    (geometricIncidentPlaquettes (geometricPolymer 6 sevenCube100To000Root)
      sevenCube100To000FourLink).length = 4 :=
  (root_surface_incidence_length_eq sevenCube100To000Root_mem_canonical
    sevenCube100To000Root_sameSupport sevenCubeCycleSurface_nodups.2.1
    sevenCube100To000FourLink).trans sevenCube100To000_four_incidence

theorem sevenCube000To111Root_four_incidence :
    (geometricIncidentPlaquettes (geometricPolymer 6 sevenCube000To111Root)
      sevenCube000To111FourLink).length = 4 :=
  (root_surface_incidence_length_eq sevenCube000To111Root_mem_canonical
    sevenCube000To111Root_sameSupport sevenCubeCycleSurface_nodups.2.2.1
    sevenCube000To111FourLink).trans sevenCube000To111_four_incidence

theorem sevenCube111To011Root_four_incidence :
    (geometricIncidentPlaquettes (geometricPolymer 6 sevenCube111To011Root)
      sevenCube111To011FourLink).length = 4 :=
  (root_surface_incidence_length_eq sevenCube111To011Root_mem_canonical
    sevenCube111To011Root_sameSupport sevenCubeCycleSurface_nodups.2.2.2
    sevenCube111To011FourLink).trans sevenCube111To011_four_incidence

#print axioms sevenCube011To100Root_four_incidence
#print axioms sevenCube100To000Root_four_incidence
#print axioms sevenCube000To111Root_four_incidence
#print axioms sevenCube111To011Root_four_incidence

theorem sevenCube011To100Root_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube011To100Root))
    (hne : link ≠ sevenCube011To100FourLink) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 sevenCube011To100Root) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    sevenCube011To100Root_mem_canonical
  have hsurfaceTouched := touchedSurface_of_sameSupport hsupport
    sevenCube011To100Root_sameSupport hlink
  exact (root_surface_incidence_length_eq
    sevenCube011To100Root_mem_canonical sevenCube011To100Root_sameSupport
    sevenCubeCycleSurface_nodups.1 link).trans
      (sevenCube011To100_other_incidence_two hsurfaceTouched hne)

theorem sevenCube100To000Root_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube100To000Root))
    (hne : link ≠ sevenCube100To000FourLink) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 sevenCube100To000Root) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    sevenCube100To000Root_mem_canonical
  have hsurfaceTouched := touchedSurface_of_sameSupport hsupport
    sevenCube100To000Root_sameSupport hlink
  exact (root_surface_incidence_length_eq
    sevenCube100To000Root_mem_canonical sevenCube100To000Root_sameSupport
    sevenCubeCycleSurface_nodups.2.1 link).trans
      (sevenCube100To000_other_incidence_two hsurfaceTouched hne)

theorem sevenCube000To111Root_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube000To111Root))
    (hne : link ≠ sevenCube000To111FourLink) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 sevenCube000To111Root) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    sevenCube000To111Root_mem_canonical
  have hsurfaceTouched := touchedSurface_of_sameSupport hsupport
    sevenCube000To111Root_sameSupport hlink
  exact (root_surface_incidence_length_eq
    sevenCube000To111Root_mem_canonical sevenCube000To111Root_sameSupport
    sevenCubeCycleSurface_nodups.2.2.1 link).trans
      (sevenCube000To111_other_incidence_two hsurfaceTouched hne)

theorem sevenCube111To011Root_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈
      touchedPhysicalLinks 6 (componentLabel sevenCube111To011Root))
    (hne : link ≠ sevenCube111To011FourLink) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 sevenCube111To011Root) link).length = 2 := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    sevenCube111To011Root_mem_canonical
  have hsurfaceTouched := touchedSurface_of_sameSupport hsupport
    sevenCube111To011Root_sameSupport hlink
  exact (root_surface_incidence_length_eq
    sevenCube111To011Root_mem_canonical sevenCube111To011Root_sameSupport
    sevenCubeCycleSurface_nodups.2.2.2 link).trans
      (sevenCube111To011_other_incidence_two hsurfaceTouched hne)

#print axioms sevenCube011To100Root_other_incidence_two
#print axioms sevenCube100To000Root_other_incidence_two
#print axioms sevenCube000To111Root_other_incidence_two
#print axioms sevenCube111To011Root_other_incidence_two

/-! ## 2. Exact common complete singleton-family activity -/

theorem sevenCube011To100Root_canonicalActivity_eqv_common
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 sevenCube011To100Root ≈
      (coeffW coupling 1) ^ 28 * 2 := by
  have h := canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    coupling sevenCube011To100FourLink
    (canonicalSurfacePolymer_mem_faceSupports
      sevenCube011To100Root_mem_canonical)
    sevenCube011To100Root_fourLink_mem_touched
    sevenCube011To100Root_four_incidence
    sevenCube011To100Root_other_incidence_two
  rw [sevenCubeCycleRoot_lengths.1] at h
  exact h

theorem sevenCube100To000Root_canonicalActivity_eqv_common
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 sevenCube100To000Root ≈
      (coeffW coupling 1) ^ 28 * 2 := by
  have h := canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    coupling sevenCube100To000FourLink
    (canonicalSurfacePolymer_mem_faceSupports
      sevenCube100To000Root_mem_canonical)
    sevenCube100To000Root_fourLink_mem_touched
    sevenCube100To000Root_four_incidence
    sevenCube100To000Root_other_incidence_two
  rw [sevenCubeCycleRoot_lengths.2.1] at h
  exact h

theorem sevenCube000To111Root_canonicalActivity_eqv_common
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 sevenCube000To111Root ≈
      (coeffW coupling 1) ^ 28 * 2 := by
  have h := canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    coupling sevenCube000To111FourLink
    (canonicalSurfacePolymer_mem_faceSupports
      sevenCube000To111Root_mem_canonical)
    sevenCube000To111Root_fourLink_mem_touched
    sevenCube000To111Root_four_incidence
    sevenCube000To111Root_other_incidence_two
  rw [sevenCubeCycleRoot_lengths.2.2.1] at h
  exact h

theorem sevenCube111To011Root_canonicalActivity_eqv_common
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 sevenCube111To011Root ≈
      (coeffW coupling 1) ^ 28 * 2 := by
  have h := canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    coupling sevenCube111To011FourLink
    (canonicalSurfacePolymer_mem_faceSupports
      sevenCube111To011Root_mem_canonical)
    sevenCube111To011Root_fourLink_mem_touched
    sevenCube111To011Root_four_incidence
    sevenCube111To011Root_other_incidence_two
  rw [sevenCubeCycleRoot_lengths.2.2.2] at h
  exact h

private theorem singletonFamilyActivity_eqv_common
    (coupling : Q') {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hcanonical : canonicalSurfaceActivity coupling 6 root ≈
      (coeffW coupling 1) ^ 28 * 2) :
    couplingParametricKSupportFamilyActivity coupling 1 6 [root] ≈
      (coeffW coupling 1) ^ 28 * 2 := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportActivity coupling 1 6 root) _
    (Q'.mul_one_eqv _) ?_
  refine Q'.eqv_trans _ (canonicalSurfaceActivity coupling 6 root) _
    (couplingParametricKSupportActivity_one_eqv_canonical coupling
      (canonicalSurfacePolymer_mem_faceSupports hroot)) ?_
  exact hcanonical

theorem sevenCube011To100_singletonFamilyActivity_eqv_common
    (coupling : Q') :
    couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube011To100Root] ≈
      (coeffW coupling 1) ^ 28 * 2 :=
  singletonFamilyActivity_eqv_common coupling
    sevenCube011To100Root_mem_canonical
    (sevenCube011To100Root_canonicalActivity_eqv_common coupling)

theorem sevenCube100To000_singletonFamilyActivity_eqv_common
    (coupling : Q') :
    couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube100To000Root] ≈
      (coeffW coupling 1) ^ 28 * 2 :=
  singletonFamilyActivity_eqv_common coupling
    sevenCube100To000Root_mem_canonical
    (sevenCube100To000Root_canonicalActivity_eqv_common coupling)

theorem sevenCube000To111_singletonFamilyActivity_eqv_common
    (coupling : Q') :
    couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube000To111Root] ≈
      (coeffW coupling 1) ^ 28 * 2 :=
  singletonFamilyActivity_eqv_common coupling
    sevenCube000To111Root_mem_canonical
    (sevenCube000To111Root_canonicalActivity_eqv_common coupling)

theorem sevenCube111To011_singletonFamilyActivity_eqv_common
    (coupling : Q') :
    couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube111To011Root] ≈
      (coeffW coupling 1) ^ 28 * 2 :=
  singletonFamilyActivity_eqv_common coupling
    sevenCube111To011Root_mem_canonical
    (sevenCube111To011Root_canonicalActivity_eqv_common coupling)

#print axioms sevenCube011To100Root_four_incidence
#print axioms sevenCube100To000Root_other_incidence_two
#print axioms sevenCube000To111Root_canonicalActivity_eqv_common
#print axioms sevenCube111To011Root_canonicalActivity_eqv_common
#print axioms sevenCube011To100_singletonFamilyActivity_eqv_common
#print axioms sevenCube100To000_singletonFamilyActivity_eqv_common
#print axioms sevenCube000To111_singletonFamilyActivity_eqv_common
#print axioms sevenCube111To011_singletonFamilyActivity_eqv_common

end YMGap.Continuum.Z4OutwardSevenCubeCycleActivity
