/-
# Exact activity of the adjacent-cube cancellation carrier

The ordinary union of two adjacent cube boundaries is not gauge closed: the
shared interface face survives once and its boundary links have odd
incidence.  Symmetric-difference cancellation removes that face and leaves
the ten-face boundary of a two-by-one-by-one rectangular cell.

This module strengthens the existing parity certificate.  Every touched link
of the cancelled carrier has incidence exactly two, so every cutoff-one Haar
multiplicity is one.  Consequently its full canonical activity is exactly the
tenth power of the fundamental face coefficient.  This is the first exact
shared-link correction: gluing two six-face cube carriers cancels two copies
of the common face and changes the independent twelve-face power to ten.
-/

import YMGap.Continuum.Z4AxisCubeSixFaceActivity

namespace YMGap.Continuum.Z4AdjacentCubeCancellationActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. No touched link carries more than two cancelled faces -/

theorem zeroXAxisCancelledSurface_faceIncidenceCount_le_two
    (link : Z4Link) :
    faceIncidenceCount link zeroXAxisCancelledSurface ≤ 2 := by
  rw [zeroXAxisCancelledSurface_eq_literal]
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [faceIncidenceCount, edgesOf, dirsOf, addE, Prod.mk.injEq]
  all_goals
    by_cases ha : a ≤ 2
    · by_cases hb : b ≤ 1
      · by_cases hc : c ≤ 1
        · by_cases hd : d = 0
          · subst d
            have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
            have hbCases : b = 0 ∨ b = 1 := by omega
            have hcCases : c = 0 ∨ c = 1 := by omega
            rcases haCases with rfl | rfl | rfl <;>
              rcases hbCases with rfl | rfl <;>
              rcases hcCases with rfl | rfl <;> decide
          · have hd0 : d ≠ 0 := hd
            simp [hd0]
        · have hc0 : c ≠ 0 := by omega
          have hc1 : c ≠ 1 := by omega
          simp [hc0, hc1]
      · have hb0 : b ≠ 0 := by omega
        have hb1 : b ≠ 1 := by omega
        simp [hb0, hb1]
    · have ha0 : a ≠ 0 := by omega
      have ha1 : a ≠ 1 := by omega
      have ha2 : a ≠ 2 := by omega
      simp [ha0, ha1, ha2]

theorem zeroXAxisCancelledSurface_incidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks zeroXAxisCancelledSurface) :
    (geometricIncidentPlaquettes zeroXAxisCancelledSurface link).length = 2 := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hlink
  have hmem :
      plaquette ∈
        geometricIncidentPlaquettes zeroXAxisCancelledSurface link := by
    simp [geometricIncidentPlaquettes, hplaquette, hedge]
  have hpositive :
      0 <
        (geometricIncidentPlaquettes
          zeroXAxisCancelledSurface link).length :=
    List.length_pos_of_mem hmem
  have hle :
      (geometricIncidentPlaquettes
        zeroXAxisCancelledSurface link).length ≤ 2 := by
    rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
    exact zeroXAxisCancelledSurface_faceIncidenceCount_le_two link
  have heven :
      (geometricIncidentPlaquettes
          zeroXAxisCancelledSurface link).length % 2 = 0 := by
    rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
    exact zeroXAxisCancelledSurface_evenFaceIncidence link
  omega

/-! ## 2. Transfer the ten-face/two-incidence certificate to the root -/

theorem zeroXAxisCancelledRoot_length_eq_ten :
    zeroXAxisCancelledRoot.length = 10 := by
  have hsame :=
    geometricSupportIds_sameSupport
      zeroXAxisCancelledSurface_subset_box_six
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricPolymer_nodup
      zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports)
    zeroXAxisCancelledSurface_nodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans zeroXAxisCancelledSurface_length

theorem zeroXAxisCancelledRoot_incidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 6
      (componentLabel zeroXAxisCancelledRoot)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 zeroXAxisCancelledRoot) link).length = 2 := by
  have hsame :=
    geometricSupportIds_sameSupport
      zeroXAxisCancelledSurface_subset_box_six
  have hsurfaceTouched :
      link ∈ geometricTouchedLinks zeroXAxisCancelledSurface :=
    touchedSurface_of_sameSupport
      zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports hsame hlink
  have hincidentSame :=
    geometricIncidentPlaquettes_sameSupport hsame link
  have hlength := sameSupport_length_eq_of_nodup hincidentSame
    (geometricIncidentPlaquettes_nodup
      zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports link)
    (by
      unfold geometricIncidentPlaquettes
      exact List.filter_sublist.nodup
        zeroXAxisCancelledSurface_nodup)
  exact hlength.trans
    (zeroXAxisCancelledSurface_incidentPlaquettes_length_eq_two
      hsurfaceTouched)

/-! ## 3. Exact overlapping-carrier activity -/

/-- The shared-interface cancellation carrier has exactly ten fundamental
face coefficients and no residual cutoff-one link multiplicity. -/
theorem zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6 zeroXAxisCancelledRoot ≈
      (coeffW coupling 1) ^ 10 := by
  have hactivity :=
    canonicalSurfaceActivity_eqv_pow_length_of_incidence_two coupling
      zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports
      zeroXAxisCancelledRoot_incidentPlaquettes_length_eq_two
  rw [zeroXAxisCancelledRoot_length_eq_ten] at hactivity
  exact hactivity

/-- Algebraic form of the shared-face correction.  Relative to the
twelve-face product of two independent six-face cube activities, the glued
carrier removes exactly two powers of the common face coefficient. -/
theorem independent_cube_power_eqv_shared_face_square_mul_cancelled
    (coupling : Q') :
    (coeffW coupling 1) ^ 12 ≈
      (coeffW coupling 1) ^ 2 *
        canonicalSurfaceActivity coupling 6 zeroXAxisCancelledRoot := by
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 2 *
      (coeffW coupling 1) ^ 10) _
    (by
      simpa only [show 12 = 2 + 10 by omega] using
        Q'.pow_add_eqv (coeffW coupling 1) 2 10)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten
          coupling)))

#print axioms zeroXAxisCancelledSurface_faceIncidenceCount_le_two
#print axioms zeroXAxisCancelledSurface_incidentPlaquettes_length_eq_two
#print axioms zeroXAxisCancelledRoot_length_eq_ten
#print axioms zeroXAxisCancelledRoot_incidentPlaquettes_length_eq_two
#print axioms zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten
#print axioms independent_cube_power_eqv_shared_face_square_mul_cancelled

end YMGap.Continuum.Z4AdjacentCubeCancellationActivity
