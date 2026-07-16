/-
# Adjacent-cube set-union obstruction and cancellation carrier

Two adjacent elementary cube boundaries share one complete plaquette.  Their
ordinary set union retains that internal plaquette once and has odd link
incidence along its boundary.  The mod-two/symmetric-difference carrier
cancels the shared plaquette and is the closed ten-face boundary of a
two-by-one-by-one rectangular cell.

The distinction is load-bearing for component sub-support observables: the
ordinary union retains the interface query but is not gauge closed, whereas
the closed cancellation carrier deletes that interface face.  This module
banks both facts and derives the strictly positive activity of the closed
carrier from the general even-incidence theorem.
-/

import YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive

namespace YMGap.Continuum.Z4AdjacentCubeCancellationCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
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
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Ordinary set union fails the gauge-closure equations -/

def zeroXAxisPlainUnionSurface : List Z4Plaq :=
  (axisCubeSurface zeroAxisOffset ++
    axisCubeSurface xAxisOffset).eraseDups

def zeroXAxisInterfaceBoundaryLink : Z4Link :=
  ((1, 0, 0, 0), .x1)

theorem zeroXAxisPlainUnionSurface_length :
    zeroXAxisPlainUnionSurface.length = 11 := by
  decide

/-- One displayed edge of the retained internal face has three incident
plaquettes, rather than an admissible even number. -/
theorem zeroXAxisPlainUnion_interface_incidence_three :
    faceIncidenceCount zeroXAxisInterfaceBoundaryLink
      zeroXAxisPlainUnionSurface = 3 := by
  decide

theorem zeroXAxisPlainUnion_not_evenFaceIncidence :
    ¬ EvenFaceIncidence zeroXAxisPlainUnionSurface := by
  intro hclosed
  have heven := hclosed zeroXAxisInterfaceBoundaryLink
  rw [zeroXAxisPlainUnion_interface_incidence_three] at heven
  cases heven

/-! ## 2. Symmetric-difference cancellation gives the closed carrier -/

def zeroXAxisCancelledSurface : List Z4Plaq :=
  (axisCubeSurface zeroAxisOffset ++ axisCubeSurface xAxisOffset).filter
    (fun plaquette => decide
      ((plaquette ∈ axisCubeSurface zeroAxisOffset) !=
        (plaquette ∈ axisCubeSurface xAxisOffset)))

theorem zeroXAxisCancelledSurface_eq_literal :
    zeroXAxisCancelledSurface =
      [((0, 0, 0, 0), .p01), ((0, 0, 1, 0), .p01),
       ((0, 0, 0, 0), .p02), ((0, 1, 0, 0), .p02),
       ((0, 0, 0, 0), .p12),
       ((1, 0, 0, 0), .p01), ((1, 0, 1, 0), .p01),
       ((1, 0, 0, 0), .p02), ((1, 1, 0, 0), .p02),
       ((2, 0, 0, 0), .p12)] := by
  decide

theorem zeroXAxisCancelledSurface_length :
    zeroXAxisCancelledSurface.length = 10 := by
  rw [zeroXAxisCancelledSurface_eq_literal]
  rfl

theorem zeroXAxisCancelledSurface_nodup :
    zeroXAxisCancelledSurface.Nodup := by
  rw [zeroXAxisCancelledSurface_eq_literal]
  decide

theorem zeroXAxisCancelledSurface_evenFaceIncidence :
    EvenFaceIncidence zeroXAxisCancelledSurface := by
  intro link
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

/-! ## 3. The shared interface is exactly what cancellation removes -/

def zeroXAxisSharedInterfaceFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)

theorem zeroXAxisSharedInterfaceFace_eq :
    zeroXAxisSharedInterfaceFace = ((1, 0, 0, 0), .p12) := by
  rfl

theorem zeroXAxisSharedInterfaceFace_mem_plainUnion :
    zeroXAxisSharedInterfaceFace ∈ zeroXAxisPlainUnionSurface := by
  decide

theorem zeroXAxisSharedInterfaceFace_not_mem_cancelled :
    zeroXAxisSharedInterfaceFace ∉ zeroXAxisCancelledSurface := by
  decide

/-! ## 4. Numerical support and positive derived activity -/

def zeroXAxisCancelledRoot : List Nat :=
  geometricSupportIds 6 zeroXAxisCancelledSurface

theorem zeroXAxisCancelledSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ zeroXAxisCancelledSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rw [zeroXAxisCancelledSurface_eq_literal] at hplaquette
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports :
    zeroXAxisCancelledRoot ∈ cutoffOneFaceSupports 6 := by
  unfold zeroXAxisCancelledRoot
  exact geometricSupportIds_mem_cutoffOneFaceSupports 6 _

private theorem evenFaceIncidence_of_sameSupport
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

theorem zeroXAxisCancelledRoot_evenFaceIncidence :
    EvenFaceIncidence (geometricPolymer 6 zeroXAxisCancelledRoot) := by
  apply evenFaceIncidence_of_sameSupport
    (geometricSupportIds_sameSupport
      zeroXAxisCancelledSurface_subset_box_six)
  · exact geometricPolymer_nodup
      zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports
  · exact zeroXAxisCancelledSurface_nodup
  · exact zeroXAxisCancelledSurface_evenFaceIncidence

/-- The cancellation carrier has a derived, exact, strictly positive
character/fusion amplitude at every positive coupling. -/
theorem zeroXAxisCancelledRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      zeroXAxisCancelledRoot := by
  exact canonicalSurfaceActivity_pos_of_evenIncidence hcoupling
    zeroXAxisCancelledRoot_mem_cutoffOneFaceSupports
    zeroXAxisCancelledRoot_evenFaceIncidence

#print axioms zeroXAxisPlainUnion_interface_incidence_three
#print axioms zeroXAxisPlainUnion_not_evenFaceIncidence
#print axioms zeroXAxisCancelledSurface_eq_literal
#print axioms zeroXAxisCancelledSurface_evenFaceIncidence
#print axioms zeroXAxisSharedInterfaceFace_mem_plainUnion
#print axioms zeroXAxisSharedInterfaceFace_not_mem_cancelled
#print axioms zeroXAxisCancelledRoot_evenFaceIncidence
#print axioms zeroXAxisCancelledRoot_activity_pos

end YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
