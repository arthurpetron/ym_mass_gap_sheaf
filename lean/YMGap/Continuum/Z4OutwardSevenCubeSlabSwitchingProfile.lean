/-
# A one-pivot seven-cube switching surface in the corrected slab

Select the literal `011 -> 100` seven-cube boundary and place it in the
boundary-complete slab of extent five.  Its already-classified geometric
profile becomes a production statement: exactly one link carries four
fundamental faces, while every other link carries either zero or two.

Consequently every non-pivot link supplies the sparse recoupling word whose
paired higher-valence weight is exactly one.  The distinguished link supplies
a separate binary word of total four; classifying its higher-valence SU(2)
block and choosing the strand-disconnecting target remain downstream.

Constructive contract: literal finite geometry, exact natural incidence, and
the production binary-support encoding only; no choice principle, unchecked
existence claim, or unbounded heartbeat option.  The finite support expansion
uses a bounded one-million-heartbeat allowance.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
import YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. The selected literal support -/

abbrev sevenCubeSwitchSurface : List Z4Plaq :=
  sevenCube011To100Surface

abbrev sevenCubeSwitchPivot : Z4Link :=
  sevenCube011To100FourLink

theorem sevenCubeSwitchSurface_subset_slab_five :
    ∀ plaquette, plaquette ∈ sevenCubeSwitchSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 := by
  intro plaquette hplaquette
  rw [mem_boundaryCompleteSlabPlaquettes]
  constructor
  · exact sevenCube011To100Surface_subset_box_six plaquette hplaquette
  · simp only [sevenCubeSwitchSurface, sevenCube011To100Surface,
      List.mem_cons, List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem sevenCubeSwitchSurface_nodup : sevenCubeSwitchSurface.Nodup :=
  sevenCubeCycleSurface_nodups.1

/-! ## 2. Exact incidence profile -/

theorem sevenCubeSwitchPivot_faceIncidenceCount :
    faceIncidenceCount sevenCubeSwitchPivot sevenCubeSwitchSurface = 4 := by
  rw [← geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
  exact sevenCube011To100_four_incidence

private theorem faceIncidenceCount_eq_zero_of_not_touched
    (link : Z4Link) : ∀ support : List Z4Plaq,
    link ∉ geometricTouchedLinks support →
      faceIncidenceCount link support = 0
  | [], _ => rfl
  | plaquette :: rest, hnot => by
      have hhead : link ∉ edgesOf plaquette := by
        intro hedge
        exact hnot (mem_geometricTouchedLinks.mpr
          ⟨plaquette, List.mem_cons_self, hedge⟩)
      have htail : link ∉ geometricTouchedLinks rest := by
        intro hrest
        obtain ⟨face, hface, hedge⟩ := mem_geometricTouchedLinks.mp hrest
        exact hnot (mem_geometricTouchedLinks.mpr
          ⟨face, List.mem_cons_of_mem plaquette hface, hedge⟩)
      simp only [faceIncidenceCount, hhead, if_false, Nat.zero_add]
      exact faceIncidenceCount_eq_zero_of_not_touched link rest htail

theorem sevenCubeSwitch_other_faceIncidenceCount_le_two
    (link : Z4Link) (hne : link ≠ sevenCubeSwitchPivot) :
    faceIncidenceCount link sevenCubeSwitchSurface ≤ 2 := by
  by_cases htouched : link ∈ geometricTouchedLinks sevenCubeSwitchSurface
  · rw [← geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
    exact Nat.le_of_eq
      (sevenCube011To100_other_incidence_two htouched hne)
  · rw [faceIncidenceCount_eq_zero_of_not_touched link
      sevenCubeSwitchSurface htouched]
    omega

theorem sevenCubeSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence sevenCubeSwitchSurface := by
  intro link
  by_cases heq : link = sevenCubeSwitchPivot
  · subst link
    rw [sevenCubeSwitchPivot_faceIncidenceCount]
  · by_cases htouched : link ∈ geometricTouchedLinks sevenCubeSwitchSurface
    · rw [← geometricIncidentPlaquettes_length_eq_faceIncidenceCount,
        sevenCube011To100_other_incidence_two htouched heq]
    · rw [faceIncidenceCount_eq_zero_of_not_touched link
        sevenCubeSwitchSurface htouched]

/-! ## 3. Production external words -/

/-- Every non-pivot production link of the selected switching surface has a
binary external word with total zero or two. -/
theorem sevenCubeSwitch_nonpivot_sparseFundamentalWord
    (link : Z4Link) (hne : link ≠ sevenCubeSwitchPivot) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 sevenCubeSwitchSurface) link) :=
  slabBinarySupport_sparseFundamentalWord
    sevenCubeSwitchSurface_subset_slab_five
    sevenCubeSwitchSurface_nodup
    sevenCubeSwitchSurface_evenFaceIncidence link
    (sevenCubeSwitch_other_faceIncidenceCount_le_two link hne)

/-- The unique pivot word is still binary, but its exact selected-spin total
is four rather than the ordinary value two. -/
structure BinaryFourFundamentalWord
    (degree : Nat) (external : EdgeLabelling) : Prop where
  label_le_one : ∀ position, position < degree → external position ≤ 1
  total_eq_four : localExternalSpinSum degree external = 4

/-- The slab boundary contributes one additional vacuum face-coordinate at
the spatial pivot, so the production block is genuinely valence five. -/
theorem sevenCubeSwitchPivot_degree_five :
    (slabIncidentPlaqIds 5 sevenCubeSwitchPivot).length = 5 := by
  decide

/-- The corrected-slab face ordering at the pivot places the four selected
fundamental faces first and its extra vacuum face last. -/
theorem sevenCubeSwitchPivot_spinList :
    (slabIncidentPlaqIds 5 sevenCubeSwitchPivot).map
        (slabBinarySupportLabelling 5 sevenCubeSwitchSurface) =
      [1, 1, 1, 1, 0] := by
  decide

theorem sevenCubeSwitchPivot_binaryFourFundamentalWord :
    BinaryFourFundamentalWord
      (slabIncidentPlaqIds 5 sevenCubeSwitchPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 sevenCubeSwitchSurface)
        sevenCubeSwitchPivot) := by
  constructor
  · intro position hposition
    let spins :=
      (slabIncidentPlaqIds 5 sevenCubeSwitchPivot).map
        (slabBinarySupportLabelling 5 sevenCubeSwitchSurface)
    have hposition' : position < spins.length := by
      simpa only [spins, List.length_map] using hposition
    change spins.getD position 0 ≤ 1
    rw [← List.getElem_eq_getD (l := spins)
      (i := position) (h := hposition') 0]
    have hmem : spins[position] ∈ spins := List.getElem_mem hposition'
    obtain ⟨id, _, hvalue⟩ := List.mem_map.mp hmem
    rw [← hvalue]
    exact slabBinarySupportLabelling_le_one 5 sevenCubeSwitchSurface id
  · unfold slabLinkExternalSpins
    rw [slabBinarySupport_localExternalSpinSum
      sevenCubeSwitchSurface_subset_slab_five
      sevenCubeSwitchSurface_nodup sevenCubeSwitchPivot]
    exact sevenCubeSwitchPivot_faceIncidenceCount

end YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile

#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitchSurface_subset_slab_five
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitch_other_faceIncidenceCount_le_two
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitchSurface_evenFaceIncidence
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitch_nonpivot_sparseFundamentalWord
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitchPivot_degree_five
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitchPivot_spinList
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile.sevenCubeSwitchPivot_binaryFourFundamentalWord
