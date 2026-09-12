/-
# Every canonical vacuum-sector state has cube support and common parity

A nonzero entry of the genuine reflected kernel yields an explicit shared
nonzero half-amplitude boundary by finite search. The singleton pins and
five parity equations then show that every support edge preserves the
cube-supported common-parity family containing the vacuum. Induction on
the already-constructed canonical component paths gives the result for
every representation cutoff and every nonnegative coupling, at half extent
zero. No finite spin table is extrapolated.

Combining this containment with the literal inward-mate orbit theorem sends
each canonical-sector state to zero within K+1 potential moves. This is NOT
the converse sector classification, positivity of every potential mate,
selected-source coverage, a uniform form bound, or a continuum theorem.
-/

import YMGap.Continuum.BF4PhysicalHalfCubeSupport
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalHalfCubeSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Finite search retains the nonzero summand as data, not a Prop-level witness. -/
private def nonzeroSummand {A : Type} (value : A → Q') :
    (items : List A) → (¬ listQSum value items ≈ 0) →
      {item : A // item ∈ items ∧ ¬ value item ≈ 0}
  | [], hne => False.elim (hne (Q'.eqv_refl 0))
  | head :: tail, hne => by
      letI : Decidable (value head ≈ 0) := by unfold Q'.eqv; infer_instance
      by_cases hz : value head ≈ 0
      · have htail : ¬ listQSum value tail ≈ 0 := by
          intro ht
          exact hne (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hz ht)
            (Q'.eqv_of_eq (Q'.zero_add' 0)))
        let found := nonzeroSummand value tail htail
        exact ⟨found.val, List.mem_cons_of_mem head found.property.1, found.property.2⟩
      · exact ⟨head, List.mem_cons_self, hz⟩

private theorem mul_left_zero (a b : Q') (ha : a ≈ 0) : a * b ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv _)

private theorem mul_right_zero (a b : Q') (hb : b ≈ 0) : a * b ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hb) (Q'.mul_zero_eqv _)

/-- Concrete shared boundary for a nonzero production reflected-kernel entry. -/
def sharedBoundaryOfKernelNeZero (w : Q') (K : Nat)
    (left right : EdgeLabelling)
    (hleft : left ∈ centralHalfStates K 0) (hright : right ∈ centralHalfStates K 0)
    (hne : ¬ centralPhysicalReflectedKernel w K 0 left right ≈ 0) :
    Σ' boundary : EdgeLabelling,
      boundary ∈ centralBoundaryChannels K 0 ∧
      ¬ centralHalfAmplitude w K 0 left boundary ≈ 0 ∧
      ¬ centralHalfAmplitude w K 0 right boundary ≈ 0 := by
  let integrand := fun boundary => centralBoundaryWeight w K 0 boundary *
    (centralHalfAmplitude w K 0 left boundary * centralHalfAmplitude w K 0 right boundary)
  have hsum : ¬ listQSum integrand (centralBoundaryChannels K 0) ≈ 0 := by
    intro hz
    exact hne (Q'.eqv_trans _ _ _
      (centralPhysicalReflectedKernel_eq_weightedGram w hleft hright) hz)
  let found := nonzeroSummand integrand (centralBoundaryChannels K 0) hsum
  refine ⟨found.val, found.property.1, ?_, ?_⟩
  · intro hz
    exact found.property.2 (mul_right_zero _ _ (mul_left_zero _ _ hz))
  · intro hz
    exact found.property.2 (mul_right_zero _ _ (mul_right_zero _ _ hz))

/-- The five parity constraints are a spanning tree on the six cube faces. -/
theorem commonParity_of_edgeParity_zero (state : EdgeLabelling)
    (hzero : ∀ edge, edge ∈ cubeParityEdges → cubeEdgeParity edge state = 0) :
    ∀ face, face ∈ centralLowerCubeFaceIds → state face % 2 = state 0 % 2 := by
  have h01 : (state 0 + state 1) % 2 = 0 := hzero ⟨0, 0, 1, 2⟩ (by decide)
  have h03 : (state 0 + state 3) % 2 = 0 := hzero ⟨1, 0, 3, 4⟩ (by decide)
  have h19 : (state 1 + state 9) % 2 = 0 := hzero ⟨5, 1, 9, 11⟩ (by decide)
  have h319 : (state 3 + state 19) % 2 = 0 := hzero ⟨8, 3, 19, 23⟩ (by decide)
  have h039 : (state 0 + state 39) % 2 = 0 := hzero ⟨3, 0, 39, 40⟩ (by decide)
  intro face hface
  simp only [centralLowerCubeFaceIds, List.mem_cons, List.not_mem_nil, or_false] at hface
  rcases hface with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- A genuine nonzero OS entry preserves the vacuum's cube-support/parity class. -/
theorem kernel_preserves_cubeSupportedCommonParity (w : Q') (K : Nat)
    (left right : EdgeLabelling)
    (hleft : left ∈ centralHalfStates K 0) (hright : right ∈ centralHalfStates K 0)
    (hne : ¬ centralPhysicalReflectedKernel w K 0 left right ≈ 0)
    (hclass : CubeSupportedCommonParity left) : CubeSupportedCommonParity right := by
  let witness := sharedBoundaryOfKernelNeZero w K left right hleft hright hne
  refine ⟨halfAmplitude_zero_off_cube w K right witness.1 hright witness.2.2.2, ?_⟩
  apply commonParity_of_edgeParity_zero
  intro edge he
  have hp := sharedBoundary_cubeEdgeParity_eq w K left right witness.1 hleft hright
    witness.2.2.1 witness.2.2.2 edge he
  rw [← hp]
  have hg := cubeParityEdge_geometry edge he
  have hl := hclass.2 edge.left hg.2.1
  have hr := hclass.2 edge.right hg.2.2
  unfold cubeEdgeParity
  omega

private theorem stateAt_mem_half {w : Q'} {hw : (0 : Q') ≤ w} {K index : Nat}
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    centralPhysicalFiniteStateAt w hw K 0 index ∈ centralHalfStates K 0 :=
  (mem_centralPositiveHalfStates_iff.mp (centralPhysicalFiniteStateAt_mem_positive w hw K 0
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K 0 hindex))).1

private theorem chain_preserves_class (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {source target : Nat}
    (chain : ChainIn (centralPhysicalFiniteSupportAdjacentB w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0) source target)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hclass : CubeSupportedCommonParity (centralPhysicalFiniteStateAt w hw K 0 source)) :
    CubeSupportedCommonParity (centralPhysicalFiniteStateAt w hw K 0 target) := by
  induction chain with
  | refl _ => exact hclass
  | @step source next target hedge hnext rest ih =>
      have hp := centralPhysicalFiniteRawKernel_pos_of_supportAdjacent hsource hnext hedge
      have hne : ¬ centralPhysicalFiniteRawKernel w hw K 0 source next ≈ 0 := by
        intro hz
        exact (Int.not_lt_of_ge (Q'.le_of_eqv hz)) hp
      have hnextClass := kernel_preserves_cubeSupportedCommonParity w K
        (centralPhysicalFiniteStateAt w hw K 0 source)
        (centralPhysicalFiniteStateAt w hw K 0 next)
        (stateAt_mem_half hsource) (stateAt_mem_half hnext) hne hclass
      exact ih hnext hnextClass

/-- **All-cutoff canonical containment**, for every nonnegative coupling at
half extent zero. No converse family-admission theorem is assumed or asserted. -/
theorem vacuumSector_cubeSupportedCommonParity
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0) :
    CubeSupportedCommonParity state := by
  obtain ⟨index, hindex, hstateAt⟩ := List.mem_map.mp hstate
  have hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0
  have hchain := centralPhysicalFiniteVacuumSector_connected w hw K 0 0 index hzero hindex
  have hroot : CubeSupportedCommonParity (centralPhysicalFiniteStateAt w hw K 0 0) := by
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hfinal := chain_preserves_class w hw K hchain hzero hroot
  rw [hstateAt] at hfinal
  exact hfinal

/-- Every pair-parity XOR used by the full-carrier obstruction vanishes on
the canonical vacuum component, at every cutoff. -/
theorem vacuumSector_cubePairParity_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0)
    (left right : Nat) (hleft : left ∈ centralLowerCubeFaceIds)
    (hright : right ∈ centralLowerCubeFaceIds) :
    (state left % 2 + state right % 2) % 2 = 0 := by
  have hs := vacuumSector_cubeSupportedCommonParity w hw K hstate
  have hl := hs.2 left hleft
  have hr := hs.2 right hright
  omega

/-- The literal mate orbit reaches vacuum from every canonical sector state.
Intermediate positive kernel support and selected-source traffic remain open. -/
theorem vacuumSector_inwardOrbit_reaches_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0) :
    cubeInwardOrbit (cubeInwardRootTime K state) state = zeroEdgeLabelling := by
  apply cubeInwardOrbit_rootTime_eq_zero K state
  · obtain ⟨index, hindex, hstateAt⟩ := List.mem_map.mp hstate
    have hhalf := stateAt_mem_half hindex
    rw [hstateAt] at hhalf
    intro face hface
    have hb := (boundedEdgeLabellings_sound K (centralLowerFaceIds 0) state hhalf).1
      face (centralLowerCubeFaceIds_subset_lower face hface)
    omega
  · exact vacuumSector_cubeSupportedCommonParity w hw K hstate

end YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.sharedBoundaryOfKernelNeZero
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.commonParity_of_edgeParity_zero
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.kernel_preserves_cubeSupportedCommonParity
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.vacuumSector_cubeSupportedCommonParity
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.vacuumSector_cubePairParity_zero
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment.vacuumSector_inwardOrbit_reaches_zero
