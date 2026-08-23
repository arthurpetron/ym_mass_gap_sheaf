/-
# A support obstruction to the BF4 vacuum-sector projective shortcut

At cutoff two, the physical vacuum half-amplitude row is an exact delta on
the vacuum boundary.  The vacuum-connected cube row has a strictly positive
entry at an explicit non-vacuum boundary.  Consequently no finite
projective spread can satisfy the four-index half-amplitude cross-ratio
inequality on the canonical vacuum sector and the full physical boundary
carrier.

This rules out the projective producer at cutoff two.  It does not by itself
rule out a cofinal family that skips cutoff two; a cofinal obstruction needs
the same support witness at arbitrary large cutoffs.  The exact posterior
`L1` route remains valid and must use a support-compatible estimate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow

namespace YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_left_pos_of_mul_pos
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  exact (Int.not_lt_of_ge
    (Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum))
    hproductNum

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  exact (Int.not_lt_of_ge
    (Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos))
    hproductNum

/-! ## 1. The explicit incompatible support rectangle -/

/-- The cutoff-two cube half-amplitude is strictly positive at the explicit
single-face leakage boundary. -/
theorem centralHalfAmplitude_cutoffTwo_cube_singleFaceBoundary_pos :
    (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState cutoffTwoCubeSingleFaceBoundary := by
  have hcube : centralLowerCubeState ∈ centralHalfStates 2 0 :=
    centralLowerCubeState_mem_centralHalfStates (by decide)
  have htarget : cutoffTwoSingleFaceTwoState ∈ centralHalfStates 2 0 :=
    cutoffTwoSingleFaceTwoState_mem_halfStates
  have htermEq := centralPhysicalTerm_eq_gram_integrand
    cutoffTwoHalfCoupling hcube
    cutoffTwoCubeSingleFaceBoundary_mem_channels htarget
  have hintegrand : (0 : Q') <
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0
          cutoffTwoCubeSingleFaceBoundary *
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            centralLowerCubeState cutoffTwoCubeSingleFaceBoundary *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            cutoffTwoSingleFaceTwoState
            cutoffTwoCubeSingleFaceBoundary) :=
    Q'.pos_of_lt_of_le cutoffTwoCubeSingleFacePhysicalTerm_pos
      (Q'.ge_of_eqv htermEq)
  have hpair : (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState cutoffTwoCubeSingleFaceBoundary *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          cutoffTwoSingleFaceTwoState
          cutoffTwoCubeSingleFaceBoundary :=
    q_right_pos_of_mul_pos
      (centralBoundaryWeight_nonnegative_on
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        cutoffTwoCubeSingleFaceBoundary
        cutoffTwoCubeSingleFaceBoundary_mem_channels)
      hintegrand
  exact q_left_pos_of_mul_pos
    (centralHalfAmplitude_nonnegative
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 cutoffTwoSingleFaceTwoState
      cutoffTwoCubeSingleFaceBoundary)
    hpair

/-- The cutoff-two vacuum row vanishes at that same explicit non-vacuum
boundary. -/
theorem centralHalfAmplitude_cutoffTwo_vacuum_singleFaceBoundary_eqv_zero :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling cutoffTwoCubeSingleFaceBoundary ≈ 0 := by
  apply centralHalfAmplitude_cutoffTwo_vacuum_eqv_zero_of_fixed_nonzero
    cutoffTwoCubeSingleFaceBoundary 2
  · decide
  · unfold cutoffTwoCubeSingleFaceBoundary
    decide
  · unfold cutoffTwoCubeSingleFaceBoundary
    decide

/-- The opposite corner, the vacuum amplitude at the vacuum boundary, is
strictly positive. -/
theorem centralHalfAmplitude_cutoffTwo_vacuum_vacuum_pos :
    (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling zeroEdgeLabelling := by
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (centralHalfAmplitude_vacuum_eqv_one
        cutoffTwoHalfCoupling 2 0))

/-! ## 2. No finite projective spread exists on the canonical sector -/

/-- **Support obstruction.**  No rational spread, regardless of size, can
satisfy the half-amplitude cross-ratio condition on the cutoff-two canonical
vacuum sector and all physical boundary channels. -/
theorem no_cutoffTwo_vacuumSector_halfAmplitudeCrossRatio
    (spread : Q') :
    ¬ (∀ left,
        left ∈ centralPhysicalFiniteVacuumSectorIndices
            cutoffTwoHalfCoupling (by decide) 2 0 →
          ∀ right,
            right ∈ centralPhysicalFiniteVacuumSectorIndices
                cutoffTwoHalfCoupling (by decide) 2 0 →
              ∀ first,
                first ∈ centralBoundaryChannels 2 0 →
                  ∀ second,
                    second ∈ centralBoundaryChannels 2 0 →
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                            cutoffTwoHalfCoupling (by decide) 2 0
                            left first *
                          centralPhysicalFiniteVacuumSectorGramAmplitude
                            cutoffTwoHalfCoupling (by decide) 2 0
                            right second ≤
                        (spread * spread) *
                          (centralPhysicalFiniteVacuumSectorGramAmplitude
                              cutoffTwoHalfCoupling (by decide) 2 0
                              left second *
                            centralPhysicalFiniteVacuumSectorGramAmplitude
                              cutoffTwoHalfCoupling (by decide) 2 0
                              right first)) := by
  intro hprojective
  have hcubeSector :
      centralLowerCubeState ∈ cutoffTwoCubeSectorStates := by
    have h := cutoffTwoSectorStateAt_mem (by decide : 0 < 65)
    rw [cutoffTwoSectorStateAt_zero_eq_cube] at h
    exact h
  have hcubeCanonical :
      centralLowerCubeState ∈
        centralPhysicalFiniteVacuumSectorStates
          cutoffTwoHalfCoupling (by decide) 2 0 :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff
      centralLowerCubeState).2 hcubeSector
  rcases List.mem_map.mp hcubeCanonical with
    ⟨cubeIndex, hcubeIndex, hcubeState⟩
  have hvacuumIndex :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0
  have hbound := hprojective
    cubeIndex hcubeIndex 0 hvacuumIndex
    cutoffTwoCubeSingleFaceBoundary
    cutoffTwoCubeSingleFaceBoundary_mem_channels
    zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralBoundaryChannels 2 0)
  unfold centralPhysicalFiniteVacuumSectorGramAmplitude at hbound
  rw [hcubeState,
    centralPhysicalFiniteStateAt_zero_eq_vacuum] at hbound
  have hleftPos : (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState cutoffTwoCubeSingleFaceBoundary *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling zeroEdgeLabelling :=
    Q'.mul_pos
      centralHalfAmplitude_cutoffTwo_cube_singleFaceBoundary_pos
      centralHalfAmplitude_cutoffTwo_vacuum_vacuum_pos
  have hinnerZero :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState zeroEdgeLabelling *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling cutoffTwoCubeSingleFaceBoundary ≈ 0 := by
    refine Q'.eqv_trans _
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState zeroEdgeLabelling * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        centralHalfAmplitude_cutoffTwo_vacuum_singleFaceBoundary_eqv_zero
    exact Q'.mul_zero_eqv _
  have hrightZero :
      (spread * spread) *
          (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
              centralLowerCubeState zeroEdgeLabelling *
            centralHalfAmplitude cutoffTwoHalfCoupling 2 0
              zeroEdgeLabelling cutoffTwoCubeSingleFaceBoundary) ≈ 0 := by
    refine Q'.eqv_trans _ ((spread * spread) * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (spread * spread) _ _ hinnerZero
    exact Q'.mul_zero_eqv _
  have hleftLeZero :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState cutoffTwoCubeSingleFaceBoundary *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling zeroEdgeLabelling ≤ 0 :=
    Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hrightZero)
  exact (Int.not_lt_of_ge hleftLeZero) hleftPos

end YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction.centralHalfAmplitude_cutoffTwo_cube_singleFaceBoundary_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction.centralHalfAmplitude_cutoffTwo_vacuum_singleFaceBoundary_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction.no_cutoffTwo_vacuumSector_halfAmplitudeCrossRatio
