/-
# The explicit spin-two cube leakage state at cutoff two

The exact scout identifies the positive mass outside the vacuum and
fundamental cube with the same six-face cube carrying doubled-spin label two.
This file rechecks that proposal directly from the production face and link
definitions.  The state is retained, differs from both earlier states, has
exact vacuum-column amplitude `729 / 2^48`, and gives a strictly positive
genuine physical vacuum-row entry.

This makes the first support-closure layer explicit.  It does not prove that
the resulting three-state sector is row-closed or spectrally invariant.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage

set_option maxRecDepth 300000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit doubled cube state -/

def centralLowerDoubleCubeState : EdgeLabelling := fun id =>
  if id ∈ centralLowerCubeFaceIds then 2 else 0

def centralLowerDoubleCubePhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 centralLowerDoubleCubeState
    zeroEdgeLabelling zeroEdgeLabelling

theorem centralLowerDoubleCubeState_le_two (id : Nat) :
    centralLowerDoubleCubeState id ≤ 2 := by
  unfold centralLowerDoubleCubeState
  by_cases hcube : id ∈ centralLowerCubeFaceIds <;> simp [hcube]

theorem centralLowerDoubleCubeState_mem_centralHalfStates :
    centralLowerDoubleCubeState ∈ centralHalfStates 2 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le (centralLowerDoubleCubeState_le_two id)
  · intro id hid
    unfold centralLowerDoubleCubeState
    rw [if_neg]
    intro hcube
    exact hid (centralLowerCubeFaceIds_subset_lower id hcube)

theorem centralLowerDoubleCubeState_ne_zero :
    centralLowerDoubleCubeState ≠ zeroEdgeLabelling := by
  intro heq
  have hvalue := congrFun heq 0
  change 2 = 0 at hvalue
  omega

theorem centralLowerDoubleCubeState_ne_cube :
    centralLowerDoubleCubeState ≠ centralLowerCubeState := by
  intro heq
  have hvalue := congrFun heq 0
  change 2 = 1 at hvalue
  omega

/-! ## 2. Closed production evaluation -/

theorem centralLowerDoubleCube_linkProduct_one :
    slabLinkMultiplicityProductOn 2 1 centralLowerDoubleCubePhysical
      (centralLowerLinks 0) = 1 := by
  rfl

/-- Direct kernel reduction of the production lower-half amplitude.  This
checks all 24 face coefficients and 48 lower-link multiplicities. -/
theorem centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_eqv :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerDoubleCubeState zeroEdgeLabelling ≈
      cutoffTwoVacuumOutsideCubeExcess := by
  unfold centralHalfAmplitude centralLowerFactor slabFaceFactorOn
    cutoffTwoHalfCoupling cutoffTwoVacuumOutsideCubeExcess
    centralLowerDoubleCubeState
  decide

/-- Direct reduction of the corresponding complete corrected-slab term. -/
theorem slabParametricKPhysicalTerm_cutoffTwo_doubleCube_eqv :
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        centralLowerDoubleCubePhysical ≈
      cutoffTwoVacuumOutsideCubeExcess := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
    slabExplicitLinkMultiplicityProduct centralLowerDoubleCubePhysical
    cutoffTwoHalfCoupling cutoffTwoVacuumOutsideCubeExcess
    centralLowerDoubleCubeState
  decide

theorem centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_pos :
    (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerDoubleCubeState zeroEdgeLabelling := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < cutoffTwoVacuumOutsideCubeExcess)
    (Q'.ge_of_eqv
      centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_eqv)

/-! ## 3. Retention in the genuine positive source carrier -/

private theorem zero_mem_bounded (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih := listQSum_member_le value hvalue tail htail
        have hmono :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

theorem centralLowerDoubleCubePhysicalReflectedKernel_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerDoubleCubeState zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
      (assembleReflectedSlabLabelling 0
        centralLowerDoubleCubeState boundary zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling ≤
        listQSum value (centralBoundaryChannels 2 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 1
          (assembleReflectedSlabLabelling 0
            centralLowerDoubleCubeState boundary zeroEdgeLabelling))
      (centralBoundaryChannels 2 0)
      (zero_mem_bounded 2 (centralFixedFaceIds 0))
  have hchosen : (0 : Q') < value zeroEdgeLabelling :=
    Q'.pos_of_lt_of_le
      (by decide : (0 : Q') < cutoffTwoVacuumOutsideCubeExcess)
      (Q'.ge_of_eqv
        slabParametricKPhysicalTerm_cutoffTwo_doubleCube_eqv)
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hchosen hmember

theorem centralLowerDoubleCubeRowMarginal_pos :
    (0 : Q') <
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 centralLowerDoubleCubeState := by
  have hnormalized :
      (0 : Q') <
        centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
          2 0 centralLowerDoubleCubeState zeroEdgeLabelling := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos centralLowerDoubleCubePhysicalReflectedKernel_pos
      (Q'.recipPos_pos _ _)
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le
    (centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 centralLowerDoubleCubeState)
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 centralLowerDoubleCubeState target)
    (centralHalfStates 2 0)
    (zero_mem_bounded 2 (centralLowerFaceIds 0))
  exact Q'.pos_of_lt_of_le hnormalized hmember

theorem centralLowerDoubleCubeState_mem_carrier :
    centralLowerDoubleCubeState ∈ cutoffTwoVacuumColumnCarrier := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralLowerDoubleCubeState_mem_centralHalfStates,
      centralLowerDoubleCubeRowMarginal_pos⟩

/-! ## 4. Explicit physical leakage and mass identification -/

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_doubleCube_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling centralLowerDoubleCubeState ≈
      cutoffTwoVacuumOutsideCubeExcess := by
  refine Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 zeroEdgeLabelling *
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerDoubleCubeState zeroEdgeLabelling) _
    (centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
      centralLowerDoubleCubeState
      centralLowerDoubleCubeState_mem_carrier) ?_
  refine Q'.eqv_trans _
    ((1 : Q') * cutoffTwoVacuumOutsideCubeExcess) _ ?_ ?_
  · exact Q'.eqv_trans _
      ((1 : Q') *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerDoubleCubeState zeroEdgeLabelling) _
      (Q'.mul_eqv_congr_right _ _ _
        centralBoundaryWeight_cutoffTwo_vacuum_eqv_one)
      (Q'.mul_eqv_congr_left 1 _ _
        centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_eqv)
  · exact Q'.one_mul_eqv _

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_doubleCube_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling centralLowerDoubleCubeState := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < cutoffTwoVacuumOutsideCubeExcess)
    (Q'.ge_of_eqv
      centralPhysicalReflectedKernel_cutoffTwo_vacuum_doubleCube_eqv)

theorem cutoffTwoOutsideSourcesMass_eqv_doubleCubeAmplitude :
    listQSum
        (fun source =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling)
        cutoffTwoOutsideVacuumCubeSources ≈
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerDoubleCubeState zeroEdgeLabelling := by
  exact Q'.eqv_trans _ cutoffTwoVacuumOutsideCubeExcess _
    cutoffTwoOutsideVacuumCubeSources_sum_eqv_expected
    (Q'.eqv_symm centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_eqv)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage.centralHalfAmplitude_cutoffTwo_doubleCube_vacuum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage.slabParametricKPhysicalTerm_cutoffTwo_doubleCube_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage.centralLowerDoubleCubeState_mem_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage.centralPhysicalReflectedKernel_cutoffTwo_vacuum_doubleCube_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage.cutoffTwoOutsideSourcesMass_eqv_doubleCubeAmplitude
