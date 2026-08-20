/-
# A fourth explicit cutoff-two physical Krylov state

An exhaustive external search over all 4095 nonzero words in the proved
fundamental-cube boundary support proposed a particularly small outgoing
transition.  The target has doubled-spin label two on lower face `1` and
zero elsewhere; the shared boundary has label two on fixed faces
`[2, 5, 11, 41]` and zero elsewhere.

This module rechecks the proposed complete production summand directly.  It
then proves that the target is retained, that the genuine cube-to-target
physical Gram entry is positive, and that the formerly explicit three-code
seed is not row-closed.  Thus every proof-carrying closed sector contains a
fourth concrete code.

The external search is not trusted, and no exhaustive closure claim is made.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage

set_option maxRecDepth 300000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The proposed target and shared boundary -/

def cutoffTwoSingleFaceTwoState : EdgeLabelling := fun id =>
  if id = 1 then 2 else 0

def cutoffTwoCubeSingleFaceBoundary : EdgeLabelling := fun id =>
  if id ∈ [2, 5, 11, 41] then 2 else 0

def cutoffTwoCubeSingleFacePhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 centralLowerCubeState
    cutoffTwoCubeSingleFaceBoundary cutoffTwoSingleFaceTwoState

theorem cutoffTwoSingleFaceTwoState_le_two (id : Nat) :
    cutoffTwoSingleFaceTwoState id ≤ 2 := by
  unfold cutoffTwoSingleFaceTwoState
  by_cases hid : id = 1 <;> simp [hid]

theorem cutoffTwoSingleFaceTwoState_mem_halfStates :
    cutoffTwoSingleFaceTwoState ∈ centralHalfStates 2 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le (cutoffTwoSingleFaceTwoState_le_two id)
  · intro id hid
    unfold cutoffTwoSingleFaceTwoState
    rw [if_neg]
    intro hone
    subst id
    exact hid (by decide)

theorem cutoffTwoCubeSingleFaceBoundary_mem_channels :
    cutoffTwoCubeSingleFaceBoundary ∈ centralBoundaryChannels 2 0 := by
  unfold centralBoundaryChannels
  apply boundedEdgeLabellings_complete
  · intro id _
    unfold cutoffTwoCubeSingleFaceBoundary
    by_cases hselected : id ∈ [2, 5, 11, 41] <;> simp [hselected]
  · intro id hid
    unfold cutoffTwoCubeSingleFaceBoundary
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [2, 5, 11, 41] →
          faceId ∈ centralFixedFaceIds 0 := by decide
    exact hid (hsubset id hselected)

theorem cutoffTwoSingleFaceTwoState_ne_zero :
    cutoffTwoSingleFaceTwoState ≠ zeroEdgeLabelling := by
  intro heq
  have hvalue := congrFun heq 1
  change 2 = 0 at hvalue
  omega

theorem cutoffTwoSingleFaceTwoState_ne_cube :
    cutoffTwoSingleFaceTwoState ≠ centralLowerCubeState := by
  intro heq
  have hvalue := congrFun heq 1
  change 2 = 1 at hvalue
  omega

theorem cutoffTwoSingleFaceTwoState_ne_doubleCube :
    cutoffTwoSingleFaceTwoState ≠ centralLowerDoubleCubeState := by
  intro heq
  have hvalue := congrFun heq 0
  change 0 = 2 at hvalue
  omega

/-! ## 2. Direct production replay and a positive physical edge -/

/-- Direct reduction of all face coefficients and all link multiplicities in
the chosen complete corrected-slab summand. -/
theorem cutoffTwoCubeSingleFacePhysicalTerm_pos :
    (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoCubeSingleFacePhysical := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
    slabExplicitLinkMultiplicityProduct cutoffTwoCubeSingleFacePhysical
    cutoffTwoHalfCoupling cutoffTwoSingleFaceTwoState
    cutoffTwoCubeSingleFaceBoundary
  decide

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

/-- Any one strictly positive complete boundary summand gives a strictly
positive entry of the genuine cutoff-two physical kernel. -/
theorem cutoffTwoPhysicalKernel_pos_of_term_pos
    (left boundary right : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hterm : (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        (assembleReflectedSlabLabelling 0 left boundary right)) :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        left right := by
  let value := fun candidate =>
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
      (assembleReflectedSlabLabelling 0 left candidate right)
  have hmember :
      value boundary ≤ listQSum value (centralBoundaryChannels 2 0) :=
    listQSum_member_le value
      (fun candidate =>
        slabParametricKPhysicalTerm_nonnegative
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 1
          (assembleReflectedSlabLabelling 0 left candidate right))
      (centralBoundaryChannels 2 0) hboundary
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hterm hmember

theorem centralPhysicalReflectedKernel_cutoffTwo_cube_singleFace_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState cutoffTwoSingleFaceTwoState := by
  exact cutoffTwoPhysicalKernel_pos_of_term_pos
    centralLowerCubeState cutoffTwoCubeSingleFaceBoundary
    cutoffTwoSingleFaceTwoState
    cutoffTwoCubeSingleFaceBoundary_mem_channels
    cutoffTwoCubeSingleFacePhysicalTerm_pos

/-- A positive edge from an enumerated source retains its enumerated target
in the positive cutoff-two carrier. -/
theorem cutoffTwoTarget_mem_carrier_of_positive_edge
    (source target : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 2 0)
    (htarget : target ∈ centralHalfStates 2 0)
    (hpositive : (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source target) :
    target ∈ cutoffTwoVacuumColumnCarrier := by
  have hreverse :
      (0 : Q') <
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          target source := by
    have hsymm := centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
      htarget hsource
    exact Q'.pos_of_lt_of_le hpositive (Q'.ge_of_eqv hsymm)
  have hnormalized :
      (0 : Q') <
        centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
          2 0 target source := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos hreverse (Q'.recipPos_pos _ _)
  have hrow :
      (0 : Q') <
        centralPhysicalRowMarginal cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
          2 0 target := by
    unfold centralPhysicalRowMarginal
    have hmember := listQSum_member_le
      (centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 target)
      (fun candidate =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
          2 0 target candidate)
      (centralHalfStates 2 0) hsource
    exact Q'.pos_of_lt_of_le hnormalized hmember
  exact mem_centralPositiveHalfStates_iff.mpr ⟨htarget, hrow⟩

/-! ## 3. Retention and the forced fourth code -/

theorem centralPhysicalReflectedKernel_cutoffTwo_singleFace_cube_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        cutoffTwoSingleFaceTwoState centralLowerCubeState := by
  have hsymm := centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
    cutoffTwoSingleFaceTwoState_mem_halfStates
    (centralLowerCubeState_mem_centralHalfStates (by decide : 1 ≤ 2))
  exact Q'.pos_of_lt_of_le
    centralPhysicalReflectedKernel_cutoffTwo_cube_singleFace_pos
    (Q'.ge_of_eqv hsymm)

theorem cutoffTwoSingleFaceTwoState_rowMarginal_pos :
    (0 : Q') <
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 cutoffTwoSingleFaceTwoState := by
  have hnormalized :
      (0 : Q') <
        centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
          2 0 cutoffTwoSingleFaceTwoState centralLowerCubeState := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos
      centralPhysicalReflectedKernel_cutoffTwo_singleFace_cube_pos
      (Q'.recipPos_pos _ _)
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le
    (centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 cutoffTwoSingleFaceTwoState)
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 cutoffTwoSingleFaceTwoState target)
    (centralHalfStates 2 0)
    (centralLowerCubeState_mem_centralHalfStates (by decide : 1 ≤ 2))
  exact Q'.pos_of_lt_of_le hnormalized hmember

theorem cutoffTwoSingleFaceTwoState_mem_carrier :
    cutoffTwoSingleFaceTwoState ∈ cutoffTwoVacuumColumnCarrier := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨cutoffTwoSingleFaceTwoState_mem_halfStates,
      cutoffTwoSingleFaceTwoState_rowMarginal_pos⟩

theorem cutoffTwoSingleFace_code_ne_vacuum :
    bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact cutoffTwoSingleFaceTwoState_ne_zero
    (bf4StateCode_injective_on_positive
      cutoffTwoSingleFaceTwoState_mem_carrier
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
      hcode)

theorem cutoffTwoSingleFace_code_ne_cube :
    bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  intro hcode
  exact cutoffTwoSingleFaceTwoState_ne_cube
    (bf4StateCode_injective_on_positive
      cutoffTwoSingleFaceTwoState_mem_carrier
      (centralLowerCubeState_mem_centralPositiveHalfStates
        (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide))
      hcode)

theorem cutoffTwoSingleFace_code_ne_doubleCube :
    bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ≠
      bf4StateCode 2 0 centralLowerDoubleCubeState := by
  intro hcode
  exact cutoffTwoSingleFaceTwoState_ne_doubleCube
    (bf4StateCode_injective_on_positive
      cutoffTwoSingleFaceTwoState_mem_carrier
      centralLowerDoubleCubeState_mem_carrier hcode)

def cutoffTwoExplicitThreeStateCodes : List Nat :=
  [bf4StateCode 2 0 zeroEdgeLabelling,
    bf4StateCode 2 0 centralLowerCubeState,
    bf4StateCode 2 0 centralLowerDoubleCubeState]

def cutoffTwoExplicitFourStateCodes : List Nat :=
  cutoffTwoExplicitThreeStateCodes ++
    [bf4StateCode 2 0 cutoffTwoSingleFaceTwoState]

theorem singleFace_code_mem_of_cube_code_mem_and_rowClosed
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (hcube : bf4StateCode 2 0 centralLowerCubeState ∈ sectorCodes) :
    bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ∈ sectorCodes := by
  exact code_mem_of_positive_physical_edge sectorCodes hclosed
    centralLowerCubeState cutoffTwoSingleFaceTwoState
    (centralLowerCubeState_mem_centralPositiveHalfStates
      (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide))
    cutoffTwoSingleFaceTwoState_mem_carrier hcube
    centralPhysicalReflectedKernel_cutoffTwo_cube_singleFace_pos

theorem closureCertificate_contains_singleFace
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate) :
    bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ∈
      certificate.sectorCodes := by
  apply singleFace_code_mem_of_cube_code_mem_and_rowClosed
    certificate.sectorCodes certificate.rowClosed
  exact certificate.forcedSeedIncluded
    (bf4StateCode 2 0 centralLowerCubeState)
    (by simp [cutoffTwoFirstKrylovSeedCodes])

theorem not_cutoffTwoExplicitThreeStateCodes_rowClosed :
    ¬ cutoffTwoPhysicalCodeSectorRowClosed
      cutoffTwoExplicitThreeStateCodes := by
  intro hclosed
  have hsingle := singleFace_code_mem_of_cube_code_mem_and_rowClosed
    cutoffTwoExplicitThreeStateCodes hclosed
    (by simp [cutoffTwoExplicitThreeStateCodes])
  unfold cutoffTwoExplicitThreeStateCodes at hsingle
  rcases List.mem_cons.mp hsingle with hvacuum | htail
  · exact cutoffTwoSingleFace_code_ne_vacuum hvacuum
  rcases List.mem_cons.mp htail with hcube | htail
  · exact cutoffTwoSingleFace_code_ne_cube hcube
  rcases List.mem_cons.mp htail with hdouble | hempty
  · exact cutoffTwoSingleFace_code_ne_doubleCube hdouble
  · exact False.elim (List.not_mem_nil hempty)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage.cutoffTwoCubeSingleFacePhysicalTerm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage.centralPhysicalReflectedKernel_cutoffTwo_cube_singleFace_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage.cutoffTwoSingleFaceTwoState_mem_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage.closureCertificate_contains_singleFace
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage.not_cutoffTwoExplicitThreeStateCodes_rowClosed
