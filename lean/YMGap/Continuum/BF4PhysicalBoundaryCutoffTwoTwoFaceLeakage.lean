/-
# A sixth explicit cutoff-two physical Krylov state

The punctured doubled cube has 256 positive boundary words.  A parallel
finite scout proposed an outgoing transition through the boundary supported
on fixed faces `[2, 4, 5, 11, 13, 23, 41]`.  Its new target carries label two
on the two lower faces `[1, 3]`.

Lean directly evaluates the proposed complete production summand, proves the
genuine physical edge positive, retains the two-face target, and rules out
row closure of the five previously explicit codes.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage

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
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. The two-face target and chosen boundary -/

def cutoffTwoTwoFaceState : EdgeLabelling := fun id =>
  if id ∈ [1, 3] then 2 else 0

def cutoffTwoPuncturedTwoFaceBoundary : EdgeLabelling := fun id =>
  if id ∈ [2, 4, 5, 11, 13, 23, 41] then 2 else 0

def cutoffTwoPuncturedTwoFacePhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 cutoffTwoPuncturedDoubleCubeState
    cutoffTwoPuncturedTwoFaceBoundary cutoffTwoTwoFaceState

theorem cutoffTwoTwoFaceState_le_two (id : Nat) :
    cutoffTwoTwoFaceState id ≤ 2 := by
  unfold cutoffTwoTwoFaceState
  by_cases hselected : id ∈ [1, 3] <;> simp [hselected]

theorem cutoffTwoTwoFaceState_mem_halfStates :
    cutoffTwoTwoFaceState ∈ centralHalfStates 2 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le (cutoffTwoTwoFaceState_le_two id)
  · intro id hid
    unfold cutoffTwoTwoFaceState
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [1, 3] →
          faceId ∈ centralLowerFaceIds 0 := by decide
    exact hid (hsubset id hselected)

theorem cutoffTwoPuncturedTwoFaceBoundary_mem_channels :
    cutoffTwoPuncturedTwoFaceBoundary ∈ centralBoundaryChannels 2 0 := by
  unfold centralBoundaryChannels
  apply boundedEdgeLabellings_complete
  · intro id _
    unfold cutoffTwoPuncturedTwoFaceBoundary
    by_cases hselected : id ∈ [2, 4, 5, 11, 13, 23, 41] <;>
      simp [hselected]
  · intro id hid
    unfold cutoffTwoPuncturedTwoFaceBoundary
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [2, 4, 5, 11, 13, 23, 41] →
          faceId ∈ centralFixedFaceIds 0 := by decide
    exact hid (hsubset id hselected)

theorem cutoffTwoTwoFaceState_ne_zero :
    cutoffTwoTwoFaceState ≠ zeroEdgeLabelling := by
  intro heq
  have hvalue := congrFun heq 1
  change 2 = 0 at hvalue
  omega

theorem cutoffTwoTwoFaceState_ne_cube :
    cutoffTwoTwoFaceState ≠ centralLowerCubeState := by
  intro heq
  have hvalue := congrFun heq 1
  change 2 = 1 at hvalue
  omega

theorem cutoffTwoTwoFaceState_ne_doubleCube :
    cutoffTwoTwoFaceState ≠ centralLowerDoubleCubeState := by
  intro heq
  have hvalue := congrFun heq 0
  change 0 = 2 at hvalue
  omega

theorem cutoffTwoTwoFaceState_ne_singleFace :
    cutoffTwoTwoFaceState ≠ cutoffTwoSingleFaceTwoState := by
  intro heq
  have hvalue := congrFun heq 3
  change 2 = 0 at hvalue
  omega

theorem cutoffTwoTwoFaceState_ne_punctured :
    cutoffTwoTwoFaceState ≠ cutoffTwoPuncturedDoubleCubeState := by
  intro heq
  have hvalue := congrFun heq 1
  change 2 = 0 at hvalue
  omega

/-! ## 2. Positive production term, edge, and target retention -/

theorem cutoffTwoPuncturedTwoFacePhysicalTerm_pos :
    (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoPuncturedTwoFacePhysical := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
    slabExplicitLinkMultiplicityProduct cutoffTwoPuncturedTwoFacePhysical
    cutoffTwoHalfCoupling cutoffTwoPuncturedDoubleCubeState
    cutoffTwoPuncturedTwoFaceBoundary cutoffTwoTwoFaceState
  decide

theorem centralPhysicalReflectedKernel_cutoffTwo_punctured_twoFace_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        cutoffTwoPuncturedDoubleCubeState cutoffTwoTwoFaceState := by
  exact cutoffTwoPhysicalKernel_pos_of_term_pos
    cutoffTwoPuncturedDoubleCubeState cutoffTwoPuncturedTwoFaceBoundary
    cutoffTwoTwoFaceState cutoffTwoPuncturedTwoFaceBoundary_mem_channels
    cutoffTwoPuncturedTwoFacePhysicalTerm_pos

theorem cutoffTwoTwoFaceState_mem_carrier :
    cutoffTwoTwoFaceState ∈ cutoffTwoVacuumColumnCarrier := by
  exact cutoffTwoTarget_mem_carrier_of_positive_edge
    cutoffTwoPuncturedDoubleCubeState cutoffTwoTwoFaceState
    cutoffTwoPuncturedDoubleCubeState_mem_halfStates
    cutoffTwoTwoFaceState_mem_halfStates
    centralPhysicalReflectedKernel_cutoffTwo_punctured_twoFace_pos

/-! ## 3. The sixth code is forced -/

theorem cutoffTwoTwoFace_code_ne_vacuum :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact cutoffTwoTwoFaceState_ne_zero
    (bf4StateCode_injective_on_positive cutoffTwoTwoFaceState_mem_carrier
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0) hcode)

theorem cutoffTwoTwoFace_code_ne_cube :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  intro hcode
  exact cutoffTwoTwoFaceState_ne_cube
    (bf4StateCode_injective_on_positive cutoffTwoTwoFaceState_mem_carrier
      (centralLowerCubeState_mem_centralPositiveHalfStates
        (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide)) hcode)

theorem cutoffTwoTwoFace_code_ne_doubleCube :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ≠
      bf4StateCode 2 0 centralLowerDoubleCubeState := by
  intro hcode
  exact cutoffTwoTwoFaceState_ne_doubleCube
    (bf4StateCode_injective_on_positive cutoffTwoTwoFaceState_mem_carrier
      centralLowerDoubleCubeState_mem_carrier hcode)

theorem cutoffTwoTwoFace_code_ne_singleFace :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ≠
      bf4StateCode 2 0 cutoffTwoSingleFaceTwoState := by
  intro hcode
  exact cutoffTwoTwoFaceState_ne_singleFace
    (bf4StateCode_injective_on_positive cutoffTwoTwoFaceState_mem_carrier
      cutoffTwoSingleFaceTwoState_mem_carrier hcode)

theorem cutoffTwoTwoFace_code_ne_punctured :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ≠
      bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState := by
  intro hcode
  exact cutoffTwoTwoFaceState_ne_punctured
    (bf4StateCode_injective_on_positive cutoffTwoTwoFaceState_mem_carrier
      cutoffTwoPuncturedDoubleCubeState_mem_carrier hcode)

theorem twoFace_code_mem_of_punctured_code_mem_and_rowClosed
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (hpunctured : bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ∈
      sectorCodes) :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ∈ sectorCodes := by
  exact code_mem_of_positive_physical_edge sectorCodes hclosed
    cutoffTwoPuncturedDoubleCubeState cutoffTwoTwoFaceState
    cutoffTwoPuncturedDoubleCubeState_mem_carrier
    cutoffTwoTwoFaceState_mem_carrier hpunctured
    centralPhysicalReflectedKernel_cutoffTwo_punctured_twoFace_pos

theorem closureCertificate_contains_twoFace
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate) :
    bf4StateCode 2 0 cutoffTwoTwoFaceState ∈ certificate.sectorCodes := by
  exact twoFace_code_mem_of_punctured_code_mem_and_rowClosed
    certificate.sectorCodes certificate.rowClosed
    (closureCertificate_contains_puncturedDoubleCube certificate)

def cutoffTwoExplicitSixStateCodes : List Nat :=
  cutoffTwoExplicitFiveStateCodes ++
    [bf4StateCode 2 0 cutoffTwoTwoFaceState]

theorem not_cutoffTwoExplicitFiveStateCodes_rowClosed :
    ¬ cutoffTwoPhysicalCodeSectorRowClosed
      cutoffTwoExplicitFiveStateCodes := by
  intro hclosed
  have htwo := twoFace_code_mem_of_punctured_code_mem_and_rowClosed
    cutoffTwoExplicitFiveStateCodes hclosed
    (by simp [cutoffTwoExplicitFiveStateCodes,
      cutoffTwoExplicitFourStateCodes, cutoffTwoExplicitThreeStateCodes])
  unfold cutoffTwoExplicitFiveStateCodes cutoffTwoExplicitFourStateCodes
    cutoffTwoExplicitThreeStateCodes at htwo
  rcases List.mem_cons.mp htwo with hvacuum | htail
  · exact cutoffTwoTwoFace_code_ne_vacuum hvacuum
  rcases List.mem_cons.mp htail with hcube | htail
  · exact cutoffTwoTwoFace_code_ne_cube hcube
  rcases List.mem_cons.mp htail with hdouble | htail
  · exact cutoffTwoTwoFace_code_ne_doubleCube hdouble
  rcases List.mem_cons.mp htail with hsingle | htail
  · exact cutoffTwoTwoFace_code_ne_singleFace hsingle
  rcases List.mem_cons.mp htail with hpunctured | hempty
  · exact cutoffTwoTwoFace_code_ne_punctured hpunctured
  · exact False.elim (List.not_mem_nil hempty)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage.cutoffTwoPuncturedTwoFacePhysicalTerm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage.centralPhysicalReflectedKernel_cutoffTwo_punctured_twoFace_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage.cutoffTwoTwoFaceState_mem_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage.closureCertificate_contains_twoFace
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage.not_cutoffTwoExplicitFiveStateCodes_rowClosed
