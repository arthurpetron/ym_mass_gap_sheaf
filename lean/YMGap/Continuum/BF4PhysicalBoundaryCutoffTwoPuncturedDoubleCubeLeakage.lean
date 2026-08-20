/-
# A fifth explicit cutoff-two physical Krylov state

The single-face doubled-spin source has exactly one boundary word with
positive half amplitude: fixed faces `[2, 5, 11, 41]` carry label two.  The
finite constraint scout found exactly four lower states compatible with that
word.  Three were already known (the fundamental cube, doubled cube, and the
single-face source); the fourth is the doubled cube with face `1` removed.

Here Lean rechecks one complete production summand joining the single-face
state to that punctured doubled cube.  It proves a positive genuine physical
edge, retains the target, and refutes row closure of the explicit four-state
seed.  Exhaustivity of the scout is not used as a premise.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage

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

/-! ## 1. The punctured doubled cube -/

def cutoffTwoPuncturedDoubleCubeState : EdgeLabelling := fun id =>
  if id ∈ [0, 3, 9, 19, 39] then 2 else 0

def cutoffTwoSingleFacePuncturedPhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 cutoffTwoSingleFaceTwoState
    cutoffTwoCubeSingleFaceBoundary cutoffTwoPuncturedDoubleCubeState

theorem cutoffTwoPuncturedDoubleCubeState_le_two (id : Nat) :
    cutoffTwoPuncturedDoubleCubeState id ≤ 2 := by
  unfold cutoffTwoPuncturedDoubleCubeState
  by_cases hselected : id ∈ [0, 3, 9, 19, 39] <;> simp [hselected]

theorem cutoffTwoPuncturedDoubleCubeState_mem_halfStates :
    cutoffTwoPuncturedDoubleCubeState ∈ centralHalfStates 2 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le (cutoffTwoPuncturedDoubleCubeState_le_two id)
  · intro id hid
    unfold cutoffTwoPuncturedDoubleCubeState
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [0, 3, 9, 19, 39] →
          faceId ∈ centralLowerFaceIds 0 := by decide
    exact hid (hsubset id hselected)

theorem cutoffTwoPuncturedDoubleCubeState_ne_zero :
    cutoffTwoPuncturedDoubleCubeState ≠ zeroEdgeLabelling := by
  intro heq
  have hvalue := congrFun heq 0
  change 2 = 0 at hvalue
  omega

theorem cutoffTwoPuncturedDoubleCubeState_ne_cube :
    cutoffTwoPuncturedDoubleCubeState ≠ centralLowerCubeState := by
  intro heq
  have hvalue := congrFun heq 0
  change 2 = 1 at hvalue
  omega

theorem cutoffTwoPuncturedDoubleCubeState_ne_doubleCube :
    cutoffTwoPuncturedDoubleCubeState ≠ centralLowerDoubleCubeState := by
  intro heq
  have hvalue := congrFun heq 1
  change 0 = 2 at hvalue
  omega

theorem cutoffTwoPuncturedDoubleCubeState_ne_singleFace :
    cutoffTwoPuncturedDoubleCubeState ≠ cutoffTwoSingleFaceTwoState := by
  intro heq
  have hvalue := congrFun heq 0
  change 2 = 0 at hvalue
  omega

/-! ## 2. Direct positive transition and retention -/

theorem cutoffTwoSingleFacePuncturedPhysicalTerm_pos :
    (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoSingleFacePuncturedPhysical := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
    slabExplicitLinkMultiplicityProduct
    cutoffTwoSingleFacePuncturedPhysical cutoffTwoHalfCoupling
    cutoffTwoSingleFaceTwoState cutoffTwoCubeSingleFaceBoundary
    cutoffTwoPuncturedDoubleCubeState
  decide

theorem centralPhysicalReflectedKernel_cutoffTwo_singleFace_punctured_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        cutoffTwoSingleFaceTwoState cutoffTwoPuncturedDoubleCubeState := by
  exact cutoffTwoPhysicalKernel_pos_of_term_pos
    cutoffTwoSingleFaceTwoState cutoffTwoCubeSingleFaceBoundary
    cutoffTwoPuncturedDoubleCubeState
    cutoffTwoCubeSingleFaceBoundary_mem_channels
    cutoffTwoSingleFacePuncturedPhysicalTerm_pos

theorem cutoffTwoPuncturedDoubleCubeState_mem_carrier :
    cutoffTwoPuncturedDoubleCubeState ∈ cutoffTwoVacuumColumnCarrier := by
  exact cutoffTwoTarget_mem_carrier_of_positive_edge
    cutoffTwoSingleFaceTwoState cutoffTwoPuncturedDoubleCubeState
    cutoffTwoSingleFaceTwoState_mem_halfStates
    cutoffTwoPuncturedDoubleCubeState_mem_halfStates
    centralPhysicalReflectedKernel_cutoffTwo_singleFace_punctured_pos

/-! ## 3. The fifth forced code -/

theorem cutoffTwoPunctured_code_ne_vacuum :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact cutoffTwoPuncturedDoubleCubeState_ne_zero
    (bf4StateCode_injective_on_positive
      cutoffTwoPuncturedDoubleCubeState_mem_carrier
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
      hcode)

theorem cutoffTwoPunctured_code_ne_cube :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  intro hcode
  exact cutoffTwoPuncturedDoubleCubeState_ne_cube
    (bf4StateCode_injective_on_positive
      cutoffTwoPuncturedDoubleCubeState_mem_carrier
      (centralLowerCubeState_mem_centralPositiveHalfStates
        (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide))
      hcode)

theorem cutoffTwoPunctured_code_ne_doubleCube :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ≠
      bf4StateCode 2 0 centralLowerDoubleCubeState := by
  intro hcode
  exact cutoffTwoPuncturedDoubleCubeState_ne_doubleCube
    (bf4StateCode_injective_on_positive
      cutoffTwoPuncturedDoubleCubeState_mem_carrier
      centralLowerDoubleCubeState_mem_carrier hcode)

theorem cutoffTwoPunctured_code_ne_singleFace :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ≠
      bf4StateCode 2 0 cutoffTwoSingleFaceTwoState := by
  intro hcode
  exact cutoffTwoPuncturedDoubleCubeState_ne_singleFace
    (bf4StateCode_injective_on_positive
      cutoffTwoPuncturedDoubleCubeState_mem_carrier
      cutoffTwoSingleFaceTwoState_mem_carrier hcode)

theorem punctured_code_mem_of_singleFace_code_mem_and_rowClosed
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (hsingle : bf4StateCode 2 0 cutoffTwoSingleFaceTwoState ∈ sectorCodes) :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ∈ sectorCodes := by
  exact code_mem_of_positive_physical_edge sectorCodes hclosed
    cutoffTwoSingleFaceTwoState cutoffTwoPuncturedDoubleCubeState
    cutoffTwoSingleFaceTwoState_mem_carrier
    cutoffTwoPuncturedDoubleCubeState_mem_carrier hsingle
    centralPhysicalReflectedKernel_cutoffTwo_singleFace_punctured_pos

theorem closureCertificate_contains_puncturedDoubleCube
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate) :
    bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState ∈
      certificate.sectorCodes := by
  exact punctured_code_mem_of_singleFace_code_mem_and_rowClosed
    certificate.sectorCodes certificate.rowClosed
    (closureCertificate_contains_singleFace certificate)

def cutoffTwoExplicitFiveStateCodes : List Nat :=
  cutoffTwoExplicitFourStateCodes ++
    [bf4StateCode 2 0 cutoffTwoPuncturedDoubleCubeState]

theorem not_cutoffTwoExplicitFourStateCodes_rowClosed :
    ¬ cutoffTwoPhysicalCodeSectorRowClosed
      cutoffTwoExplicitFourStateCodes := by
  intro hclosed
  have hpunctured := punctured_code_mem_of_singleFace_code_mem_and_rowClosed
    cutoffTwoExplicitFourStateCodes hclosed
    (by simp [cutoffTwoExplicitFourStateCodes,
      cutoffTwoExplicitThreeStateCodes])
  unfold cutoffTwoExplicitFourStateCodes
    cutoffTwoExplicitThreeStateCodes at hpunctured
  rcases List.mem_cons.mp hpunctured with hvacuum | htail
  · exact cutoffTwoPunctured_code_ne_vacuum hvacuum
  rcases List.mem_cons.mp htail with hcube | htail
  · exact cutoffTwoPunctured_code_ne_cube hcube
  rcases List.mem_cons.mp htail with hdouble | htail
  · exact cutoffTwoPunctured_code_ne_doubleCube hdouble
  rcases List.mem_cons.mp htail with hsingle | hempty
  · exact cutoffTwoPunctured_code_ne_singleFace hsingle
  · exact False.elim (List.not_mem_nil hempty)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage.cutoffTwoSingleFacePuncturedPhysicalTerm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage.centralPhysicalReflectedKernel_cutoffTwo_singleFace_punctured_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage.cutoffTwoPuncturedDoubleCubeState_mem_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage.closureCertificate_contains_puncturedDoubleCube
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPuncturedDoubleCubeLeakage.not_cutoffTwoExplicitFourStateCodes_rowClosed
