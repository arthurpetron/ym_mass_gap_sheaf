/-
# A positive cutoff-two state outside the 65-state invariant sector

The 65-state cube-subset sector is genuinely proper inside the literal
positive physical carrier.  A single fundamental lower face at identifier
`39`, together with the four fundamental fixed faces

    [40, 41, 49, 59],

and its reflected upper copy forms one transverse closed cube.  The complete
cutoff-two production summand is strictly positive, so the lower state has a
positive diagonal kernel entry and belongs to the retained physical carrier.
Its label `1` at one cube face, with the other five cube faces zero, excludes
it from both branches of the exact 65-state classifier.

Combining this witness with the already checked row-closure theorem proves
that the full cutoff-two kernel has a nonempty block orthogonal to the
65-state block.  This is a finite-cutoff reducibility statement, not a
continuum or Clay mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
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

/-! ## 1. The transverse cube witness -/

/-- Fundamental spin on one lower spatial face. -/
def cutoffTwoTransverseSingleFaceState : EdgeLabelling := fun id =>
  if id = 39 then 1 else 0

/-- The four fixed temporal faces which complete the reflected transverse
cube. -/
def cutoffTwoTransverseCubeBoundary : EdgeLabelling := fun id =>
  if id ∈ [40, 41, 49, 59] then 1 else 0

def cutoffTwoTransverseCubePhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 cutoffTwoTransverseSingleFaceState
    cutoffTwoTransverseCubeBoundary cutoffTwoTransverseSingleFaceState

theorem cutoffTwoTransverseSingleFaceState_le_two (id : Nat) :
    cutoffTwoTransverseSingleFaceState id ≤ 2 := by
  unfold cutoffTwoTransverseSingleFaceState
  by_cases hid : id = 39 <;> simp [hid]

theorem cutoffTwoTransverseSingleFaceState_mem_halfStates :
    cutoffTwoTransverseSingleFaceState ∈ centralHalfStates 2 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le (cutoffTwoTransverseSingleFaceState_le_two id)
  · intro id hid
    unfold cutoffTwoTransverseSingleFaceState
    rw [if_neg]
    intro heq
    subst id
    exact hid (by decide)

theorem cutoffTwoTransverseCubeBoundary_mem_channels :
    cutoffTwoTransverseCubeBoundary ∈ centralBoundaryChannels 2 0 := by
  unfold centralBoundaryChannels
  apply boundedEdgeLabellings_complete
  · intro id _
    unfold cutoffTwoTransverseCubeBoundary
    by_cases hselected : id ∈ [40, 41, 49, 59] <;> simp [hselected]
  · intro id hid
    unfold cutoffTwoTransverseCubeBoundary
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [40, 41, 49, 59] →
          faceId ∈ centralFixedFaceIds 0 := by decide
    exact hid (hsubset id hselected)

/-- Direct kernel reduction of every face coefficient and link multiplicity
in the transverse closed-cube summand. -/
theorem cutoffTwoTransverseCubePhysicalTerm_pos :
    (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoTransverseCubePhysical := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
    slabExplicitLinkMultiplicityProduct cutoffTwoTransverseCubePhysical
    cutoffTwoHalfCoupling cutoffTwoTransverseSingleFaceState
    cutoffTwoTransverseCubeBoundary
  decide

theorem centralPhysicalReflectedKernel_cutoffTwo_transverse_self_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        cutoffTwoTransverseSingleFaceState
        cutoffTwoTransverseSingleFaceState := by
  exact cutoffTwoPhysicalKernel_pos_of_term_pos
    cutoffTwoTransverseSingleFaceState cutoffTwoTransverseCubeBoundary
    cutoffTwoTransverseSingleFaceState
    cutoffTwoTransverseCubeBoundary_mem_channels
    cutoffTwoTransverseCubePhysicalTerm_pos

theorem cutoffTwoTransverseSingleFaceState_mem_carrier :
    cutoffTwoTransverseSingleFaceState ∈ cutoffTwoVacuumColumnCarrier := by
  exact cutoffTwoTarget_mem_carrier_of_positive_edge
    cutoffTwoTransverseSingleFaceState cutoffTwoTransverseSingleFaceState
    cutoffTwoTransverseSingleFaceState_mem_halfStates
    cutoffTwoTransverseSingleFaceState_mem_halfStates
    centralPhysicalReflectedKernel_cutoffTwo_transverse_self_pos

/-! ## 2. Properness and the second exact block -/

theorem cutoffTwoTransverseSingleFaceState_not_mem_sector :
    cutoffTwoTransverseSingleFaceState ∉ cutoffTwoCubeSectorStates := by
  intro hmem
  have hsemantics :=
    (mem_cutoffTwoCubeSectorStates_iff
      cutoffTwoTransverseSingleFaceState).mp hmem
  rcases hsemantics with heq | hdoubled
  · have hvalue := congrFun heq 0
    change 0 = 1 at hvalue
    omega
  · rcases hdoubled.1 39 (by decide) with hzero | htwo
    · change 1 = 0 at hzero
      omega
    · change 1 = 2 at htwo
      omega

/-- The checked sector-to-complement kernel block vanishes at the explicit
positive complement state. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sector_transverse_eqv_zero
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source cutoffTwoTransverseSingleFaceState ≈ 0 := by
  exact centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
    source cutoffTwoTransverseSingleFaceState hsource
    cutoffTwoTransverseSingleFaceState_mem_halfStates
    cutoffTwoTransverseSingleFaceState_not_mem_sector

/-- Symmetry supplies the reverse complement-to-sector zero block. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_transverse_sector_eqv_zero
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffTwoCubeSectorStates) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        cutoffTwoTransverseSingleFaceState target ≈ 0 := by
  have hsymm := centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
    cutoffTwoTransverseSingleFaceState_mem_halfStates
    (cutoffTwoCubeSectorState_mem_halfStates htarget)
  exact Q'.eqv_trans _ _ _ hsymm
    (centralPhysicalReflectedKernel_cutoffTwo_sector_transverse_eqv_zero
      target htarget)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness.cutoffTwoTransverseCubePhysicalTerm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness.cutoffTwoTransverseSingleFaceState_mem_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness.cutoffTwoTransverseSingleFaceState_not_mem_sector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness.centralPhysicalReflectedKernel_cutoffTwo_transverse_sector_eqv_zero
