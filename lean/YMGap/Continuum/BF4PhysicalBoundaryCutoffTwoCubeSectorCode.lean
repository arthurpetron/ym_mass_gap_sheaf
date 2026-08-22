/-
# A constructive finite code for the cutoff-two cube sector

The exact 65-state cube sector consists of function-valued edge labellings, so
membership in its literal list must not be split by an implicit classical
decider.  This module exposes the already faithful natural-number state code
as a shared executable classifier for that sector.

This is finite cutoff two only.  It supplies neither a compatible cofinal
sector family nor any thermodynamic or continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-- Faithful finite codes of the 65 exact sector states. -/
def cutoffTwoCubeSectorCodes : List Nat :=
  cutoffTwoCubeSectorStates.map (bf4StateCode 2 0)

/-- On the bounded cutoff-two carrier, membership in the executable code list
is equivalent to membership in the literal 65-state sector. -/
theorem cutoffTwoSectorCode_mem_iff_of_halfState
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0) :
    bf4StateCode 2 0 state ∈ cutoffTwoCubeSectorCodes ↔
      state ∈ cutoffTwoCubeSectorStates := by
  constructor
  · intro hcode
    rcases List.mem_map.mp hcode with ⟨candidate, hcand, hsameCode⟩
    have hcandHalf := cutoffTwoCubeSectorState_mem_halfStates hcand
    have hsame := bf4StateCode_injective_on_centralHalfStates
      hstate hcandHalf (Eq.symm hsameCode)
    subst candidate
    exact hcand
  · intro hsector
    exact List.mem_map.mpr ⟨state, hsector, rfl⟩

/-- Constructive sector-membership decision on the bounded cutoff-two carrier,
transported from decidable natural-number list membership. -/
def cutoffTwoCubeSectorMembershipDecidable
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0) :
    Decidable (state ∈ cutoffTwoCubeSectorStates) :=
  decidable_of_iff
    (bf4StateCode 2 0 state ∈ cutoffTwoCubeSectorCodes)
    (cutoffTwoSectorCode_mem_iff_of_halfState hstate)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode.cutoffTwoSectorCode_mem_iff_of_halfState
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode.cutoffTwoCubeSectorMembershipDecidable
