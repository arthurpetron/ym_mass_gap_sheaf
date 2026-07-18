/-
# Exact symmetry of the adjacent-even physical reflected kernel

The one-step reflection carrier is the adjacent even slab.  Before any
positive-semidefinite or Gram question is considered, its literal corrected
physical kernel already has an exact symmetry: reflection swaps the two lower
half-state inputs and fixes the common boundary input.

This leaf records only that symmetry.  It is valid for every rational
coupling, uses no positivity hypothesis, and does not depend on the refuted
unrestricted endpoint Gram factorization.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## Finite half-state and fixed-boundary coordinates -/

/-- Enumerated lower-half face labellings for the adjacent-even slab. -/
def adjacentEvenHalfStates (K radius : Nat) : List EdgeLabelling :=
  boundedEdgeLabellings K (adjacentEvenLowerFaceIds radius)

/-- Enumerated fixed-plane face labellings shared by both reflected halves. -/
def adjacentEvenBoundaryChannels (K radius : Nat) : List EdgeLabelling :=
  boundedEdgeLabellings K (adjacentEvenFixedFaceIds radius)

/-! ## Literal physical reflected kernel -/

/-- The corrected physical slab weight, summed over the common fixed-plane
face labelling, with the two lower half-state inputs assembled by reflection.

No normalization or positivity claim is built into this raw finite kernel. -/
def adjacentEvenPhysicalReflectedKernel
    (w : Q') (K radius : Nat)
    (left right : EdgeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      slabParametricKPhysicalTerm w K (adjacentEvenExtent radius)
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right))
    (adjacentEvenBoundaryChannels K radius)

/-- Exact symmetry of the literal adjacent-even physical kernel.

For each common boundary coordinate, the supported slab reflection swaps the
two half-state inputs.  Reflection invariance of the complete physical term
then supplies the pointwise equality; the finite boundary sum preserves it. -/
theorem adjacentEvenPhysicalReflectedKernel_symm
    (w : Q') {K radius : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius)
    (hright : right ∈ adjacentEvenHalfStates K radius) :
    adjacentEvenPhysicalReflectedKernel w K radius left right ≈
      adjacentEvenPhysicalReflectedKernel w K radius right left := by
  unfold adjacentEvenPhysicalReflectedKernel
  apply listQSum_congr_on
  intro boundary hboundary
  have hbounded :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hleft hboundary hright
  have hreflection :=
    slabParametricKPhysicalTerm_supported_reflection w hbounded
  rw [assembleAdjacentEvenReflectedSlabLabelling_reflection_swap] at hreflection
  exact Q'.eqv_symm hreflection

#print axioms adjacentEvenPhysicalReflectedKernel_symm

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry
