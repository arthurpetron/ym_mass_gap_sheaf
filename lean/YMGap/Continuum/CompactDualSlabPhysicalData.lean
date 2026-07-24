/-
# Corrected-slab physical datum for the compact-dual RG route

The legacy finite box is not closed under half-time reflection.  This module
therefore packages the already constructed boundary-complete slab as the
single finite physical datum consumed by CD-2.  Its physical summand and
partition include every corrected-slab face and link multiplicity.  The
existing exact reflection reindex, weighted-Gram identity, Cartesian coverage
theorem, and full quadratic nonnegativity are exposed through one value.

This closes the finite reflection-positive carrier.  It does not construct a
fine-to-coarse block kernel, a retained remainder, a contraction estimate, or
any spacing-uniform limit.

## Axiom gate

Definitions and previously audited finite reflection theorems only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.CompactDualSlabPhysicalData

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-- The corrected finite physical choices shared by every CD-2 consumer. -/
structure SlabPhysicalData : Type where
  coupling : Q'
  coupling_nonnegative : (0 : Q') ≤ coupling
  cutoff : Nat
  half : Nat

namespace SlabPhysicalData

/-- Odd central extent, with the reflection plane between time slices. -/
def extent (D : SlabPhysicalData) : Nat :=
  centralExtent D.half

/-- Every physical face of the boundary-complete corrected slab. -/
def faceEdges (D : SlabPhysicalData) : List Nat :=
  slabPhysicalFaceEdges D.extent

/-- The literal bounded Cartesian state space of the corrected slab. -/
def physicalLabellings (D : SlabPhysicalData) : List EdgeLabelling :=
  boundedEdgeLabellings D.cutoff D.faceEdges

/-- The complete corrected-slab physical summand. -/
def physicalTerm (D : SlabPhysicalData) (physical : EdgeLabelling) : Q' :=
  slabParametricKPhysicalTerm
    D.coupling D.cutoff D.extent physical

/-- The complete corrected-slab physical partition. -/
def physicalPartition (D : SlabPhysicalData) : Q' :=
  slabParametricKPhysicalPartition D.coupling D.cutoff D.extent

/-- The supported face-labelling reflection on the selected slab. -/
def reflectLabelling
    (D : SlabPhysicalData) (physical : EdgeLabelling) : EdgeLabelling :=
  reflectSupportedSlabFaceLabelling D.extent physical

/-- The exact lower-half state list used by the physical Gram theorem. -/
def halfStates (D : SlabPhysicalData) : List EdgeLabelling :=
  centralHalfStates D.cutoff D.half

/-- The exact fixed-plane channel list used by the physical Gram theorem. -/
def boundaryChannels (D : SlabPhysicalData) : List EdgeLabelling :=
  centralBoundaryChannels D.cutoff D.half

/-- The physical reflected kernel before its weighted-Gram identification. -/
def reflectedKernel
    (D : SlabPhysicalData) (left right : EdgeLabelling) : Q' :=
  centralPhysicalReflectedKernel
    D.coupling D.cutoff D.half left right

/-- The assembled finite reflection quadratic. -/
def reflectionQuadratic
    (D : SlabPhysicalData) (coefficient : EdgeLabelling → Q') : Q' :=
  centralPhysicalReflectionQuadratic
    D.coupling D.cutoff D.half coefficient

/-- The independently enumerated full corrected-slab reflection quadratic. -/
def fullReflectionQuadratic
    (D : SlabPhysicalData) (coefficient : EdgeLabelling → Q') : Q' :=
  centralFullPhysicalReflectionQuadratic
    D.coupling D.cutoff D.half coefficient

/-- Every bounded corrected-slab summand is exactly reflection invariant. -/
theorem physicalTerm_reflection
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    D.physicalTerm (D.reflectLabelling physical) ≈
      D.physicalTerm physical := by
  exact slabParametricKPhysicalTerm_supported_reflection D.coupling
    (fun id hid => Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound D.cutoff D.faceEdges
        physical hphysical).1 id hid))

/-- Reflection is an exact Cartesian reindex of the full physical partition. -/
theorem physicalPartition_reflection_reindex (D : SlabPhysicalData) :
    listQSum
        (fun physical => D.physicalTerm (D.reflectLabelling physical))
        D.physicalLabellings ≈
      D.physicalPartition := by
  exact slabParametricKPhysicalPartition_reflection_reindex
    D.coupling D.cutoff D.extent

/-- The corrected physical kernel is exactly a weighted Gram kernel. -/
theorem reflectedKernel_eq_weightedGram
    (D : SlabPhysicalData) {left right : EdgeLabelling}
    (hleft : left ∈ D.halfStates)
    (hright : right ∈ D.halfStates) :
    D.reflectedKernel left right ≈
      weightedGram D.boundaryChannels
        (centralBoundaryWeight D.coupling D.cutoff D.half)
        (centralHalfAmplitude D.coupling D.cutoff D.half)
        left right := by
  exact centralPhysicalReflectedKernel_eq_weightedGram
    D.coupling hleft hright

/-- The assembled exact rational reflection form is nonnegative. -/
theorem reflectionQuadratic_nonnegative
    (D : SlabPhysicalData) (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤ D.reflectionQuadratic coefficient := by
  exact centralPhysicalReflectionQuadratic_nonnegative
    D.coupling_nonnegative coefficient

/-- The independently enumerated full physical reflection form is
nonnegative.  The imported Cartesian coverage theorem ensures that this is
not merely positivity on a hand-selected assembled subspace. -/
theorem fullReflectionQuadratic_nonnegative
    (D : SlabPhysicalData) (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤ D.fullReflectionQuadratic coefficient := by
  exact centralFullPhysicalReflectionQuadratic_nonnegative
    D.coupling_nonnegative coefficient

end SlabPhysicalData

end YMGap.Continuum.CompactDualSlabPhysicalData

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.physicalTerm_reflection
#print axioms YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.physicalPartition_reflection_reindex
#print axioms YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.reflectedKernel_eq_weightedGram
#print axioms YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.reflectionQuadratic_nonnegative
#print axioms YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.fullReflectionQuadratic_nonnegative
