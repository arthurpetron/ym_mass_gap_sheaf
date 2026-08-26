/-
# A fixed peel-size carrier for component-animal tour codes

The exact Euler word of a component has length `2 * (animalSize - 1)`, while
the entropy comparison is indexed by the generally larger physical peel size.
This module appends the decoder's top backtrack symbol until every component
word has the common length `2 * peelSize`.

Backtracking never changes the decoder's visited list, including at an empty
stack.  Hence the padded word decodes to the same geometric support as the
exact tour.  It lies in one explicit 25-symbol carrier of cardinality

  `25 ^ (2 * peelSize) = 625 ^ peelSize`.

This is the desired volume- and cutoff-independent shape factor.  It records
only the plaquette support rooted at the selected plaquette; strand-copy
multiplicities and sparse auxiliary row keys remain separate code factors.

Constructive contract: finite list recursion and decidable arithmetic only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimalTourCode

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Backtrack padding preserves the decoder's visited support -/

/-- The top symbol of the `D+1` decoder alphabet, interpreted as backtrack. -/
def backtrackSymbol (BL : BddLattice) : Fin (BL.D + 1) :=
  ⟨BL.D, Nat.lt_succ_self BL.D⟩

/-- One backtrack instruction leaves the visited list literally unchanged. -/
theorem step_backtrack_visited (BL : BddLattice) (state : DState BL) :
    (step BL state (backtrackSymbol BL)).visited = state.visited := by
  unfold backtrackSymbol step
  simp only [Nat.lt_irrefl]
  cases state.stack <;> rfl

/-- Any finite suffix of backtrack instructions leaves the visited list
literally unchanged. -/
theorem foldl_replicate_backtrack_visited (BL : BddLattice) :
    forall padding : Nat, forall state : DState BL,
      ((List.replicate padding (backtrackSymbol BL)).foldl
        (step BL) state).visited = state.visited
  | 0, _ => rfl
  | padding + 1, state => by
      rw [List.replicate_succ, List.foldl_cons,
        foldl_replicate_backtrack_visited BL padding
          (step BL state (backtrackSymbol BL))]
      exact step_backtrack_visited BL state

/-- Appending any number of backtracks to a code preserves its decoded visited
support exactly. -/
theorem decode_append_replicate_backtrack
    (BL : BddLattice) (root : BL.toLattice.Plaquette)
    (code : List (Fin (BL.D + 1))) (padding : Nat) :
    decode BL root (code ++ List.replicate padding (backtrackSymbol BL)) =
      decode BL root code := by
  unfold decode
  rw [List.foldl_append]
  exact foldl_replicate_backtrack_visited BL padding _

/-! ## 2. The production padded component word -/

/-- The exact tour fits inside twice the physical peel length. -/
theorem componentPlaquetteTourCode_length_le_two_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquetteTourCode seed).length <=
      2 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  rw [componentPlaquetteTourCode_length]
  have hsupport := componentPlaquetteSupport_length_le_peelFaces seed
  omega

/-- The number of inert backtrack symbols required to reach the common
peel-size length. -/
def componentPlaquetteTourPadding
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : Nat :=
  2 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length -
    (componentPlaquetteTourCode seed).length

/-- The deterministic component tour padded to its common physical peel-size
carrier. -/
def componentPlaquettePaddedTourCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    List (Fin (z4Chain.D + 1)) :=
  componentPlaquetteTourCode seed ++
    List.replicate (componentPlaquetteTourPadding seed)
      (backtrackSymbol z4Chain)

/-- The padded production word has exactly twice the peel length. -/
theorem componentPlaquettePaddedTourCode_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquettePaddedTourCode seed).length =
      2 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentPlaquettePaddedTourCode componentPlaquetteTourPadding
  rw [List.length_append, List.length_replicate]
  have hfit := componentPlaquetteTourCode_length_le_two_mul_peelFaces seed
  omega

/-- Backtrack padding preserves the exact component-support decode. -/
theorem componentPlaquettePaddedTourCode_decode_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    sameSupport (componentPlaquetteSupport seed)
      (decode z4Chain (slabPlaquetteAt extent seed.root.faceId)
        (componentPlaquettePaddedTourCode seed)) := by
  unfold componentPlaquettePaddedTourCode
  rw [decode_append_replicate_backtrack]
  exact componentPlaquetteTourCode_decode_sameSupport seed

/-! ## 3. The fixed `625^n` shape carrier -/

/-- All 25-symbol words of the common length `2 * peelSize`. -/
def componentPlaquettePaddedTourCarrier (peelSize : Nat) :
    List (List (Fin (z4Chain.D + 1))) :=
  choiceSeqs (z4Chain.D + 1) (2 * peelSize)

/-- Every production padded word lies in the carrier indexed only by its
physical peel size. -/
theorem componentPlaquettePaddedTourCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    componentPlaquettePaddedTourCode seed ∈
      componentPlaquettePaddedTourCarrier
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentPlaquettePaddedTourCarrier
  exact mem_choiceSeqs_of_length _ _ _
    (componentPlaquettePaddedTourCode_length seed)

/-- The fixed shape carrier has exactly `625^peelSize` words. -/
theorem componentPlaquettePaddedTourCarrier_length (peelSize : Nat) :
    (componentPlaquettePaddedTourCarrier peelSize).length =
      625 ^ peelSize := by
  unfold componentPlaquettePaddedTourCarrier
  rw [choiceSeqs_length]
  change 25 ^ (2 * peelSize) = 625 ^ peelSize
  rw [deg_pow_two_mul]

/-- For components with the same literal root, equality of padded shape codes
forces equality of geometric supports up to membership.  Thus the code is
faithful at exactly the support-set granularity needed by animal counting. -/
theorem componentPlaquettePaddedTourCode_eq_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (left right : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hroot : slabPlaquetteAt extent left.root.faceId =
      slabPlaquetteAt extent right.root.faceId)
    (hcode : componentPlaquettePaddedTourCode left =
      componentPlaquettePaddedTourCode right) :
    sameSupport (L := z4Chain.toLattice) (componentPlaquetteSupport left)
      (componentPlaquetteSupport right) := by
  have hleft := componentPlaquettePaddedTourCode_decode_sameSupport left
  have hright := componentPlaquettePaddedTourCode_decode_sameSupport right
  rw [hroot, hcode] at hleft
  exact sameSupport_trans hleft (sameSupport_symm hright)

#print axioms backtrackSymbol
#print axioms step_backtrack_visited
#print axioms foldl_replicate_backtrack_visited
#print axioms decode_append_replicate_backtrack
#print axioms componentPlaquetteTourCode_length_le_two_mul_peelFaces
#print axioms componentPlaquetteTourPadding
#print axioms componentPlaquettePaddedTourCode
#print axioms componentPlaquettePaddedTourCode_length
#print axioms componentPlaquettePaddedTourCode_decode_sameSupport
#print axioms componentPlaquettePaddedTourCarrier
#print axioms componentPlaquettePaddedTourCode_mem_carrier
#print axioms componentPlaquettePaddedTourCarrier_length
#print axioms componentPlaquettePaddedTourCode_eq_sameSupport

end YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
