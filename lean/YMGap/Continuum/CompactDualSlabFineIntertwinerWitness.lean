/-
# Global fine-intertwiner witnesses for the corrected slab

The corrected-slab physical term contains, at every lattice link, the exact
cardinality of the bounded SU(2) fusion paths compatible with the incident
physical face spins.  This module exposes those paths as finite data instead
of leaving them compressed into a natural-number multiplicity.

For each slab link we enumerate the canonical auxiliary labellings accepted
by the production trivalent resolver.  Taking the finite Cartesian product
over all slab links gives a global fine-intertwiner field.  Its list length is
proved exactly equal to the complete product of link multiplicities appearing
in `slabParametricKPhysicalTerm`.  Consequently every strictly positive
physical corrected-slab summand has an explicit global fine-intertwiner
witness.

This closes the fine-side witness extraction needed by the general-source
adjacent-cube kernel.  It does not yet construct the globally consistent
coarse face-fusion field: that is the next recoupling/gluing gate.

## Axiom gate

Finite list algebra and the audited explicit valence formulas only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualSlabPhysicalData
import YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity

namespace YMGap.Continuum.CompactDualSlabFineIntertwinerWitness

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

local infix:50 " ≈ " => Q'.eqv

abbrev SlabLabelling := EdgeLabelling
abbrev SlabLink :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Link

/-! ## 1. One literal link-intertwiner fiber -/

def slabLinkExternalSpins
    (extent : Nat) (physical : SlabLabelling)
    (link : SlabLink) : SlabLabelling :=
  externalSpinsOfList ((slabIncidentPlaqIds extent link).map physical)

/-- Every accepted canonical auxiliary labelling for one corrected-slab
link.  The list is the literal finite fiber counted by the production
multiplicity. -/
def slabLinkFusionWitnesses
    (K extent : Nat) (physical : SlabLabelling)
    (link : SlabLink) : List SlabLabelling :=
  let degree := (slabIncidentPlaqIds extent link).length
  let external := slabLinkExternalSpins extent physical link
  (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates degree)).filter
    (canonicalLinkConditionalAllowedB degree external)

theorem slabLinkFusionWitnesses_length
    (K extent : Nat) (physical : SlabLabelling)
    (link : SlabLink) :
    (slabLinkFusionWitnesses K extent physical link).length =
      slabExplicitLinkMultiplicity K extent physical link := by
  unfold slabLinkFusionWitnesses slabExplicitLinkMultiplicity
    slabLinkExternalSpins
  change canonicalLinkInvariantMultiplicityCount
      (linkAuxiliaryCutoff K)
      (slabIncidentPlaqIds extent link).length
      (externalSpinsOfList
        ((slabIncidentPlaqIds extent link).map physical)) =
    explicitValenceMultiplicity
      (linkAuxiliaryCutoff K)
      ((slabIncidentPlaqIds extent link).map physical).length
      (externalSpinsOfList
        ((slabIncidentPlaqIds extent link).map physical))
  rw [List.length_map]
  exact canonicalMultiplicity_eq_explicit _
    (slabIncidentPlaqIds_length_le_six extent link)

/-! ## 2. Cartesian assembly of the whole fine auxiliary field -/

abbrev SlabFusionWitnessAssignment :=
  List (SlabLink × SlabLabelling)

def slabFusionWitnessAssignmentsOn
    (K extent : Nat) (physical : SlabLabelling) :
    List SlabLink → List SlabFusionWitnessAssignment
  | [] => [[]]
  | link :: rest =>
      (slabLinkFusionWitnesses K extent physical link).flatMap
        (fun auxiliary =>
          (slabFusionWitnessAssignmentsOn K extent physical rest).map
            (fun tail => (link, auxiliary) :: tail))

private theorem length_flatMap_map
    {A B C : Type} (entries : List A) (tails : List B)
    (combine : A → B → C) :
    (entries.flatMap
        (fun entry => tails.map (combine entry))).length =
      entries.length * tails.length := by
  induction entries with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem slabFusionWitnessAssignmentsOn_length
    (K extent : Nat) (physical : SlabLabelling) :
    ∀ links : List SlabLink,
      (slabFusionWitnessAssignmentsOn
        K extent physical links).length =
        natListProduct
          (slabExplicitLinkMultiplicity K extent physical) links
  | [] => rfl
  | link :: rest => by
      simp only [slabFusionWitnessAssignmentsOn, natListProduct]
      rw [length_flatMap_map,
        slabFusionWitnessAssignmentsOn_length K extent physical rest,
        slabLinkFusionWitnesses_length]

/-- The complete finite global fine-intertwiner field over every
boundary-complete corrected-slab link. -/
def slabFineFusionWitnesses
    (D : SlabPhysicalData) (physical : SlabLabelling) :
    List SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentsOn D.cutoff D.extent physical
    (boundaryCompleteSlabLinks D.extent)

/-- The global witness list has exactly the multiplicity appearing in the
complete corrected-slab physical summand. -/
theorem slabFineFusionWitnesses_length
    (D : SlabPhysicalData) (physical : SlabLabelling) :
    (slabFineFusionWitnesses D physical).length =
      slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent physical := by
  unfold slabFineFusionWitnesses slabExplicitLinkMultiplicityProduct
  exact slabFusionWitnessAssignmentsOn_length
    D.cutoff D.extent physical (boundaryCompleteSlabLinks D.extent)

/-! ## 3. Positive physical mass supplies a global witness -/

private theorem pos_not_eqv_zero {a : Q'}
    (ha : (0 : Q') < a) : ¬ a ≈ 0 := by
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) ha

/-- Every strictly positive corrected-slab spin-foam summand carries at least
one explicit, globally assembled fine-intertwiner field. -/
theorem positivePhysicalTerm_has_fineFusionWitness
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical) :
    ∃ witness, witness ∈ slabFineFusionWitnesses D physical := by
  have hproduct :
      slabExplicitLinkMultiplicityProduct
          D.cutoff D.extent physical ≠ 0 := by
    intro hzero
    have htermZero : D.physicalTerm physical ≈ 0 := by
      unfold SlabPhysicalData.physicalTerm
        slabParametricKPhysicalTerm
      rw [hzero]
      exact Q'.mul_zero_eqv _
    exact (pos_not_eqv_zero hpositive) htermZero
  have hlength :
      (slabFineFusionWitnesses D physical).length ≠ 0 := by
    rw [slabFineFusionWitnesses_length]
    exact hproduct
  cases hwitnesses : slabFineFusionWitnesses D physical with
  | nil =>
      exact False.elim (hlength (by simp [hwitnesses]))
  | cons witness rest =>
      exact ⟨witness, List.mem_cons_self⟩

#print axioms slabLinkFusionWitnesses_length
#print axioms slabFusionWitnessAssignmentsOn_length
#print axioms slabFineFusionWitnesses_length
#print axioms positivePhysicalTerm_has_fineFusionWitness

end YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
