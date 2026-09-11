/-
# Finite fusion-witness fibers for inward-mate debt words

The preceding expansion names each stretched term only by its natural-number
multiplicity.  Here that number is exposed as the length of a literal finite
list of accepted canonical SU(2) auxiliary labellings.  A Boolean debt word
then selects, link by link, either the ordinary mate fiber or the stretched
fiber, and a finite Cartesian compiler enumerates their complete product.

Consequently every summand of the nonempty remainder has a concrete witness
carrier whose cardinality is exactly the arithmetic term already present in
the expansion.  The carrier is the finite input on which the closed-strand
rerouting map must act.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Literal canonical fiber for an arbitrary external spin word -/

/-- Accepted canonical auxiliary labellings for one external spin word. -/
def fusionWitnessesForSpins (cutoff : Nat) (spins : List Nat) :
    List EdgeLabelling :=
  (boundedEdgeLabellings cutoff
      (canonicalUsedAuxiliaryCoordinates spins.length)).filter
    (canonicalLinkConditionalAllowedB spins.length
      (externalSpinsOfList spins))

/-- At geometric valence at most six, the literal fiber has exactly the
existing explicit SU(2) fusion multiplicity. -/
theorem fusionWitnessesForSpins_length_eq_explicit
    (cutoff : Nat) (spins : List Nat) (hlength : spins.length ≤ 6) :
    (fusionWitnessesForSpins cutoff spins).length =
      explicitValenceMultiplicity cutoff spins.length
        (externalSpinsOfList spins) := by
  unfold fusionWitnessesForSpins
  change canonicalLinkInvariantMultiplicityCount cutoff spins.length
      (externalSpinsOfList spins) = _
  exact canonicalMultiplicity_eq_explicit _ hlength

/-! ## 2. The actual stretched fiber at one cube-boundary link -/

def cubeInwardMateStretchedSpins
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : List Nat :=
  (physical (centralLowerCubeFaceId linked.1.left) +
      physical (centralLowerCubeFaceId linked.1.right)) ::
    cubeInwardMateLinkRest K physical hK hbounded linked

theorem cubeInwardMateStretchedSpins_length_le_six
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateStretchedSpins
      K physical hK hbounded linked).length ≤ 6 := by
  have hsource :=
    (cubeInwardMateLinkCertificate K physical hK hbounded linked).2.1
  have hlength := hsource.length_eq
  have hdegree := slabIncidentPlaqIds_length_le_six 1 linked.1.link
  unfold cubeInwardMateStretchedSpins cubeInwardMateLinkRest
  simp only [List.length_cons]
  simp only [List.length_map, List.length_cons] at hlength
  omega

/-- The literal accepted auxiliary labellings counted by the stretched debt
at one attached cube-boundary incidence. -/
def cubeInwardMateStretchedFusionWitnesses
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : List EdgeLabelling :=
  fusionWitnessesForSpins (linkAuxiliaryCutoff K)
    (cubeInwardMateStretchedSpins K physical hK hbounded linked)

theorem cubeInwardMateStretchedFusionWitnesses_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateStretchedFusionWitnesses
      K physical hK hbounded linked).length =
      cubeInwardMateStretchedDebt K physical hK hbounded linked := by
  unfold cubeInwardMateStretchedFusionWitnesses
  rw [fusionWitnessesForSpins_length_eq_explicit _ _
    (cubeInwardMateStretchedSpins_length_le_six
      K physical hK hbounded linked)]
  rfl

/-! ## 3. Cartesian witness carrier selected by one Boolean word -/

abbrev CubeDebtFusionAssignment :=
  List (CubeProductionIncidenceMember × EdgeLabelling)

/-- Generic finite Cartesian compiler choosing one of two fibers at each
item.  A short word has no assignments, matching `debtChoiceProduct`. -/
def choiceFiberAssignments {A B : Type}
    (target debt : A → List B) :
    List A → List Bool → List (List (A × B))
  | [], _ => [[]]
  | _ :: _, [] => []
  | head :: tail, false :: word =>
      (target head).flatMap fun witness =>
        (choiceFiberAssignments target debt tail word).map fun rest =>
          (head, witness) :: rest
  | head :: tail, true :: word =>
      (debt head).flatMap fun witness =>
        (choiceFiberAssignments target debt tail word).map fun rest =>
          (head, witness) :: rest

private theorem length_flatMap_choice_map
    {A B C : Type} (entries : List A) (tails : List B)
    (combine : A → B → C) :
    (entries.flatMap (fun entry => tails.map (combine entry))).length =
      entries.length * tails.length := by
  induction entries with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem choiceFiberAssignments_length {A B : Type}
    (target debt : A → List B) : ∀ (items : List A) (word : List Bool),
    (choiceFiberAssignments target debt items word).length =
      debtChoiceProduct
        (fun item => (target item).length)
        (fun item => (debt item).length) items word
  | [], word => rfl
  | _ :: _, [] => rfl
  | head :: tail, false :: word => by
      simp only [choiceFiberAssignments, debtChoiceProduct]
      rw [length_flatMap_choice_map,
        choiceFiberAssignments_length target debt tail word]
  | head :: tail, true :: word => by
      simp only [choiceFiberAssignments, debtChoiceProduct]
      rw [length_flatMap_choice_map,
        choiceFiberAssignments_length target debt tail word]

/-- Concrete local-intertwiner assignments for one exact cube debt word. -/
def cubeDebtWordFusionAssignments
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (word : List Bool) : List CubeDebtFusionAssignment :=
  choiceFiberAssignments
    (fun linked => slabLinkFusionWitnesses K 1
      (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link)
    (cubeInwardMateStretchedFusionWitnesses K physical hK hbounded)
    cubeProductionIncidences.attach word

/-- The concrete assignment carrier has exactly the multiplicity of its
Boolean summand in the stretched-debt expansion. -/
theorem cubeDebtWordFusionAssignments_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (word : List Bool) :
    (cubeDebtWordFusionAssignments K physical hK hbounded word).length =
      debtChoiceProduct
        (cubeInwardMateTargetLinkMultiplicity K physical)
        (cubeInwardMateStretchedDebt K physical hK hbounded)
        cubeProductionIncidences.attach word := by
  unfold cubeDebtWordFusionAssignments
  rw [choiceFiberAssignments_length]
  have htarget :
      (fun linked : CubeProductionIncidenceMember =>
        (slabLinkFusionWitnesses K 1
          (centralLowerCubeEvenInwardMatePhysical physical)
          linked.1.link).length) =
        cubeInwardMateTargetLinkMultiplicity K physical := by
    funext linked
    exact slabLinkFusionWitnesses_length K 1
      (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link
  have hdebt :
      (fun linked : CubeProductionIncidenceMember =>
        (cubeInwardMateStretchedFusionWitnesses
          K physical hK hbounded linked).length) =
        cubeInwardMateStretchedDebt K physical hK hbounded := by
    funext linked
    exact cubeInwardMateStretchedFusionWitnesses_length
      K physical hK hbounded linked
  rw [htarget, hdebt]

/-! ## 4. One finite carrier for the complete nonempty remainder -/

abbrev CubeNonemptyDebtFusionCarrier :=
  CubeNonemptyDebtWord × CubeDebtFusionAssignment

/-- Attach the nonempty-word proof to every word and flatten all of its exact
Cartesian fusion-witness fibers into one finite carrier. -/
def cubeInwardMateNonemptyDebtFusionCarriers
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List CubeNonemptyDebtFusionCarrier :=
  (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.flatMap
    fun word =>
      (cubeDebtWordFusionAssignments
        K physical hK hbounded word.1).map fun assignment =>
          (word, assignment)

private theorem length_flatMap_fiber_maps {A B : Type}
    (fiber : A → List B) : ∀ items : List A,
    (items.flatMap fun item =>
      (fiber item).map fun value => (item, value)).length =
      natListSum (items.map fun item => (fiber item).length)
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.map_cons, natListSum]
      rw [length_flatMap_fiber_maps fiber tail]

/-- The named arithmetic remainder is exactly the cardinality of one
observable finite carrier of nonempty debt words and their local fusion
witness assignments. -/
theorem cubeInwardMateNonemptyDebtFusionCarriers_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateNonemptyDebtFusionCarriers
      K physical hK hbounded).length =
      cubeInwardMateNonemptyStretchedRemainder
        K physical hK hbounded := by
  unfold cubeInwardMateNonemptyDebtFusionCarriers
    cubeInwardMateNonemptyStretchedRemainder nonemptyDebtExpansion
  rw [length_flatMap_fiber_maps]
  apply congrArg natListSum
  calc
    (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
        (fun word =>
          (cubeDebtWordFusionAssignments
            K physical hK hbounded word.1).length) =
        (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
          (fun word => debtChoiceProduct
            (cubeInwardMateTargetLinkMultiplicity K physical)
            (cubeInwardMateStretchedDebt K physical hK hbounded)
            cubeProductionIncidences.attach word.1) := by
              apply List.map_congr_left
              intro word _
              exact cubeDebtWordFusionAssignments_length
                K physical hK hbounded word.1
    _ = ((nonemptyDebtChoiceWords
          cubeProductionIncidences.attach).attach.map Subtype.val).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro word _
            rfl
    _ = (nonemptyDebtChoiceWords cubeProductionIncidences.attach).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.attach_map_subtype_val]

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.fusionWitnessesForSpins_length_eq_explicit
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.cubeInwardMateStretchedFusionWitnesses_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.choiceFiberAssignments_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.cubeDebtWordFusionAssignments_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.cubeInwardMateNonemptyDebtFusionCarriers_length
