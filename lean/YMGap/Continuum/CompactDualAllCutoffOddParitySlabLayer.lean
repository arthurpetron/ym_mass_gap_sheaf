/-
# The all-cutoff odd-parity surface on the corrected slab

The cutoff-one closure theorem identifies a physical state itself with the
binary indicator of its odd-spin support.  That identification is false at
higher cutoff, but it is stronger than parity closure requires.

Here the original incident spin word is compared modulo two with the binary
word carried by the same geometric odd-spin support.  The corrected-slab
binary-support incidence theorem identifies the latter word with geometric
face incidence.  Hence the SU(2) parity selection rule closes the odd-spin
support at every cutoff whenever the physical Gibbs summand is positive.

This supplies one canonical closed binary layer of an arbitrary positive
fine state.  It does not decompose the whole higher-spin state into binary
layers: that stronger conclusion still requires a bounded global routing or
strand-colouring theorem.

## Axiom gate

Finite list algebra and the audited production multiplicities only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
import YMGap.Continuum.Z4DyadicSU2ParitySpinKernel

namespace YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicSU2ParitySpinKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pointwise parity identification on physical slab faces -/

/-- On every physical numerical face, the binary indicator of the geometric
odd-spin support is exactly the original twice-spin label reduced modulo
two. -/
theorem slabBinaryFineOddSupport_eq_mod_two
    {S : SlabScalePair} {fineState : EdgeLabelling} {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges S.fine.extent) :
    slabBinarySupportLabelling S.fine.extent
        (fineOddSlabSupport S fineState) id =
      fineState id % 2 := by
  have hsupport :
      slabPlaquetteAt S.fine.extent id ∈
          fineOddSlabSupport S fineState ↔
        fineState id % 2 = 1 := by
    unfold fineOddSlabSupport
    simp only [List.mem_filter, slabPlaquetteAt_mem hid,
      decide_eq_true_eq, true_and]
    rw [slabSpinAtPlaquette_slabPlaquetteAt
      S.fine.extent fineState hid]
  rw [slabBinarySupportLabelling_eq_indicator hid]
  by_cases hodd : fineState id % 2 = 1
  · rw [if_pos (hsupport.mpr hodd), hodd]
  · rw [if_neg (fun hmem => hodd (hsupport.mp hmem))]
    have hlt : fineState id % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega

/-! ## 2. Parity of finite incident words -/

/-- Pointwise congruence modulo two passes through the constructive finite
sum used by the production multiplicity. -/
theorem natListSum_map_mod_two_congr {A : Type}
    (left right : A → Nat) :
    ∀ entries : List A,
      (∀ entry, entry ∈ entries →
        left entry % 2 = right entry % 2) →
      natListSum (entries.map left) % 2 =
        natListSum (entries.map right) % 2
  | [], _ => rfl
  | head :: tail, hagree => by
      have ih :
          natListSum (tail.map left) % 2 =
            natListSum (tail.map right) % 2 := by
        apply natListSum_map_mod_two_congr left right tail
        intro entry hentry
        exact hagree entry (List.mem_cons_of_mem head hentry)
      simp only [List.map_cons, natListSum]
      calc
        (left head + natListSum (tail.map left)) % 2 =
            (left head % 2 +
              natListSum (tail.map left) % 2) % 2 :=
          Nat.add_mod _ _ _
        _ = (right head % 2 +
              natListSum (tail.map right) % 2) % 2 := by
          rw [hagree head List.mem_cons_self, ih]
        _ = (right head + natListSum (tail.map right)) % 2 :=
          (Nat.add_mod _ _ _).symm

/-- `externalSpinsOfList` merely reindexes a finite word; summing all its
external coordinates recovers the original word sum. -/
theorem localExternalSpinSum_externalSpinsOfList_allCutoff
    (spins : List Nat) :
    localExternalSpinSum spins.length (externalSpinsOfList spins) =
      natListSum spins := by
  induction spins with
  | nil => rfl
  | cons head tail ih =>
      change
        natListSum
            ((List.range (tail.length + 1)).map
              (externalSpinsOfList (head :: tail))) =
          natListSum (head :: tail)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, natListSum, List.map_map]
      change head +
          natListSum
            ((List.range tail.length).map
              (externalSpinsOfList tail)) =
        head + natListSum tail
      unfold localExternalSpinSum at ih
      rw [ih]

/-- At every corrected-slab link, geometric incidence of the odd-spin
support has the same parity as the original incident SU(2) twice-spin sum. -/
theorem fineOddSlabSupport_incidenceParity_eq_localExternalSpinSum
    (S : SlabScalePair) (fineState : EdgeLabelling) (link : Z4Link) :
    faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 =
      localExternalSpinSum
          (slabIncidentPlaqIds S.fine.extent link).length
          (externalSpinsOfList
            ((slabIncidentPlaqIds S.fine.extent link).map fineState)) % 2 := by
  let binaryState :=
    slabBinarySupportLabelling S.fine.extent
      (fineOddSlabSupport S fineState)
  have hbinarySum :=
    slabBinarySupport_localExternalSpinSum
      (fun _ hmem => fineOddSlabSupport_subset hmem)
      (fineOddSlabSupport_nodup S fineState) link
  have hbinaryWord :=
    localExternalSpinSum_externalSpinsOfList_allCutoff
      ((slabIncidentPlaqIds S.fine.extent link).map binaryState)
  have hfineWord :=
    localExternalSpinSum_externalSpinsOfList_allCutoff
      ((slabIncidentPlaqIds S.fine.extent link).map fineState)
  simp only [List.length_map] at hbinaryWord hfineWord
  have hwordParity :
      natListSum
          ((slabIncidentPlaqIds S.fine.extent link).map binaryState) % 2 =
        natListSum
          ((slabIncidentPlaqIds S.fine.extent link).map fineState) % 2 := by
    apply natListSum_map_mod_two_congr binaryState fineState
    intro id hid
    unfold binaryState
    rw [slabBinaryFineOddSupport_eq_mod_two
      (S := S) (fineState := fineState)
      (slabIncidentPlaqId_physical hid)]
    exact Nat.mod_mod _ _
  calc
    faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 =
        localExternalSpinSum
            (slabIncidentPlaqIds S.fine.extent link).length
            (externalSpinsOfList
              ((slabIncidentPlaqIds S.fine.extent link).map binaryState)) %
          2 := by rw [hbinarySum]
    _ = natListSum
          ((slabIncidentPlaqIds S.fine.extent link).map binaryState) % 2 := by
      rw [hbinaryWord]
    _ = natListSum
          ((slabIncidentPlaqIds S.fine.extent link).map fineState) % 2 :=
      hwordParity
    _ = localExternalSpinSum
          (slabIncidentPlaqIds S.fine.extent link).length
          (externalSpinsOfList
            ((slabIncidentPlaqIds S.fine.extent link).map fineState)) % 2 := by
      rw [hfineWord]

/-! ## 3. Arbitrary-cutoff closure from physical positivity -/

private theorem faceIncidenceCount_eq_zero_of_no_incidence_allCutoff
    (link : Z4Link) :
    ∀ support : List Z4Plaq,
      (∀ plaquette, plaquette ∈ support → link ∉ edgesOf plaquette) →
        faceIncidenceCount link support = 0
  | [], _ => rfl
  | head :: tail, hnone => by
      have hhead := hnone head List.mem_cons_self
      have htail : ∀ plaquette, plaquette ∈ tail →
          link ∉ edgesOf plaquette :=
        fun plaquette hmem =>
          hnone plaquette (List.mem_cons_of_mem head hmem)
      simp [faceIncidenceCount, hhead,
        faceIncidenceCount_eq_zero_of_no_incidence_allCutoff
          link tail htail]

/-- A strictly positive corrected-slab physical summand has a closed
odd-spin parity surface at every cutoff. -/
theorem positivePhysicalTerm_fineOddSupport_even
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (_hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    EvenFaceIncidence (fineOddSlabSupport S fineState) := by
  intro link
  by_cases hlink :
      link ∈ boundaryCompleteSlabLinks S.fine.extent
  · have hlocal :=
      positivePhysicalTerm_localMultiplicity_ne_zero
        S.fine fineState hpositive hlink
    have hparity :=
      fineOddSlabSupport_incidenceParity_eq_localExternalSpinSum
        S fineState link
    have hnotOdd :
        faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 ≠ 1 := by
      intro hodd
      apply hlocal
      unfold slabExplicitLinkMultiplicity
      apply explicitValenceMultiplicity_eq_zero_of_odd_sum
      · simpa only [List.length_map] using
          slabIncidentPlaqIds_length_le_six S.fine.extent link
      · rw [List.length_map, ← hparity]
        exact hodd
    have hlt :
        faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega
  · rw [faceIncidenceCount_eq_zero_of_no_incidence_allCutoff]
    intro plaquette hmem hincident
    apply hlink
    exact (mem_boundaryCompleteSlabLinks_iff
      S.fine.extent link).mpr
        ⟨plaquette, fineOddSlabSupport_subset hmem, hincident⟩

#print axioms slabBinaryFineOddSupport_eq_mod_two
#print axioms natListSum_map_mod_two_congr
#print axioms fineOddSlabSupport_incidenceParity_eq_localExternalSpinSum
#print axioms positivePhysicalTerm_fineOddSupport_even

end YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
