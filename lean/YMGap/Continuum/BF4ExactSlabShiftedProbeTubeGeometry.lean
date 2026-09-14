/-
# The literal three-step tube for the original shifted probe

At volume margin m the ORIGINAL response probe lies at spatial base
(1+m,1+m,1+m), time m. Its actual reflection lies at time m+3. Twelve
distinct temporal faces connect these two ordered spatial plaquettes.
All faces belong to the same original slab at every margin.

This pins the geometry required by the selected-channel composition. It
does not yet identify the complete three-layer gauge-transformed interacting
integrand with the compact tube polynomial, nor bound its signed dressing.
No original positive-response certificate or continuum claim follows here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse
import YMGap.Continuum.SU2QuaternionFundamentalTubeComposition

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (probe probeId_lower)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)

/-- These are the original response family slabs, not a new volume schedule. -/
def responseExtent (margin : Nat) : Nat := centralExtent (1+margin)

def sliceFace (margin time : Nat) : Z4Plaq :=
  ((1+margin,1+margin,1+margin,margin+time), .p01)

theorem base_probe_face :
    slabPlaquetteAt 3 (bulkFaceId 0 1 1 0) = sliceFace 0 0 := by
  exact (bulkFaceId_pin (padding := 1) (lag := 1)
    (mem_centralLowerFaceIds.mp probeId_lower).1).trans (by rfl)

/-- Exact original lower observable, including its existing enlargement map. -/
theorem lower_shifted_probe_pin (margin : Nat) :
    lower (enlarge margin shiftedProbe) =
      characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin) (sliceFace margin 0)).scalar 1 := by
  unfold enlarge
  rw [bulkLower_pin]
  change characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin)
    (shiftFace margin margin (slabPlaquetteAt 3 (bulkFaceId 0 1 1 0)))).scalar 1 = _
  rw [base_probe_face]
  simp only [sliceFace, shiftFace, shiftVertex, Nat.zero_add, Nat.add_zero]

/-- Exact original reflected upper observable, not an independent top probe. -/
theorem upper_shifted_probe_pin (margin : Nat) :
    upper (enlarge margin shiftedProbe) =
      characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin) (sliceFace margin 3)).scalar 1 := by
  unfold enlarge
  rw [bulkUpper_pin]
  change characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin)
    (shiftFace margin margin (timeReflectPlaquette 3 (slabPlaquetteAt 3 (bulkFaceId 0 1 1 0))))).scalar 1 = _
  rw [base_probe_face]
  simp [sliceFace, shiftFace, shiftVertex, timeReflectPlaquette, Nat.add_comm]

theorem endpoint_reflection (margin : Nat) :
    timeReflectPlaquette (responseExtent margin) (sliceFace margin 0) = sliceFace margin 3 := by
  have ht : responseExtent margin - margin = margin + 3 := by unfold responseExtent centralExtent; omega
  simp only [sliceFace, timeReflectPlaquette, Nat.add_zero, ht]

theorem endpoint_separation (margin : Nat) :
    (sliceFace margin 3).1.2.2.2 = (sliceFace margin 0).1.2.2.2 + 3 := rfl

theorem slice_physical (margin : Nat) (time : Fin 4) :
    sliceFace margin time.val ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  have ht := time.isLt
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change 1+margin < responseExtent margin+1 ∧ 1+margin < responseExtent margin+1 ∧
      1+margin < responseExtent margin+1 ∧ margin+time.val < responseExtent margin+1
    unfold responseExtent centralExtent
    exact ⟨by omega, by omega, by omega, by omega⟩
  · change margin+time.val ≤ responseExtent margin
    unfold responseExtent centralExtent
    omega

/-- Four temporal faces in lower plaquette word order A,B,C,D. -/
def baseLayer (time : Nat) : List Z4Plaq :=
  [((1,1,1,time),.p03), ((2,1,1,time),.p13),
    ((1,2,1,time),.p03), ((1,1,1,time),.p13)]

def baseSides : List Z4Plaq := baseLayer 0 ++ baseLayer 1 ++ baseLayer 2

/-- The same twelve faces, bulk translated with the actual response family. -/
def tubeSides (margin : Nat) : List Z4Plaq := baseSides.map (shiftFace margin margin)

theorem tubeSides_length (margin : Nat) : (tubeSides margin).length = 12 := by
  rw [tubeSides, List.length_map]
  rfl

theorem tubeSides_nodup (margin : Nat) : (tubeSides margin).Nodup :=
  nodup_map_of_injOn _ _ (by decide +kernel : baseSides.Nodup)
    (fun _ _ _ _ => shiftFace_injective margin margin)

private theorem baseSides_physical : ∀ face, face ∈ baseSides → face ∈ boundaryCompleteSlabPlaquettes 3 := by
  have h : baseSides.all (fun face => decide (face ∈ boundaryCompleteSlabPlaquettes 3)) = true := by decide +kernel
  intro face hf
  exact of_decide_eq_true (List.all_eq_true.mp h face hf)

theorem tubeSides_physical (margin : Nat) :
    ∀ face, face ∈ tubeSides margin → face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  intro face hf
  obtain ⟨f,hbase,rfl⟩ := List.mem_map.mp hf
  exact shiftFace_mem (by unfold responseExtent centralExtent; omega)
    (by unfold responseExtent centralExtent; omega) (baseSides_physical f hbase)

def sliceLinks (margin time : Nat) : List Z4Link :=
  [((1+margin,1+margin,1+margin,margin+time),.x0),
   ((2+margin,1+margin,1+margin,margin+time),.x1),
   ((1+margin,2+margin,1+margin,margin+time),.x0),
   ((1+margin,1+margin,1+margin,margin+time),.x1)]

theorem slice_word_links (margin time : Nat) :
    [faceLinkA (sliceFace margin time), faceLinkB (sliceFace margin time),
      faceLinkC (sliceFace margin time), faceLinkD (sliceFace margin time)] = sliceLinks margin time := by
  simp [sliceFace, sliceLinks, faceLinkA, faceLinkB, faceLinkC, faceLinkD, dirsOf, addE, Nat.add_comm, Nat.add_left_comm]

/-- Each selected side joins the literal corresponding lower/upper link.
This is an ordered equality of link lists, not a cardinality comparison. -/
theorem layer_link_pairs (margin time : Nat) :
    ((baseLayer time).map (shiftFace margin margin)).map (fun face => (faceLinkA face,faceLinkC face)) =
      (sliceLinks margin time).zip (sliceLinks margin (time+1)) := by
  simp [baseLayer, shiftFace, shiftVertex, sliceLinks, faceLinkA, faceLinkC, dirsOf, addE,
    Nat.add_comm, Nat.add_assoc]

end YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.responseExtent
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.sliceFace
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.base_probe_face
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.lower_shifted_probe_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.upper_shifted_probe_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.endpoint_reflection
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.endpoint_separation
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.slice_physical
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.tubeSides
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.tubeSides_length
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.tubeSides_nodup
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.tubeSides_physical
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.slice_word_links
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry.layer_link_pairs
