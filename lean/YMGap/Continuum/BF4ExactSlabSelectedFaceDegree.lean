/-
# Light selected-face degree layer for the exact BF4 slab

This module isolates the exposed-block incidence facts used by selected-face
Haar arguments.  It derives block independence from the literal link
geometry and therefore does not import the full reflection covariance
computation or a polynomial truth table.
-/

import YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.BF4ExactSlabSelectedFaceDegree

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

/-- Slab-link block occupied by the canonical exposed link. -/
def exactFixedFaceExposedBlock (face : Z4Plaq) : Nat :=
  (boundaryCompleteSlabLinks 1).idxOf
    (exactFixedFaceExposedLink face)

theorem exactFixedFaceExposedBlock_lt
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceExposedBlock face < 116 := by
  unfold exactFixedFaceExposedBlock
  rw [← correctedSlabLinks_extent_one_length]
  exact List.idxOf_lt_length_of_mem
    (exactFixedFaceExposedLink_spec hface).2.1

private theorem fixedFace_mem_complete
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    face ∈ boundaryCompleteSlabPlaquettes 1 := by
  have hpartition : face ∈ exactCorrectedSlabPartitionedFaces := by
    unfold exactCorrectedSlabPartitionedFaces
    simp [hface]
  exact (List.Perm.mem_iff
    exactCorrectedSlabPartitionedFaces_perm).mp hpartition

private def otherFaceEntryBlockCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun selected =>
    exactCorrectedSlabFixedFaces.all (fun other =>
      if decide (other = selected) then true
      else (orientedPlaquetteBoundary other).all (fun entry =>
        decide (exactFixedFaceExposedBlock selected ≠
          (boundaryCompleteSlabLinks 1).idxOf entry.link))))

private theorem otherFaceEntryBlock_check :
    otherFaceEntryBlockCheck = true := by
  decide

private theorem otherFaceEntry_block_ne
    {selected other : Z4Plaq} {entry : OrientedBF4Link}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ selected)
    (hentry : entry ∈ orientedPlaquetteBoundary other) :
    exactFixedFaceExposedBlock selected ≠
      (boundaryCompleteSlabLinks 1).idxOf entry.link := by
  have hselectedRow := List.all_eq_true.mp
    otherFaceEntryBlock_check selected hselected
  have hotherRow := List.all_eq_true.mp hselectedRow other hother
  simp [hne] at hotherRow
  exact hotherRow entry hentry

private theorem hasPolyQuaternionBlockDegree_one
    (block : Nat) :
    HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one := by
  constructor
  · exact hasQuaternionBlockDegree_one block
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0

private theorem otherFaceEntry_blockDegree_zero
    {selected other : Z4Plaq} {entry : OrientedBF4Link}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ selected)
    (hentry : entry ∈ orientedPlaquetteBoundary other) :
    HasPolyQuaternionBlockDegree
      (exactFixedFaceExposedBlock selected) 0
      (orientedCorrectedSlabLinkPolynomial 1 entry) := by
  have hlink := orientedPlaquetteBoundary_link_mem_slab
    (fixedFace_mem_complete hother) hentry
  have hblockNe := otherFaceEntry_block_ne
    hselected hother hne hentry
  have hcoordinate :=
    hasPolyQuaternionBlockDegree_coordinateVariable
      ((boundaryCompleteSlabLinks 1).idxOf entry.link)
      (exactFixedFaceExposedBlock selected)
  have hzero :
      HasPolyQuaternionBlockDegree
        (exactFixedFaceExposedBlock selected) 0
        (PolyQuaternion.coordinateVariable
          ((boundaryCompleteSlabLinks 1).idxOf entry.link)) := by
    exact HasPolyQuaternionBlockDegree.relabel
      (if_neg hblockNe) hcoordinate
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem hlink]
  cases hreverse : entry.reverse with
  | false => simpa [hreverse] using hzero
  | true => simpa [hreverse] using hzero.conj

private theorem otherFaceWordFold_blockDegree_zero
    {selected other : Z4Plaq}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ selected) :
    ∀ (entries : List OrientedBF4Link) (total : PolyQuaternion),
      HasPolyQuaternionBlockDegree
        (exactFixedFaceExposedBlock selected) 0 total →
      (∀ entry, entry ∈ entries →
        entry ∈ orientedPlaquetteBoundary other) →
      HasPolyQuaternionBlockDegree
        (exactFixedFaceExposedBlock selected) 0
        (entries.foldl
          (fun product entry => PolyQuaternion.mul product
            (orientedCorrectedSlabLinkPolynomial 1 entry)) total)
  | [], total, htotal, _ => htotal
  | entry :: rest, total, htotal, hentries => by
      simp only [List.foldl_cons]
      apply otherFaceWordFold_blockDegree_zero
        hselected hother hne rest
      · exact HasPolyQuaternionBlockDegree.relabel (by omega)
          (htotal.mul
            (otherFaceEntry_blockDegree_zero hselected hother hne
              (hentries entry List.mem_cons_self)))
      · intro item hitem
        exact hentries item (List.mem_cons_of_mem entry hitem)

/-- Every other fixed-face scalar is independent of the selected exposed
block.  The proof follows the four literal link incidences rather than
enumerating expanded plaquette monomials. -/
theorem otherFaceScalar_degree_zero
    {selected other : Z4Plaq}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ selected) :
    HasQuaternionBlockDegree (exactFixedFaceExposedBlock selected) 0
      (correctedSlabPlaquettePolynomial 1 other).scalar := by
  have hword :
      HasPolyQuaternionBlockDegree
        (exactFixedFaceExposedBlock selected) 0
        (correctedSlabPlaquettePolynomial 1 other) := by
    unfold correctedSlabPlaquettePolynomial
    apply otherFaceWordFold_blockDegree_zero hselected hother hne
      (orientedPlaquetteBoundary other) PolyQuaternion.one
      (hasPolyQuaternionBlockDegree_one _)
    intro entry hentry
    exact hentry
  exact hword.scalar

end YMGap.Continuum.BF4ExactSlabSelectedFaceDegree

#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegree.exactFixedFaceExposedBlock_lt
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegree.otherFaceScalar_degree_zero
