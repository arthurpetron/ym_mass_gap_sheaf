/-
# Exposed-link independence at every odd slab extent

Every central crossing face has a lower spatial link A. The other three
links are fixed, upper, and fixed; distinct crossing faces have distinct
A links. Thus every other crossing-face character has degree zero in the
selected A block, at arbitrary spin and extent. The complete product of
all other characters retains this independence, including shared links.

These are structural incidence and degree proofs, with no finite slab
scan. They supply the geometric input for high-spin cutoff selection;
they do not themselves assert cutoff convergence or a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePathGram
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold

namespace YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

private theorem spatial_not_fixed (half time : Nat) : spatialHalfSide half time ≠ .fixed := by
  unfold spatialHalfSide
  split <;> decide

theorem fixed_face_plane {half : Nat} {face : Z4Plaq}
    (hf : plaquetteHalfSide half face = .fixed) :
    face.2 = .p03 ∨ face.2 = .p13 ∨ face.2 = .p23 := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := face
  cases plane
  · exact False.elim (spatial_not_fixed half time hf)
  · exact False.elim (spatial_not_fixed half time hf)
  · exact Or.inl rfl
  · exact False.elim (spatial_not_fixed half time hf)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The lower spatial link determines its crossing face uniquely. -/
theorem fixed_face_eq_of_exposed_eq {half : Nat} {selected other : Z4Plaq}
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed)
    (he : faceLinkA selected = faceLinkA other) : selected = other := by
  have hb : selected.1 = other.1 := congrArg (fun link : Z4Link => link.1) he
  have hd : (dirsOf selected.2).1 = (dirsOf other.2).1 := congrArg Prod.snd he
  have hp : selected.2 = other.2 := by
    rcases fixed_face_plane hs with hs | hs | hs <;>
      rcases fixed_face_plane ho with ho | ho | ho <;> simp_all [dirsOf]
  exact Prod.ext hb hp

/-- No boundary link of another central crossing face is this exposed link. -/
theorem exposed_link_not_in_other {half : Nat} {selected other : Z4Plaq}
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected)
    {entry : OrientedBF4Link} (he : entry ∈ orientedPlaquetteBoundary other) :
    faceLinkA selected ≠ entry.link := by
  have hss := crossing_face_path_sides hs
  have hos := crossing_face_path_sides ho
  change entry ∈ [⟨faceLinkA other, false⟩, ⟨faceLinkB other, false⟩,
    ⟨faceLinkC other, true⟩, ⟨faceLinkD other, true⟩] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fun h => hne (fixed_face_eq_of_exposed_eq ho hs h.symm)
  · intro h
    have hh := congrArg (linkHalfSide half) h
    rw [hss.1, hos.2.1] at hh
    cases hh
  · intro h
    have hh := congrArg (linkHalfSide half) h
    rw [hss.1, hos.2.2.1] at hh
    cases hh
  · intro h
    have hh := congrArg (linkHalfSide half) h
    rw [hss.1, hos.2.2.2] at hh
    cases hh

/-- Actual original slab coordinate, not an independent replacement link. -/
def exposedBlock (half : Nat) (face : Z4Plaq) : Nat :=
  (boundaryCompleteSlabLinks (centralExtent half)).idxOf (faceLinkA face)

theorem exposed_link_physical {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    faceLinkA face ∈ boundaryCompleteSlabLinks extent :=
  (mem_boundaryCompleteSlabLinks_iff extent _).mpr ⟨face, hf, by simp [faceLinkA, edgesOf]⟩

theorem exposedBlock_lt {half : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    exposedBlock half face < (boundaryCompleteSlabLinks (centralExtent half)).length :=
  List.idxOf_lt_length_of_mem (exposed_link_physical hf)

theorem other_entry_block_ne {half : Nat} {selected other : Z4Plaq}
    (hsp : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hop : other ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected)
    {entry : OrientedBF4Link} (he : entry ∈ orientedPlaquetteBoundary other) :
    exposedBlock half selected ≠
      (boundaryCompleteSlabLinks (centralExtent half)).idxOf entry.link := by
  intro hh
  exact exposed_link_not_in_other hs ho hne he
    (idxOf_injective_on_members (exposed_link_physical hsp)
      (orientedPlaquetteBoundary_link_mem_slab hop he) hh)

private theorem quaternion_one_degree_zero (block : Nat) :
    HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one :=
  ⟨hasQuaternionBlockDegree_one block, hasQuaternionBlockDegree_zero block 0,
    hasQuaternionBlockDegree_zero block 0, hasQuaternionBlockDegree_zero block 0⟩

private theorem other_entry_degree_zero {half : Nat} {selected other : Z4Plaq}
    (hsp : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hop : other ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected)
    {entry : OrientedBF4Link} (he : entry ∈ orientedPlaquetteBoundary other) :
    HasPolyQuaternionBlockDegree (exposedBlock half selected) 0
      (orientedCorrectedSlabLinkPolynomial (centralExtent half) entry) := by
  have hn := other_entry_block_ne hsp hop hs ho hne he
  have hz := HasPolyQuaternionBlockDegree.relabel (if_neg hn)
    (hasPolyQuaternionBlockDegree_coordinateVariable
      ((boundaryCompleteSlabLinks (centralExtent half)).idxOf entry.link)
      (exposedBlock half selected))
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem (orientedPlaquetteBoundary_link_mem_slab hop he)]
  cases hr : entry.reverse with
  | false => simpa only [hr] using hz
  | true => simpa only [hr] using hz.conj

private theorem other_fold_degree_zero {half : Nat} {selected other : Z4Plaq}
    (hsp : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hop : other ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected) :
    ∀ (entries : List OrientedBF4Link) (total : PolyQuaternion),
      HasPolyQuaternionBlockDegree (exposedBlock half selected) 0 total →
      (∀ entry, entry ∈ entries → entry ∈ orientedPlaquetteBoundary other) →
      HasPolyQuaternionBlockDegree (exposedBlock half selected) 0
        (entries.foldl (fun p e => PolyQuaternion.mul p
          (orientedCorrectedSlabLinkPolynomial (centralExtent half) e)) total)
  | [], _, ht, _ => ht
  | e :: rest, total, ht, he => by
    apply other_fold_degree_zero hsp hop hs ho hne rest
    · exact HasPolyQuaternionBlockDegree.relabel (by omega)
        (ht.mul (other_entry_degree_zero hsp hop hs ho hne (he e List.mem_cons_self)))
    · exact fun e hh => he e (List.mem_cons_of_mem _ hh)

/-- Arbitrary spin on the other face; no spin enters its exposed degree. -/
theorem other_character_degree_zero {half : Nat} {selected other : Z4Plaq}
    (hsp : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hop : other ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected) (spin : Nat) :
    HasQuaternionBlockDegree (exposedBlock half selected) 0
      (characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half) other).scalar spin) :=
  characterPolynomial_blockDegree_zero
    (other_fold_degree_zero hsp hop hs ho hne _ _ (quaternion_one_degree_zero _)
      (fun _ h => h)).scalar spin

/-- Every other physical face factor remains, with unrestricted labels. -/
theorem other_characters_degree_zero {half : Nat} {selected : Z4Plaq}
    (hsp : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed) (spin : Z4Plaq → Nat) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces → face ∈ boundaryCompleteSlabPlaquettes (centralExtent half) ∧
        plaquetteHalfSide half face = .fixed ∧ face ≠ selected) →
      HasQuaternionBlockDegree (exposedBlock half selected) 0
        (faces.foldr (fun face p => polyMul
          (characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half) face).scalar
            (spin face)) p) polyOne)
  | [], _ => hasQuaternionBlockDegree_one _
  | face :: rest, h => by
    have hf := h face List.mem_cons_self
    exact HasQuaternionBlockDegree.relabel (by omega)
      ((other_character_degree_zero hsp hf.1 hs hf.2.1 hf.2.2 (spin face)).mul
        (other_characters_degree_zero hsp hs spin rest (fun f hf => h f (List.mem_cons_of_mem _ hf))))

end YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.fixed_face_plane
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.fixed_face_eq_of_exposed_eq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.exposed_link_not_in_other
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.exposedBlock
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.exposed_link_physical
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.exposedBlock_lt
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.other_entry_block_ne
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.other_character_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree.other_characters_degree_zero
