/-
# Original spin charge is odd-face incidence modulo two

The existing all-spin charge uses oriented words and slab link indices.
This module identifies it with incidence in the distinct original faces
whose labels are odd. It does not replace the physical integrand or sum.
No connectedness, nonzero coefficient or sign follows from even parity.
-/

import YMGap.Continuum.BF4ExactSlabCenterCharge
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.BF4ExactSlabOddFaceIncidence

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

private abbrev idx (extent : Nat) (link : Z4Link) : Nat := (boundaryCompleteSlabLinks extent).idxOf link

theorem entryCharge_pin (extent : Nat) (link : Z4Link) (entry : OrientedBF4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (he : entry.link ∈ boundaryCompleteSlabLinks extent) :
    entryCharge extent (idx extent link) entry = if entry.link = link then 1 else 0 := by
  by_cases h : entry.link = link
  · simp only [entryCharge, h, ↓reduceIte]
  · have hi : idx extent link ≠ idx extent entry.link :=
      fun hh => h (idxOf_injective_on_members hl he hh).symm
    simp only [entryCharge, if_neg h, if_neg hi]

theorem wordCharge_pin (extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) :
    ∀ es : List OrientedBF4Link, (∀ e, e ∈ es → e.link ∈ boundaryCompleteSlabLinks extent) →
    wordCharge extent (idx extent link) es = occurrenceCount link (es.map OrientedBF4Link.link)
  | [], _ => rfl
  | e::es, hp => by
    rw [wordCharge, List.map_cons, occurrenceCount, entryCharge_pin extent link e hl (hp e List.mem_cons_self)]
    rw [wordCharge_pin extent link hl es (fun f hf => hp f (List.mem_cons_of_mem e hf))]

theorem faceDegree_pin (extent : Nat) (link : Z4Link) (face : Z4Plaq)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    faceDegree extent (idx extent link) face = if link ∈ edgesOf face then 1 else 0 := by
  rw [faceDegree, wordCharge_pin extent link hl _
    (fun _ he => orientedPlaquetteBoundary_link_mem_slab hf he)]
  rw [← occurrenceCount_edgesOf]
  simp only [orientedPlaquetteBoundary, edgesOf, List.map_cons, List.map_nil, occurrenceCount]
  omega

def oddSelection (extent : Nat) (labels : EdgeLabelling) (faces : List Z4Plaq) : List Z4Plaq :=
  faces.filter (fun f => decide (labels ((boundaryCompleteSlabPlaquettes extent).idxOf f) % 2 = 1))

def oddFaces (extent : Nat) (labels : EdgeLabelling) : List Z4Plaq :=
  oddSelection extent labels (boundaryCompleteSlabPlaquettes extent)

theorem oddFaces_nodup (extent : Nat) (labels : EdgeLabelling) : (oddFaces extent labels).Nodup :=
  (boundaryCompleteSlabPlaquettes_nodup extent).filter _

theorem oddFaces_physical {extent : Nat} {labels : EdgeLabelling} {face : Z4Plaq}
    (hf : face ∈ oddFaces extent labels) : face ∈ boundaryCompleteSlabPlaquettes extent :=
  (List.mem_filter.mp hf).1

theorem selectedCharge_parity (extent : Nat) (labels : EdgeLabelling) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    ∀ faces : List Z4Plaq, (∀ f, f ∈ faces → f ∈ boundaryCompleteSlabPlaquettes extent) →
    selectedCharge extent (idx extent link) labels faces % 2 =
      faceIncidenceCount link (oddSelection extent labels faces) % 2
  | [], _ => rfl
  | f::fs, hp => by
    have ih := selectedCharge_parity extent labels link hl fs (fun g hg => hp g (List.mem_cons_of_mem f hg))
    have hd := faceDegree_pin extent link f hl (hp f List.mem_cons_self)
    by_cases ho : labels ((boundaryCompleteSlabPlaquettes extent).idxOf f) % 2 = 1
    · simp only [selectedCharge, hd, oddSelection, List.filter_cons, ho, decide_true, ↓reduceIte,
        faceIncidenceCount] at ih ⊢
      by_cases he : link ∈ edgesOf f
      · simp only [if_pos he, Nat.mul_one] at *
        omega
      · simp only [if_neg he, Nat.mul_zero, Nat.zero_add] at *
        exact ih
    · have hz : labels ((boundaryCompleteSlabPlaquettes extent).idxOf f) % 2 = 0 := by omega
      simp only [selectedCharge, hd, oddSelection, List.filter_cons, ho, decide_false, Bool.false_eq_true,
        ↓reduceIte] at ih ⊢
      by_cases he : link ∈ edgesOf f
      · simp only [if_pos he, Nat.mul_one] at *
        omega
      · simp only [if_neg he, Nat.mul_zero, Nat.zero_add] at *
        exact ih

theorem totalCharge_parity (extent : Nat) (labels : EdgeLabelling) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    totalCharge extent (idx extent link) labels % 2 = faceIncidenceCount link (oddFaces extent labels) % 2 :=
  selectedCharge_parity extent labels link hl _ (fun _ h => h)

theorem incidence_outside (extent : Nat) (link : Z4Link) (hl : link ∉ boundaryCompleteSlabLinks extent) :
    ∀ faces : List Z4Plaq, (∀ f, f ∈ faces → f ∈ boundaryCompleteSlabPlaquettes extent) →
    faceIncidenceCount link faces = 0
  | [], _ => rfl
  | f::fs, hp => by
    have he : link ∉ edgesOf f := fun h => hl
      ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨f,hp f List.mem_cons_self,h⟩)
    rw [faceIncidenceCount, if_neg he, Nat.zero_add]
    exact incidence_outside extent link hl fs (fun g hg => hp g (List.mem_cons_of_mem f hg))

/-- Spatial insertions can leave vertical charge zero without being independent of the action. -/
theorem vertical_even_of_check (extent : Nat) (labels : EdgeLabelling) (charges : Nat → Nat)
    (hc : ∀ v : Z4Vertex, (v,Dir4.x3) ∈ boundaryCompleteSlabLinks extent → charges (idx extent (v,Dir4.x3)) = 0)
    (ht : insertionCheck extent labels charges = true) (v : Z4Vertex) :
    faceIncidenceCount (v,Dir4.x3) (oddFaces extent labels) % 2 = 0 := by
  by_cases hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks extent
  · have h := List.all_eq_true.mp ht (idx extent (v,Dir4.x3))
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
    have hp := of_decide_eq_true h
    rw [hc v hl, Nat.zero_add, totalCharge_parity extent labels _ hl] at hp
    exact hp
  · rw [incidence_outside extent _ hl _ (fun _ hf => oddFaces_physical hf)]

end YMGap.Continuum.BF4ExactSlabOddFaceIncidence

#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.entryCharge_pin
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.wordCharge_pin
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.faceDegree_pin
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.oddFaces
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.oddFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.oddFaces_physical
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.selectedCharge_parity
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.totalCharge_parity
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.incidence_outside
#print axioms YMGap.Continuum.BF4ExactSlabOddFaceIncidence.vertical_even_of_check
