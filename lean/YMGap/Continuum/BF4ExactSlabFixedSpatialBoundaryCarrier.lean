/-
# A width-only carrier for the ORIGINAL two-layer boundary kernel

Enumerate the spatial box on slices zero and two once, then place this
same finite list on the two ambient endpoint slices. The explicit room
guards guarantee that even the unused box-fringe coordinates are physical.
Compressing the actual `gluedMiddle` along this embedding reconstructs it
on the ambient carrier and preserves its Haar integral exactly.

This constructs a fixed-size two-endpoint polynomial carrier, not yet a
single-slice transfer operator, its powers, or its stationary vacuum.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
import YMGap.Continuum.SU2QuaternionHaarBlockCompression

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local infix:50 " ≈ " => Q'.eqv
local notation "nlinks" extent => List.length (boundaryCompleteSlabLinks extent)

local instance (width time : Nat) (link : Z4Link) : Decidable (SliceLink width time link) := by
  unfold SliceLink
  infer_instance

local instance (width start : Nat) (link : Z4Link) : Decidable (BoundaryLink width start link) := by
  unfold BoundaryLink
  infer_instance

private theorem slice_physical {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    {link : Z4Link} (hl : SliceLink width time link) :
    link ∈ boundaryCompleteSlabLinks extent := by
  rcases link with ⟨⟨x,y,z,t⟩,dir⟩
  obtain ⟨hd,hx,hy,hz,he⟩ := hl
  have hp (plane : Z4Plane) (ha : plaquetteTimeAdmissible extent ((x,y,z,t),plane)) :
      ((x,y,z,t),plane) ∈ boundaryCompleteSlabPlaquettes extent := by
    apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
    refine ⟨(mem_boxPlaquettes _ _).mpr ?_,ha⟩
    dsimp only at hx hy hz he ⊢
    exact ⟨by omega,by omega,by omega,by omega⟩
  cases dir
  · exact (mem_boundaryCompleteSlabLinks_iff _ _).mpr
      ⟨((x,y,z,t),.p01),hp .p01 (by change t ≤ extent; dsimp only at he; omega),
        by simp [edgesOf,dirsOf]⟩
  · exact (mem_boundaryCompleteSlabLinks_iff _ _).mpr
      ⟨((x,y,z,t),.p01),hp .p01 (by change t ≤ extent; dsimp only at he; omega),
        by simp [edgesOf,dirsOf]⟩
  · exact (mem_boundaryCompleteSlabLinks_iff _ _).mpr
      ⟨((x,y,z,t),.p02),hp .p02 (by change t ≤ extent; dsimp only at he; omega),
        by simp [edgesOf,dirsOf]⟩
  · exact False.elim (hd rfl)

private theorem boundary_physical {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+2 ≤ extent) {link : Z4Link}
    (hl : BoundaryLink width start link) : link ∈ boundaryCompleteSlabLinks extent :=
  hl.elim (slice_physical hw (by omega)) (slice_physical hw ht)

/-- This enumeration depends only on spatial width, not ambient volume/time/cutoff. -/
def baseLinks (width : Nat) : List Z4Link :=
  (boundaryCompleteSlabLinks (width+2)).filter fun link => decide (BoundaryLink width 0 link)

theorem baseLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ baseLinks width ↔ BoundaryLink width 0 link := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨boundary_physical (by omega) (by omega) h,decide_eq_true h⟩

theorem baseLinks_nodup (width : Nat) : (baseLinks width).Nodup :=
  List.filter_sublist.nodup (boundaryCompleteSlabLinks_nodup _)

def boundaryLinks (width start : Nat) : List Z4Link :=
  (baseLinks width).map (timeShiftLink start)

private theorem shift_slice {width time : Nat} {link : Z4Link} (h : SliceLink width time link)
    (start : Nat) : SliceLink width (time+start) (timeShiftLink start link) := by
  rcases link with ⟨⟨x,y,z,t⟩,dir⟩
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,congrArg (fun t => t+start) h.2.2.2.2⟩

theorem boundaryLinks_mem_iff (width start : Nat) (link : Z4Link) :
    link ∈ boundaryLinks width start ↔ BoundaryLink width start link := by
  constructor
  · intro h
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp h
    rcases (baseLinks_mem_iff width l).mp hl with h | h
    · exact Or.inl (by simpa only [Nat.zero_add] using shift_slice h start)
    · exact Or.inr (by simpa only [Nat.add_comm 2 start] using shift_slice h start)
  · intro h
    rcases link with ⟨⟨x,y,z,t⟩,dir⟩
    have hl : BoundaryLink width 0 ((x,y,z,t-start),dir) := by
      rcases h with h | h
      · exact Or.inl ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,by have := h.2.2.2.2; dsimp only at this ⊢; omega⟩
      · exact Or.inr ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,by have := h.2.2.2.2; dsimp only at this ⊢; omega⟩
    apply List.mem_map.mpr
    refine ⟨((x,y,z,t-start),dir),(baseLinks_mem_iff width _).mpr hl,?_⟩
    have ht : start ≤ t := h.elim
      (fun h => by have := h.2.2.2.2; dsimp only at this; omega)
      (fun h => by have := h.2.2.2.2; dsimp only at this; omega)
    simp only [timeShiftLink,timeShiftVertex,Nat.sub_add_cancel ht]

private theorem shift_injective (start : Nat) {a b : Z4Link}
    (h : timeShiftLink start a = timeShiftLink start b) : a = b := by
  rcases a with ⟨⟨x,y,z,t⟩,d⟩
  rcases b with ⟨⟨x',y',z',t'⟩,d'⟩
  simpa only [timeShiftLink,timeShiftVertex,Prod.mk.injEq,Nat.add_right_cancel_iff] using h

theorem boundaryLinks_nodup (width start : Nat) : (boundaryLinks width start).Nodup :=
  nodup_map_of_injOn _ _ (baseLinks_nodup width) (fun _ _ _ _ => shift_injective start)

theorem boundaryLinks_physical {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    {link : Z4Link} (hl : link ∈ boundaryLinks width start) : link ∈ boundaryCompleteSlabLinks extent :=
  boundary_physical hw ht ((boundaryLinks_mem_iff width start link).mp hl)

/-- A computed placement of one width-only carrier into the original slab. -/
def embedding {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent) :
    BlockEmbedding (baseLinks width).length (nlinks extent) where
  image := (boundaryLinks width start).map (boundaryCompleteSlabLinks extent).idxOf
  length := by rw [List.length_map,boundaryLinks,List.length_map]
  nodup := nodup_map_of_injOn _ _ (boundaryLinks_nodup width start)
    (fun _ ha _ hb => idxOf_injective_on_members (boundaryLinks_physical hw ht ha)
      (boundaryLinks_physical hw ht hb))
  physical := by
    intro b hb
    obtain ⟨link,hl,rfl⟩ := List.mem_map.mp hb
    exact List.idxOf_lt_length_of_mem (boundaryLinks_physical hw ht hl)

theorem embedding_mem_iff {width start extent b : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (hb : b < nlinks extent) :
    b ∈ (embedding hw ht).image ↔ BoundaryLink width start (correctedSlabLinkAt extent b) := by
  constructor
  · intro h
    obtain ⟨link,hl,rfl⟩ := List.mem_map.mp h
    rw [correctedSlabLinkAt_idxOf (boundaryLinks_physical hw ht hl)]
    exact (boundaryLinks_mem_iff width start link).mp hl
  · intro h
    have hl := (boundaryLinks_mem_iff width start _).mpr h
    apply List.mem_map.mpr
    refine ⟨correctedSlabLinkAt extent b,hl,?_⟩
    apply correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem (boundaryLinks_physical hw ht hl)))
      (List.mem_range.mpr hb)
    exact correctedSlabLinkAt_idxOf (boundaryLinks_physical hw ht hl)

private theorem glued_local {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (w : Q') (K : Nat) :
    BlockLocal (nlinks extent) (fun b => b ∈ (embedding hw ht).image)
      (gluedMiddle w K extent width start) := by
  intro term hm b hb hn
  exact gluedMiddle_local w K extent width start term hm b hb
    (fun h => hn ((embedding_mem_iff hw ht hb).mpr h))

def kernel {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (w : Q') (K : Nat) : RatPoly :=
  (embedding hw ht).compress (gluedMiddle w K extent width start)

theorem kernel_supported {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (w : Q') (K : Nat) : SupportedQuaternionBlocks (baseLinks width).length (kernel hw ht w K) :=
  (embedding hw ht).compress_supported _

/-- Reconstruction, not just equality of one scalar moment. -/
theorem kernel_reconstructs {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (w : Q') (K : Nat) : QuaternionPrefixPolynomialEqv (nlinks extent)
      ((embedding hw ht).polynomial (kernel hw ht w K)) (gluedMiddle w K extent width start) :=
  (embedding hw ht).polynomial_compress_prefix _ (glued_local hw ht w K)

theorem kernel_haar {width start extent : Nat} (hw : width ≤ extent) (ht : start+2 ≤ extent)
    (w : Q') (K : Nat) :
    quaternionHaar (nlinks extent) (gluedMiddle w K extent width start) ≈
      quaternionHaar (baseLinks width).length (kernel hw ht w K) :=
  (embedding hw ht).haar_compress _ (gluedMiddle_supported w K extent width start) (glued_local hw ht w K)

end YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.baseLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.baseLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.baseLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.boundaryLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.boundaryLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.boundaryLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.boundaryLinks_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.embedding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.embedding_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.kernel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.kernel_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.kernel_reconstructs
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier.kernel_haar
