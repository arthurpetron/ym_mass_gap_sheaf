/-
# Retiming spatial plaquettes preserves their projected boundary

The projection keeps the spatial base and plane and replaces only time.
Equal projected boundary indicators determine the projected plaquette.
Its original time then recovers the original plaquette without a choice.
-/

import YMGap.Continuum.Z4PlaquetteBoundaryRigidity
import YMGap.Continuum.Z4FiniteTemporalSpatialSources

namespace YMGap.Continuum.Z4SpatialPlaquetteProjection

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity

def faceAt (time : Nat) (face : Z4Plaq) : Z4Plaq :=
  ((face.1.1,face.1.2.1,face.1.2.2.1,time),face.2)

theorem faceAt_own (face : Z4Plaq) : faceAt face.1.2.2.2 face=face := rfl

theorem faceAt_twice (s t : Nat) (face : Z4Plaq) : faceAt s (faceAt t face)=faceAt s face := rfl

theorem projection_and_time_injective (left right : Z4Plaq)
    (hp : faceAt 0 left=faceAt 0 right) (ht : left.1.2.2.2=right.1.2.2.2) : left=right := by
  have h := congrArg (faceAt left.1.2.2.2) hp
  rw [faceAt_twice,faceAt_twice,faceAt_own,ht,faceAt_own] at h
  exact h

theorem spatial_boundary_dir (face : Z4Plaq) (hs : (dirsOf face.2).2 ≠ Dir4.x3)
    (link : Z4Link) (hl : link ∈ edgesOf face) : link.2 ≠ Dir4.x3 := by
  rcases face with ⟨v,p⟩
  cases p <;> simp only [dirsOf, ne_eq] at hs
  all_goals try exact False.elim (hs True.intro)
  all_goals
    simp only [edgesOf, dirsOf, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem spatial_edges_retime (time : Nat) (face : Z4Plaq)
    (hs : (dirsOf face.2).2 ≠ Dir4.x3) :
    edgesOf (faceAt time face)=(edgesOf face).map (atTime time) := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp only [dirsOf, ne_eq] at hs
  all_goals first | exact False.elim (hs True.intro) | rfl

theorem retimed_spatial_boundary_mem (time : Nat) (face : Z4Plaq)
    (hs : (dirsOf face.2).2 ≠ Dir4.x3) (link : Z4Link) :
    atTime time link ∈ edgesOf (faceAt time face) ↔ atTime face.1.2.2.2 link ∈ edgesOf face := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  rcases link with ⟨⟨x,y,z,s⟩,d⟩
  cases p <;> simp only [dirsOf, ne_eq] at hs
  all_goals try exact False.elim (hs True.intro)
  all_goals
    simp only [faceAt, atTime, edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq, and_true]

theorem projected_boundary_eq (left right : Z4Plaq)
    (hl : (dirsOf left.2).2 ≠ Dir4.x3) (hr : (dirsOf right.2).2 ≠ Dir4.x3)
    (hp : ∀ link : Z4Link, link.2 ≠ Dir4.x3 →
      (atTime left.1.2.2.2 link ∈ edgesOf left ↔ atTime right.1.2.2.2 link ∈ edgesOf right)) :
    faceAt 0 left=faceAt 0 right := by
  apply boundary_subset_eq
  intro link hm
  have ht : link.1.2.2.2=0 := spatial_boundary_time (faceAt 0 left) hl link hm
  have he : atTime 0 link=link := by rw [← ht]; rfl
  have hd := spatial_boundary_dir (faceAt 0 left) hl link hm
  have hm' := (retimed_spatial_boundary_mem 0 left hl link).mp (he ▸ hm)
  have hr' := (retimed_spatial_boundary_mem 0 right hr link).mpr ((hp link hd).mp hm')
  exact he ▸ hr'

end YMGap.Continuum.Z4SpatialPlaquetteProjection

#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.faceAt
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.faceAt_own
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.faceAt_twice
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.projection_and_time_injective
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.spatial_boundary_dir
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.spatial_edges_retime
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.retimed_spatial_boundary_mem
#print axioms YMGap.Continuum.Z4SpatialPlaquetteProjection.projected_boundary_eq
