/-
# The original pair's projected spatial faces form an even boundary cycle

The accepted moment checkers prescribe complementary endpoint charges.
Finite temporal conservation in each replica cancels these charges in
their combined spatial projection. The projected list keeps EVERY replica
occurrence; duplicates are not erased. This is an all-spin, all-volume
constraint on the original nonzero pair, with no spatial-count assumption.
-/

import YMGap.Continuum.Z4FiniteProjectedBoundaryParity
import YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode

namespace YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4FiniteProjectedBoundaryParity
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap
open YMGap.Continuum.BF4ExactSlabSingleCapDecoder
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode

local infix:50 " ≈ " => Q'.eqv

theorem endpoint_source_two (margin : Nat) (lo hi : Bool) (link : Z4Link) (time : Nat) :
    endpointCharge margin lo hi (atTime time link)=
      twoImpulses margin (margin+3) (if lo then boundaryBit margin link else 0)
        (if hi then boundaryBit margin link else 0) time := by
  change ((if lo then (if atTime time link ∈ edgesOf (capFace margin margin) then 1 else 0) else 0)+
    (if hi then (if atTime time link ∈ edgesOf (capFace margin (margin+3)) then 1 else 0) else 0))=_
  rw [cap_indicator,cap_indicator]
  cases lo <;> cases hi <;> simp only [twoImpulses,Bool.false_eq_true,↓reduceIte,ite_self]

theorem moment_projected_parity (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hc : momentCheck margin lo hi state=true) (link : Z4Link) (hd : link.2 ≠ Dir4.x3) :
    ((if lo then boundaryBit margin link else 0)+(if hi then boundaryBit margin link else 0)+
      projectedCount link (spatialOddFaces margin state))%2=0 :=
  endpoint_projected_parity margin (margin+3) _ _ link hd (oddFaces (responseExtent margin) state)
    (oddFaces_nodup _ _) (fun time => by
      rw [← endpoint_source_two margin lo hi link time]
      exact moment_odd_geometry_parity margin lo hi state hc (atTime time link))

theorem spatialList_spatial (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (face : Z4Plaq) (hf : face ∈ spatialList margin pair) : (dirsOf face.2).2 ≠ Dir4.x3 := by
  rcases List.mem_append.mp hf with hl | hr
  · exact of_decide_eq_true (List.mem_filter.mp hl).2
  · exact of_decide_eq_true (List.mem_filter.mp hr).2

theorem original_projectedCount_even (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (link : Z4Link) (hd : link.2 ≠ Dir4.x3) :
    projectedCount link (spatialList margin pair)%2=0 := by
  have hc := nonzero_pair_channel_checks margin pair hne
  have hl := moment_projected_parity margin true (jointCheck margin pair) pair.1 hc.1 link hd
  have hr := moment_projected_parity margin false (!(jointCheck margin pair)) pair.2 hc.2 link hd
  rw [spatialList,projectedCount_append]
  cases hj : jointCheck margin pair <;>
    simp only [hj,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte] at hl hr
  all_goals omega

def projectedFaces (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List Z4Plaq :=
  (spatialList margin pair).map (faceAt 0)

theorem projectedFaces_geometry (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (face : Z4Plaq) (hf : face ∈ projectedFaces margin pair) :
    (dirsOf face.2).2 ≠ Dir4.x3 ∧ face.1.2.2.2=0 := by
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hf
  exact ⟨spatialList_spatial margin pair original ho,rfl⟩

theorem incidence_zero_of_avoids (link : Z4Link) : ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → link ∉ edgesOf face) → faceIncidenceCount link faces=0
  | [], _ => rfl
  | face::faces, hs => by
    rw [faceIncidenceCount,if_neg (hs face List.mem_cons_self),Nat.zero_add]
    exact incidence_zero_of_avoids link faces (fun f hf => hs f (List.mem_cons_of_mem face hf))

theorem original_projectedFaces_closed (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (link : Z4Link) :
    faceIncidenceCount link (projectedFaces margin pair)%2=0 := by
  by_cases hd : link.2 ≠ Dir4.x3
  · by_cases ht : link.1.2.2.2=0
    · have he : atTime 0 link=link := by rw [← ht]; rfl
      have hp := original_projectedCount_even margin pair hne link hd
      rw [projectedCount_eq_incidence link _ (spatialList_spatial margin pair),he] at hp
      exact hp
    · rw [incidence_zero_of_avoids link _ (fun face hf hmem => ht
        ((spatial_boundary_time face (projectedFaces_geometry margin pair face hf).1 link hmem).trans
          (projectedFaces_geometry margin pair face hf).2))]
  · rw [incidence_zero_of_avoids link _ (fun face hf hmem => hd
      (spatial_boundary_dir face (projectedFaces_geometry margin pair face hf).1 link hmem))]

end YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle

#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.endpoint_source_two
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.moment_projected_parity
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.spatialList_spatial
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.original_projectedCount_even
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.projectedFaces
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.projectedFaces_geometry
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.incidence_zero_of_avoids
#print axioms YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle.original_projectedFaces_closed
