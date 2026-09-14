/-
# Original one-endpoint moments with one spatial odd face

Finite temporal conservation fixes the cap's spatial base and plane to
those of the ORIGINAL probe. Only its absolute time remains free. That
time is extracted directly from the original spatial odd-face list.
No fundamental-spin assumption or time-window restriction is imposed.
-/

import YMGap.Continuum.Z4FiniteTemporalSpatialSources
import YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

namespace YMGap.Continuum.BF4ExactSlabSingleSpatialCap

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

/-- Absolute time, which may initially lie on either side of the endpoint. -/
def capFace (margin time : Nat) : Z4Plaq :=
  ((1+margin,1+margin,1+margin,time),.p01)

theorem projected_probe_boundary_pin (margin target : Nat) (face : Z4Plaq)
    (hs : (dirsOf face.2).2 ≠ Dir4.x3)
    (hp : ∀ link : Z4Link, link.2 ≠ Dir4.x3 →
      (atTime face.1.2.2.2 link ∈ edgesOf face ↔
        atTime (margin+target) link ∈ edgesOf (sliceFace margin target))) :
    face = capFace margin face.1.2.2.2 := by
  have hd : (dirsOf face.2).1 ≠ Dir4.x3 := by
    rcases face with ⟨v,p⟩
    cases p <;> dsimp only [dirsOf] <;> decide
  have h0 := (hp (face.1,(dirsOf face.2).1) hd).mp
    (show atTime face.1.2.2.2 (face.1,(dirsOf face.2).1) ∈ edgesOf face from List.mem_cons_self)
  have h1 := (hp (face.1,(dirsOf face.2).2) hs).mp
    (show atTime face.1.2.2.2 (face.1,(dirsOf face.2).2) ∈ edgesOf face from
      List.mem_cons_of_mem _ List.mem_cons_self)
  have h2 := (hp (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1) hd).mp (by
    rcases face with ⟨⟨a,b,c,t⟩,p⟩
    cases p <;> simp only [dirsOf, ne_eq] at hs
    all_goals try exact False.elim (hs True.intro)
    all_goals
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  clear hp hd
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp only [dirsOf, ne_eq] at hs
  all_goals try exact False.elim (hs True.intro)
  all_goals simp [atTime, sliceFace, edgesOf, dirsOf, addE, Prod.mk.injEq] at h0 h1 h2
  have ha : a = 1+margin := by omega
  have hb : b = 1+margin := by omega
  have hc : c = 1+margin := by omega
  subst a
  subst b
  subst c
  rfl

theorem single_spatial_face_pin (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (cap : Z4Plaq) (hs : spatialOddFaces margin state = [cap])
    (hc : momentCheck margin lo (!lo) state = true) :
    cap = capFace margin cap.1.2.2.2 := by
  have hcap : (dirsOf cap.2).2 ≠ Dir4.x3 :=
    of_decide_eq_true (List.mem_filter.mp (show cap ∈ spatialOddFaces margin state from hs ▸ List.mem_cons_self)).2
  apply projected_probe_boundary_pin margin (if lo then 0 else 3) cap hcap
  intro link hd
  have hp := single_spatial_boundary_projection (sliceFace margin (if lo then 0 else 3)) cap
    (by change Dir4.x1 ≠ Dir4.x3; decide)
    (oddFaces (responseExtent margin) state) (oddFaces_nodup _ _) hs
    (fun ell => by
      have h := moment_odd_geometry_parity margin lo (!lo) state hc ell
      cases lo <;>
        simpa only [endpointCharge, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, Nat.zero_add, Nat.add_zero] using h) link hd
  exact hp

/-- Computed from the original list; the default is irrelevant under length one. -/
def singleCapTime (margin : Nat) (state : EdgeLabelling) : Nat :=
  ((spatialOddFaces margin state).headD (capFace margin 0)).1.2.2.2

theorem single_spatial_cap_pin (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (hs : (spatialOddFaces margin state).length = 1)
    (hc : momentCheck margin lo (!lo) state = true) :
    spatialOddFaces margin state = [capFace margin (singleCapTime margin state)] := by
  cases he : spatialOddFaces margin state with
  | nil => rw [he] at hs; contradiction
  | cons cap rest =>
    have hr : rest = [] := by
      apply List.length_eq_zero_iff.mp
      rw [he, List.length_cons] at hs
      omega
    subst rest
    have ht : singleCapTime margin state = cap.1.2.2.2 := by
      simp only [singleCapTime, he, List.headD_cons]
    rw [ht, ← single_spatial_face_pin margin lo state cap he hc]

end YMGap.Continuum.BF4ExactSlabSingleSpatialCap

#print axioms YMGap.Continuum.BF4ExactSlabSingleSpatialCap.capFace
#print axioms YMGap.Continuum.BF4ExactSlabSingleSpatialCap.projected_probe_boundary_pin
#print axioms YMGap.Continuum.BF4ExactSlabSingleSpatialCap.single_spatial_face_pin
#print axioms YMGap.Continuum.BF4ExactSlabSingleSpatialCap.singleCapTime
#print axioms YMGap.Continuum.BF4ExactSlabSingleSpatialCap.single_spatial_cap_pin
