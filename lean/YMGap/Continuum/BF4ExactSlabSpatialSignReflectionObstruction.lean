/-
# Boundary obstruction to literal x0 sign-reflection closure

The geometric reflection x0 -> width-x0, after recanonicalizing a positive
plaquette, moves an x0-incident base to width-1-a and a transverse base to
width-a. The fourth coordinate remains physical time. The original face
families require every spatial base coordinate STRICTLY below width, while
the original slice-link carrier permits coordinates equal to width.

At every positive width, origin p12 and p13 witness the resulting failure of
spatial and temporal face-list closure. All four reflected p12 edges still
belong to the SAME inclusive base-link carrier. This is only geometry/list
nonclosure: it proves no functional inequality, failure of action invariance,
or impossibility of a completed parity operation or continuum symmetry.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

namespace YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)

/-- Recanonicalized positive face. Nat subtraction is literal; no global
involution claim outside the geometric box is made. -/
def reflectPositiveFace (width : Nat) : Z4Plaq → Z4Plaq
  | ((a,b,c,t), .p01) => ((width-1-a,b,c,t), .p01)
  | ((a,b,c,t), .p02) => ((width-1-a,b,c,t), .p02)
  | ((a,b,c,t), .p03) => ((width-1-a,b,c,t), .p03)
  | ((a,b,c,t), .p12) => ((width-a,b,c,t), .p12)
  | ((a,b,c,t), .p13) => ((width-a,b,c,t), .p13)
  | ((a,b,c,t), .p23) => ((width-a,b,c,t), .p23)

def origin12 : Z4Plaq := ((0,0,0,0), .p12)
def origin13 : Z4Plaq := ((0,0,0,0), .p13)

theorem reflected_origin12 (width : Nat) :
    reflectPositiveFace width origin12 = ((width,0,0,0), .p12) := by
  simp only [reflectPositiveFace, origin12, Nat.sub_zero]

theorem reflected_origin13 (width : Nat) :
    reflectPositiveFace width origin13 = ((width,0,0,0), .p13) := by
  simp only [reflectPositiveFace, origin13, Nat.sub_zero]

theorem origin12_spatial {width : Nat} (hw : 1 ≤ width) :
    origin12 ∈ spatialFaces width :=
  (spatialFaces_mem_iff width origin12).mpr
    ⟨(by change 0 < width; omega), (by change 0 < width; omega),
      (by change 0 < width; omega), rfl, (by decide)⟩

theorem reflected_origin12_not_spatial (width : Nat) :
    reflectPositiveFace width origin12 ∉ spatialFaces width := by
  intro h
  rw [reflected_origin12] at h
  exact Nat.lt_irrefl width ((spatialFaces_mem_iff width _).mp h).1

/-- This face is absent despite every boundary edge being an original
inclusive spatial coordinate; no unsupported/out-of-carrier edge is used. -/
theorem reflected_origin12_edges_in_baseLinks {width : Nat} (hw : 1 ≤ width) :
    ∀ link, link ∈ edgesOf (reflectPositiveFace width origin12) →
      link ∈ baseLinks width := by
  intro link hl
  rw [reflected_origin12] at hl
  simp only [edgesOf, dirsOf, addE, Nat.zero_add,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals apply (baseLinks_mem_iff width _).mpr
  all_goals simp [SliceLink, hw]

theorem origin13_temporal {width : Nat} (hw : 1 ≤ width) :
    origin13 ∈ temporalFaces width :=
  (temporalFaces_mem_iff width origin13).mpr
    ⟨(by change 0 < width; omega), (by change 0 < width; omega),
      (by change 0 < width; omega), rfl, rfl⟩

theorem reflected_origin13_not_temporal (width : Nat) :
    reflectPositiveFace width origin13 ∉ temporalFaces width := by
  intro h
  rw [reflected_origin13] at h
  exact Nat.lt_irrefl width ((temporalFaces_mem_iff width _).mp h).1

/-- In the transverse spatial bulk, ONLY the lower x0 boundary is lost.
The reflected face remains in the original family exactly when a is positive. -/
theorem transverse12_reflected_mem_iff {width a b c : Nat}
    (ha : a < width) (hb : b < width) (hc : c < width) :
    reflectPositiveFace width ((a,b,c,0), .p12) ∈ spatialFaces width ↔ 0 < a := by
  rw [spatialFaces_mem_iff]
  change (width-a < width ∧ b < width ∧ c < width ∧
    (0 : Nat) = 0 ∧ Dir4.x2 ≠ Dir4.x3) ↔ 0 < a
  constructor
  · intro h
    have hfirst := h.1
    omega
  · intro h
    exact ⟨(by omega), hb, hc, rfl, (by decide)⟩

theorem incident_origin01_reflected_spatial {width : Nat} (hw : 1 ≤ width) :
    reflectPositiveFace width ((0,0,0,0), .p01) ∈ spatialFaces width :=
  (spatialFaces_mem_iff width _).mpr
    ⟨(by change width-1-0 < width; omega), (by change 0 < width; omega),
      (by change 0 < width; omega), rfl, (by change Dir4.x1 ≠ Dir4.x3; decide)⟩

theorem incident_origin02_reflected_spatial {width : Nat} (hw : 1 ≤ width) :
    reflectPositiveFace width ((0,0,0,0), .p02) ∈ spatialFaces width :=
  (spatialFaces_mem_iff width _).mpr
    ⟨(by change width-1-0 < width; omega), (by change 0 < width; omega),
      (by change 0 < width; omega), rfl, (by change Dir4.x2 ≠ Dir4.x3; decide)⟩

theorem spatialFaces_not_closed {width : Nat} (hw : 1 ≤ width) :
    ¬ (∀ p, p ∈ spatialFaces width → reflectPositiveFace width p ∈ spatialFaces width) :=
  fun h => reflected_origin12_not_spatial width (h origin12 (origin12_spatial hw))

theorem temporalFaces_not_closed {width : Nat} (hw : 1 ≤ width) :
    ¬ (∀ p, p ∈ temporalFaces width → reflectPositiveFace width p ∈ temporalFaces width) :=
  fun h => reflected_origin13_not_temporal width (h origin13 (origin13_temporal hw))

/-- The actual spatial list is not permuted by this literal reflection. -/
theorem spatialFaces_no_perm {width : Nat} (hw : 1 ≤ width) :
    ¬ (((spatialFaces width).map (reflectPositiveFace width)).Perm (spatialFaces width)) := by
  intro h
  exact reflected_origin12_not_spatial width
    (h.mem_iff.mp (List.mem_map.mpr ⟨origin12, origin12_spatial hw, rfl⟩))

/-- The actual one-step temporal face list is likewise not permuted. -/
theorem temporalFaces_no_perm {width : Nat} (hw : 1 ≤ width) :
    ¬ (((temporalFaces width).map (reflectPositiveFace width)).Perm (temporalFaces width)) := by
  intro h
  exact reflected_origin13_not_temporal width
    (h.mem_iff.mp (List.mem_map.mpr ⟨origin13, origin13_temporal hw, rfl⟩))

end YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction

#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflectPositiveFace
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.origin12
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.origin13
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflected_origin12
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflected_origin13
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.origin12_spatial
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflected_origin12_not_spatial
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflected_origin12_edges_in_baseLinks
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.origin13_temporal
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.reflected_origin13_not_temporal
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.transverse12_reflected_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.incident_origin01_reflected_spatial
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.incident_origin02_reflected_spatial
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.spatialFaces_not_closed
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.temporalFaces_not_closed
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.spatialFaces_no_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSignReflectionObstruction.temporalFaces_no_perm
