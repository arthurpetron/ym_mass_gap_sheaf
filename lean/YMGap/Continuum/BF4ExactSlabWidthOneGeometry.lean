/-
# Literal width-one geometry for an original-action seed test

Pin the original numeric ordering of the nine spatial-action links, the
three spatial faces and the three active kinetic coordinates. Every
width-one spatial face touches the inactive fringe, so its fully-active
face sublist is empty. Unused retained Haar coordinates are not removed.

Only finite geometry is reduced here: no heat polynomial, terminal message,
source budget or spectral statement is evaluated. The prospective probe at
the origin x2 link is active but its quaternion scalar is not gauge-invariant.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight

namespace YMGap.Continuum.BF4ExactSlabWidthOneGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces temporalFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight (activeSpatialFaces)

section LiteralEnumeration

-- The original box enumeration is deeper than the default recursion limit.
-- Only the fixed finite geometric certificates use this local setting.
set_option maxRecDepth 10000

/-- The inclusive original carrier retains its unused box-fringe links. -/
theorem baseLinks_length : (baseLinks 1).length = 24 := by decide

theorem origin_x0_index : (baseLinks 1).idxOf ((0,0,0,0), Dir4.x0) = 0 := by decide

theorem origin_x1_index : (baseLinks 1).idxOf ((0,0,0,0), Dir4.x1) = 1 := by decide

theorem far01_x0_index : (baseLinks 1).idxOf ((0,1,0,0), Dir4.x0) = 2 := by decide

theorem far01_x1_index : (baseLinks 1).idxOf ((1,0,0,0), Dir4.x1) = 3 := by decide

theorem origin_x2_index : (baseLinks 1).idxOf ((0,0,0,0), Dir4.x2) = 4 := by decide

theorem far02_x0_index : (baseLinks 1).idxOf ((0,0,1,0), Dir4.x0) = 5 := by decide

theorem far02_x2_index : (baseLinks 1).idxOf ((1,0,0,0), Dir4.x2) = 6 := by decide

theorem far12_x1_index : (baseLinks 1).idxOf ((0,0,1,0), Dir4.x1) = 7 := by decide

theorem far12_x2_index : (baseLinks 1).idxOf ((0,1,0,0), Dir4.x2) = 8 := by decide

/-- The complete original spatial face list, not a selected action packet. -/
theorem spatialFaces_one : spatialFaces 1 =
    [((0,0,0,0), Z4Plane.p01), ((0,0,0,0), Z4Plane.p02), ((0,0,0,0), Z4Plane.p12)] := by
  decide

theorem temporalFaces_one : temporalFaces 1 =
    [((0,0,0,0), Z4Plane.p03), ((0,0,0,0), Z4Plane.p13), ((0,0,0,0), Z4Plane.p23)] := by
  decide

end LiteralEnumeration

theorem activeBlocks_one : activeBlocks 1 = [0,1,4] := by
  rw [activeBlocks, temporalFaces_one]
  change [(baseLinks 1).idxOf ((0,0,0,0), Dir4.x0),
    (baseLinks 1).idxOf ((0,0,0,0), Dir4.x1),
    (baseLinks 1).idxOf ((0,0,0,0), Dir4.x2)] = [0,1,4]
  rw [origin_x0_index, origin_x1_index, origin_x2_index]

/-- Each original spatial face has a far edge outside the kinetic list. -/
theorem activeSpatialFaces_one : activeSpatialFaces 1 = [] := by
  have h01 : ¬ FullyActive 1 ((0,0,0,0), Z4Plane.p01) := by
    intro h
    have ha := h ((0,1,0,0), Dir4.x0) (by decide)
    rw [far01_x0_index, activeBlocks_one] at ha
    exact (by decide : ¬ ((2 : Nat) ∈ [0,1,4])) ha
  have h02 : ¬ FullyActive 1 ((0,0,0,0), Z4Plane.p02) := by
    intro h
    have ha := h ((0,0,1,0), Dir4.x0) (by decide)
    rw [far02_x0_index, activeBlocks_one] at ha
    exact (by decide : ¬ ((5 : Nat) ∈ [0,1,4])) ha
  have h12 : ¬ FullyActive 1 ((0,0,0,0), Z4Plane.p12) := by
    intro h
    have ha := h ((0,0,1,0), Dir4.x1) (by decide)
    rw [far12_x1_index, activeBlocks_one] at ha
    exact (by decide : ¬ ((7 : Nat) ∈ [0,1,4])) ha
  simp only [activeSpatialFaces, spatialFaces_one, List.filter_cons, List.filter_nil,
    decide_eq_false h01, decide_eq_false h02, decide_eq_false h12, Bool.false_eq_true,
    ↓reduceIte]

theorem action_fringe_mem (i : Nat) (hi : i ∈ [2,3,5,6,7,8]) : i ∈ fringeBlocks 1 := by
  apply (fringeBlocks_mem_iff 1 i).mpr
  constructor
  · rw [baseLinks_length]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  · rw [activeBlocks_one]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega

theorem probe_active : (4 : Nat) ∈ activeBlocks 1 := by
  rw [activeBlocks_one]
  decide

theorem early_fringe : (2 : Nat) ∈ fringeBlocks 1 := action_fringe_mem 2 (by decide)

end YMGap.Continuum.BF4ExactSlabWidthOneGeometry

#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.baseLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.origin_x0_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.origin_x1_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far01_x0_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far01_x1_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.origin_x2_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far02_x0_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far02_x2_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far12_x1_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.far12_x2_index
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.spatialFaces_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.temporalFaces_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.activeBlocks_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.activeSpatialFaces_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.action_fringe_mem
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.probe_active
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneGeometry.early_fringe
