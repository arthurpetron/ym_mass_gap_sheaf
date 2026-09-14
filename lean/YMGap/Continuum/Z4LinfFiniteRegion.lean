/-
# A fixed-size finite region containing a lattice L-infinity ball

Translate the existing four-dimensional box by the componentwise truncated
lower corner root-radius. The resulting explicit list contains every face
within the given L-infinity radius and has (2*radius+1)^4*6 entries,
independently of the root. Near the coordinate boundary it is a superset,
not an assertion that the truncated ball has that exact cardinality.
-/

import YMGap.Continuum.SepLatticeZ4Linf
import YMGap.Continuum.Z4FiniteBoxExhaustion

namespace YMGap.Continuum.Z4LinfFiniteRegion

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4FiniteBoxExhaustion

def offsetFace (root : Z4Plaq) (radius : Nat) (face : Z4Plaq) : Z4Plaq :=
  ((root.1.1-radius+face.1.1, root.1.2.1-radius+face.1.2.1,
    root.1.2.2.1-radius+face.1.2.2.1, root.1.2.2.2-radius+face.1.2.2.2), face.2)

/-- An explicit local coordinate witness, not a chosen preimage. -/
def relativeFace (root : Z4Plaq) (radius : Nat) (face : Z4Plaq) : Z4Plaq :=
  ((face.1.1-(root.1.1-radius), face.1.2.1-(root.1.2.1-radius),
    face.1.2.2.1-(root.1.2.2.1-radius), face.1.2.2.2-(root.1.2.2.2-radius)), face.2)

def region (root : Z4Plaq) (radius : Nat) : List Z4Plaq :=
  (boxPlaquettes (2*radius+1)).map (offsetFace root radius)

theorem coordinate_window (center value radius : Nat) (h : natDist center value ≤ radius) :
    center-radius ≤ value ∧ value-(center-radius) < 2*radius+1 := by
  unfold natDist at h
  constructor <;> omega

theorem relative_mem (root face : Z4Plaq) (radius : Nat) (h : linfDist root face ≤ radius) :
    relativeFace root radius face ∈ boxPlaquettes (2*radius+1) := by
  have h0 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x0) h)
  have h1 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x1) h)
  have h2 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x2) h)
  have h3 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x3) h)
  exact (mem_boxPlaquettes _ _).mpr ⟨h0.2,h1.2,h2.2,h3.2⟩

theorem offset_relative (root face : Z4Plaq) (radius : Nat) (h : linfDist root face ≤ radius) :
    offsetFace root radius (relativeFace root radius face) = face := by
  have h0 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x0) h)
  have h1 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x1) h)
  have h2 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x2) h)
  have h3 := coordinate_window _ _ radius (Nat.le_trans (le_linfDist_comp root face .x3) h)
  rcases root with ⟨⟨a,b,c,t⟩,p⟩
  rcases face with ⟨⟨x,y,z,s⟩,q⟩
  dsimp only [cPlaq, vComp] at h0 h1 h2 h3
  simp only [offsetFace, relativeFace, Prod.mk.injEq]
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,True.intro⟩

theorem mem_region_of_linf (root face : Z4Plaq) (radius : Nat) (h : linfDist root face ≤ radius) :
    face ∈ region root radius :=
  List.mem_map.mpr ⟨relativeFace root radius face,relative_mem root face radius h,offset_relative root face radius h⟩

theorem region_length (root : Z4Plaq) (radius : Nat) :
    (region root radius).length = ((2*radius+1)*(2*radius+1)*(2*radius+1)*(2*radius+1))*6 := by
  rw [region, List.length_map, boxPlaquettes_length]

end YMGap.Continuum.Z4LinfFiniteRegion

#print axioms YMGap.Continuum.Z4LinfFiniteRegion.offsetFace
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.relativeFace
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.region
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.coordinate_window
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.relative_mem
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.offset_relative
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.mem_region_of_linf
#print axioms YMGap.Continuum.Z4LinfFiniteRegion.region_length
