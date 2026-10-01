/-
# Literal spatial-family incidence at one physical quaternion block

The row is computed from actual face edges and the fixed-slice link index.
For a Nodup signed family it contains at most six faces, even when the
ambient width and the family length grow.  Off-row angular derivatives of
the literal spin-one face trace vanish coefficientwise.  No source or action
weight is replaced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)

/-- A face is in the row of block `b` exactly when one of its literal edges
is a physical fixed-slice link whose actual index is `b`. -/
def blockRow (width b : Nat) (face : Z4Plaq) : Bool :=
  (edgesOf face).any (fun link =>
    decide (link ∈ baseLinks width ∧ (baseLinks width).idxOf link = b))

def blockRowFaces (width b : Nat) (qs : List Z4Plaq) : List Z4Plaq :=
  qs.filter (blockRow width b)

theorem blockRow_iff (width b : Nat) (face : Z4Plaq) :
    blockRow width b face = true ↔
      ∃ link : Z4Link, link ∈ edgesOf face ∧
        link ∈ baseLinks width ∧ (baseLinks width).idxOf link = b := by
  constructor
  · intro h
    obtain ⟨link, hedge, htest⟩ := List.any_eq_true.mp h
    have hp : link ∈ baseLinks width ∧ (baseLinks width).idxOf link = b :=
      of_decide_eq_true htest
    exact ⟨link, hedge, hp.1, hp.2⟩
  · rintro ⟨link, hedge, hphysical, hindex⟩
    exact List.any_eq_true.mpr
      ⟨link, hedge, decide_eq_true ⟨hphysical, hindex⟩⟩

theorem blockRowFaces_mem_iff (width b : Nat) (qs : List Z4Plaq) (face : Z4Plaq) :
    face ∈ blockRowFaces width b qs ↔
      face ∈ qs ∧ blockRow width b face = true := by
  unfold blockRowFaces
  exact List.mem_filter

/-- The six-carrier bound is valid for ANY Nodup literal face list.  The
spatial-family condition is thus supplied to consumers only for their other
geometric pins, not needed for this finite incidence count. -/
theorem blockRowFaces_length_le_six (width b : Nat) (qs : List Z4Plaq)
    (hqs : qs.Nodup) : (blockRowFaces width b qs).length ≤ 6 := by
  let row := blockRowFaces width b qs
  have hn : row.Nodup := List.filter_sublist.nodup hqs
  cases hrow : row with
  | nil =>
      change row.length ≤ 6
      rw [hrow]
      decide
  | cons first rest =>
      have hfirst : first ∈ row := by rw [hrow]; exact List.mem_cons_self
      obtain ⟨selected, hselectedFace, hselectedPhysical, hselectedIndex⟩ :=
        (blockRow_iff width b first).mp
          ((blockRowFaces_mem_iff width b qs first).mp hfirst).2
      have hs : ∀ face, face ∈ row →
          face ∈ edgePlaqs selected.1 selected.2 := by
        intro face hface
        obtain ⟨link, hlinkFace, hlinkPhysical, hlinkIndex⟩ :=
          (blockRow_iff width b face).mp
            ((blockRowFaces_mem_iff width b qs face).mp hface).2
        have heq : link = selected :=
          idxOf_injective_on_members hlinkPhysical hselectedPhysical
            (hlinkIndex.trans hselectedIndex.symm)
        subst link
        exact edge_complete face selected.1 selected.2 hlinkFace
      have hle := CayleyPruferInjection.nodup_subset_length_le
        row (edgePlaqs selected.1 selected.2) hn hs
      simpa only [edgePlaqs_length] using hle

/-- This adapter exposes the requested spatial-family signature explicitly. -/
theorem spatial_blockRowFaces_length_le_six (width b : Nat) (qs : List Z4Plaq)
    (hqs : qs.Nodup) (_hspatial : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    (blockRowFaces width b qs).length ≤ 6 :=
  blockRowFaces_length_le_six width b qs hqs

/-- No listed incident physical edge means the literal spin-one character
is independent of the selected quaternion block. -/
theorem blockRow_character_independent (width b : Nat) (face : Z4Plaq)
    (hb : b < N width) (hoff : blockRow width b face = false) :
    QuaternionBlockIndependent b
      (characterPolynomial (plaquette width face).scalar 1) := by
  apply characterFace_independent_index width face b 1 hb
  intro link hedge hphysical hindex
  have hrow : blockRow width b face = true :=
    (blockRow_iff width b face).mpr ⟨link, hedge, hphysical, hindex⟩
  rw [hoff] at hrow
  cases hrow

/-- All six ordered coordinate-plane generators vanish off the computed
row; the statement permits any `i,j<4`, including repeated coordinates. -/
theorem blockRow_derivative_zero (width b : Nat) (face : Z4Plaq)
    (hb : b < N width) (hoff : blockRow width b face = false)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv
      (angularDerivative (4*b+i) (4*b+j)
        (characterPolynomial (plaquette width face).scalar 1)) polyZero :=
  angularDerivative_blockIndependent_zero hi hj
    (blockRow_character_independent width b face hb hoff)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.blockRow_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.blockRowFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.blockRowFaces_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.spatial_blockRowFaces_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.blockRow_character_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence.blockRow_derivative_zero
