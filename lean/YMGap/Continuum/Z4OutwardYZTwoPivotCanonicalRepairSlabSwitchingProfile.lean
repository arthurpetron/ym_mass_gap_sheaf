/-
# Production profile of the two-pivot outward Y/Z repair surface

Embed the explicit same-marked repair surface in the corrected extent-five
slab.  Exactly two links carry four selected fundamental faces.  Every other
link carries a sparse binary word of total zero or two.  The spatial and
temporal pivot words are respectively `[1,1,1,1,0]` and `[1,1,0,1,1]`.

Constructive contract: literal finite geometry and the production binary
support encoding only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier

abbrev outwardYZCanonicalRepairSwitchSurface : List Z4Plaq :=
  outwardYZCanonicalRepairSurface

abbrev outwardYZCanonicalRepairSwitchSpatialPivot : Z4Link :=
  outwardYZCanonicalRepairSpatialPivot

abbrev outwardYZCanonicalRepairSwitchTemporalPivot : Z4Link :=
  outwardYZCanonicalRepairTemporalPivot

theorem outwardYZCanonicalRepairSwitchSurface_subset_slab_five :
    ∀ plaquette, plaquette ∈ outwardYZCanonicalRepairSwitchSurface →
      plaquette ∈
        YMGap.Continuum.Z4HalfTimeReflectionGeometry.boundaryCompleteSlabPlaquettes 5 :=
  outwardYZCanonicalRepairSurface_subset_slab_five

theorem outwardYZCanonicalRepairSwitchSurface_nodup :
    outwardYZCanonicalRepairSwitchSurface.Nodup :=
  outwardYZCanonicalRepairSurface_nodup

theorem outwardYZCanonicalRepairSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYZCanonicalRepairSwitchSurface :=
  outwardYZCanonicalRepairSurface_even

theorem outwardYZCanonicalRepairSwitch_nonpivot_sparseFundamentalWord
    (link : Z4Link)
    (hneSpatial : link ≠ outwardYZCanonicalRepairSwitchSpatialPivot)
    (hneTemporal : link ≠ outwardYZCanonicalRepairSwitchTemporalPivot) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5
          outwardYZCanonicalRepairSwitchSurface) link) :=
  slabBinarySupport_sparseFundamentalWord
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
    outwardYZCanonicalRepairSwitchSurface_nodup
    outwardYZCanonicalRepairSwitchSurface_evenFaceIncidence link
    (outwardYZCanonicalRepair_other_faceIncidenceCount_le_two
      link hneSpatial hneTemporal)

theorem outwardYZCanonicalRepairSwitchSpatialPivot_degree_five :
    (slabIncidentPlaqIds 5
      outwardYZCanonicalRepairSwitchSpatialPivot).length = 5 := by
  decide

theorem outwardYZCanonicalRepairSwitchTemporalPivot_degree_five :
    (slabIncidentPlaqIds 5
      outwardYZCanonicalRepairSwitchTemporalPivot).length = 5 := by
  decide

theorem outwardYZCanonicalRepairSwitchSpatialPivot_spinList :
    (slabIncidentPlaqIds 5
      outwardYZCanonicalRepairSwitchSpatialPivot).map
        (slabBinarySupportLabelling 5
          outwardYZCanonicalRepairSwitchSurface) =
      [1, 1, 1, 1, 0] := by
  decide

theorem outwardYZCanonicalRepairSwitchTemporalPivot_spinList :
    (slabIncidentPlaqIds 5
      outwardYZCanonicalRepairSwitchTemporalPivot).map
        (slabBinarySupportLabelling 5
          outwardYZCanonicalRepairSwitchSurface) =
      [1, 1, 0, 1, 1] := by
  decide

theorem outwardYZCanonicalRepairSwitchSpatialPivot_localExternalSpinSum :
    localExternalSpinSum
      (slabIncidentPlaqIds 5
        outwardYZCanonicalRepairSwitchSpatialPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5
          outwardYZCanonicalRepairSwitchSurface)
        outwardYZCanonicalRepairSwitchSpatialPivot) = 4 := by
  unfold slabLinkExternalSpins
  rw [slabBinarySupport_localExternalSpinSum
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
    outwardYZCanonicalRepairSwitchSurface_nodup
    outwardYZCanonicalRepairSwitchSpatialPivot]
  exact outwardYZCanonicalRepairSpatialPivot_faceIncidenceCount

theorem outwardYZCanonicalRepairSwitchTemporalPivot_localExternalSpinSum :
    localExternalSpinSum
      (slabIncidentPlaqIds 5
        outwardYZCanonicalRepairSwitchTemporalPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5
          outwardYZCanonicalRepairSwitchSurface)
        outwardYZCanonicalRepairSwitchTemporalPivot) = 4 := by
  unfold slabLinkExternalSpins
  rw [slabBinarySupport_localExternalSpinSum
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
    outwardYZCanonicalRepairSwitchSurface_nodup
    outwardYZCanonicalRepairSwitchTemporalPivot]
  exact outwardYZCanonicalRepairTemporalPivot_faceIncidenceCount

#print axioms outwardYZCanonicalRepairSwitch_nonpivot_sparseFundamentalWord
#print axioms outwardYZCanonicalRepairSwitchSpatialPivot_spinList
#print axioms outwardYZCanonicalRepairSwitchTemporalPivot_spinList
#print axioms outwardYZCanonicalRepairSwitchSpatialPivot_localExternalSpinSum
#print axioms outwardYZCanonicalRepairSwitchTemporalPivot_localExternalSpinSum

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile
