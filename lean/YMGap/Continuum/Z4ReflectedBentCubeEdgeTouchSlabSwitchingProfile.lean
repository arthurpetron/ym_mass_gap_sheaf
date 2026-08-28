/-
# Production slab profile of the reflected bent-cube cut

Embed the reflected sixteen-face two-lobe carrier in the corrected extent-five
slab.  Its unique pivot has physical word `[1,0,1,1,1]`, reflecting the
interleaved vacuum slot in corrected-slab incidence order.  Every other link
has a sparse binary word of total zero or two.

Constructive contract: literal finite geometry and the production binary
support encoding only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

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
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier

abbrev reflectedBentSwitchSurface : List Z4Plaq :=
  YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface

abbrev reflectedBentSwitchPivot : Z4Link :=
  reflectedBentPivot

theorem reflectedBentSwitchSurface_subset_slab_five :
    ∀ plaquette, plaquette ∈ reflectedBentSwitchSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 :=
  YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface_subset_slab_five

theorem reflectedBentSwitchSurface_nodup :
    reflectedBentSwitchSurface.Nodup :=
  YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface_nodup

theorem reflectedBentSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence reflectedBentSwitchSurface :=
  YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface_evenFaceIncidence

theorem reflectedBentSwitch_nonpivot_sparseFundamentalWord
    (link : Z4Link) (hne : link ≠ reflectedBentSwitchPivot) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 reflectedBentSwitchSurface) link) :=
  slabBinarySupport_sparseFundamentalWord
    reflectedBentSwitchSurface_subset_slab_five
    reflectedBentSwitchSurface_nodup
    reflectedBentSwitchSurface_evenFaceIncidence link
    (reflectedBent_other_faceIncidenceCount_le_two link hne)

theorem reflectedBentSwitchPivot_degree_five :
    (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).length = 5 := by
  decide

theorem reflectedBentSwitchPivot_spinList :
    (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).map
        (slabBinarySupportLabelling 5 reflectedBentSwitchSurface) =
      [1, 0, 1, 1, 1] := by
  decide

theorem reflectedBentSwitchPivot_componentTagList :
    (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).map
        reflectedBentComponentTag = [1, 0, 1, 2, 2] :=
  reflectedBentPivot_componentTagList

theorem reflectedBentSwitchPivot_localExternalSpinSum :
    localExternalSpinSum
      (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 reflectedBentSwitchSurface)
        reflectedBentSwitchPivot) = 4 := by
  unfold slabLinkExternalSpins
  rw [slabBinarySupport_localExternalSpinSum
    reflectedBentSwitchSurface_subset_slab_five
    reflectedBentSwitchSurface_nodup reflectedBentSwitchPivot]
  exact reflectedBentPivot_faceIncidenceCount

#print axioms reflectedBentSwitchSurface_subset_slab_five
#print axioms reflectedBentSwitch_nonpivot_sparseFundamentalWord
#print axioms reflectedBentSwitchPivot_degree_five
#print axioms reflectedBentSwitchPivot_spinList
#print axioms reflectedBentSwitchPivot_componentTagList
#print axioms reflectedBentSwitchPivot_localExternalSpinSum

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
