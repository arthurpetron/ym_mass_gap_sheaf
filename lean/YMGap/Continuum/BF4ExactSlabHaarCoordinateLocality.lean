/-
# Locality of the original Haar coordinate projection

The raw conditional Haar integration at a physical link preserves the full
slab support and removes only that selected quaternion coordinate. The
result is fixed by the actual completed conditional projection on the
original full-action carrier. No coordinate is deleted or reindexed.
-/

import YMGap.Continuum.BF4ExactSlabStarIndependentProbe
import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "C" => conditionalProjection hw0 hw1 K extent hK link hl
local notation "i" => List.idxOf link (boundaryCompleteSlabLinks extent)

include hl in
/-- The original full-coordinate Haar projection remains supported on the
literal physical links other than the selected one. -/
theorem raw_project_local (p : (F).V) :
    LinkLocal extent (independentLinks extent link)
      (project i p.val) := by
  intro t ht b hb hnot
  have hphys := correctedSlabLinkAt_mem (List.mem_range.mpr hb)
  have hselected : correctedSlabLinkAt extent b = link := by
    by_cases he : correctedSlabLinkAt extent b = link
    · exact he
    have hm : correctedSlabLinkAt extent b ∈ independentLinks extent link := by
      apply List.mem_filter.mpr
      refine ⟨hphys, ?_⟩
      apply decide_eq_true
      exact he
    exact False.elim (hnot hm)
  have hbi : b = i := correctedSlabLinkAt_injective_on_physical
    (List.mem_range.mpr hb)
    (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
    (hselected.trans (correctedSlabLinkAt_idxOf hl).symm)
  subst b
  have hind := project_independent i p.val t ht
  intro c hc
  have hclearzero := exponentAt_clearQuaternionBlock_self t.1 i c hc
  rw [hind] at hclearzero
  exact hclearzero

/-- The actual completed original conditional projection fixes the raw
selected-coordinate Haar projection, using its literal exterior support. -/
theorem conditional_fixes_raw_project (p : (F).V) :
    C (embedV F ⟨project i p.val, project_supported i p.property⟩) =
      embedV F ⟨project i p.val, project_supported i p.property⟩ := by
  let r : (F).V := ⟨project i p.val, project_supported i p.property⟩
  exact conditionalProjection_fix_local hw0 hw1 K extent hK link hl
    (independentLinks extent link) r
    (raw_project_local hw0 hw1 K extent hK link hl p)
    (by
      intro h
      have hm := List.mem_filter.mp h
      exact (decide_eq_true_eq.mp hm.2) rfl)

end YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality

#print axioms YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality.raw_project_local
#print axioms YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality.conditional_fixes_raw_project
