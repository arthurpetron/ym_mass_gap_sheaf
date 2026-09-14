/-
# Temporal-cut obstruction for ORIGINAL shifted-probe moments

The two actual probe plaquettes are spatial. Their charge at every
integrated temporal link is zero, even though their spatial links are
shared with the full action. A passing original moment test therefore
gives even vertical incidence of the original odd-labelled faces.

One, two or three odd faces at any time cut force the actual moment to
vanish. Nonzero moments crossing three cuts in odd faces use at least
twelve odd faces. Empty odd cuts are allowed; connectedness alone is NOT
asserted to force nonempty odd cuts. No sign or response floor is claimed.
-/

import YMGap.Continuum.BF4ExactSlabOddFaceIncidence
import YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
import YMGap.Continuum.Z4TemporalCutParityMinimum

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

theorem probe_vertical_charge_zero (margin : Nat) (lo hi : Bool) (v : Z4Vertex)
    (hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks (responseExtent margin)) :
    charges margin lo hi ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf (v,Dir4.x3)) = 0 := by
  have h0 := faceDegree_pin (responseExtent margin) (v,Dir4.x3) (sliceFace margin 0)
    hl (slice_physical margin ⟨0,by decide⟩)
  have h3 := faceDegree_pin (responseExtent margin) (v,Dir4.x3) (sliceFace margin 3)
    hl (slice_physical margin ⟨3,by decide⟩)
  have hn (time : Nat) : (v,Dir4.x3) ∉ edgesOf (sliceFace margin time) := by
    simp [sliceFace, edgesOf, dirsOf]
  rw [if_neg (hn 0)] at h0
  rw [if_neg (hn 3)] at h3
  simp only [charges, h0, h3, ite_self, Nat.zero_add]

theorem moment_vertical_even (margin : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (ht : momentCheck margin lo hi labels = true) (v : Z4Vertex) :
    faceIncidenceCount (v,Dir4.x3) (oddFaces (responseExtent margin) labels) % 2 = 0 :=
  vertical_even_of_check (responseExtent margin) labels (charges margin lo hi)
    (probe_vertical_charge_zero margin lo hi) ht v

theorem moment_check_cut_minimum_four (margin time : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (ht : momentCheck margin lo hi labels = true)
    (hn : cut time (oddFaces (responseExtent margin) labels) ≠ []) :
    4 ≤ (cut time (oddFaces (responseExtent margin) labels)).length :=
  cut_minimum_four time _ (oddFaces_nodup _ _) (moment_vertical_even margin lo hi labels ht) hn

/-- The original signed moment is zero; no positivity assumption is used. -/
theorem moment_thin_cut_zero (margin time : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (hl : 0 < (cut time (oddFaces (responseExtent margin) labels)).length)
    (hu : (cut time (oddFaces (responseExtent margin) labels)).length < 4) :
    moment margin lo hi labels ≈ 0 := by
  cases ht : momentCheck margin lo hi labels with
  | false => exact moment_rejected margin lo hi labels ht
  | true =>
    have hn : cut time (oddFaces (responseExtent margin) labels) ≠ [] := by
      intro h
      rw [h] at hl
      cases hl
    have hb := moment_check_cut_minimum_four margin time lo hi labels ht hn
    omega

/-- Nonzero is an actual rational moment, not merely a passing parity check. -/
theorem nonzero_three_cut_minimum_twelve (margin time : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (hvalue : ¬ moment margin lo hi labels ≈ 0)
    (h0 : cut time (oddFaces (responseExtent margin) labels) ≠ [])
    (h1 : cut (time+1) (oddFaces (responseExtent margin) labels) ≠ [])
    (h2 : cut (time+2) (oddFaces (responseExtent margin) labels) ≠ []) :
    12 ≤ (oddFaces (responseExtent margin) labels).length := by
  cases ht : momentCheck margin lo hi labels with
  | false => exact False.elim (hvalue (moment_rejected margin lo hi labels ht))
  | true =>
    exact three_cut_minimum_twelve time _ (oddFaces_nodup _ _)
      (moment_vertical_even margin lo hi labels ht) h0 h1 h2

/-- Empty odd support is retained, including even-spin possibilities. -/
def cutKeep (margin time : Nat) (labels : EdgeLabelling) : Bool :=
  let n := (cut time (oddFaces (responseExtent margin) labels)).length
  decide (n = 0 ∨ 4 ≤ n)

theorem cut_rejected_zero (margin time : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (h : cutKeep margin time labels = false) : moment margin lo hi labels ≈ 0 := by
  have hn := of_decide_eq_false h
  have hpos : 0 < (cut time (oddFaces (responseExtent margin) labels)).length := by
    by_cases he : (cut time (oddFaces (responseExtent margin) labels)).length = 0
    · exact False.elim (hn (Or.inl he))
    · omega
  have hlt : (cut time (oddFaces (responseExtent margin) labels)).length < 4 := by
    by_cases he : 4 ≤ (cut time (oddFaces (responseExtent margin) labels)).length
    · exact False.elim (hn (Or.inr he))
    · omega
  exact moment_thin_cut_zero margin time lo hi labels hpos hlt

theorem moment_cut_filter (margin time : Nat) (lo hi : Bool) (labels : EdgeLabelling) :
    moment margin lo hi labels ≈
      (if cutKeep margin time labels then moment margin lo hi labels else 0) := by
  cases h : cutKeep margin time labels with
  | false => exact cut_rejected_zero margin time lo hi labels h
  | true => exact Q'.eqv_refl _

end YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.probe_vertical_charge_zero
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.moment_vertical_even
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.moment_check_cut_minimum_four
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.moment_thin_cut_zero
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.nonzero_three_cut_minimum_twelve
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.cutKeep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.cut_rejected_zero
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut.moment_cut_filter
