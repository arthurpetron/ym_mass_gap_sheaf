/-
# Sum the ACTUAL original boundary cores with a volume-independent budget

The original active-core count and collar-adjusted weights are now summed,
using exact size fibers. If s(w)=625*rho(w)<1, their geometric sum is at
most C(probe)*s(w)^d/(1-s(w)) whenever d is a proved minimum core size.
Every active core has size at least one, giving an unconditional finite
volume-independent budget under the stated coupling and carrier guards.

The bound is consumed by the EXISTING mixed numerator and boundary D_K,
retaining their two ORIGINAL unit moments. The existing w=1/1024 point
inhabits the combined-rate guard. A distance-growing size floor, normalized
cutoff-limit transport, thermodynamic convergence and a physical gap are
not proved here.
-/

import YMGap.Continuum.BF4ExactSlabActiveCoreCount
import YMGap.Continuum.BF4ExactSlabSummableCoreRate

namespace YMGap.Continuum.BF4ExactSlabUniformCoreBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabActiveCoreCount
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

theorem geometricCoreSum_tail_bound {rate : Q'} (hr : (0 : Q') ≤ rate)
    (hs : entropyRate 625 rate < 1) {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (keep : Nat → Bool) (ambient : List Nat) (d : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ anchor, anchor ∈ activeAnchors extent links keep ambient → d ≤ anchor.length) :
    geometricCoreSum rate extent links keep ambient ≤ tailBudget (countPrefactor probe) 625 d rate hs := by
  apply size_sum_bound (activeAnchors extent links keep ambient) List.length (countPrefactor probe) 625 d
    ambient.length hr hs hsize
  · intro anchor ha
    exact (selected_sublist (List.mem_filter.mp (List.mem_filter.mp ha).1).1).length_le
  · intro n
    have he : (activeAnchors extent links keep ambient).filter (fun anchor => decide (n = anchor.length)) =
        activeAtSize extent links keep ambient n := by
      apply List.filter_congr
      intro anchor _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (eq_comm : n = anchor.length ↔ anchor.length = n)
    rw [he]
    exact activeAtSize_length_le probe extent keep ambient n hn hphys

theorem active_core_size_pos {extent : Nat} {links : List Z4Link} {keep : Nat → Bool}
    {ambient anchor : List Nat} (ha : anchor ∈ activeAnchors extent links keep ambient) : 1 ≤ anchor.length := by
  obtain ⟨id, hi, _⟩ := outsideWitness keep anchor (List.mem_filter.mp ha).2
  cases anchor with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons _ rest => exact Nat.succ_le_succ (Nat.zero_le rest.length)

/-- No distance premise: every actual active core contains an exterior face. -/
theorem geometricCoreSum_uniform_bound {rate : Q'} (hr : (0 : Q') ≤ rate)
    (hs : entropyRate 625 rate < 1) {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (keep : Nat → Bool) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    geometricCoreSum rate extent links keep ambient ≤ tailBudget (countPrefactor probe) 625 1 rate hs :=
  geometricCoreSum_tail_bound hr hs probe extent keep ambient 1 hn hphys (fun _ ha => active_core_size_pos ha)

/-- The cutoff/volume-independent coefficient; probe and coupling dependence remain explicit. -/
def summedBoundaryBudget {links : List Z4Link} (probe : ProbeCarrier links) (w : Q')
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (d : Nat) : Q' :=
  probePrefactor w hd links.length * tailBudget (countPrefactor probe) 625 d (adjustedCoreRate w hd) hs

theorem finiteBoundaryBudget_tail_bound {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (keep : Nat → Bool) (ambient : List Nat) (d : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ anchor, anchor ∈ activeAnchors extent links keep ambient → d ≤ anchor.length) :
    finiteBoundaryBudget w hd extent links keep ambient ≤ summedBoundaryBudget probe w hd hs d :=
  Q'.le_trans' _ _ _ (finiteBoundaryBudget_le_geometric hw hd extent links keep ambient hn hphys)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (geometricCoreSum_tail_bound (adjustedCoreRate_nonnegative hw hd) hs probe extent keep ambient d hn hphys hsize)
      (probePrefactor_nonnegative w hd links.length))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
include hw0 hw1 hsmall hd hs

theorem mixedNumerator_tail_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link) (probe : ProbeCarrier links)
    (hl : LinkLocal extent links p) (ambient : List Nat) (d : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ anchor, anchor ∈ activeAnchors extent links keep ambient → d ≤ anchor.length) :
    Q'.abs (mixedNumerator w K extent keep p ambient) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs d) * mixedPartition w K extent keep ambient :=
  Q'.le_trans' _ _ _ (mixedNumerator_budget_bound hw0 hw1 hsmall hd K extent keep p c P links hl ambient hn hphys)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (finiteBoundaryBudget_tail_bound hw0 hd hs probe extent keep ambient d hn hphys hsize)
        (Q'.zero_le_add _ _ P.nonnegative P.nonnegative))
      (mixedPartition_nonnegative hw0 hw1 hsmall (Q'.le_of_lt hd) K extent keep ambient hphys))

/-- Original determinant and original unit moments, with an explicit size-tail budget. -/
theorem boundaryNumerator_tail_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal (centralExtent (half+padding)) links p)
    (d : Nat) (hsize : ∀ anchor, anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding))) → d ≤ anchor.length) :
    Q'.abs (boundaryNumerator w half padding p K) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs d) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (boundary_mixedNumerator w K half padding p)))
    (Q'.le_trans' _ _ _ (mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (centralExtent (half+padding))
      (boundaryKeep half padding) p c P links probe hl _ d (CayleyParentInj.range_nodup _) (fun _ hi => hi) hsize)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition w K half padding))))

/-- The size-one floor is proved, not a supplied boundary-decay hypothesis. -/
theorem boundaryNumerator_uniform_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal (centralExtent (half+padding)) links p) :
    Q'.abs (boundaryNumerator w half padding p K) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs 1) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  boundaryNumerator_tail_bound hw0 hw1 hsmall hd hs K half padding p c P links probe hl 1
    (fun _ ha => active_core_size_pos ha)

end SmallNome

/-- Concrete coupling guards are all proved at the existing pilot; no strict-rate input remains. -/
theorem existingNome_boundary_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal (centralExtent (half+padding)) links p) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    Q'.abs (boundaryNumerator w half padding p K) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs 1) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  boundaryNumerator_uniform_bound (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos)
    (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one)
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2 K half padding p c P links probe hl

end YMGap.Continuum.BF4ExactSlabUniformCoreBudget

#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.geometricCoreSum_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.active_core_size_pos
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.geometricCoreSum_uniform_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.summedBoundaryBudget
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.finiteBoundaryBudget_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.mixedNumerator_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.boundaryNumerator_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.boundaryNumerator_uniform_bound
#print axioms YMGap.Continuum.BF4ExactSlabUniformCoreBudget.existingNome_boundary_bound
