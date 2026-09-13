/-
# The ORIGINAL boundary estimate reduced to a geometric rooted-core sum

The local collar cost is absorbed into the proved adjusted rate rho(w).
The entire existing boundary determinant is now controlled by

  2*c*probePrefactor * sum_active rho(w)^|core| * Z_full,K*Z_inside,K.

The remaining sum is computed from literal geometry only and has no cutoff.
Neither its volume-uniform bound nor its decay in the probe/boundary distance
is assumed or proved here. A strict per-face rate alone does not bound the
number of rooted cores.
-/

import YMGap.Continuum.BF4ExactSlabCollarAdjustedRate

namespace YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget

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
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- A purely geometric finite sum at the supplied per-face rate. -/
def geometricCoreSum (rate : Q') (extent : Nat) (links : List Z4Link)
    (keep : Nat → Bool) (ambient : List Nat) : Q' :=
  listQSum (fun core => rate^core.length) (activeAnchors extent links keep ambient)

theorem geometricCoreSum_nonnegative {rate : Q'} (hr : (0 : Q') ≤ rate)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient : List Nat) :
    (0 : Q') ≤ geometricCoreSum rate extent links keep ambient :=
  listQSum_nonnegative_on _ _ (fun core _ => Q'.pow_nonneg rate hr core.length)

private theorem sum_le {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' _
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem finiteBoundaryBudget_le_geometric {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    finiteBoundaryBudget w hd extent links keep ambient ≤
      probePrefactor w hd links.length * geometricCoreSum (adjustedCoreRate w hd) extent links keep ambient :=
  Q'.le_trans' _ _ _ (sum_le _ _ _
    (fun anchor _ => normalizedCoreWeight_geometric_bound hw hd extent links keep ambient anchor hn hphys))
    (Q'.le_of_eqv (listQSum_mul_left (probePrefactor w hd links.length) _ _))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
include hw0 hw1 hsmall hd

theorem mixedNumerator_geometric_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link)
    (hl : LinkLocal extent links p) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (mixedNumerator w K extent keep p ambient) ≤
      ((c+c)*(probePrefactor w hd links.length * geometricCoreSum (adjustedCoreRate w hd) extent links keep ambient)) *
        mixedPartition w K extent keep ambient :=
  Q'.le_trans' _ _ _ (mixedNumerator_budget_bound hw0 hw1 hsmall hd K extent keep p c P links hl ambient hn hphys)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (finiteBoundaryBudget_le_geometric hw0 hd extent links keep ambient hn hphys)
        (Q'.zero_le_add _ _ P.nonnegative P.nonnegative))
      (mixedPartition_nonnegative hw0 hw1 hsmall (Q'.le_of_lt hd) K extent keep ambient hphys))

/-- The quantitative consumer retains the existing determinant and its two
original unit moments, not a surrogate partition function. -/
theorem boundaryNumerator_geometric_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (hl : LinkLocal (centralExtent (half+padding)) links p) :
    Q'.abs (boundaryNumerator w half padding p K) ≤
      ((c+c)*(probePrefactor w hd links.length *
        geometricCoreSum (adjustedCoreRate w hd) (centralExtent (half+padding)) links (boundaryKeep half padding)
          (slabPhysicalFaceEdges (centralExtent (half+padding))))) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (boundary_mixedNumerator w K half padding p)))
    (Q'.le_trans' _ _ _ (mixedNumerator_geometric_bound hw0 hw1 hsmall hd K (centralExtent (half+padding))
      (boundaryKeep half padding) p c P links hl _ (YMGap.Continuum.CayleyParentInj.range_nodup _) (fun _ h => h))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition w K half padding))))

end SmallNome

/-- A small scalar block at the existing nome; used six times rather than
reducing one deeply nested forty-eighth power. -/
theorem existingNome_eighthPower_bound :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    (inverseFaceFloor w hd)^8 ≤ (2 : Q') := by decide

/-- Existing rational pilot only; this does not assert summability of cores. -/
theorem existingNome_adjustedRate :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    (0 : Q') < adjustedCoreRate w hd ∧ adjustedCoreRate w hd < (1 : Q') := by
  let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
  let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
  let r := inverseFaceFloor w hd
  have hr : (0 : Q') < r := inverseFaceFloor_pos w hd
  have hp : r^48 ≤ (64 : Q') := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r 8 6))
    (Q'.le_trans' _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.pow_nonneg r (Q'.le_of_lt hr) 8) existingNome_eighthPower_bound 6)
      (Q'.le_of_eqv (by decide : Q'.eqv ((2 : Q')^6) 64)))
  have hk : pairedHeatRate w * 64 < (1 : Q') := by
    change pairedHeatRate BF4ExactSlabPlaquetteSmallNomeCertificate.nome * 64 < (1 : Q')
    decide
  exact ⟨Q'.mul_pos existingNome_rate.1 (HKPos.pow_pos hr 48),
    Q'.lt_of_le_of_lt (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (Q'.le_of_lt existingNome_rate.1)) hk⟩

end YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget

#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.geometricCoreSum
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.geometricCoreSum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.finiteBoundaryBudget_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.mixedNumerator_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.boundaryNumerator_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.existingNome_eighthPower_bound
#print axioms YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget.existingNome_adjustedRate
