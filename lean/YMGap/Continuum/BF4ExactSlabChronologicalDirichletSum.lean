/-
# Chronological enumeration of the original conditional Dirichlet energy

The chronological path and the existing eight-color conditional sweep use
different orders of the SAME original physical links.  The final energy is
a sum of residual norms at one fixed completed vector, so its value is
permutation-invariant.  This does not reorder the sweep operators.
-/

import YMGap.Continuum.BF4ExactSlabChronologicalPathSum
import YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
import YMGap.Continuum.GNSProjectionSweepEnergyOrder

namespace YMGap.Continuum.BF4ExactSlabChronologicalDirichletSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
open YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
open YMGap.Continuum.BF4ExactSlabChronologicalPathSum
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionOrderedReplicaPath
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem sumOn_ext {A : Type} (xs : List A) (f g : A → RC)
    (h : ∀ a, a ∈ xs → f a = g a) : sumOn xs f = sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [sumOn]
      rw [h a List.mem_cons_self]
      exact congrArg (fun v => RCadd (g a) v)
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sumOn_map {A B : Type} (xs : List A) (f : A → B) (g : B → RC) :
    sumOn xs (fun a => g (f a)) = sumOn (xs.map f) g := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [sumOn, List.map_cons, ih]

private theorem map_range_getD {A : Type} (xs : List A) (fallback : A) :
    (List.range xs.length).map (fun k => xs.getD k fallback) = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      change a :: (List.range rest.length).map (fun k => rest.getD k fallback) =
        a :: rest
      rw [ih]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- The actual residual energy at chronological position `k`.  The zero
branch only makes this a total function; all summed positions are in range. -/
def chronologicalResidualEnergy (p : (F).V) (k : Nat) : RC :=
  if hk : k < blocks extent then
    normSq ((P).residual (nextPhysicalLink extent k hk) (embedV F p))
  else RCzero

theorem chronologicalResidualEnergy_nonnegative (p : (F).V) (k : Nat) :
    RCnonneg (chronologicalResidualEnergy hw0 hw1 K extent hK p k) := by
  unfold chronologicalResidualEnergy
  split
  · exact (F).cinner_self_nonneg _
  · exact RCle_refl _

/-- The energy of a physical block index, with an unused out-of-range zero. -/
private def blockResidualEnergy (p : (F).V) (j : Nat) : RC :=
  if hj : j < blocks extent then
    normSq ((P).residual
      ⟨correctedSlabLinkAt extent j,
        correctedSlabLinkAt_mem (List.mem_range.mpr hj)⟩ (embedV F p))
  else RCzero

private theorem position_energy_pin (p : (F).V) (k : Nat)
    (hk : k < blocks extent) :
    chronologicalResidualEnergy hw0 hw1 K extent hK p k =
      blockResidualEnergy hw0 hw1 K extent hK p
        ((chronologicalBlocks extent).getD k 0) := by
  have hj := next_in_range (blocks extent) (chronologicalBlocks extent)
    (chronologicalBlocks_perm extent) k hk
  simp only [chronologicalResidualEnergy, blockResidualEnergy,
    dif_pos hk, dif_pos hj]
  rfl

private theorem schedule_energy_pin (p : (F).V)
    (i : PhysicalLink extent) :
    blockResidualEnergy hw0 hw1 K extent hK p (slot extent i.val) =
      normSq ((P).residual i (embedV F p)) := by
  have hj : slot extent i.val < blocks extent :=
    List.idxOf_lt_length_of_mem i.property
  simp only [blockResidualEnergy, dif_pos hj]
  have hlink :
      (⟨correctedSlabLinkAt extent (slot extent i.val),
        correctedSlabLinkAt_mem (List.mem_range.mpr hj)⟩ : PhysicalLink extent) = i := by
    apply Subtype.ext
    exact correctedSlabLinkAt_idxOf i.property
  rw [hlink]

/-- Chronological residual payment is exactly the existing final energy of
the original eight-color physical-link test list.  Only the finite scalar
summands are permuted; no conditional projections are reordered. -/
theorem chronologicalResidualEnergy_sum (p : (F).V) :
    sumOn (List.range (blocks extent))
      (chronologicalResidualEnergy hw0 hw1 K extent hK p) =
      (P).finalEnergy (schedule extent) (embedV F p) := by
  let e := blockResidualEnergy hw0 hw1 K extent hK p
  have hpos :
      sumOn (List.range (blocks extent))
          (chronologicalResidualEnergy hw0 hw1 K extent hK p) =
        sumOn (chronologicalBlocks extent) e := by
    rw [sumOn_ext (List.range (blocks extent))
      (chronologicalResidualEnergy hw0 hw1 K extent hK p)
      (fun k => e ((chronologicalBlocks extent).getD k 0))
      (fun k hk => position_energy_pin hw0 hw1 K extent hK p k
        (List.mem_range.mp hk))]
    rw [sumOn_map]
    have hlen : (chronologicalBlocks extent).length = blocks extent :=
      chronologicalBlocks_length extent
    rw [← hlen]
    rw [map_range_getD]
  have hsched :
      sumOn (physicalScheduleIndex extent) e =
        (P).finalEnergy (schedule extent) (embedV F p) := by
    unfold physicalScheduleIndex
    change sumOn ((schedule extent).map (fun i => slot extent i.val)) e =
      (P).finalEnergy (schedule extent) (embedV F p)
    rw [← sumOn_map (schedule extent)
      (fun i => slot extent i.val) e]
    rw [sumOn_ext (schedule extent)
      (fun i => e (slot extent i.val))
      (fun i => normSq ((P).residual i (embedV F p)))
      (fun i _ => schedule_energy_pin hw0 hw1 K extent hK p i)]
    rfl
  rw [hpos]
  exact (sumOn_perm e ((chronologicalBlocks_perm extent).trans
    (physical_schedule_index_perm extent).symm)).trans hsched

#print axioms chronologicalResidualEnergy
#print axioms chronologicalResidualEnergy_nonnegative
#print axioms chronologicalResidualEnergy_sum

end YMGap.Continuum.BF4ExactSlabChronologicalDirichletSum
