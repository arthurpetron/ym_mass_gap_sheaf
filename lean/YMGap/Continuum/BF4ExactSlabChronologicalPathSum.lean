/-
# Chronological path bound by original conditional residual energies

The finite path sum, actual physical cut geometry and full-action
conditional-energy comparison meet here on the SAME observable and action.
The exact varying comparison costs and the original partition are retained.
Their area dependence is not a useful spatial/scaling bound or OS-time gap.
-/

import YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
import YMGap.Continuum.BF4ExactSlabOrderedPathVariance
import YMGap.Continuum.BF4ExactSlabOrderedPathEnergy
import YMGap.Continuum.GNSProjectionSweepEnergy

namespace YMGap.Continuum.BF4ExactSlabChronologicalPathSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabOrderedPathVariance
open YMGap.Continuum.BF4ExactSlabOrderedPathCut
open YMGap.Continuum.BF4ExactSlabOrderedPathEnergy
open YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionOrderedReplicaPath
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem add_rat (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem weighted_sum_rat {A : Type} (n : Nat) (W : RatPoly) (f : A → RatPoly) :
    ∀ xs : List A,
    rat (quaternionHaar n (polyMul W (polySum (xs.map f)))) =
      sumOn xs (fun i => rat (quaternionHaar n (polyMul W (f i))))
  | [] => Quotient.sound (ofQ'_equiv_of_eqv
      (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right W)))
  | i::xs => by
      change rat (quaternionHaar n (polyMul W (polyAdd (f i) (polySum (xs.map f))))) =
        RCadd (rat (quaternionHaar n (polyMul W (f i))))
          (sumOn xs (fun j => rat (quaternionHaar n (polyMul W (f j)))))
      rw [← weighted_sum_rat n W f xs, add_rat]
      exact Quotient.sound (ofQ'_equiv_of_eqv (quaternionHaar_polyMul_add_right _ _ _ _))

/-- The next chronological coordinate is witnessed to be an actual physical link. -/
def nextPhysicalLink (extent k : Nat) (hk : k < blocks extent) :
    {link : Z4Link // link ∈ boundaryCompleteSlabLinks extent} :=
  ⟨correctedSlabLinkAt extent ((chronologicalBlocks extent).getD k 0),
    correctedSlabLinkAt_mem (List.mem_range.mpr
      (next_in_range (blocks extent) (chronologicalBlocks extent)
        (chronologicalBlocks_perm extent) k hk))⟩

theorem nextPhysicalLink_slot (extent k : Nat) (hk : k < blocks extent) :
    slot extent (nextPhysicalLink extent k hk).val =
      (chronologicalBlocks extent).getD k 0 := by
  apply correctedSlabLinkAt_injective_on_physical
    (List.mem_range.mpr (List.idxOf_lt_length_of_mem (nextPhysicalLink extent k hk).property))
    (List.mem_range.mpr (next_in_range (blocks extent) (chronologicalBlocks extent)
      (chronologicalBlocks_perm extent) k hk))
  exact correctedSlabLinkAt_idxOf (nextPhysicalLink extent k hk).property

private theorem prefix_in_range (extent k : Nat) :
    ∀ j, j ∈ (chronologicalBlocks extent).take k → j < blocks extent := by
  intro j hj
  exact List.mem_range.mp ((chronologicalBlocks_perm extent).mem_iff.mp
    (List.mem_of_mem_take hj))

/-- The crossing count in stepCost is exactly the one bounded by chronological
geometry; no raw-coordinate or eight-color ordering is substituted. -/
theorem chronological_cost_crossing_bound (extent k : Nat) (hk : k < blocks extent) :
    crossingCount extent (selectedLinks extent ((chronologicalBlocks extent).take k)) ≤
      12 * (extent+1)^3 :=
  prefix_crossingCount_le_area extent k (by rwa [chronologicalBlocks_length])

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

/-- Literal per-step energy payment. The out-of-range value is zero only
to give a total Nat function; the path sum uses exclusively k < blocks. -/
def chronologicalEnergyTerm (p : (F).V) (k : Nat) : RC :=
  if hk : k < blocks extent then
    let link := nextPhysicalLink extent k hk
    let E := normSq ((projections hw0 hw1 K extent hK).residual link (embedV F p))
    RCscale (stepCost hw0 hw1 extent ((chronologicalBlocks extent).take k) link.val *
      quaternionHaar (blocks extent) (fullWeight w K extent)) (RCadd E E)
  else RCzero

theorem chronological_increment_energy_bound (p : (F).V) (k : Nat)
    (hk : k < blocks extent) :
    RCle (rat (incrementIntegral w K extent ((chronologicalBlocks extent).take k)
      ((chronologicalBlocks extent).getD k 0) p.val))
      (chronologicalEnergyTerm hw0 hw1 K extent hK p k) := by
  have hnot : slot extent (nextPhysicalLink extent k hk).val ∉
      (chronologicalBlocks extent).take k := by
    rw [nextPhysicalLink_slot]
    exact next_not_in_prefix (blocks extent) (chronologicalBlocks extent)
      (chronologicalBlocks_perm extent) k hk
  have h := original_selected_increment_energy_bound hw0 hw1 K extent hK
    ((chronologicalBlocks extent).take k) (prefix_in_range extent k)
    (nextPhysicalLink extent k hk).val (nextPhysicalLink extent k hk).property hnot p
  rw [nextPhysicalLink_slot] at h
  simpa only [chronologicalEnergyTerm, dif_pos hk] using h

/-- Constructed global finite path-energy inequality for every original
supported polynomial. Both copies use the original full action, and every
energy is the existing conditional residual of its actual next link.
The exact costs remain nome/extent dependent. -/
theorem original_chronological_path_energy_bound (p : (F).V) :
    RCle (Quotient.mk crealSetoid (ofQ' (2 * varianceDeterminant w K extent p.val)))
      (RCscale (Q'.ofNat (blocks extent))
        (sumOn (List.range (blocks extent))
          (chronologicalEnergyTerm hw0 hw1 K extent hK p))) := by
  have hv := original_ordered_path_variance_bound hw0 hw1 K extent hK
    (chronologicalBlocks extent) (chronologicalBlocks_perm extent) p.val p.property
  have hv' : RCle (rat (2 * varianceDeterminant w K extent p.val))
      (RCscale (Q'.ofNat (blocks extent))
        (rat (quaternionHaar (blocks extent + blocks extent)
          (polyMul (originalPair w K extent)
            (orderedSquareSum extent (chronologicalBlocks extent) p.val))))) := by
    rw [scale_rat]
    exact leEv_ofQ'_of_approx_ge (fun _ => hv)
  apply RCle_trans hv'
  apply RCscale_mono (Q'.ofNat_nonneg (blocks extent))
  unfold orderedSquareSum increments
  rw [List.map_map, weighted_sum_rat]
  apply sumOn_mono
  intro k hk
  have hk' : k < blocks extent := List.mem_range.mp hk
  have hlen : k < (chronologicalBlocks extent).length := by
    rwa [chronologicalBlocks_length]
  dsimp only [Function.comp_def]
  rw [ordered_increment_eq (blocks extent) (chronologicalBlocks extent) k hlen p.val]
  exact chronological_increment_energy_bound hw0 hw1 K extent hK p k hk'

#print axioms nextPhysicalLink
#print axioms nextPhysicalLink_slot
#print axioms chronological_cost_crossing_bound
#print axioms chronologicalEnergyTerm
#print axioms chronological_increment_energy_bound
#print axioms original_chronological_path_energy_bound

end YMGap.Continuum.BF4ExactSlabChronologicalPathSum
