/-
# Literal local representatives for the actual completed Chebyshev cone

Prune each color layer using the existing SAME-operator equality. All retained
links belong to the input region, so their conditional representatives stay
inside one star expansion, however many retained links there are. The resulting
Type-level witnesses retain explicit Cauchy moduli. The first-kind recurrence
then gives radius 16*n rather than paying twice for each coupled step.

This constructs representatives, not a useful scaling-uniform decay rate.
-/

import YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative
import YMGap.Continuum.BF4ExactSlabChebyshevAuxiliaryCone

namespace YMGap.Continuum.BF4ExactSlabLocalCauchyCone

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabChebyshevCone
open YMGap.Continuum.BF4ExactSlabChebyshevAuxiliaryCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarConditionalLocality
open YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.Z4LinkEightColor

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "LR" => LocalRep hw0 hw1 K extent hK

private def retainedSweep (support : List Z4Link) (word : List (PhysicalLink extent))
    (hword : ∀ i, i ∈ word → i.val ∈ support)
    {x : GNSCompletionSpace F} (R : LR (expand extent support) x) :
    LR (expand extent support) ((P).sweep word x) :=
  match word with
  | [] => R
  | i :: rest => by
    have Ri := LocalRep.conditional hw0 hw1 K extent hK R i
    have Rnext : LR (expand extent support) ((P).op i x) :=
      LocalRep.mono hw0 hw1 K extent hK Ri (fun j hj => by
        have hj' := (List.mem_filter.mp hj).1
        rcases List.mem_append.mp hj' with hbase | hstar
        · exact hbase
        · exact (mem_expand extent support j).mpr
            ⟨i.val, hword i List.mem_cons_self, List.mem_cons_of_mem i.val hstar⟩)
    exact retainedSweep support rest
      (fun j hj => hword j (List.mem_cons_of_mem i hj)) Rnext

/-- Exact full-layer output, with literal support in one star expansion.
Operational locality is used only for the already-proved pruning equality. -/
def layerRep (c : Color) (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (expand extent support) ((P).sweep (layer extent c) x) := by
  rw [layer_prune hw0 hw1 K extent hK c support x hx]
  exact retainedSweep hw0 hw1 K extent hK support (activeLayer extent c support)
    (fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2)
    (LocalRep.mono hw0 hw1 K extent hK R
      (fun i hi => support_mem_expand extent support i hi))

/-- Computed local Cauchy data for every finite word of original color layers. -/
def runLayersRep (cs : List Color) (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (grow extent cs.length support) (runLayers hw0 hw1 K extent hK cs x) :=
  match cs with
  | [] => R
  | c :: rest => by
    rw [runLayers_cons]
    exact runLayersRep rest (expand extent support)
      (layerRep hw0 hw1 K extent hK c support R hx)
      (layer_localized hw0 hw1 K extent hK c support x hx)

/-- The actual balanced sweep, with a sixteen-star literal representative. -/
def balancedRep (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (grow extent 16 support) ((P).balanced (schedule extent) x) := by
  rw [balanced_runLayers hw0 hw1 K extent hK]
  have h := runLayersRep hw0 hw1 K extent hK (colors ++ colors.reverse) support R hx
  have hl : (colors ++ colors.reverse).length = 16 := by
    rw [List.length_append, colors_length, List.length_reverse, colors_length]
  rw [hl] at h
  exact h

/-- Rational affine balanced rescaling changes no support beyond that cone. -/
def affineRep (c : Q') (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (grow extent 16 support) (affine hw0 hw1 K extent hK c x) := by
  exact LocalRep.sub hw0 hw1 K extent hK _
    (LocalRep.smul hw0 hw1 K extent hK _ c
      (balancedRep hw0 hw1 K extent hK support R hx))
    (LocalRep.mono hw0 hw1 K extent hK R (fun i hi => mem_grow extent 16 support i hi))

/-- Explicit representative of the LITERAL degree-n first component. -/
def firstRep (c : Q') (n : Nat) (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (grow extent (16*n) support) (coupled hw0 hw1 K extent hK c x n).1 := by
  let rec pair : (m : Nat) →
      LR (grow extent (16*m) support) (coupled hw0 hw1 K extent hK c x m).1 ×
      LR (grow extent (16*(m+1)) support) (coupled hw0 hw1 K extent hK c x (m+1)).1
    | 0 => by
      refine ⟨R, ?_⟩
      have he : (coupled hw0 hw1 K extent hK c x 1).1 = affine hw0 hw1 K extent hK c x :=
        GNSChebyshevRecurrence.first_one _ (affine_selfAdjoint hw0 hw1 K extent hK c) x
      rw [he]
      exact affineRep hw0 hw1 K extent hK c support R hx
    | m+1 => by
      let ih := pair m
      refine ⟨ih.2, ?_⟩
      have RA0 := affineRep hw0 hw1 K extent hK c (grow extent (16*(m+1)) support) ih.2
        (coupled_first_localized hw0 hw1 K extent hK c (m+1) support x hx)
      have RA : LR (grow extent (16*(m+2)) support)
          (affine hw0 hw1 K extent hK c (coupled hw0 hw1 K extent hK c x (m+1)).1) := by
        have he : 16*(m+2) = 16*(m+1)+16 := by omega
        rw [he, grow_add]
        exact RA0
      have RP : LR (grow extent (16*(m+2)) support) (coupled hw0 hw1 K extent hK c x m).1 :=
        LocalRep.mono hw0 hw1 K extent hK ih.1 (fun i hi =>
          grow_mono_steps extent (16*m) (16*(m+2)) support (by omega) i hi)
      rw [coupled_first_recurrence hw0 hw1 K extent hK c x m]
      exact LocalRep.sub hw0 hw1 K extent hK _
        (LocalRep.add hw0 hw1 K extent hK _ RA RA) RP
  exact (pair n).1

private theorem affine_zero (c : Q') :
    affine hw0 hw1 K extent hK c (embedV F (F).zero) = embedV F (F).zero := by
  apply eq_of_pairings_equal
  intro z
  rw [affine_selfAdjoint hw0 hw1 K extent hK c,
    (F).cinnerCompl_embedZero_left, (F).cinnerCompl_embedZero_left]

/-- The actual auxiliary at n+1 has a literal representative in radius 16*n,
not merely fixation by conditional projections outside that radius. -/
def auxiliaryRep (c : Q') (n : Nat) (support : List Z4Link) {x : GNSCompletionSpace F}
    (R : LR support x) (hx : Localized hw0 hw1 K extent hK support x) :
    LR (grow extent (16*n) support) (coupled hw0 hw1 K extent hK c x (n+1)).2 :=
  match n with
  | 0 => by
    change LR support ((F).cAdd x (affine hw0 hw1 K extent hK c (embedV F (F).zero)))
    rw [affine_zero hw0 hw1 K extent hK c]
    exact LocalRep.add hw0 hw1 K extent hK support R (LocalRep.zero hw0 hw1 K extent hK support)
  | n+1 => by
    let ih := auxiliaryRep c n support R hx
    have RA0 := affineRep hw0 hw1 K extent hK c (grow extent (16*n) support) ih
      (coupled_second_succ_localized hw0 hw1 K extent hK c n support x hx)
    have RA : LR (grow extent (16*(n+1)) support)
        (affine hw0 hw1 K extent hK c (coupled hw0 hw1 K extent hK c x (n+1)).2) := by
      have he : 16*(n+1) = 16*n+16 := by omega
      rw [he, grow_add]
      exact RA0
    exact LocalRep.add hw0 hw1 K extent hK _
      (firstRep hw0 hw1 K extent hK c (n+1) support R hx) RA

#print axioms layerRep
#print axioms runLayersRep
#print axioms balancedRep
#print axioms affineRep
#print axioms firstRep
#print axioms auxiliaryRep

end YMGap.Continuum.BF4ExactSlabLocalCauchyCone
