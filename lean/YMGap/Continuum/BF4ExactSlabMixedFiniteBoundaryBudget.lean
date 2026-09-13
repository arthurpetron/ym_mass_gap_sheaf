/-
# A computed cutoff-independent finite budget for the ORIGINAL boundary D

Each surviving probe-rooted core contributes its selective insertion weight
divided by its own positive collar-removal floor. The exact finite sum of
these nonnegative rational costs bounds D relative to its TWO original
partition factors, for every representation cutoff K. The budget explicitly
depends on w, extent, probe support, interior test and ambient face list.

This is a finite budget, NOT a volume-uniform bound or a summability/decay
theorem. Controlling this computed sum by collar and rooted-path counts is
the next mathematical obligation. No analytic input is assumed to do so.
-/

import YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRootedResummation
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedCoefficientBound
open YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem mixedRemovalFloor_pos {w : Q'} (hd : heatRemainderBound w < 1)
    (keep : Nat → Bool) (removed : List Nat) : (0 : Q') < mixedRemovalFloor w keep removed :=
  Q'.mul_pos (HKPos.pow_pos (HKPos.one_sub_pos hd) _) (HKPos.pow_pos (HKPos.one_sub_pos hd) _)

/-- The reciprocal is constructed from the proved positive local floor. -/
def normalizedCoreWeight (w : Q') (hd : heatRemainderBound w < 1) (extent : Nat)
    (links : List Z4Link) (keep : Nat → Bool) (ambient anchor : List Nat) : Q' :=
  mixedHeatWeight w keep anchor * Q'.recipPos (mixedRemovalFloor w keep (collarIds extent links anchor ambient))
    (mixedRemovalFloor_pos hd keep _)

/-- All parameters of the finite budget are data; there is no cutoff K. -/
def finiteBoundaryBudget (w : Q') (hd : heatRemainderBound w < 1) (extent : Nat)
    (links : List Z4Link) (keep : Nat → Bool) (ambient : List Nat) : Q' :=
  listQSum (normalizedCoreWeight w hd extent links keep ambient) (activeAnchors extent links keep ambient)

theorem normalizedCoreWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient anchor : List Nat) :
    (0 : Q') ≤ normalizedCoreWeight w hd extent links keep ambient anchor :=
  Q'.mul_nonneg _ _ (mixedHeatWeight_nonnegative hw keep anchor) (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem finiteBoundaryBudget_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient : List Nat) :
    (0 : Q') ≤ finiteBoundaryBudget w hd extent links keep ambient :=
  listQSum_nonnegative_on _ _ (fun anchor _ => normalizedCoreWeight_nonnegative hw hd extent links keep ambient anchor)

private theorem remove_positive_factor {R x b : Q'} (hR : (0 : Q') < R) (h : R*x ≤ b) :
    x ≤ Q'.recipPos R hR * b := by
  let i := Q'.recipPos R hR
  have hi : i*R ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv R hR)
  have he : i*(R*x) ≈ x := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv i R x))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x hi) (Q'.one_mul_eqv x))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm he))
    (Q'.mul_le_mul_of_nonneg_left _ _ i h (Q'.le_of_lt (Q'.recipPos_pos R hR)))

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x :: xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w < 1)
include hw0 hw1 hsmall hdelta

theorem mixedFamily_relative_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link)
    (hl : LinkLocal extent links p) (ambient anchor : List Nat) (hn : ambient.Nodup)
    (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
      ((c+c)*normalizedCoreWeight w hdelta extent links keep ambient anchor) * mixedPartition w K extent keep ambient := by
  have h := remove_positive_factor (mixedRemovalFloor_pos hdelta keep (collarIds extent links anchor ambient))
    (mixedFamily_weight_bound hw0 hw1 hsmall (Q'.le_of_lt hdelta) K extent keep p c P links hl ambient anchor hn ha hf hphys)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.var 1) (.mul (.var 2) (.var 0))) (.var 3)) (by decide)
    (fun i => if i = 0 then Q'.recipPos (mixedRemovalFloor w keep (collarIds extent links anchor ambient))
        (mixedRemovalFloor_pos hdelta keep _) else if i = 1 then c+c
      else if i = 2 then mixedHeatWeight w keep anchor else mixedPartition w K extent keep ambient)))

/-- The entire original mixed determinant is bounded by the computed sum. -/
theorem mixedNumerator_budget_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link)
    (hl : LinkLocal extent links p) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (mixedNumerator w K extent keep p ambient) ≤
      ((c+c)*finiteBoundaryBudget w hdelta extent links keep ambient) * mixedPartition w K extent keep ambient := by
  let weights := normalizedCoreWeight w hdelta extent links keep ambient
  let anchors := activeAnchors extent links keep ambient
  let Z := mixedPartition w K extent keep ambient
  have hsum : Q'.abs (listQSum (fun anchor => mixedCoefficient w K extent keep p anchor *
      mixedPartition w K extent keep (detachedIds extent links anchor ambient)) anchors) ≤
      listQSum (fun anchor => ((c+c)*weights anchor)*Z) anchors := by
    apply abs_sum_bound
    intro anchor ha
    have hs : anchor ∈ selections ambient := (List.mem_filter.mp (List.mem_filter.mp ha).1).1
    have hf : core extent links anchor = anchor := of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm
        (mixedFamily_resummed w K extent keep p links P.support hl ambient anchor hn hs hf))))
      (mixedFamily_relative_bound hw0 hw1 hsmall hdelta K extent keep p c P links hl ambient anchor hn hs hf hphys)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (mixedNumerator_active_expansion w K extent keep p links P.support hl ambient hn)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (listQSum_mul_right (fun anchor => (c+c)*weights anchor) Z anchors)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left (c+c) weights anchors)))))

/-- Concrete SAME boundary D and SAME full/interior unit moments, every K. -/
theorem boundaryNumerator_budget_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (hl : LinkLocal (centralExtent (half+padding)) links p) :
    Q'.abs (boundaryNumerator w half padding p K) ≤
      ((c+c)*finiteBoundaryBudget w hdelta (centralExtent (half+padding)) links (boundaryKeep half padding)
        (slabPhysicalFaceEdges (centralExtent (half+padding)))) *
          (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (boundary_mixedNumerator w K half padding p)))
    (Q'.le_trans' _ _ _ (mixedNumerator_budget_bound hw0 hw1 hsmall hdelta K (centralExtent (half+padding))
      (boundaryKeep half padding) p c P links hl _ (YMGap.Continuum.CayleyParentInj.range_nodup _) (fun _ h => h))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition w K half padding))))

end SmallNome
end YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget

#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.mixedRemovalFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.normalizedCoreWeight
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.finiteBoundaryBudget
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.normalizedCoreWeight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.finiteBoundaryBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.mixedFamily_relative_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.mixedNumerator_budget_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget.boundaryNumerator_budget_bound
