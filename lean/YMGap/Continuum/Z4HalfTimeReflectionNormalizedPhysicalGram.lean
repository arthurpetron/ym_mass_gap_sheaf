/-
# Normalized finite corrected-slab reflection positivity

The full-slab OS numerator is useful as a finite expectation only after its
normalizing partition is proved strictly positive.  This file derives that
fact from the exact vacuum summand.  Every corrected-slab summand is
nonnegative at nonnegative coupling, the all-zero summand is exactly one, and
the complete partition is therefore at least one and strictly positive.

Division uses the substrate's positive-denominator rational `Q'.divPos`.
The normalized full-slab OS quadratic is nonnegative for every rational test
function, and the constant-one test is exactly normalized to one.
-/

import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
import YMGap.Continuum.Z4ExplicitExcitationLocalization
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every corrected-slab production summand is nonnegative -/

private theorem slabParametricCoefficient_nonnegative
    {w : Q'} (hw : (0 : Q') <= w) (K spin : Nat) :
    (0 : Q') <= coeffAt (heatKernelPacket K w) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local
    (value : Nat -> Q') (hvalue : ∀ id, (0 : Q') <= value id) :
    ∀ ids : List Nat, (0 : Q') <= eliminateLinks value ids
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (eliminateLinks_nonnegative_local value hvalue tail)

theorem slabParametricKPhysicalTerm_nonnegative
    {w : Q'} (hw : (0 : Q') <= w) (K extent : Nat)
    (physical : EdgeLabelling) :
    (0 : Q') <= slabParametricKPhysicalTerm w K extent physical := by
  unfold slabParametricKPhysicalTerm slabParametricKPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_nonnegative_local _
      (fun id => slabParametricCoefficient_nonnegative
        hw K (physical id)) _)
    (zero_le_ofNat _)

/-! ## 2. The exact corrected-slab vacuum summand -/

private theorem eliminateLinks_eqv_one_local (value : Nat -> Q') :
    ∀ ids : List Nat, (∀ id, id ∈ ids -> value id ≈ 1) ->
      eliminateLinks value ids ≈ 1
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hvalue => by
      have hhead := hvalue head List.mem_cons_self
      have htail := eliminateLinks_eqv_one_local value tail
        (fun id hid => hvalue id (List.mem_cons_of_mem head hid))
      refine Q'.eqv_trans _ (1 * 1) _ ?_ (Q'.one_mul_eqv 1)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hhead)
        (Q'.mul_eqv_congr_left _ _ _ htail)

theorem slabParametricKPhysicalFaceFactor_zero_eqv_one
    (w : Q') (K extent : Nat) :
    slabParametricKPhysicalFaceFactor w K extent zeroEdgeLabelling ≈ 1 := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_eqv_one_local
  intro id _
  change coeffAt (heatKernelPacket K w) 0 ≈ 1
  rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
  exact Q'.eqv_refl 1

private theorem externalSpinsOfList_map_zero : ∀ ids : List Nat,
    externalSpinsOfList (ids.map zeroEdgeLabelling) =
      zeroEdgeLabelling
  | [] => by
      funext position
      simp [externalSpinsOfList, zeroEdgeLabelling]
  | head :: tail => by
      funext position
      cases position with
      | zero => simp [externalSpinsOfList, zeroEdgeLabelling]
      | succ position =>
          simpa [externalSpinsOfList, zeroEdgeLabelling] using
            congrFun (externalSpinsOfList_map_zero tail) position

theorem slabExplicitLinkMultiplicity_zero_eq_one
    (K extent : Nat) (link :
      YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    slabExplicitLinkMultiplicity K extent zeroEdgeLabelling link = 1 := by
  simp only [slabExplicitLinkMultiplicity]
  rw [externalSpinsOfList_map_zero]
  apply explicitValenceMultiplicity_eq_one_of_zero_prefix
  · simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  · intro position hposition
    rfl

theorem slabExplicitLinkMultiplicityProduct_zero_eq_one
    (K extent : Nat) :
    slabExplicitLinkMultiplicityProduct K extent zeroEdgeLabelling = 1 := by
  unfold slabExplicitLinkMultiplicityProduct
  generalize boundaryCompleteSlabLinks extent = links
  induction links with
  | nil => rfl
  | cons head tail ih =>
      simp only [natListProduct]
      rw [slabExplicitLinkMultiplicity_zero_eq_one K extent head, ih]

theorem slabParametricKPhysicalTerm_zero_eqv_one
    (w : Q') (K extent : Nat) :
    slabParametricKPhysicalTerm w K extent zeroEdgeLabelling ≈ 1 := by
  unfold slabParametricKPhysicalTerm
  rw [slabExplicitLinkMultiplicityProduct_zero_eq_one K extent]
  refine Q'.eqv_trans _ (1 * 1) _ ?_ (Q'.one_mul_eqv 1)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (slabParametricKPhysicalFaceFactor_zero_eqv_one w K extent))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl 1))

private theorem zeroEdgeLabelling_mem_bounded
    (K : Nat) : ∀ ids : List Nat,
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_nonnegative_local {A : Type}
    (value : A -> Q') (hvalue : ∀ x, (0 : Q') <= value x) :
    ∀ xs : List A, (0 : Q') <= listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_local {A : Type}
    (value : A -> Q') (hvalue : ∀ x, (0 : Q') <= value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs ->
      value x <= listQSum value xs
  | [], _, h => absurd h List.not_mem_nil
  | head :: tail, x, h => by
      rcases List.mem_cons.mp h with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail <=
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 3. Strict positivity of the full corrected-slab partition -/

theorem slabParametricKPhysicalPartition_one_le
    {w : Q'} (hw : (0 : Q') <= w) (K extent : Nat) :
    (1 : Q') <= slabParametricKPhysicalPartition w K extent := by
  unfold slabParametricKPhysicalPartition
  have hmember := listQSum_member_le_local
    (slabParametricKPhysicalTerm w K extent)
    (slabParametricKPhysicalTerm_nonnegative hw K extent)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))
    (zeroEdgeLabelling_mem_bounded K (slabPhysicalFaceEdges extent))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (slabParametricKPhysicalTerm_zero_eqv_one w K extent)))
    hmember

theorem slabParametricKPhysicalPartition_pos
    {w : Q'} (hw : (0 : Q') <= w) (K extent : Nat) :
    (0 : Q') < slabParametricKPhysicalPartition w K extent :=
  lt_of_lt_of_le (by decide)
    (slabParametricKPhysicalPartition_one_le hw K extent)

/-! ## 4. The normalized full-slab OS quadratic -/

def centralNormalizedFullPhysicalReflectionQuadratic
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  Q'.divPos
    (centralFullPhysicalReflectionQuadratic w K half coefficient)
    (slabParametricKPhysicalPartition w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))

theorem centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    (0 : Q') <=
      centralNormalizedFullPhysicalReflectionQuadratic
        w hw K half coefficient := by
  unfold centralNormalizedFullPhysicalReflectionQuadratic Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralFullPhysicalReflectionQuadratic_nonnegative hw coefficient)
    (Q'.le_of_lt (Q'.recipPos_pos _
      (slabParametricKPhysicalPartition_pos hw K
        (centralExtent half))))

theorem centralFullPhysicalReflectionQuadratic_one_eq_partition
    (w : Q') (K half : Nat) :
    centralFullPhysicalReflectionQuadratic w K half (fun _ => 1) ≈
      slabParametricKPhysicalPartition w K (centralExtent half) := by
  unfold centralFullPhysicalReflectionQuadratic
    slabParametricKPhysicalPartition
  apply listQSum_congr
  intro physical
  refine Q'.eqv_trans _ (1 *
    slabParametricKPhysicalTerm w K (centralExtent half) physical) _ ?_
    (Q'.one_mul_eqv _)
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1)

/-- Exact normalization check: the constant-one OS observable has expectation
one, so no vacuum or multiplicity factor has been lost in the full-slab
reindexing. -/
theorem centralNormalizedFullPhysicalReflectionQuadratic_one
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat) :
    centralNormalizedFullPhysicalReflectionQuadratic
      w hw K half (fun _ => 1) ≈ 1 := by
  unfold centralNormalizedFullPhysicalReflectionQuadratic Q'.divPos
  refine Q'.eqv_trans _
    (slabParametricKPhysicalPartition w K (centralExtent half) *
      Q'.recipPos
        (slabParametricKPhysicalPartition w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos hw K
          (centralExtent half))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralFullPhysicalReflectionQuadratic_one_eq_partition
        w K half)
  · exact Q'.mul_recipPos_eqv _
      (slabParametricKPhysicalPartition_pos hw K
        (centralExtent half))

end YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalTerm_nonnegative
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalFaceFactor_zero_eqv_one
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabExplicitLinkMultiplicity_zero_eq_one
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabExplicitLinkMultiplicityProduct_zero_eq_one
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalTerm_zero_eqv_one
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalPartition_one_le
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalPartition_pos
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.centralFullPhysicalReflectionQuadratic_one_eq_partition
#print axioms YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.centralNormalizedFullPhysicalReflectionQuadratic_one
