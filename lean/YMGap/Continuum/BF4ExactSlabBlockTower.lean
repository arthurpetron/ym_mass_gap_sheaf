/-
# Nested actual block conditional projections

For nested physical block families, the larger-block conditional output is
already exterior to the smaller block. This proves the tower identity on the
SAME original full-action completion. The mixed residual is nonnegative by
the ordinary Hilbert-form identity for commuting orthogonal projections.
There is no strict contraction, block-angle bound, or scaling assertion.
-/

import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.GNSDenseFixedPoint
import YMGap.Continuum.GNSProjectionResidualPair

namespace YMGap.Continuum.BF4ExactSlabBlockTower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSDenseFixedPoint
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

/-- One family on the actual original completion, indexed by all supplied
finite in-range physical link lists. No disjointness or gap is built in. -/
def blockFamily : Family F
    {links : List Z4Link //
      ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent} where
  op := fun s => conditionalProjection hw0 hw1 K extent hK s.val s.property
  adjoint := fun s x y =>
    conditionalProjection_selfAdjoint hw0 hw1 K extent hK s.val s.property x y
  idem := fun s x =>
    conditionalProjection_idempotent hw0 hw1 K extent hK s.val s.property x

/-- Literal list inclusion entails inclusion of the coordinate slots used
by the block Haar projection. -/
theorem slots_subset_of_links_subset (A B : List Z4Link)
    (hAB : ∀ link, link ∈ A → link ∈ B) :
    ∀ i, i ∈ slots extent A → i ∈ slots extent B := by
  intro i hi
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨link, hAB link hlink, rfl⟩

variable (A B : List Z4Link)
  (hA : ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent)
  (hB : ∀ link, link ∈ B → link ∈ boundaryCompleteSlabLinks extent)

local notation "PA" => conditionalProjection hw0 hw1 K extent hK A hA
local notation "PB" => conditionalProjection hw0 hw1 K extent hK B hB

/-- The larger-block output has a supplied Cauchy representative whose
every term is independent of every smaller-block slot. -/
theorem tower_dense
    (hAB : ∀ i, i ∈ slots extent A → i ∈ slots extent B)
    (p : (F).V) : PA (PB (embedV F p)) = PB (embedV F p) := by
  rw [conditionalProjection_embed hw0 hw1 K extent hK B hB]
  exact fixed_of_cauchy_terms PA
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK A hA)
    (conditionalRep hw0 hw1 K extent hK B hB p)
    (fun n => conditionalProjection_fix_exterior_polynomial
      hw0 hw1 K extent hK A hA _
      (fun i hi => by
        change QuaternionBlockIndependent i
          ((inverseCauchy hw0 hw1 K extent hK B hB
            (numeratorVector hw0 hw1 K extent hK B p.val p.property)).seq n).val
        exact inverseCauchy_independent hw0 hw1 K extent hK B hB p
          n i (hAB i hi)))

/-- Nested-block tower on every vector of the original completed carrier.
The argument transports dense fixedness using existing Cauchy moduli. -/
theorem tower
    (hAB : ∀ i, i ∈ slots extent A → i ∈ slots extent B)
    (x : GNSCompletionSpace F) : PA (PB x) = PB x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact fixed_of_cauchy_images PA PB
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK A hA)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK B hB)
    X (fun n => tower_dense hw0 hw1 K extent hK A B hA hB hAB (X.seq n))

/-- The reverse composition follows from the tower law by taking adjoints;
it is not a second independence assertion on the smaller-block output. -/
theorem reverse_tower
    (hAB : ∀ i, i ∈ slots extent A → i ∈ slots extent B)
    (x : GNSCompletionSpace F) : PB (PA x) = PB x := by
  apply eq_of_pairings_equal
  intro y
  calc
    (F).cinnerCompl (PB (PA x)) y =
        (F).cinnerCompl (PA x) (PB y) :=
      conditionalProjection_selfAdjoint hw0 hw1 K extent hK B hB _ _
    _ = (F).cinnerCompl x (PA (PB y)) :=
      conditionalProjection_selfAdjoint hw0 hw1 K extent hK A hA _ _
    _ = (F).cinnerCompl x (PB y) := by
      rw [tower hw0 hw1 K extent hK A B hA hB hAB y]
    _ = (F).cinnerCompl (PB x) y :=
      (conditionalProjection_selfAdjoint hw0 hw1 K extent hK B hB _ _).symm

theorem nested_commute
    (hAB : ∀ i, i ∈ slots extent A → i ∈ slots extent B)
    (x : GNSCompletionSpace F) : PA (PB x) = PB (PA x) :=
  (tower hw0 hw1 K extent hK A B hA hB hAB x).trans
    (reverse_tower hw0 hw1 K extent hK A B hA hB hAB x).symm

/-- The nested residual-pair contribution is nonnegative in the ORIGINAL
completed full-action form. This is not a strict angle estimate. -/
theorem nested_residual_pair_nonnegative
    (hAB : ∀ i, i ∈ slots extent A → i ∈ slots extent B)
    (x : GNSCompletionSpace F) :
    RCle RCzero
      ((F).cinnerCompl ((F).cSub x (PA x)) ((F).cSub x (PB x))) := by
  let sA : {links : List Z4Link //
      ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent} := ⟨A, hA⟩
  let sB : {links : List Z4Link //
      ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent} := ⟨B, hB⟩
  have hcomm : ∀ y : GNSCompletionSpace F,
      (blockFamily hw0 hw1 K extent hK).op sA
        ((blockFamily hw0 hw1 K extent hK).op sB y) =
      (blockFamily hw0 hw1 K extent hK).op sB
        ((blockFamily hw0 hw1 K extent hK).op sA y) :=
    nested_commute hw0 hw1 K extent hK A B hA hB hAB
  change RCle RCzero
    ((F).cinnerCompl
      ((blockFamily hw0 hw1 K extent hK).residual sA x)
      ((blockFamily hw0 hw1 K extent hK).residual sB x))
  exact (blockFamily hw0 hw1 K extent hK).commuting_residual_pairing_nonnegative
    sA sB hcomm x

#print axioms blockFamily
#print axioms slots_subset_of_links_subset
#print axioms tower_dense
#print axioms tower
#print axioms reverse_tower
#print axioms nested_commute
#print axioms nested_residual_pair_nonnegative

end YMGap.Continuum.BF4ExactSlabBlockTower
