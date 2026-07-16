/-
# Exact deterministic pushforward of a finite joint kernel

A joint kernel on a finite source list can be grouped by any finite
deterministic state code.  Each target entry is the complete source-pair
fiber, so unobserved source coordinates are summed rather than set to zero.
The quadratic with a target coefficient is exactly the source quadratic with
that coefficient pulled back along the code.
-/

import YMGap.Continuum.FiniteCoefficientZeroExtension
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.FiniteJointKernelPushforward

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Complete source-pair mass with prescribed left and right target codes. -/
def finiteJointKernelPushforward
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (code : Source → Target) (left right : Target) : Q' :=
  fiberWeight (cartesian source source)
    (fun pair => joint pair.1 pair.2)
    (fun pair => (code pair.1, code pair.2))
    (left, right)

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- Exact quadratic identity for deterministic joint pushforward.  The source
list may contain duplicates and the code need not be injective. -/
theorem finiteJointQuadratic_pushforward_eqv_pullback
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (code : Source → Target) (targets : List Target)
    (hnodup : targets.Nodup)
    (hcoverage : ∀ item, item ∈ source → code item ∈ targets)
    (coefficient : Target → Q') :
    finiteJointQuadratic targets coefficient
        (finiteJointKernelPushforward source joint code) ≈
      finiteJointQuadratic source
        (fun item => coefficient (code item)) joint := by
  let sourcePairs := cartesian source source
  let targetPairs := cartesian targets targets
  let pairCode : Source × Source → Target × Target := fun pair =>
    (code pair.1, code pair.2)
  let sourceWeight : Source × Source → Q' := fun pair =>
    joint pair.1 pair.2
  let targetCoefficient : Target × Target → Q' := fun pair =>
    coefficient pair.1 * coefficient pair.2
  have htargetNodup : targetPairs.Nodup := by
    unfold targetPairs
    exact cartesian_nodup targets targets hnodup hnodup
  have hpairsCovered : ∀ pair, pair ∈ sourcePairs →
      pairCode pair ∈ targetPairs := by
    intro pair hpair
    have hparts := (mem_cartesian_iff source source pair).1 hpair
    apply (mem_cartesian_iff targets targets (pairCode pair)).2
    exact ⟨hcoverage pair.1 hparts.1,
      hcoverage pair.2 hparts.2⟩
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        targetCoefficient pair *
          fiberWeight sourcePairs sourceWeight pairCode pair)
      targetPairs) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_cartesian_eq_nested_local
        (fun pair =>
          targetCoefficient pair *
            fiberWeight sourcePairs sourceWeight pairCode pair)
        targets targets)
  · refine Q'.eqv_trans _
      (listQSum
        (fun pair =>
          finiteCoefficientZeroExtension
              sourcePairs sourceWeight pairCode pair *
            targetCoefficient pair)
        targetPairs) _ ?_ ?_
    · apply listQSum_congr
      intro pair
      exact Q'.mul_comm_eqv
        (targetCoefficient pair)
        (fiberWeight sourcePairs sourceWeight pairCode pair)
    · refine Q'.eqv_trans _
        (listQSum
          (fun pair =>
            sourceWeight pair * targetCoefficient (pairCode pair))
          sourcePairs) _
        (finiteCoefficientZeroExtension_reindex_mul
          sourcePairs sourceWeight pairCode targetPairs
          htargetNodup hpairsCovered targetCoefficient) ?_
      refine Q'.eqv_trans _
        (listQSum
          (fun pair =>
            targetCoefficient (pairCode pair) * sourceWeight pair)
          sourcePairs) _ ?_ ?_
      · apply listQSum_congr
        intro pair
        exact Q'.mul_comm_eqv
          (sourceWeight pair) (targetCoefficient (pairCode pair))
      · exact listQSum_cartesian_eq_nested_local
          (fun pair =>
            targetCoefficient (pairCode pair) * sourceWeight pair)
          source source

#print axioms finiteJointQuadratic_pushforward_eqv_pullback

end YMGap.Continuum.FiniteJointKernelPushforward
