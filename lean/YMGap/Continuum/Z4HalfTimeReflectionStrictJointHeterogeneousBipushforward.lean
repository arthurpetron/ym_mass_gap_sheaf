/-
# Heterogeneous two-code pushforward for strict reflection forms

The existing oriented bipushforward used one Boolean target space and one
coefficient table because it was introduced for a reflection diagonal.  An
off-diagonal strict-cylinder coefficient can have different root counts and
different coefficient tables on its two sides.  This file proves the exact
finite pushforward with separate left and right target spaces, then applies
it to the normalized support reflection form.

All identities are finite exact-rational identities.  No covariance,
positivity, limiting argument, or numerical estimate is assumed.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite heterogeneous pushforward -/

/-- Push a source-pair kernel through unrelated left and right finite codes. -/
def finiteJointKernelHeterogeneousBipushforward
    {Source LeftTarget RightTarget : Type}
    [DecidableEq LeftTarget] [DecidableEq RightTarget]
    (source : List Source) (joint : Source → Source → Q')
    (leftCode : Source → LeftTarget)
    (rightCode : Source → RightTarget)
    (left : LeftTarget) (right : RightTarget) : Q' :=
  fiberWeight (cartesian source source)
    (fun pair => joint pair.1 pair.2)
    (fun pair => (leftCode pair.1, rightCode pair.2))
    (left, right)

/-- A finite cross form whose two coefficient indices may have unrelated
types and unrelated enumerations. -/
def finiteHeterogeneousCrossBilinear
    {LeftTarget RightTarget : Type}
    (leftTargets : List LeftTarget) (rightTargets : List RightTarget)
    (leftCoefficient : LeftTarget → Q')
    (rightCoefficient : RightTarget → Q')
    (joint : LeftTarget → RightTarget → Q') : Q' :=
  listQSum (fun left => listQSum (fun right =>
    (leftCoefficient left * rightCoefficient right) * joint left right)
    rightTargets) leftTargets

/-- Exact heterogeneous two-code pushforward of an oriented cross form. -/
theorem finiteHeterogeneousCrossBilinear_bipushforward_eqv_cross
    {Source LeftTarget RightTarget : Type}
    [DecidableEq LeftTarget] [DecidableEq RightTarget]
    (source : List Source) (joint : Source → Source → Q')
    (leftCode : Source → LeftTarget)
    (rightCode : Source → RightTarget)
    (leftTargets : List LeftTarget) (rightTargets : List RightTarget)
    (hleftNodup : leftTargets.Nodup)
    (hrightNodup : rightTargets.Nodup)
    (hleft : ∀ item, item ∈ source → leftCode item ∈ leftTargets)
    (hright : ∀ item, item ∈ source → rightCode item ∈ rightTargets)
    (leftCoefficient : LeftTarget → Q')
    (rightCoefficient : RightTarget → Q') :
    finiteHeterogeneousCrossBilinear
        leftTargets rightTargets leftCoefficient rightCoefficient
        (finiteJointKernelHeterogeneousBipushforward
          source joint leftCode rightCode) ≈
      finiteJointCrossBilinear source
        (fun item => leftCoefficient (leftCode item))
        (fun item => rightCoefficient (rightCode item)) joint := by
  let sourcePairs := cartesian source source
  let targetPairs := cartesian leftTargets rightTargets
  let pairCode : Source × Source → LeftTarget × RightTarget := fun pair =>
    (leftCode pair.1, rightCode pair.2)
  let sourceWeight : Source × Source → Q' := fun pair =>
    joint pair.1 pair.2
  let targetCoefficient : LeftTarget × RightTarget → Q' := fun pair =>
    leftCoefficient pair.1 * rightCoefficient pair.2
  have htargetNodup : targetPairs.Nodup := by
    unfold targetPairs
    exact cartesian_nodup leftTargets rightTargets
      hleftNodup hrightNodup
  have hpairsCovered : ∀ pair, pair ∈ sourcePairs →
      pairCode pair ∈ targetPairs := by
    intro pair hpair
    have hparts := (mem_cartesian_iff source source pair).1 hpair
    apply (mem_cartesian_iff leftTargets rightTargets (pairCode pair)).2
    exact ⟨hleft pair.1 hparts.1, hright pair.2 hparts.2⟩
  unfold finiteHeterogeneousCrossBilinear
    finiteJointCrossBilinear
    finiteJointKernelHeterogeneousBipushforward
  refine Q'.eqv_trans _
    (listQSum (fun pair =>
      targetCoefficient pair *
        fiberWeight sourcePairs sourceWeight pairCode pair)
      targetPairs) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_cartesian_eq_nested
        (fun pair => targetCoefficient pair *
          fiberWeight sourcePairs sourceWeight pairCode pair)
        leftTargets rightTargets)
  · refine Q'.eqv_trans _
      (listQSum (fun pair =>
        finiteCoefficientZeroExtension
            sourcePairs sourceWeight pairCode pair *
          targetCoefficient pair) targetPairs) _ ?_ ?_
    · apply listQSum_congr
      intro pair
      exact Q'.mul_comm_eqv _ _
    · refine Q'.eqv_trans _
        (listQSum (fun pair =>
          sourceWeight pair * targetCoefficient (pairCode pair))
          sourcePairs) _
        (finiteCoefficientZeroExtension_reindex_mul
          sourcePairs sourceWeight pairCode targetPairs
          htargetNodup hpairsCovered targetCoefficient) ?_
      refine Q'.eqv_trans _
        (listQSum (fun pair =>
          targetCoefficient (pairCode pair) * sourceWeight pair)
          sourcePairs) _ ?_ ?_
      · apply listQSum_congr
        intro pair
        exact Q'.mul_comm_eqv _ _
      · exact listQSum_cartesian_eq_nested
          (fun pair =>
            targetCoefficient (pairCode pair) * sourceWeight pair)
          source source

/-! ## 2. Normalized strict-support specialization -/

def centralNormalizedSupportHeterogeneousBipairLaw
    {LeftTarget RightTarget : Type}
    [DecidableEq LeftTarget] [DecidableEq RightTarget]
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCode : List Nat → LeftTarget)
    (rightCode : List Nat → RightTarget)
    (left : LeftTarget) (right : RightTarget) : Q' :=
  finiteJointKernelHeterogeneousBipushforward
    (centralHalfSupportSpace half)
    (centralNormalizedSupportPairLaw coupling hcoupling cutoff half)
    leftCode rightCode left right

/-- The normalized support reflection form is the heterogeneous finite cross
form of its two-code pushforward law. -/
theorem centralNormalizedSupportReflectionBilinear_eqv_heterogeneousBipair
    {LeftTarget RightTarget : Type}
    [DecidableEq LeftTarget] [DecidableEq RightTarget]
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCode : List Nat → LeftTarget)
    (rightCode : List Nat → RightTarget)
    (leftTargets : List LeftTarget) (rightTargets : List RightTarget)
    (hleftNodup : leftTargets.Nodup)
    (hrightNodup : rightTargets.Nodup)
    (hleft : ∀ support, support ∈ centralHalfSupportSpace half →
      leftCode support ∈ leftTargets)
    (hright : ∀ support, support ∈ centralHalfSupportSpace half →
      rightCode support ∈ rightTargets)
    (leftCoefficient : LeftTarget → Q')
    (rightCoefficient : RightTarget → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
        (fun support => leftCoefficient (leftCode support))
        (fun support => rightCoefficient (rightCode support)) ≈
      finiteHeterogeneousCrossBilinear
        leftTargets rightTargets leftCoefficient rightCoefficient
        (centralNormalizedSupportHeterogeneousBipairLaw
          coupling hcoupling cutoff half leftCode rightCode) := by
  let denominator := slabParametricKPhysicalPartition
    coupling cutoff (centralExtent half)
  have hdenominator : (0 : Q') < denominator :=
    slabParametricKPhysicalPartition_pos
      hcoupling cutoff (centralExtent half)
  let raw := centralSupportReflectedKernel coupling cutoff half
  let normalized := centralNormalizedSupportPairLaw
    coupling hcoupling cutoff half
  have hpolarized :=
    finiteJointPolarizedBilinear_eqv_cross_of_joint_symm
      (centralHalfSupportSpace half)
      (fun support => leftCoefficient (leftCode support))
      (fun support => rightCoefficient (rightCode support))
      raw
      (fun left _ right _ =>
        centralSupportReflectedKernel_symm
          coupling cutoff half left right)
  have hnormalized :
      finiteJointCrossBilinear
          (centralHalfSupportSpace half)
          (fun support => leftCoefficient (leftCode support))
          (fun support => rightCoefficient (rightCode support))
          normalized ≈
        Q'.divPos
          (finiteJointCrossBilinear
            (centralHalfSupportSpace half)
            (fun support => leftCoefficient (leftCode support))
            (fun support => rightCoefficient (rightCode support))
            raw)
          denominator hdenominator := by
    simpa only [normalized, raw, denominator,
      centralNormalizedSupportPairLaw] using
      (finiteJointCrossBilinear_divPos_kernel_eqv
        (centralHalfSupportSpace half)
        (fun support => leftCoefficient (leftCode support))
        (fun support => rightCoefficient (rightCode support))
        raw denominator hdenominator)
  have hpush :=
    finiteHeterogeneousCrossBilinear_bipushforward_eqv_cross
      (centralHalfSupportSpace half) normalized leftCode rightCode
      leftTargets rightTargets hleftNodup hrightNodup hleft hright
      leftCoefficient rightCoefficient
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hpolarized) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hnormalized) ?_
  exact Q'.eqv_symm hpush

#print axioms finiteHeterogeneousCrossBilinear_bipushforward_eqv_cross
#print axioms centralNormalizedSupportReflectionBilinear_eqv_heterogeneousBipair

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
