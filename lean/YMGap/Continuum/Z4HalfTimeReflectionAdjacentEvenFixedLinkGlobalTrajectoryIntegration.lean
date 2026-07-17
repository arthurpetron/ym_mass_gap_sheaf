/-
# Global integration of adjacent-even fixed-link trajectories

This file lifts the pointwise incidence regrouping through the actual bounded
source, target, and internal-trajectory sums.  The literal endpoint-channel
kernel is first expanded into global incidence trajectories, target and
trajectory sums are interchanged exactly, the link-major transition product is
regrouped by face, and terminal target deltas are collapsed.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qMulCongrLocal {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Lower-half endpoint amplitudes -/

def adjacentEvenLowerLinkAmplitude
    (K radius : Nat) (physical : Nat → Nat)
    (link : Z4Link) (channel : Nat) : Q' :=
  Q'.ofNat (fusionChannelAmplitude (linkAuxiliaryCutoff K)
    (adjacentEvenIncidentLowerSpins radius physical link) channel)

def adjacentEvenLowerAmplitudeProduct
    (K radius : Nat) (physical : Nat → Nat)
    (channel : Z4Link → Nat) : Q' :=
  listQProduct (fun link =>
    adjacentEvenLowerLinkAmplitude
      K radius physical link (channel link))
    (adjacentEvenFixedLinks radius)

private theorem listQProduct_pointwise_mul_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    listQProduct (fun item => left item * right item) items ≈
      listQProduct left items * listQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (listQProduct_pointwise_mul_local left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (listQProduct left tail) (listQProduct right tail)

private theorem listQProduct_pointwise_triple_local
    {A : Type} (first second third : A → Q')
    (items : List A) :
    listQProduct (fun item =>
        (first item * second item) * third item) items ≈
      (listQProduct first items * listQProduct second items) *
        listQProduct third items := by
  refine Q'.eqv_trans _ _ _
    (listQProduct_pointwise_mul_local
      (fun item => first item * second item) third items) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (listQProduct_pointwise_mul_local first second items)

/-! ## 2. Fixed source/target endpoint product expands into trajectories -/

private theorem endpointLinkProduct_eqv_separated
    (K radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat) :
    listQProduct (fun link =>
        adjacentEvenFixedLinkEndpointFactor K radius physical link
          (source link) (target link))
        (adjacentEvenFixedLinks radius) ≈
      (adjacentEvenLowerAmplitudeProduct K radius physical source *
        listQProduct (fun link =>
          Q'.ofNat (fusionWalkMultiplicity (linkAuxiliaryCutoff K)
            (source link) (target link)
            (adjacentEvenIncidentFixedSpins radius physical link)))
          (adjacentEvenFixedLinks radius)) *
        adjacentEvenReflectedUpperAmplitudeProduct
          K radius physical target := by
  unfold adjacentEvenFixedLinkEndpointFactor
    adjacentEvenLowerAmplitudeProduct adjacentEvenLowerLinkAmplitude
    adjacentEvenReflectedUpperAmplitudeProduct
    adjacentEvenReflectedUpperLinkAmplitude
  exact listQProduct_pointwise_triple_local _ _ _
    (adjacentEvenFixedLinks radius)

private theorem endpointLinkProduct_eqv_trajectorySum
    (K radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat) :
    listQProduct (fun link =>
        adjacentEvenFixedLinkEndpointFactor K radius physical link
          (source link) (target link))
        (adjacentEvenFixedLinks radius) ≈
      listQSum (fun trajectory =>
        (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenTrajectoryLinkProduct
            radius physical source target trajectory) *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target)
        (adjacentEvenFixedIncidenceTrajectoryStates K radius) := by
  let lower := adjacentEvenLowerAmplitudeProduct K radius physical source
  let upper := adjacentEvenReflectedUpperAmplitudeProduct K radius physical target
  let trajectoryTerm : FixedIncidenceTrajectoryState → Q' :=
    fun trajectory => adjacentEvenTrajectoryLinkProduct
      radius physical source target trajectory
  let walkProduct := listQProduct (fun link =>
    Q'.ofNat (fusionWalkMultiplicity (linkAuxiliaryCutoff K)
      (source link) (target link)
      (adjacentEvenIncidentFixedSpins radius physical link)))
    (adjacentEvenFixedLinks radius)
  let trajectoryKernel :=
    adjacentEvenGlobalFixedIncidenceTrajectoryKernel
      K radius physical source target
  have hwalk : walkProduct ≈ trajectoryKernel :=
    Q'.eqv_symm
      (adjacentEvenGlobalFixedIncidenceTrajectoryKernel_eqv_transitionProduct
        K radius physical source target)
  have hreplace :
      (lower * walkProduct) * upper ≈
        (lower * trajectoryKernel) * upper :=
    Q'.mul_eqv_congr_right _ _ upper
      (Q'.mul_eqv_congr_left lower _ _ hwalk)
  refine Q'.eqv_trans _ _ _
    (endpointLinkProduct_eqv_separated
      K radius physical source target) ?_
  refine Q'.eqv_trans _ _ _ hreplace ?_
  unfold trajectoryKernel adjacentEvenGlobalFixedIncidenceTrajectoryKernel
    adjacentEvenFixedIncidenceTrajectoryFactor
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ upper
      (Q'.eqv_symm
        (listQSum_mul_left lower trajectoryTerm
          (adjacentEvenFixedIncidenceTrajectoryStates K radius)))) ?_
  exact Q'.eqv_symm
    (listQSum_mul_right
      (fun trajectory => lower * trajectoryTerm trajectory) upper
      (adjacentEvenFixedIncidenceTrajectoryStates K radius))

/-! ## 3. The fully expanded and collapsed global sums -/

def adjacentEvenExpandedFixedLinkTrajectorySum
    (K radius : Nat) (physical : Nat → Nat) : Q' :=
  let sources := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let targets := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let trajectories := adjacentEvenFixedIncidenceTrajectoryStates K radius
  listQSum (fun source =>
    listQSum (fun target =>
      listQSum (fun trajectory =>
        (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenTrajectoryLinkProduct
            radius physical source target trajectory) *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target)
        trajectories) targets) sources

theorem adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_expanded
    (K radius : Nat) (physical : Nat → Nat) :
    adjacentEvenGlobalFixedLinkEndpointTrajectorySum
        K radius physical ≈
      adjacentEvenExpandedFixedLinkTrajectorySum
        K radius physical := by
  unfold adjacentEvenGlobalFixedLinkEndpointTrajectorySum
    adjacentEvenExpandedFixedLinkTrajectorySum
  apply listQSum_congr
  intro source
  apply listQSum_congr
  intro target
  exact endpointLinkProduct_eqv_trajectorySum
    K radius physical source target

def adjacentEvenCollapsedFixedLinkTrajectorySum
    (K radius : Nat) (physical : Nat → Nat) : Q' :=
  let sources := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let trajectories := adjacentEvenFixedIncidenceTrajectoryStates K radius
  listQSum (fun source =>
    listQSum (fun trajectory =>
      (adjacentEvenLowerAmplitudeProduct K radius physical source *
        adjacentEvenFaceTransitionProduct
          radius physical source trajectory) *
        adjacentEvenReflectedUpperAmplitudeProduct K radius physical
          (fun link => adjacentEvenTrajectoryFinalChannel
            radius source trajectory link))
      trajectories) sources

private theorem expandedSourceTerm_eqv_collapsed
    (K radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (hsource : source ∈ boundedLabellingsOn (linkAuxiliaryCutoff K)
      (adjacentEvenFixedLinks radius)) :
    listQSum (fun target =>
        listQSum (fun trajectory =>
          (adjacentEvenLowerAmplitudeProduct K radius physical source *
            adjacentEvenTrajectoryLinkProduct
              radius physical source target trajectory) *
            adjacentEvenReflectedUpperAmplitudeProduct
              K radius physical target)
          (adjacentEvenFixedIncidenceTrajectoryStates K radius))
      (boundedLabellingsOn (linkAuxiliaryCutoff K)
        (adjacentEvenFixedLinks radius)) ≈
      listQSum (fun trajectory =>
        (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenFaceTransitionProduct
            radius physical source trajectory) *
          adjacentEvenReflectedUpperAmplitudeProduct K radius physical
            (fun link => adjacentEvenTrajectoryFinalChannel
              radius source trajectory link))
        (adjacentEvenFixedIncidenceTrajectoryStates K radius) := by
  let targets := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let trajectories := adjacentEvenFixedIncidenceTrajectoryStates K radius
  let lower := adjacentEvenLowerAmplitudeProduct K radius physical source
  change listQSum (fun target =>
      listQSum (fun trajectory =>
        (lower * adjacentEvenTrajectoryLinkProduct
          radius physical source target trajectory) *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target) trajectories) targets ≈ _
  have hswap := listQSum_swap
    (fun target trajectory =>
      (lower * adjacentEvenTrajectoryLinkProduct
        radius physical source target trajectory) *
        adjacentEvenReflectedUpperAmplitudeProduct
          K radius physical target)
    targets trajectories
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm hswap) ?_
  apply listQSum_congr_on
  intro trajectory htrajectory
  let face := adjacentEvenFaceTransitionProduct
    radius physical source trajectory
  have hpoint : ∀ target,
      (lower * adjacentEvenTrajectoryLinkProduct
          radius physical source target trajectory) *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target ≈
        (lower * face) *
          (adjacentEvenLinkTerminalProduct
              radius source target trajectory *
            adjacentEvenReflectedUpperAmplitudeProduct
              K radius physical target) := by
    intro target
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left lower _ _
          (adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal
            radius physical source target trajectory))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv lower face
        (adjacentEvenLinkTerminalProduct
          radius source target trajectory) |>.symm |>
        Q'.mul_eqv_congr_right _ _
          (adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target)) ?_
    exact Q'.mul_assoc_eqv (lower * face)
      (adjacentEvenLinkTerminalProduct
        radius source target trajectory)
      (adjacentEvenReflectedUpperAmplitudeProduct
        K radius physical target)
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hpoint targets) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_left (lower * face)
      (fun target =>
        adjacentEvenLinkTerminalProduct radius source target trajectory *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target) targets) ?_
  exact Q'.mul_eqv_congr_left (lower * face) _ _
    (adjacentEvenSeparatedTerminalTargetSum_collapse
      hsource htrajectory)

theorem adjacentEvenExpandedFixedLinkTrajectorySum_eqv_collapsed
    (K radius : Nat) (physical : Nat → Nat) :
    adjacentEvenExpandedFixedLinkTrajectorySum
        K radius physical ≈
      adjacentEvenCollapsedFixedLinkTrajectorySum
        K radius physical := by
  unfold adjacentEvenExpandedFixedLinkTrajectorySum
    adjacentEvenCollapsedFixedLinkTrajectorySum
  apply listQSum_congr_on
  intro source hsource
  exact expandedSourceTerm_eqv_collapsed
    K radius physical source hsource

/-- Complete finite integration bridge for the literal fixed-link product. -/
theorem adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_collapsed
    (K radius : Nat) (physical : Nat → Nat) :
    adjacentEvenGlobalFixedLinkEndpointTrajectorySum
        K radius physical ≈
      adjacentEvenCollapsedFixedLinkTrajectorySum
        K radius physical :=
  Q'.eqv_trans _ _ _
    (adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_expanded
      K radius physical)
    (adjacentEvenExpandedFixedLinkTrajectorySum_eqv_collapsed
      K radius physical)

#print axioms adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_expanded
#print axioms adjacentEvenExpandedFixedLinkTrajectorySum_eqv_collapsed
#print axioms adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_collapsed

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
