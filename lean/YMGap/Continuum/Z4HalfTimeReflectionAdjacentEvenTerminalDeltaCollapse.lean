/-
# Collapse of adjacent-even terminal endpoint channels

After pointwise incidence regrouping, the internal fixed-word transitions are
face-major and the only remaining target-channel dependence from the fixed
word is one terminal Kronecker delta per fixed link.  This file sums the
bounded target assignment exactly, replacing it by the reflected-upper
amplitude evaluated at the trajectory's final channel.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qMulCongrLocal {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Final-channel bounds -/

theorem fixedIdFinalChannel_le
    (cutoff : Nat) (channel : Nat → Nat) :
    ∀ start ids, start ≤ cutoff →
      (∀ id, id ∈ ids → channel id ≤ cutoff) →
      fixedIdFinalChannel channel start ids ≤ cutoff
  | start, [], hstart, _ => hstart
  | _, id :: rest, _, hchannel => by
      apply fixedIdFinalChannel_le cutoff channel (channel id) rest
      · exact hchannel id List.mem_cons_self
      · intro item hitem
        exact hchannel item (List.mem_cons_of_mem id hitem)

def adjacentEvenTrajectoryFinalChannel
    (radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (link : Z4Link) : Nat :=
  fixedIdFinalChannel (trajectory link) (source link)
    (adjacentEvenIncidentFixedFaceIds radius link)

theorem adjacentEvenTrajectoryFinalChannel_le
    {K radius : Nat}
    {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : source ∈ boundedLabellingsOn
      (linkAuxiliaryCutoff K) (adjacentEvenFixedLinks radius))
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius) :
    adjacentEvenTrajectoryFinalChannel
        radius source trajectory link ≤ linkAuxiliaryCutoff K := by
  apply fixedIdFinalChannel_le
  · exact boundedLabellingsOn_sound
      (linkAuxiliaryCutoff K) (adjacentEvenFixedLinks radius)
      source hsource link hlink
  · intro id hid
    have hlinkChoice : trajectory link ∈
        adjacentEvenFixedLinkTrajectoryOptions K radius link := by
      exact heterogeneousChoices_sound
        (zeroLabellingOn : Nat → Nat)
        (adjacentEvenFixedLinkTrajectoryOptions K radius)
        (adjacentEvenFixedLinks radius) trajectory
        (adjacentEvenFixedLinks_nodup radius) htrajectory link hlink
    unfold adjacentEvenFixedLinkTrajectoryOptions at hlinkChoice
    exact boundedLabellingsOn_sound
      (linkAuxiliaryCutoff K)
      (adjacentEvenIncidentFixedFaceIds radius link)
      (trajectory link) hlinkChoice id hid

/-! ## 2. One terminal delta -/

def adjacentEvenTerminalDeltaFactor
    (radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (link : Z4Link) : Q' :=
  Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
    (source link) (target link)
    (adjacentEvenIncidentFixedFaceIds radius link))

private theorem ofNat_fixedIdTerminalIndicator_eqv_delta
    (channel : Nat → Nat) (start finish : Nat) (ids : List Nat) :
    Q'.ofNat (fixedIdTerminalIndicator channel start finish ids) ≈
      (if finish = fixedIdFinalChannel channel start ids
        then (1 : Q') else 0) := by
  unfold fixedIdTerminalIndicator
  by_cases heq : finish = fixedIdFinalChannel channel start ids
  · rw [if_pos heq]
    simp [heq.symm, boolMultiplicity]
    decide
  · rw [if_neg heq]
    have hne : fixedIdFinalChannel channel start ids ≠ finish :=
      fun h => heq h.symm
    simp [hne, boolMultiplicity]
    exact Q'.ofNat_zero_eqv

theorem adjacentEvenTerminalDeltaFactor_eqv_delta
    (radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (link : Z4Link) :
    adjacentEvenTerminalDeltaFactor
        radius source target trajectory link ≈
      (if target link = adjacentEvenTrajectoryFinalChannel
          radius source trajectory link then (1 : Q') else 0) := by
  unfold adjacentEvenTerminalDeltaFactor
    adjacentEvenTrajectoryFinalChannel
  exact ofNat_fixedIdTerminalIndicator_eqv_delta
    (trajectory link) (source link) (target link)
    (adjacentEvenIncidentFixedFaceIds radius link)

/-! ## 3. Reflected-upper amplitude and global target collapse -/

def adjacentEvenReflectedUpperLinkAmplitude
    (K radius : Nat) (physical : Nat → Nat)
    (link : Z4Link) (channel : Nat) : Q' :=
  Q'.ofNat (fusionChannelAmplitude (linkAuxiliaryCutoff K)
    (adjacentEvenIncidentUpperSpins radius physical link).reverse
    channel)

def adjacentEvenReflectedUpperAmplitudeProduct
    (K radius : Nat) (physical : Nat → Nat)
    (channel : Z4Link → Nat) : Q' :=
  listQProduct (fun link =>
    adjacentEvenReflectedUpperLinkAmplitude
      K radius physical link (channel link))
    (adjacentEvenFixedLinks radius)

private theorem terminalWeightedFsum_collapse
    (K radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (link : Z4Link)
    (hfinal : adjacentEvenTrajectoryFinalChannel
      radius source trajectory link ≤ linkAuxiliaryCutoff K) :
    fsum (fun target =>
      Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
          (source link) target
          (adjacentEvenIncidentFixedFaceIds radius link)) *
        adjacentEvenReflectedUpperLinkAmplitude
          K radius physical link target)
        (linkAuxiliaryCutoff K + 1) ≈
      adjacentEvenReflectedUpperLinkAmplitude K radius physical link
        (adjacentEvenTrajectoryFinalChannel
          radius source trajectory link) := by
  let final := adjacentEvenTrajectoryFinalChannel
    radius source trajectory link
  let upper := adjacentEvenReflectedUpperLinkAmplitude
    K radius physical link
  have hterm : ∀ target,
      Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
          (source link) target
          (adjacentEvenIncidentFixedFaceIds radius link)) *
          upper target ≈
        (if target = final then (1 : Q') else 0) * upper target := by
    intro target
    exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_fixedIdTerminalIndicator_eqv_delta
        (trajectory link) (source link) target
        (adjacentEvenIncidentFixedFaceIds radius link))
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      _ _ hterm (linkAuxiliaryCutoff K + 1)) ?_
  exact delta_fsum upper final (linkAuxiliaryCutoff K + 1) (by omega)

def adjacentEvenTerminalWeightedTargetSum
    (K radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQSum (fun target =>
    listQProduct (fun link =>
      adjacentEvenTerminalDeltaFactor radius source target trajectory link *
        adjacentEvenReflectedUpperLinkAmplitude
          K radius physical link (target link))
      (adjacentEvenFixedLinks radius))
    (boundedLabellingsOn (linkAuxiliaryCutoff K)
      (adjacentEvenFixedLinks radius))

theorem adjacentEvenTerminalWeightedTargetSum_collapse
    {K radius : Nat} {physical : Nat → Nat}
    {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : source ∈ boundedLabellingsOn
      (linkAuxiliaryCutoff K) (adjacentEvenFixedLinks radius))
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenTerminalWeightedTargetSum
        K radius physical source trajectory ≈
      adjacentEvenReflectedUpperAmplitudeProduct K radius physical
        (fun link => adjacentEvenTrajectoryFinalChannel
          radius source trajectory link) := by
  unfold adjacentEvenTerminalWeightedTargetSum
    adjacentEvenReflectedUpperAmplitudeProduct
  refine Q'.eqv_trans _ _ _
    (boundedLabellingsOn_product_fubini
      (linkAuxiliaryCutoff K)
      (fun link target =>
        Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
            (source link) target
            (adjacentEvenIncidentFixedFaceIds radius link)) *
          adjacentEvenReflectedUpperLinkAmplitude
            K radius physical link target)
      (adjacentEvenFixedLinks radius)
      (adjacentEvenFixedLinks_nodup radius)) ?_
  apply listQProduct_congr_eqv
  intro link hlink
  exact terminalWeightedFsum_collapse K radius physical source
    trajectory link
    (adjacentEvenTrajectoryFinalChannel_le hsource htrajectory hlink)

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

/-- The separated terminal-product × upper-product form produced by the
pointwise regrouping collapses to the same final-channel upper amplitude. -/
theorem adjacentEvenSeparatedTerminalTargetSum_collapse
    {K radius : Nat} {physical : Nat → Nat}
    {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : source ∈ boundedLabellingsOn
      (linkAuxiliaryCutoff K) (adjacentEvenFixedLinks radius))
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    listQSum (fun target =>
        adjacentEvenLinkTerminalProduct radius source target trajectory *
          adjacentEvenReflectedUpperAmplitudeProduct
            K radius physical target)
      (boundedLabellingsOn (linkAuxiliaryCutoff K)
        (adjacentEvenFixedLinks radius)) ≈
      adjacentEvenReflectedUpperAmplitudeProduct K radius physical
        (fun link => adjacentEvenTrajectoryFinalChannel
          radius source trajectory link) := by
  refine Q'.eqv_trans _ _ _
    (listQSum_congr (fun target => Q'.eqv_symm
      (listQProduct_pointwise_mul_local
        (fun link => adjacentEvenTerminalDeltaFactor
          radius source target trajectory link)
        (fun link => adjacentEvenReflectedUpperLinkAmplitude
          K radius physical link (target link))
        (adjacentEvenFixedLinks radius)))
      (boundedLabellingsOn (linkAuxiliaryCutoff K)
        (adjacentEvenFixedLinks radius))) ?_
  exact adjacentEvenTerminalWeightedTargetSum_collapse
    hsource htrajectory

#print axioms adjacentEvenTrajectoryFinalChannel_le
#print axioms adjacentEvenTerminalDeltaFactor_eqv_delta
#print axioms adjacentEvenTerminalWeightedTargetSum_collapse
#print axioms adjacentEvenSeparatedTerminalTargetSum_collapse

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
