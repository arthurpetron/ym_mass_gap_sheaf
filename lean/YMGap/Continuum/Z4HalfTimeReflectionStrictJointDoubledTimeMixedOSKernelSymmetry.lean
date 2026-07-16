/-
# Exact symmetry of the finite reflected support kernel

The doubled-time direct OS bilinear is defined by real polarization.  To
compare it with the oriented mixed signed cylinder, its two cross terms must
be reduced to one orientation.  This file derives the needed symmetry from
the already proved finite weighted-Gram representation of the physical
reflected kernel.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSQuadratic
import YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

local infix:50 " ≈ " => Q'.eqv

private theorem weightedGram_symm_local
    {State Channel : Type}
    (channels : List Channel) (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right : State) :
    weightedGram channels weight amplitude left right ≈
      weightedGram channels weight amplitude right left := by
  unfold weightedGram
  apply listQSum_congr
  intro channel
  exact Q'.mul_eqv_congr_left (weight channel) _ _
    (Q'.mul_comm_eqv
      (amplitude left channel) (amplitude right channel))

/-- The finite physical reflected kernel is symmetric on its enumerated
half-state space. -/
theorem centralPhysicalReflectedKernel_symm
    (coupling : Q') {cutoff half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates cutoff half)
    (hright : right ∈ centralHalfStates cutoff half) :
    centralPhysicalReflectedKernel coupling cutoff half left right ≈
      centralPhysicalReflectedKernel coupling cutoff half right left := by
  have hforward := centralPhysicalReflectedKernel_eq_weightedGram
    coupling hleft hright
  have hbackward := centralPhysicalReflectedKernel_eq_weightedGram
    coupling hright hleft
  exact Q'.eqv_trans _ _ _ hforward
    (Q'.eqv_trans _ _ _
      (weightedGram_symm_local
        (centralBoundaryChannels cutoff half)
        (centralBoundaryWeight coupling cutoff half)
        (centralHalfAmplitude coupling cutoff half) left right)
      (Q'.eqv_symm hbackward))

private theorem centralPhysicalReflectionBilinear_symm_local
    (coupling : Q') (cutoff half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') :
    centralPhysicalReflectionBilinear coupling cutoff half
        leftCoefficient rightCoefficient ≈
      centralPhysicalReflectionBilinear coupling cutoff half
        rightCoefficient leftCoefficient := by
  let states := centralHalfStates cutoff half
  let forward : EdgeLabelling → EdgeLabelling → Q' := fun left right =>
    (leftCoefficient left * rightCoefficient right) *
      centralPhysicalReflectedKernel coupling cutoff half left right
  let backward : EdgeLabelling → EdgeLabelling → Q' := fun left right =>
    (rightCoefficient left * leftCoefficient right) *
      centralPhysicalReflectedKernel coupling cutoff half left right
  have hswap :
      listQSum (fun left => listQSum (backward left) states) states ≈
        listQSum (fun right =>
          listQSum (fun left => backward left right) states) states :=
    Q'.eqv_symm (listQSum_swap backward states states)
  have hrecode :
      listQSum (fun right =>
          listQSum (fun left => backward left right) states) states ≈
        listQSum (fun left => listQSum (forward left) states) states := by
    apply listQSum_congr_on
    intro outer houter
    apply listQSum_congr_on
    intro inner hinner
    unfold backward forward
    have hkernel := centralPhysicalReflectedKernel_symm coupling
      hinner houter
    have hcoefficient := Q'.mul_comm_eqv
      (rightCoefficient inner) (leftCoefficient outer)
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
      (Q'.mul_eqv_congr_left _ _ _ hkernel)
  unfold centralPhysicalReflectionBilinear
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hswap hrecode)

/-- The complete-support reflected kernel is symmetric. -/
theorem centralSupportReflectedKernel_symm
    (coupling : Q') (cutoff half : Nat)
    (left right : List Nat) :
    centralSupportReflectedKernel coupling cutoff half left right ≈
      centralSupportReflectedKernel coupling cutoff half right left := by
  have hleft := centralSupportReflectedKernel_eq_bilinear
    coupling cutoff half left right
  have hright := centralSupportReflectedKernel_eq_bilinear
    coupling cutoff half right left
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _
      (centralPhysicalReflectionBilinear_symm_local
        coupling cutoff half
        (centralSupportPointCoefficient half left)
        (centralSupportPointCoefficient half right))
      (Q'.eqv_symm hright))

/-- The normalized complete-support pair law inherits exact symmetry. -/
theorem centralNormalizedSupportPairLaw_symm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (left right : List Nat) :
    centralNormalizedSupportPairLaw coupling hcoupling cutoff half left right ≈
      centralNormalizedSupportPairLaw coupling hcoupling cutoff half right left := by
  unfold centralNormalizedSupportPairLaw
  exact Q'.mul_eqv_congr_right _ _ _
    (centralSupportReflectedKernel_symm
      coupling cutoff half left right)

#print axioms centralPhysicalReflectedKernel_symm
#print axioms centralSupportReflectedKernel_symm
#print axioms centralNormalizedSupportPairLaw_symm

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry
