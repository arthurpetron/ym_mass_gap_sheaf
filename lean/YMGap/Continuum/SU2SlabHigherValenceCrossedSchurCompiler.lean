/-
# Crossed production pairs at valence five and six

The geometric switch produces two accepted auxiliary outputs at every slab
link.  The higher-valence carrier bridge turns each output into its exact
left fusion chain, and the iterated Schur modules give normalized finite rows
on those chains.  Since the two crossed replicas generally have different
external labels, their pair law is a heterogeneous Cartesian product.

This module performs that construction at actual degree-five and degree-six
links.  The resulting local pair kernels are nonnegative and have exact mass
one.  Assembly over all link degrees and comparison with the spin-foam Gibbs
weight remain separate obligations.

Constructive contract: literal production witnesses, exact `Q'`, finite
lists, no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
import YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
import YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
import YMGap.Continuum.SU2ValenceSixIteratedSchurTransport
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
open YMGap.Continuum.SU2ValenceSixIteratedSchurTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One geometric switch indexed by its actual link degree -/

structure CrossedSlabSwitchPhysicalData where
  leftPhysical : SlabLabelling
  rightPhysical : SlabLabelling
  mask : Nat → Bool

structure CrossedSlabSwitchData (K extent degree : Nat) where
  physical : CrossedSlabSwitchPhysicalData
  link : SlabLink
  leftAuxiliary : SlabLabelling
  rightAuxiliary : SlabLabelling
  leftAuxiliary_mem : leftAuxiliary ∈
    slabLinkFusionWitnesses K extent physical.leftPhysical link
  rightAuxiliary_mem : rightAuxiliary ∈
    slabLinkFusionWitnesses K extent physical.rightPhysical link
  leftBounded : SlabFaceLabellingBounded K extent physical.leftPhysical
  rightBounded : SlabFaceLabellingBounded K extent physical.rightPhysical
  leftSelection : SlabLinkPartnerClosedFaceSelection
    K extent physical.leftPhysical link leftAuxiliary leftAuxiliary_mem
  rightSelection : SlabLinkPartnerClosedFaceSelection
    K extent physical.rightPhysical link rightAuxiliary rightAuxiliary_mem
  leftConstant : ∀ copy,
    leftSelection.selected copy = physical.mask copy.faceId
  rightConstant : ∀ copy,
    rightSelection.selected copy = physical.mask copy.faceId
  degree_eq : (slabIncidentPlaqIds extent link).length = degree

def CrossedSlabSwitchData.leftPhysical {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  D.physical.leftPhysical

def CrossedSlabSwitchData.rightPhysical {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  D.physical.rightPhysical

def CrossedSlabSwitchData.mask {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : Nat → Bool :=
  D.physical.mask

def higherCrossedLeftPhysical {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  twoReplicaFaceSwapLeft D.mask D.leftPhysical D.rightPhysical

def higherCrossedRightPhysical {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  twoReplicaFaceSwapRight D.mask D.leftPhysical D.rightPhysical

def higherCrossedLeftAuxiliary {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  slabCrossReplicaLeftAuxiliary D.leftSelection D.rightSelection

def higherCrossedRightAuxiliary {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) : SlabLabelling :=
  slabCrossReplicaRightAuxiliary D.leftSelection D.rightSelection

theorem higherCrossedLeftAuxiliary_mem {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) :
    higherCrossedLeftAuxiliary D ∈
      slabLinkFusionWitnesses K extent
        (higherCrossedLeftPhysical D) D.link := by
  exact slabCrossReplicaLeftAuxiliary_mem
    D.mask D.leftBounded D.rightBounded D.leftSelection D.rightSelection
    D.leftConstant D.rightConstant

theorem higherCrossedRightAuxiliary_mem {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) :
    higherCrossedRightAuxiliary D ∈
      slabLinkFusionWitnesses K extent
        (higherCrossedRightPhysical D) D.link := by
  exact slabCrossReplicaRightAuxiliary_mem
    D.mask D.leftBounded D.rightBounded D.leftSelection D.rightSelection
    D.leftConstant D.rightConstant

/-! ## 2. Actual valence-five crossed chains and their pair row -/

def crossedValenceFiveLeftChain {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  fixedLeftCGValenceFiveOfSlab K extent
    (higherCrossedLeftPhysical D) D.link (higherCrossedLeftAuxiliary D)
    D.degree_eq (higherCrossedLeftAuxiliary_mem D)

def crossedValenceFiveRightChain {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  fixedLeftCGValenceFiveOfSlab K extent
    (higherCrossedRightPhysical D) D.link (higherCrossedRightAuxiliary D)
    D.degree_eq (higherCrossedRightAuxiliary_mem D)

abbrev CrossedValenceFiveTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  ValenceFiveRightTreeTarget (crossedValenceFiveLeftChain D) ×
    ValenceFiveRightTreeTarget (crossedValenceFiveRightChain D)

def crossedValenceFiveTargets {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :
    List (CrossedValenceFiveTarget D) :=
  cartesian
    (valenceFiveRightTreeTargets (crossedValenceFiveLeftChain D))
    (valenceFiveRightTreeTargets (crossedValenceFiveRightChain D))

def crossedValenceFiveKernelAt {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5)
    (target : CrossedValenceFiveTarget D) : Q' :=
  valenceFiveIteratedSchurKernelAt
      (crossedValenceFiveLeftChain D) target.1 *
    valenceFiveIteratedSchurKernelAt
      (crossedValenceFiveRightChain D) target.2

theorem crossedValenceFiveKernelAt_nonnegative {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5)
    (target : CrossedValenceFiveTarget D) :
    (0 : Q') ≤ crossedValenceFiveKernelAt D target := by
  exact Q'.mul_nonneg _ _
    (valenceFiveIteratedSchurKernelAt_nonnegative
      (crossedValenceFiveLeftChain D) target.1)
    (valenceFiveIteratedSchurKernelAt_nonnegative
      (crossedValenceFiveRightChain D) target.2)

theorem crossedValenceFiveKernel_row_normalized {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :
    listQSum (crossedValenceFiveKernelAt D)
      (crossedValenceFiveTargets D) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
        (valenceFiveIteratedSchurKernelAt
          (crossedValenceFiveLeftChain D))
        (valenceFiveRightTreeTargets (crossedValenceFiveLeftChain D)) *
      listQSum
        (valenceFiveIteratedSchurKernelAt
          (crossedValenceFiveRightChain D))
        (valenceFiveRightTreeTargets (crossedValenceFiveRightChain D))) _ ?_ ?_
  · exact listQSum_cartesian_product
      (valenceFiveIteratedSchurKernelAt (crossedValenceFiveLeftChain D))
      (valenceFiveIteratedSchurKernelAt (crossedValenceFiveRightChain D))
      (valenceFiveRightTreeTargets (crossedValenceFiveLeftChain D))
      (valenceFiveRightTreeTargets (crossedValenceFiveRightChain D))
  · exact Q'.eqv_trans _ ((1 : Q') * 1) _
      (Q'.eqv_trans _
        ((1 : Q') *
          listQSum
            (valenceFiveIteratedSchurKernelAt
              (crossedValenceFiveRightChain D))
            (valenceFiveRightTreeTargets
              (crossedValenceFiveRightChain D))) _
        (Q'.mul_eqv_congr_right _ _ _
          (valenceFiveIteratedSchurKernel_row_normalized
            (crossedValenceFiveLeftChain D)))
        (Q'.mul_eqv_congr_left 1 _ _
          (valenceFiveIteratedSchurKernel_row_normalized
            (crossedValenceFiveRightChain D))))
      (Q'.one_mul_eqv 1)

/-! ## 3. Actual six-valent bulk crossed chains and their pair row -/

def crossedValenceSixLeftChain {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  fixedLeftCGValenceSixOfSlab K extent
    (higherCrossedLeftPhysical D) D.link (higherCrossedLeftAuxiliary D)
    D.degree_eq (higherCrossedLeftAuxiliary_mem D)

def crossedValenceSixRightChain {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  fixedLeftCGValenceSixOfSlab K extent
    (higherCrossedRightPhysical D) D.link (higherCrossedRightAuxiliary D)
    D.degree_eq (higherCrossedRightAuxiliary_mem D)

abbrev CrossedValenceSixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  ValenceSixRightTreeTarget (crossedValenceSixLeftChain D) ×
    ValenceSixRightTreeTarget (crossedValenceSixRightChain D)

def crossedValenceSixTargets {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :
    List (CrossedValenceSixTarget D) :=
  cartesian
    (valenceSixRightTreeTargets (crossedValenceSixLeftChain D))
    (valenceSixRightTreeTargets (crossedValenceSixRightChain D))

def crossedValenceSixKernelAt {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6)
    (target : CrossedValenceSixTarget D) : Q' :=
  valenceSixIteratedSchurKernelAt
      (crossedValenceSixLeftChain D) target.1 *
    valenceSixIteratedSchurKernelAt
      (crossedValenceSixRightChain D) target.2

theorem crossedValenceSixKernelAt_nonnegative {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6)
    (target : CrossedValenceSixTarget D) :
    (0 : Q') ≤ crossedValenceSixKernelAt D target := by
  exact Q'.mul_nonneg _ _
    (valenceSixIteratedSchurKernelAt_nonnegative
      (crossedValenceSixLeftChain D) target.1)
    (valenceSixIteratedSchurKernelAt_nonnegative
      (crossedValenceSixRightChain D) target.2)

/-- **The two complete six-valent crossed bulk rows have exact product mass
one.** -/
theorem crossedValenceSixKernel_row_normalized {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :
    listQSum (crossedValenceSixKernelAt D)
      (crossedValenceSixTargets D) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
        (valenceSixIteratedSchurKernelAt
          (crossedValenceSixLeftChain D))
        (valenceSixRightTreeTargets (crossedValenceSixLeftChain D)) *
      listQSum
        (valenceSixIteratedSchurKernelAt
          (crossedValenceSixRightChain D))
        (valenceSixRightTreeTargets (crossedValenceSixRightChain D))) _ ?_ ?_
  · exact listQSum_cartesian_product
      (valenceSixIteratedSchurKernelAt (crossedValenceSixLeftChain D))
      (valenceSixIteratedSchurKernelAt (crossedValenceSixRightChain D))
      (valenceSixRightTreeTargets (crossedValenceSixLeftChain D))
      (valenceSixRightTreeTargets (crossedValenceSixRightChain D))
  · exact Q'.eqv_trans _ ((1 : Q') * 1) _
      (Q'.eqv_trans _
        ((1 : Q') *
          listQSum
            (valenceSixIteratedSchurKernelAt
              (crossedValenceSixRightChain D))
            (valenceSixRightTreeTargets
              (crossedValenceSixRightChain D))) _
        (Q'.mul_eqv_congr_right _ _ _
          (valenceSixIteratedSchurKernel_row_normalized
            (crossedValenceSixLeftChain D)))
        (Q'.mul_eqv_congr_left 1 _ _
          (valenceSixIteratedSchurKernel_row_normalized
            (crossedValenceSixRightChain D))))
      (Q'.one_mul_eqv 1)

#print axioms higherCrossedLeftAuxiliary_mem
#print axioms higherCrossedRightAuxiliary_mem
#print axioms crossedValenceFiveLeftChain
#print axioms crossedValenceFiveRightChain
#print axioms crossedValenceFiveKernelAt_nonnegative
#print axioms crossedValenceFiveKernel_row_normalized
#print axioms crossedValenceSixLeftChain
#print axioms crossedValenceSixRightChain
#print axioms crossedValenceSixKernelAt_nonnegative
#print axioms crossedValenceSixKernel_row_normalized

end YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
