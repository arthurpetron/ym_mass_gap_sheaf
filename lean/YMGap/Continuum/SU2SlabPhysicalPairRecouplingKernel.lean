/-
# Complete SU(2) recoupling above a fixed physical pair

The earlier crossed-link compiler bundled two logically different inputs:
the physical output pair, which determines the complete recoupling matrix,
and one accepted auxiliary pair, which selects a row of that matrix.  A
column argument needs the former to stay literally fixed while many source
rows vary.

This module separates those dependencies.  `SlabPhysicalPairRecouplingData`
contains only the two physical fields and one actual slab link.  It determines
one complete bistochastic matrix at every possible four-dimensional link
valence.  An accepted auxiliary pair is added only in
`SlabPhysicalPairRecouplingWitnessData`, and selects one production source of
that already fixed matrix.

This is the common-kernel interface needed by the physical-support switch.
It remains pure finite SU(2) recoupling: no Gibbs, correlation, spectral-gap,
or continuum claim is made here.

Constructive contract: exact finite carriers, structural degree cases, and
literal accepted witnesses only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
import YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
import YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The physical pair determines the complete matrix -/

structure SlabPhysicalPairRecouplingData (extent degree : Nat) where
  leftPhysical : SlabLabelling
  rightPhysical : SlabLabelling
  link : SlabLink
  degree_eq : (slabIncidentPlaqIds extent link).length = degree

theorem SlabPhysicalPairRecouplingData.degree_le_six
    {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree) : degree ≤ 6 := by
  rw [← D.degree_eq]
  exact slabIncidentPlaqIds_length_le_six extent D.link

/-- The complete tensor-product associator matrix at a fixed physical pair.
Only the physical external spins and the displayed link enter this object. -/
def slabPhysicalPairRecouplingKernelPackage {extent : Nat} :
    (degree : Nat) → SlabPhysicalPairRecouplingData extent degree →
      FiniteBistochasticQKernelPackage
  | 0, _ => unitFiniteBistochasticQKernelPackage
  | 1, _ => unitFiniteBistochasticQKernelPackage
  | 2, _ => unitFiniteBistochasticQKernelPackage
  | 3, _ => unitFiniteBistochasticQKernelPackage
  | 4, D =>
      { Source :=
          FixedLeftCGChannel
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
            FixedLeftCGChannel
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
        Target :=
          FixedRightCGChannel
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
            FixedRightCGChannel
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
        kernel := tensor
          (physicalSchurBistochasticKernel
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 3))
          (physicalSchurBistochasticKernel
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)) }
  | 5, D =>
      { Source :=
          ValenceFiveLeftCarrier
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 4) ×
            ValenceFiveLeftCarrier
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
        Target :=
          ValenceFiveRightCarrier
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 4) ×
            ValenceFiveRightCarrier
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
        kernel := tensor
          (valenceFiveBistochasticKernel
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 4))
          (valenceFiveBistochasticKernel
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)) }
  | 6, D =>
      { Source :=
          ValenceSixLeftCarrier
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 4)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 5) ×
            ValenceSixLeftCarrier
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 5)
        Target :=
          ValenceSixRightCarrier
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 4)
              ((slabLinkExternalSpins extent D.leftPhysical D.link) 5) ×
            ValenceSixRightCarrier
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
              ((slabLinkExternalSpins extent D.rightPhysical D.link) 5)
        kernel := tensor
          (valenceSixBistochasticKernel
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 4)
            ((slabLinkExternalSpins extent D.leftPhysical D.link) 5))
          (valenceSixBistochasticKernel
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
            ((slabLinkExternalSpins extent D.rightPhysical D.link) 5)) }
  | degree + 7, D => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-! ## 2. Accepted auxiliaries select a row of the fixed matrix -/

structure SlabPhysicalPairRecouplingWitnessData
    (K : Nat) {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree) where
  leftAuxiliary : SlabLabelling
  rightAuxiliary : SlabLabelling
  left_mem : leftAuxiliary ∈
    slabLinkFusionWitnesses K extent D.leftPhysical D.link
  right_mem : rightAuxiliary ∈
    slabLinkFusionWitnesses K extent D.rightPhysical D.link

/-- Two accepted witnesses over the same physical link are equal as soon as
they agree on the literal auxiliary-coordinate carrier.  Off that carrier
both finite enumerations are definitionally supported by zero. -/
theorem slabLinkFusionWitness_eq_of_eq_on_used
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    (left_mem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent physical link)
    (right_mem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent physical link)
    (heq : ∀ edge,
      edge ∈ canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length →
        leftAuxiliary edge = rightAuxiliary edge) :
    leftAuxiliary = rightAuxiliary := by
  apply funext
  intro edge
  by_cases hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length
  · exact heq edge hedge
  · have left_bounded := (List.mem_filter.mp left_mem).1
    have right_bounded := (List.mem_filter.mp right_mem).1
    have left_sound := boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      leftAuxiliary left_bounded
    have right_sound := boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      rightAuxiliary right_bounded
    rw [left_sound.2 edge hedge, right_sound.2 edge hedge]

/-- The two accepted left-tree witnesses choose one source row without
changing the matrix determined above. -/
def slabPhysicalPairRecouplingProductionSource
    {K extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      SlabPhysicalPairRecouplingWitnessData K D →
      (slabPhysicalPairRecouplingKernelPackage degree D).Source
  | 0, _, _ => ()
  | 1, _, _ => ()
  | 2, _, _ => ()
  | 3, _, _ => ()
  | 4, D, W =>
      (fixedLeftChannelOfSlabValenceFour K extent
          D.leftPhysical D.link W.leftAuxiliary D.degree_eq W.left_mem,
        fixedLeftChannelOfSlabValenceFour K extent
          D.rightPhysical D.link W.rightAuxiliary D.degree_eq W.right_mem)
  | 5, D, W =>
      (valenceFiveLeftCarrierOfChain
          (fixedLeftCGValenceFiveOfSlab K extent
            D.leftPhysical D.link W.leftAuxiliary D.degree_eq W.left_mem),
        valenceFiveLeftCarrierOfChain
          (fixedLeftCGValenceFiveOfSlab K extent
            D.rightPhysical D.link W.rightAuxiliary D.degree_eq W.right_mem))
  | 6, D, W =>
      (valenceSixLeftCarrierOfChain
          (fixedLeftCGValenceSixOfSlab K extent
            D.leftPhysical D.link W.leftAuxiliary D.degree_eq W.left_mem),
        valenceSixLeftCarrierOfChain
          (fixedLeftCGValenceSixOfSlab K extent
            D.rightPhysical D.link W.rightAuxiliary D.degree_eq W.right_mem))
  | degree + 7, D, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-- **The row coordinate retains both literal production witnesses.**  This
is the local decoder required by the later source-to-column injection. -/
theorem slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (left right : SlabPhysicalPairRecouplingWitnessData K D)
    (heq : slabPhysicalPairRecouplingProductionSource degree D left =
      slabPhysicalPairRecouplingProductionSource degree D right) :
    left.leftAuxiliary = right.leftAuxiliary ∧
      left.rightAuxiliary = right.rightAuxiliary := by
  cases degree with
  | zero =>
      constructor
      · apply slabLinkFusionWitness_eq_of_eq_on_used
          left.left_mem right.left_mem
        intro edge hedge
        simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
          canonicalUsedCoordinates] at hedge
      · apply slabLinkFusionWitness_eq_of_eq_on_used
          left.right_mem right.right_mem
        intro edge hedge
        simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
          canonicalUsedCoordinates] at hedge
  | succ degree =>
      cases degree with
      | zero =>
          have left_allowed_one := slabLinkFusionWitness_allowed
            K extent D.leftPhysical D.link
              left.leftAuxiliary left.left_mem
          have right_allowed_one := slabLinkFusionWitness_allowed
            K extent D.leftPhysical D.link
              right.leftAuxiliary right.left_mem
          have left_right_allowed_one := slabLinkFusionWitness_allowed
            K extent D.rightPhysical D.link
              left.rightAuxiliary left.right_mem
          have right_right_allowed_one := slabLinkFusionWitness_allowed
            K extent D.rightPhysical D.link
              right.rightAuxiliary right.right_mem
          rw [D.degree_eq] at left_allowed_one
          rw [D.degree_eq] at right_allowed_one
          rw [D.degree_eq] at left_right_allowed_one
          rw [D.degree_eq] at right_right_allowed_one
          have left_zero :=
            canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
              (degree := 1) (external :=
                slabLinkExternalSpins extent D.leftPhysical D.link)
              (auxiliary := left.leftAuxiliary)
              (by decide) left_allowed_one
          have right_zero :=
            canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
              (degree := 1) (external :=
                slabLinkExternalSpins extent D.leftPhysical D.link)
              (auxiliary := right.leftAuxiliary)
              (by decide) right_allowed_one
          have left_right_zero :=
            canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
              (degree := 1) (external :=
                slabLinkExternalSpins extent D.rightPhysical D.link)
              (auxiliary := left.rightAuxiliary)
              (by decide) left_right_allowed_one
          have right_right_zero :=
            canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
              (degree := 1) (external :=
                slabLinkExternalSpins extent D.rightPhysical D.link)
              (auxiliary := right.rightAuxiliary)
              (by decide) right_right_allowed_one
          constructor
          · apply slabLinkFusionWitness_eq_of_eq_on_used
              left.left_mem right.left_mem
            intro edge hedge
            simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
              canonicalUsedCoordinates] at hedge
            subst edge
            rw [left_zero, right_zero]
          · apply slabLinkFusionWitness_eq_of_eq_on_used
              left.right_mem right.right_mem
            intro edge hedge
            simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
              canonicalUsedCoordinates] at hedge
            subst edge
            rw [left_right_zero, right_right_zero]
      | succ degree =>
          cases degree with
          | zero =>
              have left_allowed_two := slabLinkFusionWitness_allowed
                K extent D.leftPhysical D.link
                  left.leftAuxiliary left.left_mem
              have right_allowed_two := slabLinkFusionWitness_allowed
                K extent D.leftPhysical D.link
                  right.leftAuxiliary right.left_mem
              have left_right_allowed_two := slabLinkFusionWitness_allowed
                K extent D.rightPhysical D.link
                  left.rightAuxiliary left.right_mem
              have right_right_allowed_two := slabLinkFusionWitness_allowed
                K extent D.rightPhysical D.link
                  right.rightAuxiliary right.right_mem
              rw [D.degree_eq] at left_allowed_two
              rw [D.degree_eq] at right_allowed_two
              rw [D.degree_eq] at left_right_allowed_two
              rw [D.degree_eq] at right_right_allowed_two
              have left_zero :=
                canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
                  (degree := 2) (external :=
                    slabLinkExternalSpins extent D.leftPhysical D.link)
                  (auxiliary := left.leftAuxiliary)
                  (by decide) left_allowed_two
              have right_zero :=
                canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
                  (degree := 2) (external :=
                    slabLinkExternalSpins extent D.leftPhysical D.link)
                  (auxiliary := right.leftAuxiliary)
                  (by decide) right_allowed_two
              have left_right_zero :=
                canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
                  (degree := 2) (external :=
                    slabLinkExternalSpins extent D.rightPhysical D.link)
                  (auxiliary := left.rightAuxiliary)
                  (by decide) left_right_allowed_two
              have right_right_zero :=
                canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
                  (degree := 2) (external :=
                    slabLinkExternalSpins extent D.rightPhysical D.link)
                  (auxiliary := right.rightAuxiliary)
                  (by decide) right_right_allowed_two
              constructor
              · apply slabLinkFusionWitness_eq_of_eq_on_used
                  left.left_mem right.left_mem
                intro edge hedge
                simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
                  canonicalUsedCoordinates] at hedge
                subst edge
                rw [left_zero, right_zero]
              · apply slabLinkFusionWitness_eq_of_eq_on_used
                  left.right_mem right.right_mem
                intro edge hedge
                simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
                  canonicalUsedCoordinates] at hedge
                subst edge
                rw [left_right_zero, right_right_zero]
          | succ degree =>
              cases degree with
              | zero =>
                  constructor
                  · apply slabLinkFusionWitness_eq_of_eq_on_used
                      left.left_mem right.left_mem
                    intro edge hedge
                    simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
                      canonicalUsedCoordinates] at hedge
                  · apply slabLinkFusionWitness_eq_of_eq_on_used
                      left.right_mem right.right_mem
                    intro edge hedge
                    simp [D.degree_eq, canonicalUsedAuxiliaryCoordinates,
                      canonicalUsedCoordinates] at hedge
              | succ degree =>
                  cases degree with
                  | zero =>
                      have left_carrier := congrArg Prod.fst heq
                      have right_carrier := congrArg Prod.snd heq
                      simp only [slabPhysicalPairRecouplingProductionSource]
                        at left_carrier right_carrier
                      have left_coordinate := congrArg
                        (fun source => source.intermediate) left_carrier
                      have right_coordinate := congrArg
                        (fun source => source.intermediate) right_carrier
                      have left_coordinate' : left.leftAuxiliary 5 =
                          right.leftAuxiliary 5 := by
                        simpa only [
                          fixedLeftChannelOfSlabValenceFour_intermediate]
                          using left_coordinate
                      have right_coordinate' : left.rightAuxiliary 5 =
                          right.rightAuxiliary 5 := by
                        simpa only [
                          fixedLeftChannelOfSlabValenceFour_intermediate]
                          using right_coordinate
                      constructor
                      · apply slabLinkFusionWitness_eq_of_eq_on_used
                          left.left_mem right.left_mem
                        intro edge hedge
                        simp [D.degree_eq,
                          canonicalUsedAuxiliaryCoordinates,
                          canonicalUsedCoordinates] at hedge
                        subst edge
                        exact left_coordinate'
                      · apply slabLinkFusionWitness_eq_of_eq_on_used
                          left.right_mem right.right_mem
                        intro edge hedge
                        simp [D.degree_eq,
                          canonicalUsedAuxiliaryCoordinates,
                          canonicalUsedCoordinates] at hedge
                        subst edge
                        exact right_coordinate'
                  | succ degree =>
                      cases degree with
                      | zero =>
                          have left_carrier := congrArg Prod.fst heq
                          have right_carrier := congrArg Prod.snd heq
                          simp only [
                            slabPhysicalPairRecouplingProductionSource]
                            at left_carrier right_carrier
                          have left_x := congrArg
                            (fun source => source.firstLeft.intermediate)
                            left_carrier
                          have left_y := congrArg
                            (fun source => source.y) left_carrier
                          have right_x := congrArg
                            (fun source => source.firstLeft.intermediate)
                            right_carrier
                          have right_y := congrArg
                            (fun source => source.y) right_carrier
                          simp only [valenceFiveLeftCarrierOfChain] at left_x
                          simp only [valenceFiveLeftCarrierOfChain] at left_y
                          simp only [valenceFiveLeftCarrierOfChain] at right_x
                          simp only [valenceFiveLeftCarrierOfChain] at right_y
                          rw [FixedLeftCGValenceFive.prefixChannel_intermediate,
                            FixedLeftCGValenceFive.prefixChannel_intermediate]
                            at left_x
                          rw [FixedLeftCGValenceFive.prefixChannel_intermediate,
                            FixedLeftCGValenceFive.prefixChannel_intermediate]
                            at right_x
                          change left.leftAuxiliary 6 =
                            right.leftAuxiliary 6 at left_x
                          change left.leftAuxiliary 7 =
                            right.leftAuxiliary 7 at left_y
                          change left.rightAuxiliary 6 =
                            right.rightAuxiliary 6 at right_x
                          change left.rightAuxiliary 7 =
                            right.rightAuxiliary 7 at right_y
                          constructor
                          · apply slabLinkFusionWitness_eq_of_eq_on_used
                              left.left_mem right.left_mem
                            intro edge hedge
                            simp [D.degree_eq,
                              canonicalUsedAuxiliaryCoordinates,
                              canonicalUsedCoordinates] at hedge
                            rcases hedge with rfl | rfl
                            · exact left_x
                            · exact left_y
                          · apply slabLinkFusionWitness_eq_of_eq_on_used
                              left.right_mem right.right_mem
                            intro edge hedge
                            simp [D.degree_eq,
                              canonicalUsedAuxiliaryCoordinates,
                              canonicalUsedCoordinates] at hedge
                            rcases hedge with rfl | rfl
                            · exact right_x
                            · exact right_y
                      | succ degree =>
                          cases degree with
                          | zero =>
                              have left_carrier := congrArg Prod.fst heq
                              have right_carrier := congrArg Prod.snd heq
                              simp only [
                                slabPhysicalPairRecouplingProductionSource]
                                at left_carrier right_carrier
                              have left_x := congrArg
                                (fun source =>
                                  source.value.firstLeft.intermediate)
                                left_carrier
                              have left_y := congrArg
                                (fun source => source.value.y) left_carrier
                              have left_z := congrArg
                                (fun source => source.index.val) left_carrier
                              have right_x := congrArg
                                (fun source =>
                                  source.value.firstLeft.intermediate)
                                right_carrier
                              have right_y := congrArg
                                (fun source => source.value.y) right_carrier
                              have right_z := congrArg
                                (fun source => source.index.val) right_carrier
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at left_x
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at left_y
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at left_z
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at right_x
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at right_y
                              simp only [valenceSixLeftCarrierOfChain,
                                valenceFiveLeftCarrierOfChain] at right_z
                              rw [
                                FixedLeftCGValenceFive.prefixChannel_intermediate,
                                FixedLeftCGValenceFive.prefixChannel_intermediate]
                                at left_x
                              rw [
                                FixedLeftCGValenceFive.prefixChannel_intermediate,
                                FixedLeftCGValenceFive.prefixChannel_intermediate]
                                at right_x
                              change left.leftAuxiliary 7 =
                                right.leftAuxiliary 7 at left_x
                              change left.leftAuxiliary 8 =
                                right.leftAuxiliary 8 at left_y
                              change left.leftAuxiliary 9 =
                                right.leftAuxiliary 9 at left_z
                              change left.rightAuxiliary 7 =
                                right.rightAuxiliary 7 at right_x
                              change left.rightAuxiliary 8 =
                                right.rightAuxiliary 8 at right_y
                              change left.rightAuxiliary 9 =
                                right.rightAuxiliary 9 at right_z
                              constructor
                              · apply slabLinkFusionWitness_eq_of_eq_on_used
                                  left.left_mem right.left_mem
                                intro edge hedge
                                simp [D.degree_eq,
                                  canonicalUsedAuxiliaryCoordinates,
                                  canonicalUsedCoordinates] at hedge
                                rcases hedge with rfl | rfl | rfl
                                · exact left_x
                                · exact left_y
                                · exact left_z
                              · apply slabLinkFusionWitness_eq_of_eq_on_used
                                  left.right_mem right.right_mem
                                intro edge hedge
                                simp [D.degree_eq,
                                  canonicalUsedAuxiliaryCoordinates,
                                  canonicalUsedCoordinates] at hedge
                                rcases hedge with rfl | rfl | rfl
                                · exact right_x
                                · exact right_y
                                · exact right_z
                          | succ degree =>
                              have hdegree := D.degree_le_six
                              have hseven_le_six : 7 ≤ 6 :=
                                Nat.le_trans (Nat.le_add_left 7 degree) hdegree
                              exact False.elim
                                (Nat.not_succ_le_self 6 hseven_le_six)

def slabPhysicalPairPointedRecouplingKernelPackage
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D) :
    PointedFiniteBistochasticQKernelPackage where
  package := slabPhysicalPairRecouplingKernelPackage degree D
  source := slabPhysicalPairRecouplingProductionSource degree D W

theorem slabPhysicalPairRecouplingProductionSource_row_normalized
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D) :
    listQSum
        ((slabPhysicalPairRecouplingKernelPackage degree D).kernel.weight
          (slabPhysicalPairRecouplingProductionSource degree D W))
        (slabPhysicalPairRecouplingKernelPackage degree D).kernel.targets
      ≈ 1 :=
  (slabPhysicalPairRecouplingKernelPackage degree D).kernel.row_normalized _

theorem slabPhysicalPairRecouplingKernelPackage_column_normalized
    {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    listQSum
        (fun source =>
          (slabPhysicalPairRecouplingKernelPackage degree D).kernel.weight
            source target)
        (slabPhysicalPairRecouplingKernelPackage degree D).kernel.sources
      ≈ 1 :=
  (slabPhysicalPairRecouplingKernelPackage degree D).kernel.column_normalized _

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.SlabPhysicalPairRecouplingData.degree_le_six
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairRecouplingKernelPackage
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairRecouplingProductionSource
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabLinkFusionWitness_eq_of_eq_on_used
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairPointedRecouplingKernelPackage
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairRecouplingProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel.slabPhysicalPairRecouplingKernelPackage_column_normalized
