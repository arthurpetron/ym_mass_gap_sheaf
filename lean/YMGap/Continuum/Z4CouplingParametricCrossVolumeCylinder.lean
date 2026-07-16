/-
# Exact cross-volume transport at arbitrary nonnegative coupling

The geometric zero-extension map does not depend on the heat-kernel
coupling.  This module threads an arbitrary rational coupling through the
existing spin-decorated locality theorem, the connected-support family
product, and the embedded target cell.  It proves that the genuine
smaller-box law is exactly the embedded conditional law in every nested
larger box.

No decay estimate is used here.  The comparison between the embedded cell
and the full target gas is the separate thermodynamic boundary-tail step.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
import YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

namespace YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Coupling-parametric embedded target cell -/

def couplingParametricKEmbeddedTargetPartition
    (coupling : Q') (cutoff small n : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (embeddedTargetFamilies small n)

def couplingParametricKEmbeddedTargetEventNumerator
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((embeddedTargetFamilies small n).filter event)

theorem couplingParametricKEmbeddedTargetPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff small n : Nat) :
    (0 : Q') ≤ couplingParametricKEmbeddedTargetPartition
      coupling cutoff small n := by
  unfold couplingParametricKEmbeddedTargetPartition
  exact listQSum_nonnegative _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n) _

theorem couplingParametricKCompatibleSupportGasPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    (0 : Q') ≤ couplingParametricKCompatibleSupportGasPartition
      coupling cutoff n := by
  unfold couplingParametricKCompatibleSupportGasPartition
  exact listQSum_nonnegative _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n) _

theorem couplingParametricKCompatibleSupportEventNumerator_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤ couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff n event := by
  unfold couplingParametricKCompatibleSupportEventNumerator
  exact listQSum_nonnegative _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n) _

theorem couplingParametricKCompatibleSupportEventNumerator_le_partition
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event ≤
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingParametricKCompatibleSupportGasPartition
  exact listQSum_filter_le _ event
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n) _

theorem couplingParametricKEmbeddedTargetPartition_one_le_of_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n) :
    (1 : Q') ≤ couplingParametricKEmbeddedTargetPartition
      coupling cutoff small n := by
  have hmember := listQSum_member_le
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n)
    (embeddedCompatibleFamilies small n)
    (x := []) (nil_mem_embeddedCompatibleFamilies small n)
  have hperm := listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (embeddedCompatibleFamilies_perm_target hsmall)
  change (1 : Q') ≤ listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
      (embeddedCompatibleFamilies small n) at hmember
  unfold couplingParametricKEmbeddedTargetPartition
  exact Q'.le_trans' _ _ _ hmember (Q'.le_of_eqv hperm)

theorem couplingParametricKEmbeddedTargetPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n) :
    (0 : Q') < couplingParametricKEmbeddedTargetPartition
      coupling cutoff small n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide)
    (couplingParametricKEmbeddedTargetPartition_one_le_of_nonnegative
      hcoupling cutoff hsmall)

def couplingParametricKEmbeddedTargetEventProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (couplingParametricKEmbeddedTargetEventNumerator
      coupling cutoff small n event)
    (couplingParametricKEmbeddedTargetPartition
      coupling cutoff small n)
    (couplingParametricKEmbeddedTargetPartition_pos
      hcoupling cutoff hsmall)

/-! ## 2. Exact support and family transport -/

def couplingTransportedKSupportActivity
    (coupling : Q') (cutoff small large : Nat)
    (support : List Nat) : Q' :=
  listQSum
    (parametricKPhysicalTerm coupling cutoff large)
    (transportedPhysicalFiber cutoff small large support)

theorem couplingParametricKSupportActivity_eqv_transported
    (coupling : Q') {cutoff small large : Nat}
    (hsmall : small ≤ large) (support : List Nat) :
    couplingParametricKSupportActivity coupling cutoff small support ≈
      couplingTransportedKSupportActivity
        coupling cutoff small large support := by
  unfold couplingParametricKSupportActivity
    couplingTransportedKSupportActivity transportedPhysicalFiber
  apply listQSum_map_eqv
  intro physical hphysical
  exact parametricKPhysicalTerm_cross_volume coupling hsmall
    (mem_physicalLabellingsWithSupport_iff.mp hphysical).1

theorem couplingParametricKSupportActivity_cross_volume
    (coupling : Q') {cutoff small large : Nat}
    (hsmall : small ≤ large) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small) :
    couplingParametricKSupportActivity coupling cutoff small support ≈
      couplingParametricKSupportActivity coupling cutoff large
        (transportPolymer small large support) := by
  refine Q'.eqv_trans _
    (couplingTransportedKSupportActivity
      coupling cutoff small large support) _
    (couplingParametricKSupportActivity_eqv_transported
      coupling hsmall support) ?_
  unfold couplingTransportedKSupportActivity
    couplingParametricKSupportActivity
  exact Z4CanonicalPolymerRange.listQSum_perm
    (parametricKPhysicalTerm coupling cutoff large)
    (transportedPhysicalFiber_perm_target hsmall hsupport)

theorem couplingParametricKSupportFamilyActivity_transport
    (coupling : Q') (cutoff : Nat) {small large : Nat}
    (hsmall : small ≤ large) :
    ∀ family : List (List Nat),
      (∀ support, support ∈ family →
        support ∈ cutoffOneFaceSupports small) →
      couplingParametricKSupportFamilyActivity
          coupling cutoff small family ≈
        couplingParametricKSupportFamilyActivity coupling cutoff large
          (transportFamily small large family)
  | [], _ => Q'.eqv_refl 1
  | support :: rest, hmembers => by
      change
        couplingParametricKSupportActivity coupling cutoff small support *
            couplingParametricKSupportFamilyActivity
              coupling cutoff small rest ≈
          couplingParametricKSupportActivity coupling cutoff large
              (transportPolymer small large support) *
            couplingParametricKSupportFamilyActivity coupling cutoff large
              (transportFamily small large rest)
      exact qmul_congr_local
        (couplingParametricKSupportActivity_cross_volume coupling hsmall
          (hmembers support List.mem_cons_self))
        (couplingParametricKSupportFamilyActivity_transport
          coupling cutoff hsmall rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem support hitem)))

theorem couplingParametricKCompatibleFamilyActivity_embedded_transport
    (coupling : Q') (cutoff : Nat) {small large : Nat}
    (hsmall : small ≤ large) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies small) :
    couplingParametricKSupportFamilyActivity
        coupling cutoff small family ≈
      couplingParametricKSupportFamilyActivity coupling cutoff large
        (embeddedTransportFamily small large family) := by
  refine Q'.eqv_trans _ _ _
    (couplingParametricKSupportFamilyActivity_transport
      coupling cutoff hsmall family
      (fun support hsupport =>
        compatibleAmbientFamily_member_faceSupport hfamily hsupport)) ?_
  exact couplingParametricKSupportFamilyActivity_perm
    coupling cutoff large
    (transportFamily_perm_embedded hsmall hfamily)

/-! ## 3. Exact embedded partition and cylinder probability -/

theorem couplingParametricKCompatiblePartition_eqv_embedded_cross_volume
    (coupling : Q') (cutoff : Nat) {small large : Nat}
    (hsmall : small ≤ large) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff small ≈
      couplingParametricKEmbeddedTargetPartition
        coupling cutoff small large := by
  have hmap :
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff small ≈
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff large)
          (embeddedCompatibleFamilies small large) := by
    unfold couplingParametricKCompatibleSupportGasPartition
      embeddedCompatibleFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_transport
      coupling cutoff hsmall hfamily
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKEmbeddedTargetPartition
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff large)
    (embeddedCompatibleFamilies_perm_target hsmall)

theorem couplingParametricKCompatibleCylinderNumerator_eqv_embedded
    (coupling : Q') (cutoff : Nat) {small large : Nat}
    (hsmall : small ≤ large) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff small
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small large
        (targetCylinderEvent small large roots predicate) := by
  have hmap :
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff small
          (sourceCylinderEvent roots predicate) ≈
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff large)
          (embeddedSourceCylinderFamilies
            small large roots predicate) := by
    unfold couplingParametricKCompatibleSupportEventNumerator
      embeddedSourceCylinderFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_transport
      coupling cutoff hsmall (List.mem_filter.mp hfamily).1
  have hperm :
      (embeddedSourceCylinderFamilies small large roots predicate).Perm
        ((embeddedTargetFamilies small large).filter
          (targetCylinderEvent small large roots predicate)) := by
    rw [embeddedSourceCylinderFamilies_eq_filter
      hsmall hroots predicate]
    exact (embeddedCompatibleFamilies_perm_target hsmall).filter _
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKEmbeddedTargetEventNumerator
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff large)
    hperm

theorem couplingParametricKCompatibleCylinderProbability_eqv_embedded
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff small
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKEmbeddedTargetEventProbability
        coupling hcoupling cutoff hsmall
        (targetCylinderEvent small large roots predicate) := by
  unfold couplingParametricKCompatibleSupportEventProbability
    couplingParametricKEmbeddedTargetEventProbability
  exact divPos_eqv_congr
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff small)
    (couplingParametricKEmbeddedTargetPartition_pos
      hcoupling cutoff hsmall)
    (couplingParametricKCompatibleCylinderNumerator_eqv_embedded
      coupling cutoff hsmall hroots predicate)
    (couplingParametricKCompatiblePartition_eqv_embedded_cross_volume
      coupling cutoff hsmall)

#print axioms couplingParametricKEmbeddedTargetPartition_nonnegative
#print axioms couplingParametricKCompatibleSupportEventNumerator_le_partition
#print axioms couplingParametricKSupportActivity_cross_volume
#print axioms couplingParametricKSupportFamilyActivity_transport
#print axioms couplingParametricKCompatiblePartition_eqv_embedded_cross_volume
#print axioms couplingParametricKCompatibleCylinderNumerator_eqv_embedded
#print axioms couplingParametricKCompatibleCylinderProbability_eqv_embedded

end YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
