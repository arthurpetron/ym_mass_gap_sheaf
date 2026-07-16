/-
# Exact cross-volume transport for arbitrary-cutoff cylinder probabilities

The spin-decorated locality theorem identifies every fixed connected-support
activity across nested boxes.  This module lifts that identity through finite
compatible-family products, the compatible-family partition, and arbitrary
finite cylinder-event numerators.  Positive rational division then identifies
the embedded target law with the genuine smaller-box law.  Composing this
exact bridge with the same-volume target stability theorem gives the first
cutoff-uniform cross-volume cylinder modulus for the spin-summed gas.
-/

import YMGap.Continuum.Z4CanonicalCylinderStability
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
import YMGap.Continuum.Z4SpinSummedTargetCylinderStability

namespace YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Exact compatible-family transport -/

/-- A finite product of arbitrary-cutoff support activities is invariant
under zero-extension of every support to a nested box. -/
theorem parametricKSupportFamilyActivity_transport
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large) :
    ∀ family : List (List Nat),
      (∀ support, support ∈ family →
        support ∈ cutoffOneFaceSupports small) →
      parametricKSupportFamilyActivity cutoff small family ≈
        parametricKSupportFamilyActivity cutoff large
          (transportFamily small large family)
  | [], _ => Q'.eqv_refl 1
  | support :: rest, hmembers => by
      change
        parametricKSupportActivity cutoff small support *
            parametricKSupportFamilyActivity cutoff small rest ≈
          parametricKSupportActivity cutoff large
              (transportPolymer small large support) *
            parametricKSupportFamilyActivity cutoff large
              (transportFamily small large rest)
      exact qmul_congr_local
        (parametricKSupportActivity_cross_volume hsmall
          (hmembers support List.mem_cons_self))
        (parametricKSupportFamilyActivity_transport cutoff hsmall rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem support hitem)))

/-- The same identity after putting the transported family into the canonical
target-box order used by the compatible-family enumeration. -/
theorem parametricKCompatibleFamilyActivity_embedded_transport
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies small) :
    parametricKSupportFamilyActivity cutoff small family ≈
      parametricKSupportFamilyActivity cutoff large
        (embeddedTransportFamily small large family) := by
  refine Q'.eqv_trans _ _ _
    (parametricKSupportFamilyActivity_transport cutoff hsmall family
      (fun support hsupport =>
        compatibleAmbientFamily_member_faceSupport hfamily hsupport)) ?_
  exact parametricKSupportFamilyActivity_perm cutoff large
    (transportFamily_perm_embedded hsmall hfamily)

/-- The complete arbitrary-cutoff compatible-family partition in a smaller
box equals the literal embedded-family partition in every larger box. -/
theorem parametricKCompatiblePartition_eqv_embedded_cross_volume
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large) :
    parametricKCompatibleSupportGasPartition cutoff small ≈
      parametricKEmbeddedTargetPartition cutoff small large := by
  have hmap :
      parametricKCompatibleSupportGasPartition cutoff small ≈
        listQSum (parametricKSupportFamilyActivity cutoff large)
          (embeddedCompatibleFamilies small large) := by
    unfold parametricKCompatibleSupportGasPartition
      embeddedCompatibleFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact parametricKCompatibleFamilyActivity_embedded_transport
      cutoff hsmall hfamily
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold parametricKEmbeddedTargetPartition
  exact listQSum_perm
    (parametricKSupportFamilyActivity cutoff large)
    (embeddedCompatibleFamilies_perm_target hsmall)

/-! ## 2. Exact cylinder numerator and probability transport -/

/-- Every finite occurrence-cylinder numerator is transported exactly from
the smaller compatible gas to the literal embedded target ensemble. -/
theorem parametricKCompatibleCylinderNumerator_eqv_embedded
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    parametricKCompatibleSupportEventNumerator cutoff small
        (sourceCylinderEvent roots predicate) ≈
      parametricKEmbeddedTargetEventNumerator cutoff small large
        (targetCylinderEvent small large roots predicate) := by
  have hmap :
      parametricKCompatibleSupportEventNumerator cutoff small
          (sourceCylinderEvent roots predicate) ≈
        listQSum (parametricKSupportFamilyActivity cutoff large)
          (embeddedSourceCylinderFamilies small large roots predicate) := by
    unfold parametricKCompatibleSupportEventNumerator
      embeddedSourceCylinderFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact parametricKCompatibleFamilyActivity_embedded_transport
      cutoff hsmall (List.mem_filter.mp hfamily).1
  have hperm :
      (embeddedSourceCylinderFamilies small large roots predicate).Perm
        ((embeddedTargetFamilies small large).filter
          (targetCylinderEvent small large roots predicate)) := by
    rw [embeddedSourceCylinderFamilies_eq_filter hsmall hroots predicate]
    exact (embeddedCompatibleFamilies_perm_target hsmall).filter _
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold parametricKEmbeddedTargetEventNumerator
  exact listQSum_perm
    (parametricKSupportFamilyActivity cutoff large) hperm

private theorem qeqv_of_le_of_ge {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

/-- Positive rational division respects semantic rational equivalence in
both the numerator and denominator.  This is proved using the two existing
division comparison lemmas, without choosing normalized representatives. -/
theorem divPos_eqv_congr {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

/-- Exact identification of the smaller-box cylinder law with the embedded
conditional law in the larger box. -/
theorem parametricKCompatibleCylinderProbability_eqv_embedded
    (cutoff : Nat) {small large : Nat} (hsmall : small ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    parametricKCompatibleSupportEventProbability cutoff small
        (sourceCylinderEvent roots predicate) ≈
      parametricKEmbeddedTargetEventProbability cutoff hsmall
        (targetCylinderEvent small large roots predicate) := by
  unfold parametricKCompatibleSupportEventProbability
    parametricKEmbeddedTargetEventProbability
  exact divPos_eqv_congr
    (parametricKCompatibleSupportGasPartition_pos cutoff small)
    (parametricKEmbeddedTargetPartition_pos cutoff hsmall)
    (parametricKCompatibleCylinderNumerator_eqv_embedded
      cutoff hsmall hroots predicate)
    (parametricKCompatiblePartition_eqv_embedded_cross_volume
      cutoff hsmall)

/-! ## 3. The cutoff-uniform cross-volume modulus -/

theorem markedTransportedCylinderEvent_eq_target
    {small large : Nat} (hsmall : small ≤ large)
    (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    markedCylinderEvent
        (transportedCanonicalCylinderAtoms hsmall roots hroots) predicate =
      targetCylinderEvent small large roots predicate := by
  funext family
  unfold markedCylinderEvent targetCylinderEvent
  rw [transportedCanonicalCylinderAtoms_values hsmall roots hroots]

/-- **Cutoff-uniform cross-volume cylinder stability.**  A finite local
event evaluated in any nested target box differs from its genuine source-box
probability by the explicit spin-summed boundary tail.  The estimate is
uniform in the representation cutoff and target volume. -/
theorem parametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
    (cutoff : Nat) {small large inner distance : Nat}
    (hsmall : small ≤ large) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool)
    (hinside : ∀ root, root ∈ roots →
      PolymerInsideBox inner small root)
    (hbox : inner + distance = small) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability cutoff large
            (markedCylinderEvent
              (transportedCanonicalCylinderAtoms hsmall roots hroots)
              predicate) -
          parametricKCompatibleSupportEventProbability cutoff small
            (sourceCylinderEvent roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  let targetRoots :=
    transportedCanonicalCylinderAtoms hsmall roots hroots
  have htargetEvent :
      markedCylinderEvent targetRoots predicate =
        targetCylinderEvent small large roots predicate := by
    exact markedTransportedCylinderEvent_eq_target
      hsmall roots hroots predicate
  have hstable :=
    parametricKTargetCylinderProbability_abs_sub_embedded_le
      cutoff hsmall targetRoots predicate
      (transportedCanonicalCylinderAtoms_inside_source hsmall hroots)
      (transportedCanonicalCylinderAtoms_inner_face
        hsmall hroots hinside)
      hbox
  have hbridge :=
    parametricKCompatibleCylinderProbability_eqv_embedded
      cutoff hsmall hroots predicate
  rw [← htargetEvent] at hbridge
  have hdiff :
      parametricKCompatibleSupportEventProbability cutoff large
            (markedCylinderEvent targetRoots predicate) -
          parametricKCompatibleSupportEventProbability cutoff small
            (sourceCylinderEvent roots predicate) ≈
        parametricKCompatibleSupportEventProbability cutoff large
            (markedCylinderEvent targetRoots predicate) -
          parametricKEmbeddedTargetEventProbability cutoff hsmall
            (markedCylinderEvent targetRoots predicate) :=
    Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hbridge)
  have hbound := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdiff)) hstable
  have hlength : targetRoots.length = roots.length := by
    exact transportedCanonicalCylinderAtoms_length hsmall roots hroots
  simpa only [hlength] using hbound

#print axioms parametricKSupportFamilyActivity_transport
#print axioms parametricKCompatiblePartition_eqv_embedded_cross_volume
#print axioms parametricKCompatibleCylinderNumerator_eqv_embedded
#print axioms divPos_eqv_congr
#print axioms parametricKCompatibleCylinderProbability_eqv_embedded
#print axioms parametricKCompatibleCylinderProbability_cross_volume_abs_sub_le

end YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
