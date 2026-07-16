/-
# Cross-volume cylinder stability below the anchor coupling

Exact zero-extension identifies the smaller-box law with the embedded target
cell.  Combining that identity with the uniform same-volume modulus gives a
genuine thermodynamic comparison, uniformly in the representation cutoff.
-/

import YMGap.Continuum.Z4CouplingParametricTargetCylinderStability

namespace YMGap.Continuum.Z4CouplingParametricCrossVolumeStability

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! A transported finite cylinder differs from its genuine source-box law by
the explicit boundary tail, with no cutoff or target-volume dependence. -/
theorem couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small large inner distance : Nat} (hsmall : small ≤ large)
    (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool)
    (hinside : ∀ root, root ∈ roots →
      PolymerInsideBox inner small root)
    (hbox : inner + distance = small) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff large
            (markedCylinderEvent
              (transportedCanonicalCylinderAtoms hsmall roots hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff small
            (sourceCylinderEvent roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  let targetRoots :=
    transportedCanonicalCylinderAtoms hsmall roots hroots
  have htargetEvent :
      markedCylinderEvent targetRoots predicate =
        targetCylinderEvent small large roots predicate :=
    markedTransportedCylinderEvent_eq_target
      hsmall roots hroots predicate
  have hstable :=
    couplingParametricKTargetCylinderProbability_abs_sub_embedded_le
      hcoupling hle cutoff hsmall targetRoots predicate
      (transportedCanonicalCylinderAtoms_inside_source hsmall hroots)
      (transportedCanonicalCylinderAtoms_inner_face
        hsmall hroots hinside)
      hbox
  have hbridge :=
    couplingParametricKCompatibleCylinderProbability_eqv_embedded
      coupling hcoupling cutoff hsmall hroots predicate
  rw [← htargetEvent] at hbridge
  have hdiff :
      couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff large
            (markedCylinderEvent targetRoots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff small
            (sourceCylinderEvent roots predicate) ≈
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff large
            (markedCylinderEvent targetRoots predicate) -
          couplingParametricKEmbeddedTargetEventProbability
            coupling hcoupling cutoff hsmall
            (markedCylinderEvent targetRoots predicate) :=
    Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hbridge)
  have hbound := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdiff)) hstable
  have hlength : targetRoots.length = roots.length :=
    transportedCanonicalCylinderAtoms_length hsmall roots hroots
  simpa only [hlength] using hbound

#print axioms couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le

end YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
