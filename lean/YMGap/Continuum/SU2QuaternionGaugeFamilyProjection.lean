/-
# Physical-link family projections through the actual auxiliary gauge ledger

The three gauge multipliers occupy only blocks 0, 1, and 2. Thus any
schedule on original links, shifted by three blocks, avoids every ledger
multiplier. The generic selected-step family theorem then applies to the
existing gaugePolynomial and its slab vertex-tag specialization.

These are finite unweighted projection identities on the augmented carrier;
no completed gauge action or interacting contraction is claimed.
-/

import YMGap.Continuum.SU2QuaternionSelectedProjectionEquivariance
import YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge

namespace YMGap.Continuum.SU2QuaternionGaugeFamilyProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionSelectedProjectionEquivariance
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge

private theorem endpointSteps_multiplier_lt_three {n : Nat} (i : Fin n)
    (tag : Option (Fin 3)) (side : SelectedTranslationSide)
    (orientation : SelectedMultiplierOrientation)
    {step : SelectedTranslationStep (n + 2)}
    (hstep : step ∈ endpointSteps i tag side orientation) :
    step.multiplier < 3 := by
  cases tag with
  | none => cases hstep
  | some j =>
      have heq := List.mem_singleton.mp hstep
      subst step
      exact j.isLt

private theorem linkSteps_multiplier_lt_three {n : Nat}
    (start finish : Fin n → Option (Fin 3)) (i : Fin n)
    {step : SelectedTranslationStep (n + 2)}
    (hstep : step ∈ linkSteps start finish i) :
    step.multiplier < 3 := by
  rcases List.mem_append.mp hstep with hleft | hright
  · exact endpointSteps_multiplier_lt_three i (start i) .left .inverse hleft
  · exact endpointSteps_multiplier_lt_three i (finish i) .right .direct hright

/-- Every multiplier in the literal common vertex-gauge ledger is one of its
three auxiliary blocks; this is derived from endpointSteps/linkSteps. -/
theorem gaugeLedger_multiplier_lt_three {n : Nat}
    (start finish : Fin n → Option (Fin 3))
    {step : SelectedTranslationStep (n + 2)}
    (hstep : step ∈ gaugeLedger start finish) :
    step.multiplier < 3 := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hstep
  exact linkSteps_multiplier_lt_three start finish i hi

/-- The actual all-link gauge ledger commutes, in the original supported
Haar carrier, with any finite schedule of physical-link integrations. -/
theorem gaugePolynomial_familyProject {n : Nat}
    (start finish : Fin n → Option (Fin 3))
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n + 3) p) :
    HaarCarrierEqv (n + 3)
      (familyProject (ids.map (fun i => i + 3)) (gaugePolynomial start finish p))
      (gaugePolynomial start finish
        (familyProject (ids.map (fun i => i + 3)) p)) := by
  let shifted := ids.map (fun i => i + 3)
  have hvalid : ∀ j, j ∈ shifted → j < (n + 2) + 1 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := hids i hi
    omega
  have hdisjoint : ∀ step, step ∈ gaugeLedger start finish →
      ∀ j, j ∈ shifted → j ≠ step.multiplier := by
    intro step hs j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    have hm := gaugeLedger_multiplier_lt_three start finish hs
    omega
  have h := familyProject_steps (tailBlocks := n + 2)
    (by omega : 0 < n + 2) (gaugeLedger start finish)
    shifted hvalid hdisjoint p (by simpa [Nat.add_assoc] using hp)
  simpa only [shifted, gaugePolynomial, Nat.add_assoc] using h

/-- Specialization to the common vertex-tag action on the actual corrected
slab's complete original-link list. -/
theorem slabGauge_familyProject (extent : Nat)
    (tags : Z4Vertex → Option (Fin 3))
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < linkCount extent)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (linkCount extent + 3) p) :
    HaarCarrierEqv (linkCount extent + 3)
      (familyProject (ids.map (fun i => i + 3))
        (slabGaugePolynomial extent tags p))
      (slabGaugePolynomial extent tags
        (familyProject (ids.map (fun i => i + 3)) p)) :=
  gaugePolynomial_familyProject (startTag extent tags) (finishTag extent tags)
    ids hids p hp

#print axioms gaugeLedger_multiplier_lt_three
#print axioms gaugePolynomial_familyProject
#print axioms slabGauge_familyProject

end YMGap.Continuum.SU2QuaternionGaugeFamilyProjection
