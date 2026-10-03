/-
# Normalized integration and lifting of actually independent heads

An original polynomial independent of every integrated lower block is the
lift of its actual partial Haar integral under EVERY original Haar insertion.
The insertion may depend on the integrated heads and all surviving variables.
One-head zero-degree moments and genuine repeated Fubini prove the statement;
no diagonal substitution, unused-coordinate deletion or conditional variance
assumption is made. Raw coefficient equality of the padded full polynomial
is not asserted: explicit zero padding can change its monomial-list data.

The consumer identifies the all-lower-independent selected heat sweep with
its lifted true output, paying the product variance endpoint on the original
carrier. No interacting relative-norm or scaling conclusion follows.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.SU2QuaternionIndependentHeadsLift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (exponentAt_drop)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem degree_zero_partial {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (partialHaarHead p) (dropHeadPolynomial p) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead p) (dropHeadPolynomial p) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        have hd := hp t List.mem_cons_self
        have hz : exponentAt t.1 0 = 0 ∧ exponentAt t.1 1 = 0 ∧
            exponentAt t.1 2 = 0 ∧ exponentAt t.1 3 = 0 := by
          change exponentAt t.1 0 + exponentAt t.1 1 + exponentAt t.1 2 +
            exponentAt t.1 3 = 0 at hd
          have h012_3 := Nat.eq_zero_of_add_eq_zero hd
          have h01_2 := Nat.eq_zero_of_add_eq_zero h012_3.1
          have h0_1 := Nat.eq_zero_of_add_eq_zero h01_2.1
          exact ⟨h0_1.1, h0_1.2, h01_2.2, h012_3.2⟩
        have hm : headQuaternionMoment t.1 ≈ (1 : Q') := by
          unfold headQuaternionMoment
          rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
          decide +kernel
        exact ⟨rfl, Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
          (Q'.mul_one_eqv _), ih
            (fun s hs => hp s (List.mem_cons_of_mem t hs))⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- Only the reduced-head representations are coefficient-equivalent.
The actual normalized head moment is one on every original occurrence. -/
theorem independent_head_partial_drop (p : RatPoly)
    (hi : QuaternionBlockIndependent 0 p) :
    RatPolyCoeffEqv (partialHaarHead p) (dropHeadPolynomial p) :=
  degree_zero_partial (independent_has_degree_zero hi)

/-- One independent head may be integrated and re-adjoined while keeping
every arbitrary original insertion, including head-dependent insertions. -/
theorem independent_head_lift (tail : Nat) (p : RatPoly)
    (hi : QuaternionBlockIndependent 0 p) :
    HaarCarrierEqv (tail+1) p (liftBoundary 1 (partialHaarHead p)) := by
  have hhead : HeadQuaternionIndependent p := independent_has_degree_zero hi
  intro insertion
  exact Q'.eqv_trans _ _ _ (independent_to_lift tail insertion p hhead)
    (haar_of_coeff ((lift_coeff 1 (independent_head_partial_drop p hi)).symm.mul_left insertion))

private theorem partial_head_degree {i d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree (i+1) d p) :
    HasQuaternionBlockDegree i d (partialHaarHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change quaternionBlockDegree (s.1.drop 4) i = d
  simpa only [quaternionBlockDegree, exponentAt_drop,
    show 4+4*i = 4*(i+1) by omega,
    show 4+(4*i+1) = 4*(i+1)+1 by omega,
    show 4+(4*i+2) = 4*(i+1)+2 by omega,
    show 4+(4*i+3) = 4*(i+1)+3 by omega] using hp s hs

/-- Actual lower-head independence, not an assumed output identification,
gives the true lifted partial integral on the SAME original carrier.
The count zero and tail zero cases are retained without special assumptions. -/
theorem independent_heads_lift (heads tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (hind : ∀ i, i < heads → QuaternionBlockIndependent i p) :
    HaarCarrierEqv (tail+heads) p (liftBoundary heads (partialHaarHeads heads p)) := by
  induction heads generalizing p with
  | zero => exact HaarCarrierEqv.refl _ _
  | succ heads ih =>
      have hfirst := independent_head_lift (tail+heads) p (hind 0 (by omega))
      have hsmall : SupportedQuaternionBlocks (tail+heads) (partialHaarHead p) :=
        partialHaarHead_supported hp
      have hsmallIndependent (i : Nat) (hi : i < heads) :
          QuaternionBlockIndependent i (partialHaarHead p) :=
        degree_zero_independent (partial_head_degree
          (independent_has_degree_zero (hind (i+1) (by omega))))
      have hrest := lift_carrier 1 (ih (partialHaarHead p) hsmall hsmallIndependent)
      exact hfirst.trans hrest

end YMGap.Continuum.SU2QuaternionIndependentHeadsLift

#print axioms YMGap.Continuum.SU2QuaternionIndependentHeadsLift.independent_head_partial_drop
#print axioms YMGap.Continuum.SU2QuaternionIndependentHeadsLift.independent_head_lift
#print axioms YMGap.Continuum.SU2QuaternionIndependentHeadsLift.independent_heads_lift
