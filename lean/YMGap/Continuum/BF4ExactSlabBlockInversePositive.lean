/-
# Positive certificates survive the ACTUAL conditional normalizer

The constructed normalizer multiplier is positive on its completion. Hence
its constructed dense preimage satisfies <I r,r> >= 0. Moving a polynomial
through the inverse pairing gives <I(p^2),1> >= 0, and induction extends
this to every existing sum-of-squares Certificate, including carrier
transports. No inverse-normalizer floor replaces the actual denominator.

This is an order theorem, not a small covariance coefficient or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
import YMGap.Continuum.QuaternionHaarCertificateSupportedRepresentative
import YMGap.Continuum.ContinuousFunctionalCalculusForm

namespace YMGap.Continuum.BF4ExactSlabBlockInversePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "I" => inverseState hw0 hw1 K extent hK links hl
local notation "MC" => normalizerCompletion hw0 hw1 K extent hK links hl
local notation "oneV" => backgroundUnit hw0 hw1 K extent hK links
local notation "mulV" => productVector hw0 hw1 K extent hK links

/-- Positivity passes through the existing explicit multiplier completion. -/
theorem normalizerCompletion_positive (x : GNSCompletionSpace G) :
    RCnonneg ((G).cinnerCompl x (MC x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  change leEv (ofQ' 0)
    ((G).cinnerRep X (normalizerCauchy hw0 hw1 K extent hK links hl X))
  apply leEv_of_convergesTo_le (convergesTo_const (ofQ' 0))
    (convergesTo_ofQ'CauchySeq _ _)
  intro n
  apply leEv_ofQ'_of_approx_ge
  intro _
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (blockLower_positive hw0 hw1 links.length))
      ((G).self_nonneg (X.seq n)))
    (normalizerMap_form_bounds hw0 hw1 K extent hK links hl (X.seq n)).1

/-- This uses the actual right inverse, not a scalar comparison inverse. -/
theorem inverseState_positive (r : (G).V) :
    RCnonneg ((G).cinnerCompl (I r) (embedV G r)) := by
  have h := normalizerCompletion_positive hw0 hw1 K extent hK links hl (I r)
  rwa [normalizer_inverseState] at h

/-- Original E/D integration on dense polynomials, represented by a fixed
constructed inverse vector. This form makes linearity explicit. -/
def inverseMean (r : (G).V) : RC :=
  (G).cinnerCompl (I oneV) (embedV G r)

local notation "meanI" => inverseMean hw0 hw1 K extent hK links hl

/-- Exact identification with the already constructed inverse pairing. -/
theorem inverseMean_pin (r : (G).V) :
    meanI r = (G).cinnerCompl (I r) (embedV G oneV) := by
  unfold inverseMean
  rw [inverseState_product_pair]
  have h : (G).rad (mulV oneV r) r :=
    rad_of_veq G (RatPolyCoeffEqv.one_mul r.val)
  rw [inverseState_rad hw0 hw1 K extent hK links hl h]

theorem inverseMean_add (r t : (G).V) :
    meanI ((G).add r t) = RCadd (meanI r) (meanI t) := by
  unfold inverseMean
  rw [← (G).cAdd_embed, (G).cinnerCompl_cAdd_right]

theorem inverseMean_sub (r t : (G).V) :
    meanI ((G).sub r t) = RCsub (meanI r) (meanI t) := by
  unfold inverseMean
  rw [← (G).cSub_embed, (G).cinnerCompl_comm, (G).cinnerCompl_cSub_left,
    (G).cinnerCompl_comm (embedV G r), (G).cinnerCompl_comm (embedV G t)]

theorem inverseMean_smul (c : Q') (r : (G).V) :
    meanI ((G).smul c r) = RCscale c (meanI r) := by
  apply Quotient.sound
  refine Equiv_of_limit_of_equal ?_
    (convergesTo_ofQ'CauchySeq _ _)
    (convergesTo_constMul c (convergesTo_ofQ'CauchySeq _ _))
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    (G).B_smul_right c
      ((inverseCauchy hw0 hw1 K extent hK links hl oneV).seq n) r)

/-- Carrier equality is tested with the actual inverse approximants and
the original detached weight. No unsupported intermediate is a GNS vector. -/
theorem inverseMean_carrier (r t : (G).V)
    (h : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length r.val t.val) :
    meanI r = meanI t := by
  apply Quotient.sound
  refine Equiv_of_limit_of_equal ?_
    (convergesTo_ofQ'CauchySeq _ _) (convergesTo_ofQ'CauchySeq _ _)
  intro n
  apply ofQ'_equiv_of_eqv
  exact haar_of_carrier (HaarCarrierEqv.mul_right (background w K extent links)
    (HaarCarrierEqv.mul_left
      ((inverseCauchy hw0 hw1 K extent hK links hl oneV).seq n).val h))

theorem inverseMean_square_nonnegative (r : (G).V) :
    RCnonneg (meanI (mulV r r)) := by
  rw [inverseMean_pin, ← inverseState_product_pair]
  exact inverseState_positive hw0 hw1 K extent hK links hl r

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_nonnegative {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rwa [rc_zero_add] at h

private theorem certificate_mean {p : RatPoly}
    (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    ∀ r : (G).V,
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length r.val p →
      RCnonneg (meanI r) := by
  induction P with
  | square p hp =>
      intro r hr
      let q : (G).V := ⟨p, hp⟩
      rw [inverseMean_carrier hw0 hw1 K extent hK links hl r (mulV q q) hr]
      exact inverseMean_square_nonnegative hw0 hw1 K extent hK links hl q
  | @add p q P Q ihP ihQ =>
      intro r hr
      let a := P.supportedRepresentative
      let b := Q.supportedRepresentative
      let av : (G).V := ⟨a.val, a.property.1⟩
      let bv : (G).V := ⟨b.val, b.property.1⟩
      have he : HaarCarrierEqv _ r.val ((G).add av bv).val :=
        hr.trans (HaarCarrierEqv.add a.property.2 b.property.2)
      rw [inverseMean_carrier hw0 hw1 K extent hK links hl r _ he, inverseMean_add]
      exact rc_add_nonnegative (ihP av a.property.2.symm) (ihQ bv b.property.2.symm)
  | @smul c hc p P ih =>
      intro r hr
      let a := P.supportedRepresentative
      let av : (G).V := ⟨a.val, a.property.1⟩
      have he : HaarCarrierEqv _ r.val ((G).smul c av).val :=
        hr.trans (HaarCarrierEqv.smul c a.property.2)
      rw [inverseMean_carrier hw0 hw1 K extent hK links hl r _ he, inverseMean_smul]
      change RCle RCzero (RCscale c (meanI av))
      rw [← RCscale_RCzero c]
      exact RCscale_mono hc (ih av a.property.2.symm)
  | @transport p q h Q ih =>
      intro r hr
      exact ih r (hr.trans h)

/-- Every original SOS certificate survives division by the actual D.
The certificate remains data; this theorem does not create it from a claim
of positivity or from a numerical solver's status. -/
theorem inverseMean_certificate (r : (G).V)
    (P : Certificate (boundaryCompleteSlabLinks extent).length r.val) :
    RCnonneg (meanI r) :=
  certificate_mean hw0 hw1 K extent hK links hl P r (.refl _ _)

private theorem le_of_sub_nonnegative (a b : RC)
    (h : RCnonneg (RCsub b a)) : RCle a b := by
  have hc : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv (B.approx n) (A.approx n)))
  have h' := RCadd_le_add h (RCle_refl a)
  rwa [rc_zero_add, hc] at h'

theorem inverseMean_mono (r t : (G).V)
    (P : Certificate (boundaryCompleteSlabLinks extent).length ((G).sub t r).val) :
    RCle (meanI r) (meanI t) := by
  apply le_of_sub_nonnegative
  rw [← inverseMean_sub]
  exact inverseMean_certificate hw0 hw1 K extent hK links hl _ P

#print axioms normalizerCompletion_positive
#print axioms inverseState_positive
#print axioms inverseMean
#print axioms inverseMean_pin
#print axioms inverseMean_add
#print axioms inverseMean_sub
#print axioms inverseMean_smul
#print axioms inverseMean_carrier
#print axioms inverseMean_square_nonnegative
#print axioms inverseMean_certificate
#print axioms inverseMean_mono

end YMGap.Continuum.BF4ExactSlabBlockInversePositive
