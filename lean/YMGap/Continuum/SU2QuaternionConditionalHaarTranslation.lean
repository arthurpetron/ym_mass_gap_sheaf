/-
# Conditional Haar invariance retains every spectator insertion

Integrating the translated head gives the SAME polynomial-valued conditional
moment modulo the original tail Haar carrier, for either Hamilton order and
arbitrary input degree. This is stronger than equality of the full integral.
The tail multiplier's radius is removed only under arbitrary Haar insertions;
no coefficient or pointwise equality with that radius deleted is asserted.

Products transform together, so original weights are retained in inserted
moments and variance determinants. The consumer is gauge covariance of block
conditional projections. The full vertex-ledger/completed-sector join and a
useful signed covariance estimate remain open.
-/

import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation
import YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.SU2QuaternionConditionalHaarTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
private abbrev translate (right : Bool) := translatedHeadPolynomial
  (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
local notation "T" => translate

/-- The sphere-ideal conclusion keeps every tail insertion, not coefficients. -/
theorem monomial_conditional (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (e0 e1 e2 e3 : Nat) :
    HaarCarrierEqv blocks
      (partialHaarHead (translatedHeadMonomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
        e0 e1 e2 e3))
      (polySmul (headQuaternionMoment (headExponentLedger e0 e1 e2 e3)) polyOne) := by
  intro r
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) ?_
  refine Q'.eqv_trans _ _ _ (translatedMoment_tail_haar right blocks hb e0 e1 e2 e3 r) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_right _ r polyOne).trans
      (RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.mul_one r))))
    (quaternionHaar_polySmul blocks _ r))

private theorem term_conditional (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (t : RatTerm) :
    HaarCarrierEqv blocks
      (partialHaarHead (translatedHeadTerm
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) t))
      (partialHaarHead [t]) := by
  let tail : RatPoly := [(t.1.drop 4, t.2)]
  have htail : headTailLiftTerm t = liftHead tail := rfl
  unfold translatedHeadTerm
  rw [htail]
  refine (RatPolyCoeffEqv.haarCarrier (partialHaarHead_mul_lift _ tail)).trans ?_
  have hm := monomial_conditional right blocks hb
    (exponentAt t.1 0) (exponentAt t.1 1) (exponentAt t.1 2) (exponentAt t.1 3)
  refine (HaarCarrierEqv.mul_right tail hm).trans ?_
  refine RatPolyCoeffEqv.haarCarrier
    ((RatPolyCoeffEqv.polyMul_smul_left _ polyOne tail).trans
      ((RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.one_mul tail)).trans ?_))
  have ht : RatPolyTermwiseEqv
      (polySmul (headQuaternionMoment t.1) tail) (partialHaarHead [t]) :=
    ⟨rfl, Q'.mul_comm_eqv _ _, True.intro⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- Exact conditional change of variables at all degrees. The multiplier
is retained in the tail; there is no test-degree or tail-independence premise. -/
theorem partialHaarHead_translated (right : Bool) (blocks : Nat) (hb : 0 < blocks) :
    ∀ p : RatPoly, HaarCarrierEqv blocks
      (partialHaarHead (T right p)) (partialHaarHead p)
  | [] => .refl _ _
  | t :: p => by
      change HaarCarrierEqv blocks
        (partialHaarHead (polyAdd (translatedHeadTerm _ t) (T right p)))
        (polyAdd (partialHaarHead [t]) (partialHaarHead p))
      rw [partialHaarHead_add]
      exact HaarCarrierEqv.add (term_conditional right blocks hb t)
        (partialHaarHead_translated right blocks hb p)

private theorem project_head_independent (r : RatPoly) :
    HeadQuaternionIndependent (project 0 r) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  change exponentAt (clearQuaternionBlock 0 s.1) (4*0+0) +
    exponentAt (clearQuaternionBlock 0 s.1) (4*0+1) +
    exponentAt (clearQuaternionBlock 0 s.1) (4*0+2) +
    exponentAt (clearQuaternionBlock 0 s.1) (4*0+3) = 0
  rw [exponentAt_clearQuaternionBlock_self s.1 0 0 (by decide),
    exponentAt_clearQuaternionBlock_self s.1 0 1 (by decide),
    exponentAt_clearQuaternionBlock_self s.1 0 2 (by decide),
    exponentAt_clearQuaternionBlock_self s.1 0 3 (by decide)]

private theorem head_project_pairing (blocks : Nat) (r p : RatPoly) :
    quaternionHaar (blocks+1) (polyMul r (project 0 p)) ≈
      quaternionHaar blocks
        (polyMul (dropHeadPolynomial (project 0 r)) (partialHaarHead p)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_selfAdjoint (blocks+1) 0 (by omega) r p))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_headIndependent blocks p (project 0 r)
          (project_head_independent r))
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- Same identity for the EXISTING in-place projection. Insertions may
depend on the integrated head; they are projected, not discarded. -/
theorem project_head_translated (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (p : RatPoly) :
    HaarCarrierEqv (blocks+1) (project 0 (T right p)) (project 0 p) := by
  intro r
  exact Q'.eqv_trans _ _ _ (head_project_pairing blocks r (T right p))
    (Q'.eqv_trans _ _ _
      (partialHaarHead_translated right blocks hb p (dropHeadPolynomial (project 0 r)))
      (Q'.eqv_symm (head_project_pairing blocks r p)))

/-- Transform BOTH the original weight and its inserted test. -/
theorem weighted_moment_translated (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (W p : RatPoly) :
    HaarCarrierEqv blocks
      (partialHaarHead (polyMul (T right W) (T right p)))
      (partialHaarHead (polyMul W p)) :=
  (RatPolyCoeffEqv.haarCarrier (partialHaarHead_congr
    (translatedHeadPolynomial_mul _ W p).symm)).trans
    (partialHaarHead_translated right blocks hb (polyMul W p))

/-- The second moment retains the same transformed weight, not a new law. -/
theorem weighted_square_translated (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (W p : RatPoly) :
    HaarCarrierEqv blocks
      (partialHaarHead (polyMul (T right W) (polyMul (T right p) (T right p))))
      (partialHaarHead (polyMul W (polyMul p p))) :=
  (RatPolyCoeffEqv.haarCarrier (partialHaarHead_congr
    (((translatedHeadPolynomial_mul _ p p).symm).mul_left (T right W)))).trans
    (weighted_moment_translated right blocks hb W (polyMul p p))

/-- The literal existing division-free variance determinant is preserved. -/
theorem determinant_translated (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (W p : RatPoly) :
    HaarCarrierEqv blocks (determinant (T right W) (T right p)) (determinant W p) :=
  HaarCarrierEqv.add
    (HaarCarrierEqv.mul (partialHaarHead_translated right blocks hb W)
      (weighted_square_translated right blocks hb W p))
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul
      (weighted_moment_translated right blocks hb W p)
      (weighted_moment_translated right blocks hb W p)))

#print axioms monomial_conditional
#print axioms partialHaarHead_translated
#print axioms project_head_translated
#print axioms weighted_moment_translated
#print axioms weighted_square_translated
#print axioms determinant_translated

end YMGap.Continuum.SU2QuaternionConditionalHaarTranslation
