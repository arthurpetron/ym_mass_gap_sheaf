/-
# Direct composition at the ORIGINAL retained output link

The input p(x,y,z) may depend on the original retained link y. The actual
conditionalHeat integrates x against k(x,y); headMap heats only the selected
head while keeping y,z shared. Their mixed composition has multiplied nome
at the SAME finite cutoff, under every surviving insertion in y,z.

The proof uses harmonic reproduction directly at y, not a non-injective
pullback of a carrier equality at a fresh output. No saturation, kernel
positivity, conditional Poincare or changing-family estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatSemigroup

namespace YMGap.Continuum.SU2QuaternionConditionalHeatComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction (heat_harmonic_reproduction)
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution (substituteRetained)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal (headMap)
open YMGap.Continuum.SU2QuaternionHeadHeatSmoothing (headMap_grouped)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (attenuation)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Direct integration transports carrier equalities, with the ORIGINAL
retained output and all spectators still present. -/
theorem conditionalHeat_carrier (tail : Nat) (w : Q') (K : Nat) {p q : RatPoly}
    (h : HaarCarrierEqv (tail+1) p q) :
    HaarCarrierEqv tail (conditionalHeat w K p) (conditionalHeat w K q) :=
  partialHaarHead_carrier (HaarCarrierEqv.mul_left (relativeHeat w K) h)

/-- Actual harmonic transmission to the already-existing retained block.
The input's harmonic coefficients may depend on this very block. -/
theorem conditionalHeat_harmonic_carrier (tail : Nat) (ht : 0 < tail)
    (w : Q') (K d : Nat) (p : RatPoly)
    (hd : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    HaarCarrierEqv tail (conditionalHeat w K p)
      (polySmul (attenuation w K d) (substituteRetained p)) := by
  intro boundary
  have h := heat_harmonic_reproduction tail ht w K d p hd hh boundary
  have hpin : quaternionHaar (tail+1)
      (polyMul (polyMul (relativeHeat w K) p) (liftHead boundary)) ≈
      attenuation w K d * quaternionHaar tail
        (polyMul (substituteRetained p) boundary) := by
    unfold attenuation
    if hK : d ≤ K then
      simpa only [if_pos hK] using h
    else
      simp only [if_neg hK] at h ⊢
      exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.zero_mul_eqv _))
  have hc : quaternionHaar tail (polyMul (substituteRetained p) boundary) ≈
      quaternionHaar tail (polyMul boundary (substituteRetained p)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm boundary _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm
      (head_pairing tail 1 (polyMul (relativeHeat w K) p) boundary))
      (Q'.eqv_trans _ _ _ hpin
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc)
          (Q'.eqv_symm (quaternionHaar_polyMul_smul_right tail
            (attenuation w K d) boundary (substituteRetained p))))))

private theorem conditional_add (w : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat w K (polyAdd p q))
      (polyAdd (conditionalHeat w K p) (conditionalHeat w K q)) := by
  unfold conditionalHeat
  have h := partialHaarHead_congr
    (RatPolyCoeffEqv.mul_add_right (relativeHeat w K) p q)
  rw [partialHaarHead_add] at h
  exact h

private theorem conditional_smul (w a : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat w K (polySmul a p))
      (polySmul a (conditionalHeat w K p)) :=
  (partialHaarHead_congr
    (RatPolyCoeffEqv.polyMul_smul_right a (relativeHeat w K) p)).trans
    (partialHaarHead_smul a _)

private theorem conditional_sum (tail : Nat) (w : Q') (K : Nat)
    (f g : Nat → RatPoly)
    (h : ∀ d, HaarCarrierEqv tail (conditionalHeat w K (f d)) (g d)) :
    ∀ ids : List Nat, HaarCarrierEqv tail
      (conditionalHeat w K (polySum (ids.map f))) (polySum (ids.map g))
  | [] => RatPolyCoeffEqv.haarCarrier
      (partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right (relativeHeat w K)))
  | d::ds => (RatPolyCoeffEqv.haarCarrier (conditional_add w K _ _)).trans
      (HaarCarrierEqv.add (h d) (conditional_sum tail w K f g h ds))

private theorem regroup (a b u v : Q') : (a*u)*(b*v) ≈ (a*b)*(u*v) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (by decide) (fun i => if i=0 then a else if i=1 then b else if i=2 then u else v)

private theorem qpow_product (u v : Q') : ∀ n : Nat,
    RGTransport.qpow v n * RGTransport.qpow u n ≈ RGTransport.qpow (u*v) n
  | 0 => by
      change Q'.eqv (1*1) 1
      decide
  | n+1 => Q'.eqv_trans _ _ _ (regroup _ _ v u)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (qpow_product u v n))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv v u)))

private theorem attenuation_product (u v : Q') (K d : Nat) :
    attenuation v K d * attenuation u K d ≈ attenuation (u*v) K d := by
  unfold attenuation
  if h : d ≤ K then
    simp only [if_pos h]
    exact qpow_product u v _
  else
    simp only [if_neg h]
    decide

/-- Heat the source head with v, then integrate it to the ORIGINAL retained
output with u. No diagonal carrier substitution or saturation is used. -/
theorem conditionalHeat_headMap_composition (tail : Nat) (ht : 0 < tail)
    (u v : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail
      (conditionalHeat u K (headMap v K p)) (conditionalHeat (u*v) K p) := by
  let ms := modes (tail+1) (Nat.zero_lt_succ tail) p
  let ids := headDegrees (sumHarmonics ms)
  let out := fun d => polySmul (attenuation (u*v) K d)
    (substituteRetained (grouped d ms))
  have hleft : HaarCarrierEqv tail
      (conditionalHeat u K (headMap v K p)) (polySum (ids.map out)) := by
    refine (conditionalHeat_carrier tail u K (headMap_grouped tail v K p hp)).trans ?_
    apply conditional_sum tail u K _ out _ ids
    intro d
    have he := conditionalHeat_harmonic_carrier tail ht u K d (grouped d ms)
      (grouped_degree d ms) (grouped_harmonic d ms)
    exact (RatPolyCoeffEqv.haarCarrier (conditional_smul u (attenuation v K d) K _)).trans
      ((HaarCarrierEqv.smul (attenuation v K d) he).trans
        (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
          (RatPolyCoeffEqv.smul_coefficient (attenuation_product u v K d) _))))
  have hsource : HaarCarrierEqv (tail+1) p
      (polySum (ids.map fun d => grouped d ms)) :=
    (polynomial_harmonic_carrier (Nat.zero_lt_succ tail) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  have hright : HaarCarrierEqv tail
      (conditionalHeat (u*v) K p) (polySum (ids.map out)) :=
    (conditionalHeat_carrier tail (u*v) K hsource).trans
      (conditional_sum tail (u*v) K _ out
        (fun d => conditionalHeat_harmonic_carrier tail ht (u*v) K d (grouped d ms)
          (grouped_degree d ms) (grouped_harmonic d ms)) ids)
  exact hleft.trans hright.symm

end YMGap.Continuum.SU2QuaternionConditionalHeatComposition

#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatComposition.conditionalHeat_carrier
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatComposition.conditionalHeat_harmonic_carrier
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatComposition.conditionalHeat_headMap_composition
