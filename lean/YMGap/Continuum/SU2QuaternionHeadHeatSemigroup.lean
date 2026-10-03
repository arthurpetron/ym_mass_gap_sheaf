/-
# Composition of the actual finite head heat maps

The original map heats its head and keeps all spectator coordinates shared.
At one fixed inclusive cutoff its harmonic attenuation is idempotently
truncated, so two successive nomes multiply even below input saturation.
Equality is under EVERY surviving Haar insertion, not raw coefficient
equality. No kernel positivity, conditional Poincare or scaling estimate is
asserted here.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow

namespace YMGap.Continuum.SU2QuaternionHeadHeatSemigroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionFischerRadial
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHeadHeatSmoothing (headMap_grouped)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (attenuation)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The actual spare-head map transports carrier equalities without
dropping or refreshing any supported spectator. -/
theorem headMap_carrier (tail : Nat) (w : Q') (K : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (h : HaarCarrierEqv (tail+1) p q) :
    HaarCarrierEqv (tail+1) (headMap w K p) (headMap w K q) := by
  exact partialHaarHead_carrier
    (HaarCarrierEqv.mul_left (relativeHeat w K)
      (copy_carrier (Nat.zero_lt_succ tail) hp hq h))

private theorem headMap_add (w : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (headMap w K (polyAdd p q))
      (polyAdd (headMap w K p) (headMap w K q)) := by
  unfold headMap conditionalHeat
  rw [copy_add]
  have h := partialHaarHead_congr
    (RatPolyCoeffEqv.mul_add_right (relativeHeat w K) (copy p) (copy q))
  rw [partialHaarHead_add] at h
  exact h

private theorem headMap_smul (w a : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (headMap w K (polySmul a p))
      (polySmul a (headMap w K p)) := by
  unfold headMap conditionalHeat
  rw [copy_smul]
  exact (partialHaarHead_congr
    (RatPolyCoeffEqv.polyMul_smul_right a (relativeHeat w K) (copy p))).trans
    (partialHaarHead_smul a _)

private theorem headMap_zero (w : Q') (K : Nat) :
    RatPolyCoeffEqv (headMap w K polyZero) polyZero :=
  partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right (relativeHeat w K))

/-- Exact retained-or-omitted harmonic transmission, including all tests
in the surviving head/spectator carrier. -/
theorem headMap_harmonic (tail : Nat) (w : Q') (K d : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hpad : HeadPadded p)
    (hd : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    HaarCarrierEqv (tail+1) (headMap w K p) (polySmul (attenuation w K d) p) := by
  intro test
  have hc : quaternionHaar (tail+1) (polyMul p test) ≈
      quaternionHaar (tail+1) (polyMul test p) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm p test)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm test _))
    (Q'.eqv_trans _ _ _ (headMap_pairing tail w K p test)
      (Q'.eqv_trans _ _ _ (harmonic_pair tail w K d p test hp hpad hd hh)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc)
          (Q'.eqv_symm (quaternionHaar_polyMul_smul_right (tail+1)
            (attenuation w K d) test p)))))

private theorem sum_padded {blocks : Nat} :
    ∀ ms : List (Mode blocks), HeadPadded (sumHarmonics ms)
  | [] => by
      intro t ht
      contradiction
  | m::ms => (m.padded.smul m.coefficient).add (sum_padded ms)

private theorem map_group_sum (tail : Nat) (u v : Q') (K : Nat)
    (ms : List (Mode (tail+1))) : ∀ ids : List Nat,
    HaarCarrierEqv (tail+1)
      (headMap u K (polySum (ids.map fun d =>
        polySmul (attenuation v K d) (grouped d ms))))
      (polySum (ids.map fun d =>
        polySmul (attenuation v K d * attenuation u K d) (grouped d ms)))
  | [] => RatPolyCoeffEqv.haarCarrier (headMap_zero u K)
  | d::ds => by
      simp only [List.map_cons, polySum]
      have hpad : HeadPadded (grouped d ms) :=
        headComponent_min_length (sum_padded ms)
      have hd := headMap_harmonic tail u K d (grouped d ms)
        (grouped_supported d ms) hpad (grouped_degree d ms) (grouped_harmonic d ms)
      have hterm : HaarCarrierEqv (tail+1)
          (headMap u K (polySmul (attenuation v K d) (grouped d ms)))
          (polySmul (attenuation v K d * attenuation u K d) (grouped d ms)) :=
        (RatPolyCoeffEqv.haarCarrier (headMap_smul u (attenuation v K d) K _)).trans
          ((HaarCarrierEqv.smul (attenuation v K d) hd).trans
            (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_assoc _ _ _)))
      exact (RatPolyCoeffEqv.haarCarrier (headMap_add u K _ _)).trans
        (HaarCarrierEqv.add hterm (map_group_sum tail u v K ms ds))

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
  | n+1 =>
      Q'.eqv_trans _ _ _ (regroup _ _ v u)
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

private theorem sum_supported {blocks : Nat} (f : Nat → RatPoly)
    (hf : ∀ d, SupportedQuaternionBlocks blocks (f d)) : ∀ ids : List Nat,
    SupportedQuaternionBlocks blocks (polySum (ids.map f))
  | [] => by
      intro t ht
      contradiction
  | d::ds => polyAdd_supported (hf d) (sum_supported f hf ds)

private theorem sum_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ d, RatPolyCoeffEqv (f d) (g d)) →
      RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | d::ds, h => (h d).add (sum_congr f g ds h)

/-- SAME-cutoff finite heat semigroup on the actual shared-spectator map.
No saturation or nome positivity is needed: omitted modes remain zero. -/
theorem headMap_semigroup (tail : Nat) (u v : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (headMap u K (headMap v K p)) (headMap (u*v) K p) := by
  let ms := modes (tail+1) (Nat.zero_lt_succ tail) p
  let ids := headDegrees (sumHarmonics ms)
  have hvs : SupportedQuaternionBlocks (tail+1)
      (polySum (ids.map fun d => polySmul (attenuation v K d) (grouped d ms))) :=
    sum_supported _ (fun d => polySmul_supported (grouped_supported d ms) _) ids
  have hv := headMap_carrier tail u K (headMap_supported tail v K hp) hvs
    (headMap_grouped tail v K p hp)
  have hc : RatPolyCoeffEqv
      (polySum (ids.map fun d =>
        polySmul (attenuation v K d * attenuation u K d) (grouped d ms)))
      (polySum (ids.map fun d => polySmul (attenuation (u*v) K d) (grouped d ms))) :=
    sum_congr _ _ ids (fun d =>
      RatPolyCoeffEqv.smul_coefficient (attenuation_product u v K d) _)
  exact hv.trans ((map_group_sum tail u v K ms ids).trans
    ((RatPolyCoeffEqv.haarCarrier hc).trans (headMap_grouped tail (u*v) K p hp).symm))

end YMGap.Continuum.SU2QuaternionHeadHeatSemigroup

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSemigroup.headMap_carrier
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSemigroup.headMap_harmonic
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSemigroup.headMap_semigroup
