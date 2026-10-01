/-
# A bounded symmetric two-slice test under the original product heat

The source itself is arbitrary and supported.  Only the observable has the
supplied square cap four.  All moments retain the original product heat.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionReplicaPairBounds
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.SU2QuaternionProductHeatSumTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (lift_cap_carrier)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order weighted_scale finite_square_bound)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

def sumCopy (n : Nat) (p : RatPoly) : RatPoly :=
  polyAdd p (liftBoundary n p)

def sumTest (n : Nat) (q f : RatPoly) : RatPoly :=
  polyMul (sumCopy n q) (sumCopy n f)

private theorem support_first {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_cap (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) := by
  unfold cap
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem gap_supported {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (gap 4 f) :=
  supported_add (support_cap n 4) (support_neg (supported_polyMul hf hf))

theorem sumCopy_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) (sumCopy n p) :=
  supported_add (support_first hp) (lift_supported hp n)

theorem sumTest_supported {n : Nat} {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) (sumTest n q f) :=
  supported_polyMul (sumCopy_supported hq) (sumCopy_supported hf)

private def lowerSquareBound {n : Nat} {f : RatPoly}
    (P : SquareBound n f 4) : SquareBound (n+n) f 4 where
  support := support_first P.support
  nonnegative := P.nonnegative
  certificate := certificate_extend n (gap_supported P.support) P.certificate

private def upperSquareBound {n : Nat} {f : RatPoly}
    (P : SquareBound n f 4) :
    SquareBound (n+n) (liftBoundary n f) 4 where
  support := lift_supported P.support n
  nonnegative := P.nonnegative
  certificate := by
    have hc : HaarCarrierEqv (n+n)
        (liftBoundary n (gap 4 f)) (gap 4 (liftBoundary n f)) := by
      unfold gap
      rw [lift_add, lift_neg, lift_product]
      exact HaarCarrierEqv.add (lift_cap_carrier n 4) (HaarCarrierEqv.refl _ _)
    exact .transport hc.symm (lift_certificate n P.certificate)

private theorem sumCopy_source_norm_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q : RatPoly} (hq : SupportedQuaternionBlocks n q) :
    H (n+n) (polyMul (productHeat n w K ids)
      (polyMul (sumCopy n q) (sumCopy n q))) ≤
      (4 : Q') * H n (polyMul q q) := by
  let W := productHeat n w K ids
  let A := H n (polyMul q q)
  have hsource : RatPolyCoeffEqv (sumCopy n q)
      (polySum [q, liftBoundary n q]) := by
    change RatPolyCoeffEqv (polyAdd q (liftBoundary n q))
      (polyAdd q (polyAdd (liftBoundary n q) polyZero))
    exact (RatPolyCoeffEqv.refl q).add
      (RatPolyCoeffEqv.add_zero (liftBoundary n q)).symm
  have hpin : H (n+n) (polyMul W (polyMul (sumCopy n q) (sumCopy n q))) ≈
      H (n+n) (polyMul W
        (polyMul (polySum [q, liftBoundary n q])
          (polySum [q, liftBoundary n q]))) :=
    haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (hsource.mul hsource))
  have hq2 := supported_polyMul hq hq
  have hlow : H (n+n) (polyMul W (polyMul q q)) ≈ A :=
    productHeat_lower_marginal n w K ids hnd hids (polyMul q q) hq2
  have hupp : H (n+n) (polyMul W
      (polyMul (liftBoundary n q) (liftBoundary n q))) ≈ A := by
    rw [← lift_product]
    exact productHeat_upper_marginal n w K ids hnd hids (polyMul q q) hq2
  have hb : ∀ p, p ∈ [q, liftBoundary n q] →
      H (n+n) (polyMul W (polyMul p p)) ≤ A := by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact Q'.le_of_eqv hlow
    · have hp' : p = liftBoundary n q := List.mem_singleton.mp hp
      subst p
      exact Q'.le_of_eqv hupp
  have hs : ∀ p, p ∈ [q, liftBoundary n q] →
      SupportedQuaternionBlocks (n+n) p := by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact support_first hq
    · have hp' : p = liftBoundary n q := List.mem_singleton.mp hp
      subst p
      exact lift_supported hq n
  have hbound := finite_square_bound
    (productHeatCertificate n hw0 hw1 K hK ids hids)
    [q, liftBoundary n q] hs A hb
  have hfour : (Q'.ofNat [q, liftBoundary n q].length *
      Q'.ofNat [q, liftBoundary n q].length) * A ≈ (4 : Q') * A := by
    change ((2 : Q') * 2) * A ≈ (4 : Q') * A
    exact poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.const 2)) (.var 0))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => A)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hfour))

/-- The symmetric test has a uniform factor 64 against the one-copy raw
source square mass.  No source-square cap or source-factorization is used. -/
theorem sumTest_square_le_rawSourceMass (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (P : SquareBound n f 4) :
    weightedPair (n+n) (productHeat n w K ids)
      (sumTest n q f) (sumTest n q f) ≤
      (64 : Q') * H n (polyMul q q) := by
  let W := productHeat n w K ids
  let qs := sumCopy n q
  let fs := sumCopy n f
  let R := polyMul W (polyMul qs qs)
  have hqs := sumCopy_supported hq
  have hfs := sumCopy_supported P.support
  have hR : Certificate (n+n) R :=
    (productHeatCertificate n hw0 hw1 K hK ids hids).mul (Certificate.square qs hqs)
  have hfsBound : SquareBound (n+n) fs 16 :=
    SquareBound.changeCap (by decide)
      ((lowerSquareBound P).add (upperSquareBound P))
  have horder := weighted_order hR hfsBound.certificate
  have hpair : weightedPair (n+n) W (sumTest n q f) (sumTest n q f) ≈
      H (n+n) (polyMul R (polyMul fs fs)) := by
    unfold weightedPair sumTest R
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => qs | 1 => fs | _ => W))
  have hcap : H (n+n) (polyMul R (cap 16)) ≈
      (16 : Q') * H (n+n) R :=
    Q'.eqv_trans _ _ _ (weighted_scale (n+n) R polyOne 16)
      (Q'.mul_eqv_congr_left 16 _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_one R)))
  have hmass := sumCopy_source_norm_le n hw0 hw1 K hK ids hnd hids hq
  have hlast : (16 : Q') * ((4 : Q') * H n (polyMul q q)) ≈
      (64 : Q') * H n (polyMul q q) :=
    poly_identity_of_normal_eq
      (.mul (.const 16) (.mul (.const 4) (.var 0)))
      (.mul (.const 64) (.var 0)) (by decide)
      (fun _ => H n (polyMul q q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpair)
    (Q'.le_trans' _ _ _ horder
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcap)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ 16 hmass (by decide))
          (Q'.le_of_eqv hlast))))

end YMGap.Continuum.SU2QuaternionProductHeatSumTest

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSumTest.sumCopy_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSumTest.sumTest_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSumTest.sumTest_square_le_rawSourceMass
