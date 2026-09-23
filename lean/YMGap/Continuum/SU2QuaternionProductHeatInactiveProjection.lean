/-
# Exact inactive projection of the ORIGINAL partial product heat

The missing heat factors are Haar projections, not identity channels.
Projecting every absent coordinate changes neither the original kernel
pairing nor its two-endpoint quadratic pairing. On that projected input,
the missing heat factors can be restored exactly by their vacuum marginal.
These identities retain all signed coefficients and use no positivity or
cutoff guard. They are the operator join for a retained-residual estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatFamilyNull
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- An absent family is averaged on the input, with every original test
retained. No support, positivity or distinctness hypothesis is used. -/
theorem productMap_family_input_pairing (n : Nat) (w : Q') (K : Nat)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (f g : RatPoly) :
    quaternionHaar n (polyMul g (productMap n w K ids f)) ≈
      quaternionHaar n (polyMul g (productMap n w K ids (familyProject F f))) := by
  let r := polyMul (productHeat n w K ids) (liftBoundary n g)
  have hr : ∀ i, i ∈ F → QuaternionBlockIndependent i r := fun i hi =>
    quaternionBlockIndependent_polyMul
      (productHeat_independent_lower n w K ids hids i (hF i hi) (hnot i hi))
      (lift_lower_independent n g i (hF i hi))
  have pin (a : RatPoly) :
      quaternionHaar n (polyMul g (productMap n w K ids a)) ≈
        quaternionHaar (n+n) (polyMul r a) :=
    Q'.eqv_trans _ _ _ (productMap_pairing n w K ids a g)
      (haar_of_coeff (((RatPolyCoeffEqv.mul_comm a (liftBoundary n g)).mul_left _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
  exact Q'.eqv_trans _ _ _ (pin f)
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_eq_after_integratingBlocks (n+n) F r f
        (fun i hi => Nat.lt_of_lt_of_le (hF i hi) (Nat.le_add_right n n)) hr)
      (Q'.eqv_symm (pin (familyProject F f))))

/-- Both occurrences of the input can be projected against the SAME
partial-product kernel, not against a replacement marginal. -/
theorem productMap_family_quadratic_pairing (n : Nat) (w : Q') (K : Nat)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (polyMul f (productMap n w K ids f)) ≈
      quaternionHaar n (polyMul (familyProject F f)
        (productMap n w K ids (familyProject F f))) := by
  let q := familyProject F f
  have hq := familyProject_supported F hf
  have ho : ∀ i, i ∈ F → QuaternionBlockIndependent i (productMap n w K ids q) :=
    fun i hi => productMap_independent_of_not_mem n w K ids hids i
      (hF i hi) (hnot i hi) q hq
  exact Q'.eqv_trans _ _ _ (productMap_family_input_pairing n w K ids F hids hF hnot f f)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlocks n F _ f hF ho)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- Restoring distinct missing factors on a family-independent input leaves
the actual output unchanged under every supported insertion. -/
theorem productMap_drop_independent_prefix (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) : ∀ (F : List Nat), (F++ids).Nodup →
      (∀ i, i ∈ F++ids → i < n) → ∀ (f : RatPoly), SupportedQuaternionBlocks n f →
      (∀ i, i ∈ F → QuaternionBlockIndependent i f) →
      SupportedHaarEqv n (productMap n w K (F++ids) f) (productMap n w K ids f)
  | [], _, _, _, _, _ => SupportedHaarEqv.refl n _
  | i::F, hn, hi, f, hf, hind => by
      have hnd := List.nodup_cons.mp hn
      have ht : ∀ j, j ∈ F++ids → j < n :=
        fun j hj => hi j (List.mem_cons_of_mem i hj)
      exact (productMap_cons_input_independent n w K i (F++ids)
        (hi i List.mem_cons_self) hnd.1 ht f hf (hind i List.mem_cons_self)).trans
        (productMap_drop_independent_prefix n w K ids F hnd.2 ht f hf
          (fun j hj => hind j (List.mem_cons_of_mem i hj)))

/-- Complete the actual active list using a proved permutation, on the
projected original input. This is an exact two-endpoint pairing identity. -/
theorem productMap_inactive_to_full_pairing (n : Nat) (w : Q') (K : Nat)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (hcover : (F++ids).Perm (List.range n))
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (polyMul f (productMap n w K ids f)) ≈
      quaternionHaar n (polyMul (familyProject F f)
        (productMap n w K (List.range n) (familyProject F f))) := by
  let q := familyProject F f
  have hq := familyProject_supported F hf
  have hd := productMap_drop_independent_prefix n w K ids F
    (hcover.symm.nodup (CayleyParentInj.range_nodup n))
    (fun i hi => List.mem_range.mp (hcover.mem_iff.mp hi)) q hq
    (familyProject_independent F f)
  have he : RatPolyCoeffEqv (productMap n w K (F++ids) q)
      (productMap n w K (List.range n) q) :=
    partialHaarHeads_congr n ((polynomialProduct_perm _ hcover).mul_right q)
  exact Q'.eqv_trans _ _ _
    (productMap_family_quadratic_pairing n w K ids F hids hF hnot f hf)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hd q hq)) (haar_of_coeff (he.mul_left q)))

end YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection

#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection.productMap_family_input_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection.productMap_family_quadratic_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection.productMap_drop_independent_prefix
#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection.productMap_inactive_to_full_pairing
