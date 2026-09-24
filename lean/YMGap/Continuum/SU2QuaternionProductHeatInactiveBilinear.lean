/-
# Exact bilinear inactive projection of the ORIGINAL partial product heat

Both inputs to the signed bilinear pairing can be Haar-projected on the
missing family. The projected propagated input is independent of that family,
so the missing heat factors can then be restored exactly. This retains every
signed coefficient and uses no positivity or cutoff guard.
-/

import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection

namespace YMGap.Continuum.SU2QuaternionProductHeatInactiveBilinear

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
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Project both entries on every inactive block, then restore the missing
heat factors on the projected propagated input. This is an exact signed
bilinear identity. -/
theorem productMap_inactive_to_full_bilinear (n : Nat) (w : Q') (K : Nat)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (hcover : (F++ids).Perm (List.range n))
    (f g : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar n (polyMul g (productMap n w K ids f)) ≈
      quaternionHaar n (polyMul (familyProject F g)
        (productMap n w K (List.range n) (familyProject F f))) := by
  let qf := familyProject F f
  let qg := familyProject F g
  have hqf := familyProject_supported F hf
  have hqg := familyProject_supported F hg
  have ho : ∀ i, i ∈ F → QuaternionBlockIndependent i (productMap n w K ids qf) :=
    fun i hi => productMap_independent_of_not_mem n w K ids hids i
      (hF i hi) (hnot i hi) qf hqf
  have hp :
      quaternionHaar n (polyMul g (productMap n w K ids qf)) ≈
        quaternionHaar n (polyMul qg (productMap n w K ids qf)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlocks n F _ g hF ho)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hd := productMap_drop_independent_prefix n w K ids F
    (hcover.symm.nodup (CayleyParentInj.range_nodup n))
    (fun i hi => List.mem_range.mp (hcover.mem_iff.mp hi)) qf hqf
    (familyProject_independent F f)
  have he : RatPolyCoeffEqv (productMap n w K (F++ids) qf)
      (productMap n w K (List.range n) qf) :=
    partialHaarHeads_congr n ((polynomialProduct_perm _ hcover).mul_right qf)
  exact Q'.eqv_trans _ _ _
    (productMap_family_input_pairing n w K ids F hids hF hnot f g)
    (Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hd qg hqg))
        (haar_of_coeff (he.mul_left qg))))

end YMGap.Continuum.SU2QuaternionProductHeatInactiveBilinear

#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveBilinear.productMap_inactive_to_full_bilinear
