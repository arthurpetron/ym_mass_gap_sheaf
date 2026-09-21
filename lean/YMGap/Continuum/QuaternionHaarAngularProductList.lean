/-
# Explicit angular budgets for original reindexed products

The finite list length controls the value and derivative budgets by actual
Leibniz certificates. Reindexing the empty product preserves its padded
constant in Haar order, not by a false literal polynomial equality.
The consumer is the at-most-six incident faces in a selected-link Ward frame.
-/

import YMGap.Continuum.QuaternionHaarAngularProductBounds
import YMGap.Continuum.AngularProductBudget
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry

namespace YMGap.Continuum.QuaternionHaarAngularProductList

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.AngularProductBudget

/-- Transport both endpoint certificates, with the reindexed constant pinned. -/
def intervalReindex {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {p : RatPoly} {c : Q'} (P : Interval blocks p c) :
    Interval blocks (reindexQuaternionPolynomial s p) c where
  support := reindex_supported s p
  nonnegative := P.nonnegative
  upper := by
    have C := reindex_certificate s
      (supported_add (polySmul_supported (supported_one blocks) c) (intervalNeg P).support) P.upper
    simp only [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul,
      reindexQuaternionPolynomial_neg] at C
    have hone := carrierOfPrefix (reindex_supported s polyOne) (supported_one blocks)
      (reindex_polyOne_prefix s)
    exact .transport (HaarCarrierEqv.add (HaarCarrierEqv.symm (HaarCarrierEqv.smul c hone))
      (HaarCarrierEqv.refl blocks _)) C
  lower := by
    have C := reindex_certificate s
      (supported_add (polySmul_supported (supported_one blocks) c) P.support) P.lower
    simp only [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul] at C
    have hone := carrierOfPrefix (reindex_supported s polyOne) (supported_one blocks)
      (reindex_polyOne_prefix s)
    exact .transport (HaarCarrierEqv.add (HaarCarrierEqv.symm (HaarCarrierEqv.smul c hone))
      (HaarCarrierEqv.refl blocks _)) C

/-- The literal reindexed product, including its empty-list constant. -/
def reindexedProductBound {blocks i j : Nat} {Index : Type}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (s : QuaternionBlockInvolution blocks) (factor : Index → RatPoly) (B C : Q') :
    (ids : List Index) →
    (∀ id, id ∈ ids → AngularBound blocks i j (reindexQuaternionPolynomial s (factor id)) B C) →
    AngularBound blocks i j (reindexQuaternionPolynomial s (polynomialProduct factor ids))
      (valueBudget B ids.length) (derivativeBudget B C ids.length)
  | [], _ => AngularBound.ofCarrier hb hi hj (reindex_supported s polyOne)
      (carrierOfPrefix (reindex_supported s polyOne) (supported_one blocks) (reindex_polyOne_prefix s))
      (AngularBound.one hb hi hj)
  | id :: ids, H => by
      change AngularBound blocks i j
        (reindexQuaternionPolynomial s (polyMul (factor id) (polynomialProduct factor ids))) _ _
      rw [reindexQuaternionPolynomial_mul]
      exact (H id List.mem_cons_self).mul hb hi hj
        (reindexedProductBound hb hi hj s factor B C ids
          (fun k hk => H k (List.mem_cons_of_mem id hk)))

end YMGap.Continuum.QuaternionHaarAngularProductList

#print axioms YMGap.Continuum.QuaternionHaarAngularProductList.intervalReindex
#print axioms YMGap.Continuum.QuaternionHaarAngularProductList.reindexedProductBound
