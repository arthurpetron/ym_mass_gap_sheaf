/-
# Algebraic extraction of one-block factors from a crossed determinant

The A-only and B-only factors are replicated in their own variables.
The shared factor remains inside the signed crossed determinant. This is
an arbitrary-insertion Haar-carrier identity, not a positivity estimate.
-/

import YMGap.Continuum.SU2QuaternionFourCopyCovariance

namespace YMGap.Continuum.SU2QuaternionSharedFactorDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionFourCopyCovariance

local infix:50 " ≈ " => Q'.eqv

/-- All one-block factors are duplicated; only the shared interaction is
inside the crossed determinant. -/
def weightedFourEnergy (n : Nat) (A B : List Nat) (L R K f g : RatPoly) : RatPoly :=
  polyMul
    (polyMul
      (polyMul (polyMul L (replica n A L)) (polyMul R (replica n B R)))
      (crossDeterminant n A B K))
    (polyMul (difference n (A++B) f) (difference n (A++B) g))

/-- Exact extraction of A-only and B-only weights from the signed
four-copy determinant. No factor involving both families is removed. -/
theorem shared_factor_determinant (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (L R K : RatPoly)
    (hL : SupportedQuaternionBlocks n L)
    (hR : SupportedQuaternionBlocks n R)
    (hLB : ∀ i, i ∈ B → QuaternionBlockIndependent i L)
    (hRA : ∀ i, i ∈ A → QuaternionBlockIndependent i R) :
    HaarCarrierEqv (n+n)
      (crossDeterminant n A B (polyMul (polyMul L R) K))
      (polyMul
        (polyMul (polyMul L (replica n A L))
          (polyMul R (replica n B R)))
        (crossDeterminant n A B K)) := by
  have hJL := joint_replica_of_right_independent n A B hdisj L hL hLB
  have hJR := joint_replica_of_left_independent n A B hdisj R hR hRA
  have hLBfix := reindex_fixed_of_selected_independent n B L hL hLB
  have hRAfix := reindex_fixed_of_selected_independent n A R hR hRA
  have hAB : HaarCarrierEqv (n+n)
      (replica n (A++B) (polyMul (polyMul L R) K))
      (polyMul (polyMul (replica n A L) (replica n B R))
        (replica n (A++B) K)) := by
    dsimp only [replica]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.mul (HaarCarrierEqv.mul hJL hJR) (.refl _ _)
  have hA : HaarCarrierEqv (n+n)
      (replica n A (polyMul (polyMul L R) K))
      (polyMul (polyMul (replica n A L) R) (replica n A K)) := by
    dsimp only [replica]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.mul
      (HaarCarrierEqv.mul (.refl _ _) hRAfix) (.refl _ _)
  have hB : HaarCarrierEqv (n+n)
      (replica n B (polyMul (polyMul L R) K))
      (polyMul (polyMul L (replica n B R)) (replica n B K)) := by
    dsimp only [replica]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.mul
      (HaarCarrierEqv.mul hLBfix (.refl _ _)) (.refl _ _)
  have hcarrier : HaarCarrierEqv (n+n)
      (crossDeterminant n A B (polyMul (polyMul L R) K))
      (polyAdd
        (polyMul (polyMul (polyMul L R) K)
          (polyMul (polyMul (replica n A L) (replica n B R))
            (replica n (A++B) K)))
        (polyNeg
          (polyMul
            (polyMul (polyMul (replica n A L) R) (replica n A K))
            (polyMul (polyMul L (replica n B R)) (replica n B K))))) := by
    dsimp only [crossDeterminant]
    exact HaarCarrierEqv.add
      (HaarCarrierEqv.mul (.refl _ _) hAB)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hA hB))
  refine hcarrier.trans (RatPolyCoeffEqv.haarCarrier ?_)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 4))
        (.mul (.mul (.var 1) (.var 3)) (.var 5)))
      (.neg
        (.mul (.mul (.mul (.var 1) (.var 2)) (.var 6))
          (.mul (.mul (.var 0) (.var 3)) (.var 7)))))
    (.mul
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.add (.mul (.var 4) (.var 5))
        (.neg (.mul (.var 6) (.var 7)))))
    (by decide)
    (fun | 0 => L | 1 => replica n A L | 2 => R
         | 3 => replica n B R | 4 => K
         | 5 => replica n (A++B) K | 6 => replica n A K
         | _ => replica n B K)

/-- The signed shared-interaction identity, with every one-block and
exterior weight retained. No division by the conditional normalizer occurs. -/
theorem weighted_four_copy_identity (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (L R K f g r : RatPoly)
    (hL : SupportedQuaternionBlocks n L) (hR : SupportedQuaternionBlocks n R)
    (hK : SupportedQuaternionBlocks n K)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hr : SupportedQuaternionBlocks n r)
    (hLB : ∀ i, i ∈ B → QuaternionBlockIndependent i L)
    (hRA : ∀ i, i ∈ A → QuaternionBlockIndependent i R)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g)
    (hrAB : ∀ i, i ∈ A++B → QuaternionBlockIndependent i r)
    (hnodup : (A++B).Nodup) (hids : ∀ i, i ∈ A++B → i < n) :
    let N := covarianceNumerator (A++B) (polyMul (polyMul L R) K) f g;
    quaternionHaar (n+n) (polyMul r (weightedFourEnergy n A B L R K f g)) ≈
      quaternionHaar n (polyMul r (polyAdd (polyAdd N N) (polyAdd N N))) := by
  have he : HaarCarrierEqv (n+n)
      (fourEnergy n A B (polyMul (polyMul L R) K) f g)
      (weightedFourEnergy n A B L R K f g) :=
    HaarCarrierEqv.mul (shared_factor_determinant n A B hdisj L R K hL hR hLB hRA)
      (.refl _ _)
  exact Q'.eqv_trans _ _ _ (he.symm r)
    (four_copy_identity n A B hdisj (polyMul (polyMul L R) K) f g r
      (supported_polyMul (supported_polyMul hL hR) hK) hf hg hr hfB hgA hrAB hnodup hids)

#print axioms shared_factor_determinant
#print axioms weighted_four_copy_identity

end YMGap.Continuum.SU2QuaternionSharedFactorDeterminant
