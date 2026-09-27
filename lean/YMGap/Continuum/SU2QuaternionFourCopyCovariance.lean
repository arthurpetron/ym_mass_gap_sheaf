/-
# Exact signed four-copy conditional covariance

For disjoint selected families A,B, a B-independent test f and an
A-independent test g, the signed crossed determinant gives FOUR times the
conditional covariance numerator. The exterior insertion is used once;
no selected or exterior action factor is silently discarded.

This exact identity preserves the cross cancellation needed by the original
shared-face route. It does not assert a sign, smallness, angle or gap bound.
-/

import YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
import YMGap.Continuum.SU2QuaternionDisjointPartialSwap

namespace YMGap.Continuum.SU2QuaternionFourCopyCovariance

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
open YMGap.Continuum.SU2QuaternionDisjointPartialSwap
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

def crossDeterminant (n : Nat) (A B : List Nat) (K : RatPoly) : RatPoly :=
  polyAdd (polyMul K (replica n (A++B) K))
    (polyNeg (polyMul (replica n A K) (replica n B K)))

/-- Joint replication equals single-block replication for the corresponding
test. Exterior dependence remains unrestricted. -/
theorem joint_replica_of_right_independent (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hB : ∀ i, i ∈ B → QuaternionBlockIndependent i p) :
    HaarCarrierEqv (n+n) (replica n (A++B) p) (replica n A p) := by
  have hp₂ : SupportedQuaternionBlocks (n+n) p := by
    intro t ht
    have := hp t ht
    omega
  exact (reindex_comp_carrier n A B hdisj p).symm.trans
    (reindex_carrier (swap n A) (reindex_supported (swap n B) p) hp₂
      (reindex_fixed_of_selected_independent n B p hp hB))

theorem joint_replica_of_left_independent (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p)
    (hA : ∀ i, i ∈ A → QuaternionBlockIndependent i p) :
    HaarCarrierEqv (n+n) (replica n (A++B) p) (replica n B p) := by
  have hp₂ : SupportedQuaternionBlocks (n+n) p := by
    intro t ht
    have := hp t ht
    omega
  exact (reindex_comp_reverse_carrier n A B hdisj p).symm.trans
    (reindex_carrier (swap n B) (reindex_supported (swap n A) p) hp₂
      (reindex_fixed_of_selected_independent n A p hp hA))

def fourEnergy (n : Nat) (A B : List Nat) (K f g : RatPoly) : RatPoly :=
  polyMul (crossDeterminant n A B K)
    (polyMul (difference n (A++B) f) (difference n (A++B) g))

/-- Exact cancellation when the interaction does not depend on the left
family. An absolute-window bound alone would lose this cancellation. -/
theorem crossDeterminant_zero_of_left_independent (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (K : RatPoly)
    (hK : SupportedQuaternionBlocks n K)
    (hKA : ∀ i, i ∈ A → QuaternionBlockIndependent i K) :
    HaarCarrierEqv (n+n) (crossDeterminant n A B K) polyZero := by
  have hj := joint_replica_of_left_independent n A B hdisj K hK hKA
  have hfix := reindex_fixed_of_selected_independent n A K hK hKA
  refine (HaarCarrierEqv.add
    (HaarCarrierEqv.mul (.refl _ _) hj)
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul hfix (.refl _ _)))).trans ?_
  exact RatPolyCoeffEqv.haarCarrier ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
    (fun _ => polyMul K (replica n B K))).trans (RatPolyCoeffEqv.zero_smul polyOne))

private theorem support_double {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p := by
  intro t ht
  have := hp t ht
  omega

private theorem supported_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem mixed_supported (n : Nat) (ids : List Nat) (K f g : RatPoly)
    (hK : SupportedQuaternionBlocks n K)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g) :
    SupportedQuaternionBlocks (n+n) (mixedEnergy n ids K f g) :=
  supported_polyMul (supported_polyMul (support_double hK) (reindex_supported _ K))
    (supported_polyMul
      (supported_add (support_double hf) (supported_neg (reindex_supported _ f)))
      (supported_add (support_double hg) (supported_neg (reindex_supported _ g))))

/-- The crossed term is the negative of the selected-swap image of the
uncrossed mixed energy. This is an arbitrary-insertion carrier identity. -/
theorem fourEnergy_as_swap_sum (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (K f g : RatPoly)
    (hK : SupportedQuaternionBlocks n K)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g) :
    HaarCarrierEqv (n+n) (fourEnergy n A B K f g)
      (polyAdd (mixedEnergy n (A++B) K f g)
        (replica n A (mixedEnergy n (A++B) K f g))) := by
  have hKswap := reindex_comp_cancel n A B hdisj K
  have hfswap := reindex_comp_cancel n A B hdisj f
  have hgswap := reindex_comp_cancel n A B hdisj g
  have hfBfix := reindex_fixed_of_selected_independent n B f hf hfB
  have hgAfix := reindex_fixed_of_selected_independent n A g hg hgA
  have hfjoint := joint_replica_of_right_independent n A B hdisj f hf hfB
  have hgjoint := joint_replica_of_left_independent n A B hdisj g hg hgA
  have hdf : HaarCarrierEqv (n+n)
      (replica n A (difference n (A++B) f))
      (polyNeg (difference n (A++B) f)) := by
    dsimp only [replica, difference]
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    refine (HaarCarrierEqv.add hfjoint.symm (HaarCarrierEqv.neg (hfswap.trans hfBfix))).trans ?_
    exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.neg (.var 0))) (.neg (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => f | _ => replica n (A++B) f))
  have hdg : HaarCarrierEqv (n+n)
      (replica n A (difference n (A++B) g)) (difference n (A++B) g) := by
    dsimp only [replica, difference]
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add hgAfix (HaarCarrierEqv.neg (hgswap.trans hgjoint.symm))
  have hs : HaarCarrierEqv (n+n)
      (replica n A (mixedEnergy n (A++B) K f g))
      (polyMul (polyMul (replica n A K) (replica n B K))
        (polyMul (polyNeg (difference n (A++B) f)) (difference n (A++B) g))) := by
    dsimp only [replica, mixedEnergy]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul,
      reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.mul (HaarCarrierEqv.mul (.refl _ _) hKswap)
      (HaarCarrierEqv.mul hdf hdg)
  refine (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.mul (.var 4) (.var 5)))
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 5)))
      (.mul (.mul (.var 2) (.var 3)) (.mul (.neg (.var 4)) (.var 5))))
    (by decide)
    (fun | 0 => K | 1 => replica n (A++B) K | 2 => replica n A K
         | 3 => replica n B K | 4 => difference n (A++B) f
         | _ => difference n (A++B) g))).trans ?_
  exact HaarCarrierEqv.add (.refl _ _) hs.symm

/-- The selected-coordinate determinant represents four times the original
conditional covariance numerator under every supported exterior insertion.
The four is written as two doublings to keep the polynomial representation
literal. This is NOT a covariance of separately averaged exterior laws. -/
theorem four_copy_identity (n : Nat) (A B : List Nat)
    (hdisj : ∀ i, i ∈ A → i ∉ B) (K f g r : RatPoly)
    (hK : SupportedQuaternionBlocks n K)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hr : SupportedQuaternionBlocks n r)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g)
    (hrAB : ∀ i, i ∈ A++B → QuaternionBlockIndependent i r)
    (hnodup : (A++B).Nodup) (hids : ∀ i, i ∈ A++B → i < n) :
    quaternionHaar (n+n) (polyMul r (fourEnergy n A B K f g)) ≈
      quaternionHaar n (polyMul r
        (polyAdd
          (polyAdd (covarianceNumerator (A++B) K f g) (covarianceNumerator (A++B) K f g))
          (polyAdd (covarianceNumerator (A++B) K f g) (covarianceNumerator (A++B) K f g)))) := by
  have hm := mixed_identity n (A++B) K f g r hK hf hg hr hrAB hnodup hids
  have hrfix := reindex_fixed_of_selected_independent n A r hr
    (fun i hi => hrAB i (List.mem_append_left B hi))
  have hswap : quaternionHaar (n+n)
      (polyMul r (replica n A (mixedEnergy n (A++B) K f g))) ≈
      quaternionHaar (n+n) (polyMul r (mixedEnergy n (A++B) K f g)) :=
    Q'.eqv_trans _ _ _
      (reindex_pair (swap n A) r _ (support_double hr) (mixed_supported n _ K f g hK hf hg))
      (haar_of_carrier (HaarCarrierEqv.mul hrfix (.refl _ _)))
  exact Q'.eqv_trans _ _ _
    ((fourEnergy_as_swap_sum n A B hdisj K f g hK hf hg hfB hgA) r)
    (pair_add_congr r hm (Q'.eqv_trans _ _ _ hswap hm))

#print axioms joint_replica_of_right_independent
#print axioms joint_replica_of_left_independent
#print axioms crossDeterminant_zero_of_left_independent
#print axioms fourEnergy_as_swap_sum
#print axioms four_copy_identity

end YMGap.Continuum.SU2QuaternionFourCopyCovariance
