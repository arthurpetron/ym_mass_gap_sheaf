/-
# A singleton replica exchange exposes the cross-exterior star

These are coordinate and Haar identities on the original doubled carrier.
The one-copy weight is split only through an explicit supported carrier
equality.  No conditional-kernel inequality or action estimate is used.
-/

import YMGap.Continuum.SU2QuaternionReplicaPathIncrement
import YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionCrossExteriorPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionDisjointPartialSwap
open YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem support_extend {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p := by
  intro term hterm
  exact Nat.le_trans (hp term hterm) (Nat.mul_le_mul_left 4 (by omega))

/-- A full upper copy with only `j` pulled back equals a lower copy whose
exterior, but not its selected block, was exchanged. -/
theorem upper_single_to_exterior (n j : Nat) (hj : j < n) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n [j]) (liftBoundary n p))
      (reindexQuaternionPolynomial (exteriorSwap n j) p) := by
  let rest := exteriorIds n j
  have hdisj : ∀ i, i ∈ [j] → i ∉ rest := by
    intro i hi hrest
    have hieq := List.mem_singleton.mp hi
    have hne : i ≠ j := ((mem_exteriorIds n j i).mp hrest).2
    exact hne hieq
  have hcover : ∀ i, i < n → i ∈ [j] ++ rest := by
    intro i hi
    by_cases he : i = j
    · exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr he))
    · exact List.mem_append.mpr (Or.inr ((mem_exteriorIds n j i).mpr ⟨hi, he⟩))
  have hfull : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n ([j] ++ rest)) p)
      (liftBoundary n p) :=
    reindex_to_lift n ([j] ++ rest) p hp
      (fun i hi hnot => False.elim (hnot (hcover i hi)))
  have hmove : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n [j])
        (reindexQuaternionPolynomial (swap n ([j] ++ rest)) p))
      (reindexQuaternionPolynomial (swap n [j]) (liftBoundary n p)) :=
    reindex_carrier (swap n [j])
      (reindex_supported (swap n ([j] ++ rest)) p)
      (lift_supported hp n) hfull
  exact hmove.symm.trans (reindex_comp_cancel n [j] rest hdisj p)

/-- A one-copy supported carrier split remains valid under every doubled
insertion, including insertions depending on the other head coordinate. -/
theorem singleton_pair_recode (n j : Nat) (hj : j < n)
    (W A B : RatPoly)
    (hW : SupportedQuaternionBlocks n W)
    (hA : SupportedQuaternionBlocks n A)
    (hB : SupportedQuaternionBlocks n B)
    (hsplit : HaarCarrierEqv n W (polyMul A B))
    (hBind : QuaternionBlockIndependent j B) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n [j])
        (polyMul W (liftBoundary n W)))
      (polyMul (reindexQuaternionPolynomial (swap n [j]) W)
        (polyMul (reindexQuaternionPolynomial (exteriorSwap n j) A)
          (liftBoundary n B))) := by
  have hsplit2 : HaarCarrierEqv (n+n) W (polyMul A B) :=
    carrier_extend n hW (supported_polyMul hA hB) hsplit
  have hother : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (exteriorSwap n j) W)
      (polyMul (reindexQuaternionPolynomial (exteriorSwap n j) A)
        (reindexQuaternionPolynomial (exteriorSwap n j) B)) := by
    have h := reindex_carrier (exteriorSwap n j)
      (support_extend hW) (support_extend (supported_polyMul hA hB)) hsplit2
    rw [reindexQuaternionPolynomial_mul] at h
    exact h
  have hupper : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n [j]) (liftBoundary n W))
      (polyMul (reindexQuaternionPolynomial (exteriorSwap n j) A)
        (liftBoundary n B)) :=
    (upper_single_to_exterior n j hj W hW).trans
      (hother.trans (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
        (normalizer_transport_to_lift n j hj B hB hBind)))
  rw [reindexQuaternionPolynomial_mul]
  exact HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) hupper

/-- The singleton replacement difference changes sign, hence its square
is fixed by the same replica exchange. -/
theorem single_difference_square_fixed (n j : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial (swap n [j])
        (polyMul (singleBlockDifference n j f) (singleBlockDifference n j f)))
      (polyMul (singleBlockDifference n j f)
        (singleBlockDifference n j f)) := by
  let s := swap n [j]
  have htwice : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial s (reindexQuaternionPolynomial s f)) f :=
    reindex_twice_carrier n [j] f (support_extend hf)
  have hreverse : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial s (singleBlockDifference n j f))
      (difference f (reindexQuaternionPolynomial s f)) := by
    change HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial s
        (difference (reindexQuaternionPolynomial s f) f))
      (difference f (reindexQuaternionPolynomial s f))
    simp only [difference, reindexQuaternionPolynomial_add,
      reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add htwice (HaarCarrierEqv.neg (HaarCarrierEqv.refl _ _))
  have hsign : HaarCarrierEqv (n+n)
      (polyMul (difference f (reindexQuaternionPolynomial s f))
        (difference f (reindexQuaternionPolynomial s f)))
      (polyMul (singleBlockDifference n j f)
        (singleBlockDifference n j f)) :=
    RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))
      (.mul (.add (.var 1) (.neg (.var 0)))
        (.add (.var 1) (.neg (.var 0))))
      (by decide) (fun | 0 => f | _ => reindexQuaternionPolynomial s f))
  rw [reindexQuaternionPolynomial_mul]
  exact (HaarCarrierEqv.mul hreverse hreverse).trans hsign

/-- Exact weighted Haar change of variables for the original pair.  The
right-hand factor is the cross-exterior star, not a replacement action. -/
theorem singleton_pair_square_haar (n j : Nat) (hj : j < n)
    (W A B f : RatPoly)
    (hW : SupportedQuaternionBlocks n W)
    (hA : SupportedQuaternionBlocks n A)
    (hB : SupportedQuaternionBlocks n B)
    (hf : SupportedQuaternionBlocks n f)
    (hsplit : HaarCarrierEqv n W (polyMul A B))
    (hBind : QuaternionBlockIndependent j B) :
    quaternionHaar (n+n)
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul (singleBlockDifference n j f)
          (singleBlockDifference n j f))) ≈
    quaternionHaar (n+n)
      (polyMul
        (polyMul (reindexQuaternionPolynomial (swap n [j]) W)
          (polyMul (reindexQuaternionPolynomial (exteriorSwap n j) A)
            (liftBoundary n B)))
        (polyMul (singleBlockDifference n j f)
          (singleBlockDifference n j f))) := by
  let s := swap n [j]
  let d := singleBlockDifference n j f
  have hd : SupportedQuaternionBlocks (n+n) d :=
    difference_supported (reindex_supported s f) (support_extend hf)
  have hpair : SupportedQuaternionBlocks (n+n) (polyMul W (liftBoundary n W)) :=
    supported_polyMul (support_extend hW) (lift_supported hW n)
  have hchange := quaternionHaar_reindex s
    (polyMul (polyMul W (liftBoundary n W)) (polyMul d d))
    (supported_polyMul hpair (supported_polyMul hd hd))
  rw [reindexQuaternionPolynomial_mul] at hchange
  have hrecode : HaarCarrierEqv (n+n)
      (polyMul
        (reindexQuaternionPolynomial s (polyMul W (liftBoundary n W)))
        (reindexQuaternionPolynomial s (polyMul d d)))
      (polyMul
        (polyMul (reindexQuaternionPolynomial s W)
          (polyMul (reindexQuaternionPolynomial (exteriorSwap n j) A)
            (liftBoundary n B)))
        (polyMul d d)) :=
    HaarCarrierEqv.mul
      (singleton_pair_recode n j hj W A B hW hA hB hsplit hBind)
      (single_difference_square_fixed n j f hf)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hchange) (haar_of_carrier hrecode)

#print axioms upper_single_to_exterior
#print axioms singleton_pair_recode
#print axioms single_difference_square_fixed
#print axioms singleton_pair_square_haar

end YMGap.Continuum.SU2QuaternionCrossExteriorPair
