/-
# Exact crossed determinants with the original product heat retained

A partial slice swap preserves EVERY product heat factor. For tests supported
on opposite sides of a complete block partition, the crossed source determinant
therefore gives twice the complete mixed jump pairing. This is exact at finite
cutoff: omitted modes are retained, not declared higher order.

The corresponding determinant of the SAME one-copy weight gives four times
its raw covariance numerator. Their signed difference is a common two-copy
pairing, not a covariance under the source square or a positive new measure.
No variance-relative estimate, changing-family rate or continuum theorem.
-/

import YMGap.Continuum.SU2QuaternionFourCopyCovariance
import YMGap.Continuum.SU2QuaternionPartialSwapHeat
import YMGap.Continuum.SU2QuaternionGlobalVarianceReplica
import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
import YMGap.Continuum.QuaternionHaarPredictionCovariance
import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.SU2QuaternionHeatFourCopy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionFourCopyCovariance
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionPartialSwapHeat
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction (haar_split_pairing)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (full_jump_pairing)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy sourceMoment)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPredictionCovariance
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_double {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem mixed_supported {n : Nat} (ids : List Nat) {a f g : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    SupportedQuaternionBlocks (n+n) (mixedEnergy n ids a f g) :=
  supported_polyMul (supported_polyMul (support_double ha) (reindex_supported _ a))
    (supported_polyMul
      (supported_add (support_double hf) (support_neg (reindex_supported _ f)))
      (supported_add (support_double hg) (support_neg (reindex_supported _ g))))

private theorem replica_full {n : Nat} {ids : List Nat}
    (hc : ids.Perm (List.range n)) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv (n+n) (replica n ids p) (liftBoundary n p) :=
  reindex_to_lift n ids p hp (fun _ hj hnot =>
    False.elim (hnot (hc.mem_iff.mpr (List.mem_range.mpr hj))))

private theorem mixed_full {n : Nat} {ids : List Nat}
    (hc : ids.Perm (List.range n)) {a f g : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    HaarCarrierEqv (n+n) (mixedEnergy n ids a f g)
      (polyMul (polyMul a (liftBoundary n a)) (polyMul (jump n f) (jump n g))) :=
  HaarCarrierEqv.mul (HaarCarrierEqv.mul (.refl _ _) (replica_full hc ha))
    (HaarCarrierEqv.mul
      (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (replica_full hc hf)))
      (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (replica_full hc hg))))

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H n p)))

/-- The complete partition produces the actual full slice jumps. -/
theorem fourEnergy_full_pin {n : Nat} {A B : List Nat}
    (hc : (A++B).Perm (List.range n)) (W : RatPoly) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g) :
    HaarCarrierEqv (n+n) (fourEnergy n A B W f g)
      (polyMul (crossDeterminant n A B W) (polyMul (jump n f) (jump n g))) :=
  HaarCarrierEqv.mul (.refl _ _) (HaarCarrierEqv.mul
    (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (replica_full hc hf)))
    (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (replica_full hc hg))))

/-- Arbitrary supported insertion fixed by the selected swap. The kernel is
used ONCE and never erased. No positivity assumption is needed. -/
theorem weighted_fourEnergy_pin (n : Nat) (A B : List Nat)
    (hd : ∀ i, i ∈ A → i ∉ B) (k a f g : RatPoly)
    (hk : SupportedQuaternionBlocks (n+n) k)
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g)
    (hfix : HaarCarrierEqv (n+n) (replica n A k) k) :
    H (n+n) (polyMul k (fourEnergy n A B a f g)) ≈
      2*H (n+n) (polyMul k (mixedEnergy n (A++B) a f g)) := by
  have hs : H (n+n) (polyMul k (replica n A (mixedEnergy n (A++B) a f g))) ≈
      H (n+n) (polyMul k (mixedEnergy n (A++B) a f g)) :=
    Q'.eqv_trans _ _ _
      (reindex_pair (swap n A) k _ hk (mixed_supported (A++B) ha hf hg))
      (haar_of_carrier (HaarCarrierEqv.mul hfix (.refl _ _)))
  exact Q'.eqv_trans _ _ _
    ((fourEnergy_as_swap_sum n A B hd a f g ha hf hg hfB hgA) k)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hs)
        (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
          (.mul (.const 2) (.var 0)) (by decide) (fun _ =>
            H (n+n) (polyMul k (mixedEnergy n (A++B) a f g))))))

/-- Exact full-heat crossed source identity. All finite-cutoff effects and
spectator heat factors remain in this one pairing. -/
theorem heat_fourEnergy_pin (n : Nat) (w : Q') (K : Nat) (A B : List Nat)
    (hd : ∀ i, i ∈ A → i ∉ B) (hc : (A++B).Perm (List.range n))
    (a f g : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g) :
    H (n+n) (polyMul (productHeat n w K (List.range n)) (fourEnergy n A B a f g)) ≈
      2*H (n+n) (polyMul (productHeat n w K (List.range n))
        (polyMul (polyMul a (liftBoundary n a)) (polyMul (jump n f) (jump n g)))) := by
  have hk := productHeat_supported n w K (List.range n) (fun _ hi => List.mem_range.mp hi)
  have hfix : HaarCarrierEqv (n+n)
      (replica n A (productHeat n w K (List.range n)))
      (productHeat n w K (List.range n)) :=
    carrier_of_supported (reindex_supported _ _) hk (fun r hr =>
      (productHeat_partialSwap_mask n w K A (List.range n)
        (fun _ hi => List.mem_range.mp hi)).haar_insert
        (reindex_supported _ _) hk r hr)
  exact Q'.eqv_trans _ _ _ (weighted_fourEnergy_pin n A B hd _ a f g hk ha hf hg hfB hgA hfix)
    (Q'.mul_eqv_congr_left 2 _ _
      (haar_of_carrier ((mixed_full hc ha hf hg).mul_left _)))

private theorem full_cross_pair (n : Nat) (W f g : RatPoly)
    (hW : SupportedQuaternionBlocks n W) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    H (n+n) (polyMul (polyMul W (liftBoundary n W)) (polyMul (jump n f) (jump n g))) ≈
      2*(H n W*H n (polyMul W (polyMul f g))-H n (polyMul W f)*H n (polyMul W g)) := by
  let e := polyMul W (liftBoundary n W)
  have lower : H (n+n) (polyMul e (polyMul f g)) ≈
      H n (polyMul W (polyMul f g))*H n W :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 1))
      (by decide) (fun | 0 => W | 1 => liftBoundary n W | 2 => f | _ => g)))
      (haar_split_pairing (supported_polyMul hW (supported_polyMul hf hg)) W)
  have upper : H (n+n) (polyMul e (polyMul (liftBoundary n f) (liftBoundary n g))) ≈
      H n W*H n (polyMul W (polyMul f g)) := by
    have hp : RatPolyCoeffEqv (polyMul e (polyMul (liftBoundary n f) (liftBoundary n g)))
        (polyMul W (liftBoundary n (polyMul W (polyMul f g)))) := by
      rw [lift_product, lift_product]
      exact RatPolyCoeffEqv.mul_assoc _ _ _
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hp) (haar_split_pairing hW _)
  have cross (p q : RatPoly) (hp : SupportedQuaternionBlocks n p) :
      H (n+n) (polyMul e (polyMul p (liftBoundary n q))) ≈
        H n (polyMul W p)*H n (polyMul W q) := by
    have hpoly : RatPolyCoeffEqv (polyMul e (polyMul p (liftBoundary n q)))
        (polyMul (polyMul W p) (liftBoundary n (polyMul W q))) := by
      rw [lift_product]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => W | 1 => liftBoundary n W | 2 => p | _ => liftBoundary n q)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (haar_split_pairing (supported_polyMul hW hp) _)
  have hpoly : RatPolyCoeffEqv (polyMul e (polyMul (jump n f) (jump n g)))
      (polyAdd (polyAdd (polyMul e (polyMul f g))
        (polyMul e (polyMul (liftBoundary n f) (liftBoundary n g))))
        (polyAdd (polyNeg (polyMul e (polyMul f (liftBoundary n g))))
          (polyNeg (polyMul e (polyMul g (liftBoundary n f)))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 3) (.neg (.var 4)))))
      (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 3)))
        (.mul (.var 0) (.mul (.var 2) (.var 4))))
        (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 4))))
          (.neg (.mul (.var 0) (.mul (.var 3) (.var 2))))))
      (by decide) (fun | 0 => e | 1 => f | 2 => liftBoundary n f | 3 => g | _ => liftBoundary n g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' lower upper))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ (cross f g hf)))
          (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ (cross g f hg))))))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
            (.add (.neg (.mul (.var 2) (.var 3))) (.neg (.mul (.var 3) (.var 2)))))
          (.mul (.const 2) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))))
          (by decide) (fun | 0 => H n W | 1 => H n (polyMul W (polyMul f g))
                           | 2 => H n (polyMul W f) | _ => H n (polyMul W g)))))

/-- Division-free full-copy covariance on the SAME weight. The exterior is
not averaged into a different law; all blocks are in the complete partition. -/
theorem covariance_fourEnergy_pin (n : Nat) (A B : List Nat)
    (hd : ∀ i, i ∈ A → i ∉ B) (hc : (A++B).Perm (List.range n))
    (W f g : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hfB : ∀ i, i ∈ B → QuaternionBlockIndependent i f)
    (hgA : ∀ i, i ∈ A → QuaternionBlockIndependent i g) :
    H (n+n) (fourEnergy n A B W f g) ≈
      4*(H n W*H n (polyMul W (polyMul f g))-H n (polyMul W f)*H n (polyMul W g)) := by
  have hswap : H (n+n) (replica n A (mixedEnergy n (A++B) W f g)) ≈
      H (n+n) (mixedEnergy n (A++B) W f g) :=
    quaternionHaar_reindex _ _ (mixed_supported (A++B) hW hf hg)
  have hm := Q'.eqv_trans _ _ _ (haar_of_carrier (mixed_full hc hW hf hg))
    (full_cross_pair n W f g hW hf hg)
  have h0 := haar_of_carrier (fourEnergy_as_swap_sum n A B hd W f g hW hf hg hfB hgA)
  exact Q'.eqv_trans _ _ _ h0
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hm (Q'.eqv_trans _ _ _ hswap hm))
        (poly_identity_of_normal_eq
          (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
          (.mul (.const 4) (.var 0)) (by decide) (fun _ =>
            H n W*H n (polyMul W (polyMul f g))-H n (polyMul W f)*H n (polyMul W g)))))

/-- Full jump square equals twice the SAME source energy. The full heat and
both endpoint sources are retained; no source eigenvector is assumed. -/
theorem sourceEnergy_jump_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    H (n+n) (polyMul (productHeat n w K ids)
      (polyMul (polyMul a (liftBoundary n a)) (polyMul (jump n f) (jump n f)))) ≈
      2*sourceEnergy n w K ids a f := by
  have he := full_jump_pairing n w K ids hids ha hf hf
  have hp : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids)
        (polyMul (polyMul a (liftBoundary n a)) (polyMul (jump n f) (jump n f))))
      (polyMul (polyMul (jump n f) (jump n f)) (edgeWeight n w K ids a)) := by
    unfold edgeWeight
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 3) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => productHeat n w K ids | 1 => a
                       | 2 => liftBoundary n a | _ => polyMul (jump n f) (jump n f))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left 2 _ _ (by
      unfold SU2QuaternionWeightedProductDualEnergy.marginalPair sourceEnergy sourceMoment
      exact Q'.add_eqv_congr'
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
          (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
          (by decide) (fun | 0 => a | 1 => productMap n w K ids a | _ => f)))
        (Q'.eqv_refl _))))

private theorem jump_add (n : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (jump n (polyAdd f g)) (polyAdd (jump n f) (jump n g)) := by
  unfold jump
  rw [lift_add]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (by decide) (fun | 0 => f | 1 => g | 2 => liftBoundary n f | _ => liftBoundary n g)

private theorem square_polarization (blocks : Nat) (e x y : RatPoly) :
    H blocks (polyMul e (polyMul (polyAdd x y) (polyAdd x y))) -
      H blocks (polyMul e (polyMul x x)) - H blocks (polyMul e (polyMul y y)) ≈
      2*H blocks (polyMul e (polyMul x y)) := by
  have hp : RatPolyCoeffEqv (polyMul e (polyMul (polyAdd x y) (polyAdd x y)))
      (polyAdd (polyAdd (polyMul e (polyMul x x)) (polyMul e (polyMul y y)))
        (polySmul 2 (polyMul e (polyMul x y)))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2))))
      (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.mul (.var 2) (.var 2))))
        (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 2)))))
      (by decide) (fun | 0 => e | 1 => x | _ => y)).trans
      ((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 _))
  have hh := Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (quaternionHaar_append blocks _ _) (quaternionHaar_polySmul blocks _ _)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hh (Q'.eqv_refl _)) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.add (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
        (.neg (.var 0))) (.neg (.var 1))) (.mul (.const 2) (.var 2))
      (by decide) (fun | 0 => H blocks (polyMul e (polyMul x x))
                       | 1 => H blocks (polyMul e (polyMul y y))
                       | _ => H blocks (polyMul e (polyMul x y))))

/-- Exact polarization of the COMPLETE source energy. The right side is
the original full jump cross, not a truncated Taylor remainder. -/
theorem sourceEnergy_mixed_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {a f g : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    sourceEnergy n w K ids a (polyAdd f g) - sourceEnergy n w K ids a f -
      sourceEnergy n w K ids a g ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyMul (polyMul a (liftBoundary n a)) (polyMul (jump n f) (jump n g)))) := by
  let e := polyMul (productHeat n w K ids) (polyMul a (liftBoundary n a))
  have rearrange (x y : RatPoly) : H (n+n) (polyMul e (polyMul x y)) ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyMul (polyMul a (liftBoundary n a)) (polyMul x y))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)
  have diag (r : RatPoly) (hr : SupportedQuaternionBlocks n r) :
      H (n+n) (polyMul e (polyMul (jump n r) (jump n r))) ≈
        2*sourceEnergy n w K ids a r :=
    Q'.eqv_trans _ _ _ (rearrange _ _) (sourceEnergy_jump_pin n w K ids hids ha hr)
  have hj := haar_of_coeff (blocks := n+n)
    (((jump_add n f g).mul (jump_add n f g)).mul_left e)
  have hh := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (diag _ (supported_add hf hg)).symm
      (Q'.neg_eqv_congr _ _ (diag f hf).symm)) (Q'.neg_eqv_congr _ _ (diag g hg).symm))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hj (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (square_polarization (n+n) e (jump n f) (jump n g))
        (Q'.mul_eqv_congr_left 2 _ _ (rearrange _ _))))
  apply Q'.mul_left_cancel_of_pos (c := (2 : Q')) (by decide)
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.const 2) (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))))
    (.add (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
      (.neg (.mul (.const 2) (.var 2)))) (by decide)
    (fun | 0 => sourceEnergy n w K ids a (polyAdd f g)
         | 1 => sourceEnergy n w K ids a f | _ => sourceEnergy n w K ids a g)) hh

/-- Normalization cleared without replacing either original endpoint mean. -/
theorem covariance_numerator_pin (n : Nat) (W f g : RatPoly)
    (hZ : (0 : Q') < H n W) :
    normalizedCovariance n W f g hZ * (H n W*H n W) ≈
      H n W*H n (polyMul W (polyMul f g))-H n (polyMul W f)*H n (polyMul W g) := by
  let Z := H n W
  let r := Q'.recipPos Z hZ
  let M := H n (polyMul W (polyMul f g))
  let F := H n (polyMul W f)
  let G := H n (polyMul W g)
  have hr : Z*r ≈ 1 := Q'.mul_recipPos_eqv Z hZ
  change (M*r-(F*r)*(G*r))*(Z*Z) ≈ Z*M-F*G
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.add (.mul (.var 1) (.var 4))
      (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 4)))))
      (.mul (.var 0) (.var 0)))
    (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 1)))
      (.neg (.mul (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 4)))
        (.mul (.var 2) (.var 3)))))
    (by decide) (fun | 0 => Z | 1 => M | 2 => F | 3 => G | _ => r))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hr)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 _ _ hr) (Q'.mul_one_eqv 1))))))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.mul (.var 0) (.var 1)))
          (.neg (.mul (.const 1) (.mul (.var 2) (.var 3)))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => Z | 1 => M | 2 => F | _ => G)))

#print axioms weighted_fourEnergy_pin
#print axioms heat_fourEnergy_pin
#print axioms covariance_fourEnergy_pin
#print axioms fourEnergy_full_pin
#print axioms sourceEnergy_jump_pin
#print axioms sourceEnergy_mixed_pin
#print axioms covariance_numerator_pin

end YMGap.Continuum.SU2QuaternionHeatFourCopy
