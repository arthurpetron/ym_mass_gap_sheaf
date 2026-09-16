/-
# Covariance numerator bound for the actual window input functional

The two certificates of a boundary bracket bound the mass of the positive
residual f-lower*u between zero and (upper-lower)*Z(u). The actual signed
window estimate bounds its numerator by the SAME residual mass. Expanding
the covariance numerator before taking absolute values cancels lower*u,
giving 2*c*(upper-lower)*Z(u)^2.

The input f and probe may be signed. Only the reference input u is required
to be certified, and its partition is allowed to vanish. No partition or
residual is inverted. All functionals retain the original K/V action and
right terminal message. This is an unnormalized finite scalar estimate,
not a norm-relative contraction or spectral-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialInputCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (Bracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks inputNumerator inputPartition

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem neg_one_mul (x : Q') : (-1) * x ≈ -x :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x))

private theorem numerator_residual (w : Q') (K width L n : Nat)
    (f u p : RatPoly) (l : Q') :
    inputNumerator w K width L n (polyAdd f (polySmul (-l) u)) p ≈
      inputNumerator w K width L n f p + -(l * inputNumerator w K width L n u p) :=
  Q'.eqv_trans _ _ _ (inputNumerator_add w K width L n f (polySmul (-l) u) p)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (inputNumerator_smul w K width L n (-l) u p)
        (Q'.neg_mul_eqv l _)))

private theorem partition_residual (w : Q') (K width L n : Nat)
    (f u : RatPoly) (l : Q') :
    inputPartition w K width L n (polyAdd f (polySmul (-l) u)) ≈
      inputPartition w K width L n f + -(l * inputPartition w K width L n u) :=
  Q'.eqv_trans _ _ _ (inputPartition_add w K width L n f (polySmul (-l) u))
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (inputPartition_smul w K width L n (-l) u)
        (Q'.neg_mul_eqv l _)))

private theorem residual_cross_bound (A B X Y l c delta : Q')
    (hY : (0 : Q') ≤ Y) (hc : (0 : Q') ≤ c)
    (hr0 : (0 : Q') ≤ X + -(l * Y))
    (hr : X + -(l * Y) ≤ delta * Y)
    (hA : Q'.abs (A + -(l * B)) ≤ c * (X + -(l * Y)))
    (hB : Q'.abs B ≤ c * Y) :
    Q'.abs (A * Y + -(X * B)) ≤ ((c + c) * delta) * (Y * Y) := by
  let r := X + -(l * Y)
  have hsplit : A * Y + -(X * B) ≈
      (A + -(l * B)) * Y + -(B * r) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 1))))
      (.add (.mul (.add (.var 0) (.neg (.mul (.var 4) (.var 1)))) (.var 3))
        (.neg (.mul (.var 1)
          (.add (.var 2) (.neg (.mul (.var 4) (.var 3)))))))
      (by decide) (fun | 0 => A | 1 => B | 2 => X | 3 => Y | _ => l)
  have hfirst : Q'.abs ((A + -(l * B)) * Y) ≤ (c * r) * Y := by
    have h := ExpNeg.abs_mul_le (A + -(l * B)) Y
    rw [ExpNeg.abs_of_nonneg hY] at h
    exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ Y hA hY)
  have hsecond : Q'.abs (-(B * r)) ≤ (c * Y) * r := by
    have h := ExpNeg.abs_mul_le B r
    rw [ExpNeg.abs_of_nonneg hr0] at h
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ r hB hr0))
  have hcollect : (c * r) * Y + (c * Y) * r ≈ ((c + c) * r) * Y :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)))
      (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.var 2))
      (by decide) (fun | 0 => c | 1 => r | _ => Y)
  have hscale : ((c + c) * r) * Y ≤ ((c + c) * (delta * Y)) * Y :=
    Q'.mul_le_mul_of_nonneg_right _ _ Y
      (Q'.mul_le_mul_of_nonneg_left _ _ (c + c) hr (Q'.zero_le_add _ _ hc hc)) hY
  have hregroup : ((c + c) * (delta * Y)) * Y ≈ ((c + c) * delta) * (Y * Y) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.add (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (.var 2))
      (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => c | 1 => delta | _ => Y)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
          (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hregroup)))))

/-- A certified boundary bracket controls the actual unnormalized covariance
numerator. The reference partition may be zero; neither a sign for f nor a
positive lower endpoint is required. The common partition square remains
explicit for the downstream positive-reference normalization. -/
theorem inputCovariance_bracket_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat)
    {f u p : RatPoly} {c : Q'}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hu : SupportedQuaternionBlocks (N width) u)
    (U : Certificate (N width) u) (I : Interval ((L + 1) * (N width)) p c)
    (B : Bracket width f u) :
    Q'.abs (inputNumerator w K width L n f p * inputPartition w K width L n u +
      -(inputPartition w K width L n f * inputNumerator w K width L n u p)) ≤
      ((c + c) * (B.upper + -B.lower)) *
        (inputPartition w K width L n u * inputPartition w K width L n u) := by
  let J := fun h => inputNumerator w K width L n h p
  let Z := inputPartition w K width L n
  have hrSupport := supported_add hf (support_smul hu (-B.lower))
  have hrZ := partition_residual w K width L n f u B.lower
  have hrJ := numerator_residual w K width L n f u p B.lower
  have hr0 : (0 : Q') ≤ Z f + -(B.lower * Z u) :=
    Q'.le_trans' _ _ _
      (inputPartition_nonnegative hw0 hw1 K width hK L n hrSupport B.lowerCertificate)
      (Q'.le_of_eqv hrZ)
  have hupper0 := inputPartition_nonnegative hw0 hw1 K width hK L n
    (supported_add (support_smul hu B.upper) (support_smul hf (-1))) B.upperCertificate
  have hupper : Z f ≤ B.upper * Z u := by
    have he : Z (polyAdd (polySmul B.upper u) (polySmul (-1) f)) ≈
        B.upper * Z u + -(Z f) :=
      Q'.eqv_trans _ _ _ (inputPartition_add w K width L n _ _)
        (Q'.add_eqv_congr' (inputPartition_smul w K width L n B.upper u)
          (Q'.eqv_trans _ _ _ (inputPartition_smul w K width L n (-1) f)
            (neg_one_mul _)))
    exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hupper0 (Q'.le_of_eqv he))
  have hrUpper : Z f + -(B.lower * Z u) ≤ (B.upper + -B.lower) * Z u := by
    have he : B.upper * Z u + -(B.lower * Z u) ≈ (B.upper + -B.lower) * Z u :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (by decide)
        (fun | 0 => B.upper | 1 => B.lower | _ => Z u)
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hupper) (Q'.le_of_eqv he)
  have hResidual : Q'.abs (J f + -(B.lower * J u)) ≤ c * (Z f + -(B.lower * Z u)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hrJ))
      (Q'.le_trans' _ _ _
        (inputNumerator_abs_le hw0 hw1 K width hK L n hrSupport B.lowerCertificate I)
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left c _ _ hrZ)))
  exact residual_cross_bound (J f) (J u) (Z f) (Z u) B.lower c (B.upper + -B.lower)
    (inputPartition_nonnegative hw0 hw1 K width hK L n hu U)
    I.nonnegative hr0 hrUpper hResidual
    (inputNumerator_abs_le hw0 hw1 K width hK L n hu U I)

end YMGap.Continuum.BF4ExactSlabFixedSpatialInputCovariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialInputCovariance.inputCovariance_bracket_bound
