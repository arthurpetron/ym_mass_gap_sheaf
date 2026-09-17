/-
# Signed input bounds under the original window partition

Two positive input certificates d*u plus or minus f give the sharp bound
|J(f)| <= c*d*Z(u), even though f itself is signed. Both certificates
are tested against the SAME original right window before their auxiliary
mass terms cancel. No observed mass is inverted and no action is removed.
The consumer is the original-partition high-spin fusion-boundary estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealExp
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
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

private theorem cancel_double {a b : Q'} (h : a+a ≤ b+b) : a ≤ b := by
  have he (x : Q') : (2 : Q')*x ≈ x+x :=
    poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
      (.add (.var 0) (.var 0)) (by decide) (fun _ => x)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (he a))
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (he b)))) (by decide)

private theorem half_difference_bound (a b za zb F B c : Q')
    (ha : a ≤ c*za) (hb : -(c*zb) ≤ b)
    (hF : a + -b ≈ F+F) (hB : c*za+c*zb ≈ B+B) : F ≤ B := by
  have hn : -b ≤ c*zb := Q'.le_trans' _ _ _ (Q'.neg_le_neg hb)
    (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  exact cancel_double (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hF)
    (Q'.le_trans' _ _ _ (Q'.add_le_add ha hn) (Q'.le_of_eqv hB)))

/-- Positive-pair cancellation retains the sharp coefficient d, not 2*d.
Neither f nor its window numerator is assumed nonnegative. -/
theorem inputNumerator_signed_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat)
    {u f p : RatPoly} {d c : Q'}
    (hu : SupportedQuaternionBlocks (N width) u)
    (hf : SupportedQuaternionBlocks (N width) f)
    (P : Certificate (N width) (polyAdd (polySmul d u) f))
    (Q : Certificate (N width) (polyAdd (polySmul d u) (polySmul (-1) f)))
    (I : Interval ((L+1)*(N width)) p c) :
    Q'.abs (inputNumerator w K width L n f p) ≤
      c*d*inputPartition w K width L n u := by
  let plus := polyAdd (polySmul d u) f
  let minus := polyAdd (polySmul d u) (polySmul (-1) f)
  let J := fun v => inputNumerator w K width L n v p
  let Z := inputPartition w K width L n
  have bp := inputNumerator_bounds hw0 hw1 K width hK L n
    (supported_add (support_smul hu d) hf) P I
  have bm := inputNumerator_bounds hw0 hw1 K width hK L n
    (supported_add (support_smul hu d) (support_smul hf (-1))) Q I
  have jp : J plus ≈ d*J u+J f :=
    Q'.eqv_trans _ _ _ (inputNumerator_add w K width L n _ _ p)
      (Q'.add_eqv_congr' (inputNumerator_smul w K width L n d u p) (Q'.eqv_refl _))
  have jm : J minus ≈ d*J u+(-1)*J f :=
    Q'.eqv_trans _ _ _ (inputNumerator_add w K width L n _ _ p)
      (Q'.add_eqv_congr' (inputNumerator_smul w K width L n d u p)
        (inputNumerator_smul w K width L n (-1) f p))
  have zp : Z plus ≈ d*Z u+Z f :=
    Q'.eqv_trans _ _ _ (inputPartition_add w K width L n _ _)
      (Q'.add_eqv_congr' (inputPartition_smul w K width L n d u) (Q'.eqv_refl _))
  have zm : Z minus ≈ d*Z u+(-1)*Z f :=
    Q'.eqv_trans _ _ _ (inputPartition_add w K width L n _ _)
      (Q'.add_eqv_congr' (inputPartition_smul w K width L n d u)
        (inputPartition_smul w K width L n (-1) f))
  have diff : J plus + -(J minus) ≈ J f+J f :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' jp (Q'.neg_eqv_congr _ _ jm))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 0) (.mul (.const (-1)) (.var 1)))))
        (.add (.var 1) (.var 1)) (by decide) (fun | 0 => d*J u | _ => J f))
  have back : J minus + -(J plus) ≈ -(J f)+-(J f) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' jm (Q'.neg_eqv_congr _ _ jp))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.neg (.add (.var 0) (.var 1))))
        (.add (.neg (.var 1)) (.neg (.var 1))) (by decide) (fun | 0 => d*J u | _ => J f))
  have mass : c*Z plus+c*Z minus ≈ c*d*Z u+c*d*Z u :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c _ _ zp) (Q'.mul_eqv_congr_left c _ _ zm))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
          (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.const (-1)) (.var 3)))))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (by decide) (fun | 0 => c | 1 => d | 2 => Z u | _ => Z f))
  have upper := half_difference_bound _ _ _ _ _ _ _ bp.2 bm.1 diff mass
  have lower := half_difference_bound _ _ _ _ _ _ _ bm.2 bp.1 back
    (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) mass)
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg lower) (Q'.le_of_eqv (Q'.neg_neg_eqv _))) upper

/-- The same signed bound for the unobserved right window. -/
theorem inputPartition_signed_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat)
    {u f : RatPoly} {d : Q'}
    (hu : SupportedQuaternionBlocks (N width) u)
    (hf : SupportedQuaternionBlocks (N width) f)
    (P : Certificate (N width) (polyAdd (polySmul d u) f))
    (Q : Certificate (N width) (polyAdd (polySmul d u) (polySmul (-1) f))) :
    Q'.abs (inputPartition w K width L n f) ≤ d*inputPartition w K width L n u := by
  have h := inputNumerator_signed_bound hw0 hw1 K width hK L n hu hf P Q
    (Interval.one ((L+1)*(N width)))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (inputNumerator_one w K width L n f)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv d))))

private theorem floor_determinant_bound (A B Y Z Z0 c d h : Q')
    (hZ : (0 : Q') ≤ Z) (hZ0 : (0 : Q') ≤ Z0)
    (hc : (0 : Q') ≤ c) (hd : (0 : Q') ≤ d) (hh : (0 : Q') ≤ h)
    (hA : Q'.abs A ≤ c*d*Z0) (hB : Q'.abs B ≤ d*Z0)
    (hY : Q'.abs Y ≤ c*Z) (hfloor : h*Z0 ≤ Z) :
    h*Q'.abs (A*Z + -(B*Y)) ≤ (2*c*d)*(Z*Z) := by
  have hfirst : Q'.abs (A*Z) ≤ (c*d*Z0)*Z := by
    have ht := ExpNeg.abs_mul_le A Z
    rw [ExpNeg.abs_of_nonneg hZ] at ht
    exact Q'.le_trans' _ _ _ ht (Q'.mul_le_mul_of_nonneg_right _ _ Z hA hZ)
  have hsecond : Q'.abs (-(B*Y)) ≤ (d*Z0)*(c*Z) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le B Y)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hB (Q'.abs_nonneg Y))
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hY (Q'.mul_nonneg _ _ hd hZ0))))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ h
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add hfirst hsecond)) hh
  have he : h*((c*d*Z0)*Z+(d*Z0)*(c*Z)) ≈ (2*c*d*Z)*(h*Z0) :=
    poly_identity_of_normal_eq
      (.mul (.var 4) (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))))
      (.mul (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))
        (.mul (.var 4) (.var 2))) (by decide)
      (fun | 0 => c | 1 => d | 2 => Z0 | 3 => Z | _ => h)
  have hn : (0 : Q') ≤ 2*c*d*Z := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hc) hd) hZ
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor hn)
        (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- A one-source floor removes the auxiliary mass from a signed determinant.
The reference is the original u; the final denominator is Z(u)^2, not Z(v)^2.
The next module constructs every certificate from the physical face action. -/
theorem inputCovariance_relative_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat)
    {u v f p : RatPoly} {d c h : Q'}
    (hu : SupportedQuaternionBlocks (N width) u)
    (hv : SupportedQuaternionBlocks (N width) v)
    (hf : SupportedQuaternionBlocks (N width) f)
    (U : Certificate (N width) u) (V : Certificate (N width) v)
    (P : Certificate (N width) (polyAdd (polySmul d v) f))
    (Q : Certificate (N width) (polyAdd (polySmul d v) (polySmul (-1) f)))
    (F : Certificate (N width) (polyAdd u (polySmul (-h) v)))
    (I : Interval ((L+1)*(N width)) p c)
    (hd : (0 : Q') ≤ d) (hh : (0 : Q') ≤ h) :
    h*Q'.abs (inputNumerator w K width L n f p * inputPartition w K width L n u +
      -(inputPartition w K width L n f * inputNumerator w K width L n u p)) ≤
      (2*c*d)*(inputPartition w K width L n u * inputPartition w K width L n u) := by
  let Z := inputPartition w K width L n
  have hF := inputPartition_nonnegative hw0 hw1 K width hK L n
    (supported_add hu (support_smul hv (-h))) F
  have he : Z (polyAdd u (polySmul (-h) v)) ≈ Z u + -(h*Z v) :=
    Q'.eqv_trans _ _ _ (inputPartition_add w K width L n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (inputPartition_smul w K width L n (-h) v)
          (Q'.neg_mul_eqv _ _)))
  exact floor_determinant_bound _ _ _ _ _ _ _ _
    (inputPartition_nonnegative hw0 hw1 K width hK L n hu U)
    (inputPartition_nonnegative hw0 hw1 K width hK L n hv V)
    I.nonnegative hd hh
    (inputNumerator_signed_bound hw0 hw1 K width hK L n hv hf P Q I)
    (inputPartition_signed_bound hw0 hw1 K width hK L n hv hf P Q)
    (inputNumerator_abs_le hw0 hw1 K width hK L n hu U I)
    (Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hF (Q'.le_of_eqv he)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound.inputNumerator_signed_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound.inputPartition_signed_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound.inputCovariance_relative_bound
