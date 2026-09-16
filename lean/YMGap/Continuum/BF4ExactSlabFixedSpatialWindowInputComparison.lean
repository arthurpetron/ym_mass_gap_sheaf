/-
# Normalized window comparison from an actual positive boundary bracket

Use the certified residual f-l*g, never divide by its possibly zero mass.
Window positivity bounds its signed numerator by C times its SAME partition.
The upper bracket controls that residual partition. Exact rational ratio
algebra then cancels the reference normalization, leaving 2*C times the
relative bracket width. The action, window and right terminal message stay
fixed throughout; this is not a surrogate probability law or physical OS gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
import YMGap.Continuum.RationalPositiveResidualRatio

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInputComparison

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

private theorem neg_one_mul (x : Q') : (-1)*x ≈ -x :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x))

private theorem numerator_residual (w : Q') (K width L n : Nat) (f g p : RatPoly) (l : Q') :
    inputNumerator w K width L n (polyAdd f (polySmul (-l) g)) p ≈
      inputNumerator w K width L n f p + -(l * inputNumerator w K width L n g p) :=
  Q'.eqv_trans _ _ _ (inputNumerator_add w K width L n f (polySmul (-l) g) p)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (inputNumerator_smul w K width L n (-l) g p) (Q'.neg_mul_eqv l _)))

private theorem partition_residual (w : Q') (K width L n : Nat) (f g : RatPoly) (l : Q') :
    inputPartition w K width L n (polyAdd f (polySmul (-l) g)) ≈
      inputPartition w K width L n f + -(l * inputPartition w K width L n g) :=
  Q'.eqv_trans _ _ _ (inputPartition_add w K width L n f (polySmul (-l) g))
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (inputPartition_smul w K width L n (-l) g) (Q'.neg_mul_eqv l _)))

/-- A relative positive bracket compares normalized expectations for the
same actual observed window. Only the endpoint partitions must be positive;
the residual partition is permitted to vanish. -/
theorem inputRatio_bracket_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat)
    {f g p : RatPoly} {c eta : Q'}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (I : Interval ((L+1)*(N width)) p c)
    (B : Bracket width f g) (hl : (0 : Q') < B.lower) (heta : (0 : Q') ≤ eta)
    (hwidth : B.upper + -B.lower ≤ eta * B.lower)
    (hX : (0 : Q') < inputPartition w K width L n f)
    (hY : (0 : Q') < inputPartition w K width L n g) :
    Q'.abs (inputNumerator w K width L n f p * Q'.recipPos _ hX +
      -(inputNumerator w K width L n g p * Q'.recipPos _ hY)) ≤ (c+c)*eta := by
  let J := fun h => inputNumerator w K width L n h p
  let Z := inputPartition w K width L n
  have hrSupport := supported_add hf (support_smul hg (-B.lower))
  have hrZ := partition_residual w K width L n f g B.lower
  have hrJ := numerator_residual w K width L n f g p B.lower
  have hr0 : (0 : Q') ≤ Z f + -(B.lower * Z g) :=
    Q'.le_trans' _ _ _
      (inputPartition_nonnegative hw0 hw1 K width hK L n hrSupport B.lowerCertificate)
      (Q'.le_of_eqv hrZ)
  have hu0 := inputPartition_nonnegative hw0 hw1 K width hK L n
    (supported_add (support_smul hg B.upper) (support_smul hf (-1))) B.upperCertificate
  have hu : Z f ≤ B.upper * Z g := by
    have he : Z (polyAdd (polySmul B.upper g) (polySmul (-1) f)) ≈ B.upper * Z g + -(Z f) :=
      Q'.eqv_trans _ _ _ (inputPartition_add w K width L n _ _)
        (Q'.add_eqv_congr' (inputPartition_smul w K width L n B.upper g)
          (Q'.eqv_trans _ _ _ (inputPartition_smul w K width L n (-1) f) (neg_one_mul _)))
    exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hu0 (Q'.le_of_eqv he))
  have hrUpper : Z f + -(B.lower * Z g) ≤ eta * (B.lower * Z g) := by
    have he : B.upper * Z g + -(B.lower * Z g) ≈ (B.upper + -B.lower) * Z g :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (by decide)
        (fun | 0 => B.upper | 1 => B.lower | _ => Z g)
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hu)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hwidth (Q'.le_of_lt hY))
          (Q'.le_of_eqv (Q'.mul_assoc_eqv eta B.lower (Z g)))))
  have hResidual : Q'.abs (J f + -(B.lower * J g)) ≤ c * (Z f + -(B.lower * Z g)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hrJ))
      (Q'.le_trans' _ _ _
        (inputNumerator_abs_le hw0 hw1 K width hK L n hrSupport B.lowerCertificate I)
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left c _ _ hrZ)))
  exact RationalPositiveResidualRatio.ratio_bound (J f) (J g) (Z f) (Z g) B.lower c eta
    hX hY hl I.nonnegative heta hr0 hrUpper hResidual
    (inputNumerator_abs_le hw0 hw1 K width hK L n hg G I)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInputComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInputComparison.inputRatio_bracket_bound
