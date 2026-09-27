/-
# Original centered norm versus finite product-Haar variance

The original weighted mean zero condition makes subtracting any constant
increase the original squared norm. Subtract the free Haar mean, then use
the constructed full-action weight ceiling. Product-Haar Efron--Stein
controls the resulting free variance without a number-of-links loss.

The ceiling counts ALL physical faces. It is independent of the late heat
cutoff but depends on nome and volume. This is a comparison input to an
original-action Dirichlet lower bound, not a scaling-uniform gap.
-/

import YMGap.Continuum.BF4ExactSlabStarFullActionProbe
import YMGap.Continuum.SU2QuaternionHaarEfronStein

namespace YMGap.Continuum.BF4ExactSlabHaarVarianceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarEfronStein
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem norm_le_sub_orthogonal (D : GNSData) (p q : D.V)
    (h : D.B p q ≈ 0) : D.B p p ≤ D.B (D.sub p q) (D.sub p q) := by
  have hz : -(D.B p q) ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ h) (by decide : Q'.eqv (-(0 : Q')) 0)
  have he : D.B (D.sub p q) (D.sub p q) ≈ D.B p p + D.B q q :=
    Q'.eqv_trans _ _ _ (D.B_sub_diag_expand p q)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
          (Q'.add_eqv_congr' hz (Q'.eqv_refl _)))
        (Q'.eqv_of_eq (by rw [Q'.add_zero', Q'.zero_add'])))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (D.self_nonneg q)) (Q'.ge_of_eqv he)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

/-- Explicit original full-action ceiling, with its volume cost retained. -/
def volumeCap (w : Q') (extent : Nat) : Q' :=
  (prefixCap w)^(slabPhysicalFaceEdges extent).length

theorem volumeCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (extent : Nat) :
    (0 : Q') ≤ volumeCap w extent :=
  Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "U" => (Subtype.mk polyOne (supported_one blocks))

/-- A centered ORIGINAL polynomial is compared with its free Haar
variance, not with an uncentered norm or a replacement weighted measure. -/
theorem centered_norm_le_haar_variance (p : (F).V)
    (hcenter : (F).B p U ≈ 0) :
    (F).B p p ≤ volumeCap w extent * quaternionHaar blocks
      (polyMul
        (polyAdd p.val (polyNeg (cap (quaternionHaar blocks p.val))))
        (polyAdd p.val (polyNeg (cap (quaternionHaar blocks p.val))))) := by
  let a := quaternionHaar blocks p.val
  let q := (F).smul a U
  let z := (F).sub p q
  have hq : (F).B p q ≈ 0 := Q'.eqv_trans _ _ _ ((F).B_smul_right a p U)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcenter) (Q'.mul_zero_eqv a))
  have hlo := norm_le_sub_orthogonal F p q hq
  have hhi := headProduct_weighted_upper hw0 hw1 K extent
    (Certificate.square z.val z.property) (slabPhysicalFaceEdges extent) (fun _ hi => hi)
  have hz : RatPolyCoeffEqv z.val (polyAdd p.val (polyNeg (cap a))) :=
    (RatPolyCoeffEqv.refl p.val).add (smul_neg (cap a))
  have hs : quaternionHaar blocks (polyMul z.val z.val) ≈
      quaternionHaar blocks (polyMul (polyAdd p.val (polyNeg (cap a)))
        (polyAdd p.val (polyNeg (cap a)))) := haar_of_coeff (hz.mul hz)
  exact Q'.le_trans' _ _ _ hlo (Q'.le_trans' _ _ _ hhi
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_eqv hs)
      (volumeCap_nonnegative hw0 extent)))

/-- The sharp free tensor variance estimate now bounds the original
centered norm. There is no extra factor equal to the number of links. -/
theorem centered_norm_le_free_energy (p : (F).V)
    (hcenter : (F).B p U ≈ 0) :
    (F).B p p ≤ volumeCap w extent * fluctuationEnergy blocks p.val :=
  Q'.le_trans' _ _ _ (centered_norm_le_haar_variance hw0 hw1 K extent hK p hcenter)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (haar_efron_stein blocks p.val p.property)
      (volumeCap_nonnegative hw0 extent))

#print axioms volumeCap
#print axioms volumeCap_nonnegative
#print axioms centered_norm_le_haar_variance
#print axioms centered_norm_le_free_energy

end YMGap.Continuum.BF4ExactSlabHaarVarianceComparison
