/-
# Local-support original norm bounded by same-background Haar variance

For an original-law centered polynomial with literal finite link support,
subtract its free Haar mean, bound only the touching heat factors, and apply
the exact product-Haar Efron--Stein inequality. The detached original mass
remains explicit. This is a finite local-support comparison, not a
volume-uniform gap or a continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabHaarVarianceComparison
import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabLocalSupportVariance

namespace YMGap.Continuum.BF4ExactSlabLocalSupportHaarVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
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

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "U" => (Subtype.mk polyOne (supported_one blocks))

/-- The original centered norm is bounded by the same detached-background
product-Haar variance, with only the finite collar charged to the ceiling. -/
theorem centered_norm_le_local_haar_variance (size : Nat) (S : List Z4Link)
    (hsize : S.length ≤ size) (p : (F).V)
    (hcenter : (F).B p U ≈ 0) (hlocal : LinkLocal extent S p.val) :
    (F).B p p ≤
      (supportCap w size * quaternionHaar blocks (background w K extent S)) *
        quaternionHaar blocks
          (polyMul
            (polyAdd p.val (polyNeg (cap (quaternionHaar blocks p.val))))
            (polyAdd p.val (polyNeg (cap (quaternionHaar blocks p.val))))) := by
  let a := quaternionHaar blocks p.val
  let q := (F).smul a U
  let z := (F).sub p q
  have hq : (F).B p q ≈ 0 := Q'.eqv_trans _ _ _ ((F).B_smul_right a p U)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcenter) (Q'.mul_zero_eqv a))
  have hlo := norm_le_sub_orthogonal F p q hq
  have hz : RatPolyCoeffEqv z.val (polyAdd p.val (polyNeg (cap a))) :=
    (RatPolyCoeffEqv.refl p.val).add (smul_neg (cap a))
  have hlz : LinkLocal extent S z.val := by
    change BlockLocal blocks (fun block => correctedSlabLinkAt extent block ∈ S)
      (polyAdd p.val (polySmul (-1) (polySmul a polyOne)))
    exact hlocal.add (((BlockLocal.one blocks
      (fun block => correctedSlabLinkAt extent block ∈ S)).smul a).smul (-1))
  have hsquare :
      quaternionHaar blocks (polyMul z.val z.val) ≈
        quaternionHaar blocks
          (polyMul (polyAdd p.val (polyNeg (cap a)))
            (polyAdd p.val (polyNeg (cap a)))) :=
    haar_of_coeff (hz.mul hz)
  have hcollar := support_collar_bounds hw0 hw1 extent S size hsize
  have hvarNonneg : (0 : Q') ≤ quaternionHaar blocks (polyMul z.val z.val) :=
    (Certificate.square z.val z.property).haar_nonnegative
  have hbgNonneg : (0 : Q') ≤ quaternionHaar blocks (background w K extent S) :=
    (background_certificate hw0 hw1 K extent hK S).haar_nonnegative
  have hlocal := (local_squared_norm_bounds hw0 hw1 K extent hK S hlz z.property).2
  have hceiling : (F).B z z ≤
      (supportCap w size) *
        (quaternionHaar blocks (polyMul z.val z.val) *
          quaternionHaar blocks (background w K extent S)) := by
    change quaternionHaar blocks
        (polyMul (polyMul z.val z.val)
          (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))) ≤ _
    exact Q'.le_trans' _ _ _ hlocal
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hcollar.2
        (Q'.mul_nonneg _ _ hvarNonneg hbgNonneg))
  have hfactor :
      supportCap w size *
          (quaternionHaar blocks (polyMul z.val z.val) *
            quaternionHaar blocks (background w K extent S)) ≈
        (supportCap w size * quaternionHaar blocks (background w K extent S)) *
          quaternionHaar blocks (polyMul z.val z.val) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => supportCap w size
           | 1 => quaternionHaar blocks (polyMul z.val z.val)
           | _ => quaternionHaar blocks (background w K extent S))
  have hfinal : (F).B z z ≤
      (supportCap w size * quaternionHaar blocks (background w K extent S)) *
        quaternionHaar blocks (polyMul
          (polyAdd p.val (polyNeg (cap a)))
          (polyAdd p.val (polyNeg (cap a)))) := by
    exact Q'.le_trans' _ _ _ hceiling
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor
        (Q'.mul_eqv_congr_left _ _ _ hsquare)))
  exact Q'.le_trans' _ _ _ hlo hfinal

/-- Product-Haar Efron--Stein turns the local background comparison into a
finite local-support upper bound by the sum of in-place coordinate
fluctuations. The detached original mass remains as an explicit factor. -/
theorem centered_norm_le_local_free_energy (size : Nat) (S : List Z4Link)
    (hsize : S.length ≤ size) (p : (F).V)
    (hcenter : (F).B p U ≈ 0) (hlocal : LinkLocal extent S p.val) :
    (F).B p p ≤
      (supportCap w size * quaternionHaar blocks (background w K extent S)) *
        fluctuationEnergy blocks p.val := by
  have hvar := centered_norm_le_local_haar_variance hw0 hw1 K extent hK
    size S hsize p hcenter hlocal
  have hcoef : (0 : Q') ≤
      supportCap w size * quaternionHaar blocks (background w K extent S) :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (supportCap_positive hw0 hw1 size))
      ((background_certificate hw0 hw1 K extent hK S).haar_nonnegative)
  exact Q'.le_trans' _ _ _ hvar
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (haar_efron_stein blocks p.val p.property) hcoef)

/-! ## Kernel axiom gate -/

#print axioms centered_norm_le_local_haar_variance
#print axioms centered_norm_le_local_free_energy

end YMGap.Continuum.BF4ExactSlabLocalSupportHaarVariance
