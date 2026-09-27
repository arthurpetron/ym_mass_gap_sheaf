/-
# A retained-exterior lower bound for the ACTUAL conditional residual

For a literal support S, the same detached full-action background is used
for every selected link. On S it is independent of the selected coordinate,
so the free coordinate average minimizes its weighted square error. Outside
S the free fluctuation is exactly zero. Only the touching heat factors are
bounded, uniformly over all exterior probes in the constructed inverse row.

The completed residual belongs to the original full-action conditional
projection. This is not an OS transfer or a scaling-uniform gap statement.
-/

import YMGap.Continuum.SU2QuaternionWeightedHaarProjectionMinimum
import YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
import YMGap.Continuum.BF4ExactSlabLocalSupportVariance
import YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor

namespace YMGap.Continuum.BF4ExactSlabLocalSupportResidualFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionMinimum
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length
private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK
local notation "B" => background w K extent S
local notation "HB" => quaternionHaar (blocks extent) B
local notation "block" => List.idxOf i.val (boundaryCompleteSlabLinks extent)

include hsize

/-- Every exterior polynomial is controlled before completion of the
original inverse. No locality of that exterior polynomial is assumed. -/
theorem probe_residual_local_floor (p : (F).V) (hp : LinkLocal extent S p.val)
    (r : (G).V) :
    (supportFloor w size * HB) * quaternionHaar (blocks extent)
      (polyMul (fluctuation block p.val) (fluctuation block p.val)) ≤
      (F).distSqQ p (J r) := by
  let f := fluctuation block p.val
  let q := (F).sub p (J r)
  by_cases hi : i.val ∈ S
  · have hf := fluctuation_supported block p.property
    have hb := List.idxOf_lt_length_of_mem i.property
    have hmin := weighted_fluctuation_le_difference (blocks extent) block hb B p.val (J r).val
      (background_certificate hw0 hw1 K extent hK S) p.property (J r).property
      (probeMap_independent_selected hw0 hw1 K extent hK i.val i.property r)
      (background_independent_on_support w K extent S i.property hi)
    have hd : RatPolyCoeffEqv q.val (polyAdd p.val (polyNeg (J r).val)) :=
      (RatPolyCoeffEqv.refl p.val).add (smul_neg (J r).val)
    have he : quaternionHaar (blocks extent) (polyMul (polyMul q.val q.val) B) ≈
        quaternionHaar (blocks extent)
          (polyMul (polyMul (polyAdd p.val (polyNeg (J r).val))
            (polyAdd p.val (polyNeg (J r).val))) B) :=
      haar_of_coeff ((hd.mul hd).mul_right B)
    have hfactor := background_factorization w K extent S
      (fluctuation_linkLocal hp block) hf
    have hfree : quaternionHaar (blocks extent) (polyMul f f) * HB ≤
        quaternionHaar (blocks extent) (polyMul (polyMul q.val q.val) B) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hfactor)
        (Q'.le_trans' _ _ _ hmin (Q'.ge_of_eqv he))
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (supportFloor w size) hfree
      (Q'.le_of_lt (supportFloor_positive hw0 hw1 size))
    have hfloor := (weighted_bounds hw0 hw1 K extent hK S
      (Certificate.square q.val q.property)).1
    have hbg := (background_certificate hw0 hw1 K extent hK S).square_insertion_nonnegative
      q.val q.property
    have hc := Q'.mul_le_mul_of_nonneg_right _ _ _
      (support_collar_bounds hw0 hw1 extent S size hsize).1 hbg
    have horder : (supportFloor w size * HB) * quaternionHaar (blocks extent) (polyMul f f) ≈
        supportFloor w size * (quaternionHaar (blocks extent) (polyMul f f) * HB) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1)))
        (by decide) (fun | 0 => supportFloor w size | 1 => HB | _ => quaternionHaar (blocks extent) (polyMul f f))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ hc hfloor))
  · have hz := fluctuation_zero_outside hp i.property hi
    have hs : quaternionHaar (blocks extent) (polyMul f f) ≈ 0 :=
      haar_of_coeff ((hz.mul hz).trans (RatPolyCoeffEqv.mul_zero_left polyZero))
    have he : (supportFloor w size * HB) * quaternionHaar (blocks extent) (polyMul f f) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hs) (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ((F).self_nonneg q)

/-- The original inverse's explicit Cauchy row inherits the same floor.
The retained mass is COMMON to all physical-link residuals. -/
theorem conditional_residual_local_floor (p : (F).V) (hp : LinkLocal extent S p.val) :
    RCle (rat ((supportFloor w size * HB) * quaternionHaar (blocks extent)
      (polyMul (fluctuation block p.val) (fluctuation block p.val))))
      (normSq ((P).residual i (embedV F p))) := by
  change RCle _ ((F).cinnerCompl
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p)))
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p))))
  rw [conditionalProjection_embed]
  change leEv (ofQ' _) ((F).cinnerRep
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p))))
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p)))))
  exact leEv_ofQ'_of_approx_ge
    (fun _ => probe_residual_local_floor hw0 hw1 K extent hK S size hsize i p hp _)

#print axioms probe_residual_local_floor
#print axioms conditional_residual_local_floor

end YMGap.Continuum.BF4ExactSlabLocalSupportResidualFloor
