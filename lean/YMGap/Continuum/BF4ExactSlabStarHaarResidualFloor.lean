/-
# A finite-volume Haar floor for the original conditional residual

Every factor of the original face action is retained.  The resulting floor
counts all faces, so it is not a volume-uniform coercivity estimate.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialDirichletComparison
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate

namespace YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarFreeCentering
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length
private def haarData (extent : Nat) : GNSData :=
  weightedGNSData (blocks extent) polyOne (.one (blocks extent))
private def rat (q : Q') : CReal.RC := Quotient.mk CReal.crealSetoid (CReal.ofQ' q)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "H" => haarData extent
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "A" => freeAverage hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK

private theorem haar_pair (a b : (H).V) :
    (H).B a b ≈ quaternionHaar (blocks extent) (polyMul a.val b.val) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one _)

/-- The restored head probe pairs with the literal unweighted free average. -/
theorem probe_haar_pair (r : (G).V) (p : (F).V) :
    (H).B (J r) p ≈
      quaternionHaar (blocks extent-1) (polyMul r.val (A p).val) :=
  Q'.eqv_trans _ _ _ (haar_pair extent (J r) p)
    (headProbe_pair (Nat.lt_of_le_of_lt (Nat.zero_le _)
      (List.idxOf_lt_length_of_mem i.property))
      (linkHeadSwap extent i.val i.property) r.val p.val r.property p.property)

/-- Both lifted probes have their ordinary Haar product on the exterior. -/
theorem probe_probe_haar_pair (a r : (G).V) :
    (H).B (J a) (J r) ≈
      quaternionHaar (blocks extent-1) (polyMul a.val r.val) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _)
    (List.idxOf_lt_length_of_mem i.property)
  have hp := headProbe_haar hb (linkHeadSwap extent i.val i.property)
    (polyMul a.val r.val) (supported_polyMul a.property r.property)
  rw [headProbe_mul] at hp
  exact Q'.eqv_trans _ _ _ (haar_pair extent (J a) (J r)) hp

/-- The computed selected-link fluctuation is ordinary-Haar orthogonal to
every exterior probe, with no positivity or heat estimate used. -/
theorem freeResidual_haar_orthogonal (p : (F).V) (r : (G).V) :
    (H).B (freeResidual hw0 hw1 K extent hK i.val i.property p) (J r) ≈ 0 := by
  have hleft : (H).B p (J r) ≈
      quaternionHaar (blocks extent-1) (polyMul r.val (A p).val) :=
    Q'.eqv_trans _ _ _ ((H).B_symm p (J r))
      (probe_haar_pair hw0 hw1 K extent hK i r p)
  have hright : (H).B (J (A p)) (J r) ≈
      quaternionHaar (blocks extent-1) (polyMul r.val (A p).val) :=
    Q'.eqv_trans _ _ _ (probe_probe_haar_pair hw0 hw1 K extent hK i (A p) r)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
  have hsame : (H).B p (J r) ≈ (H).B (J (A p)) (J r) :=
    Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)
  change (H).B ((H).sub p (J (A p))) (J r) ≈ 0
  exact Q'.eqv_trans _ _ _ ((H).B_add_left p ((H).neg (J (A p))) (J r))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hsame ((H).B_neg_left (J (A p)) (J r)))
      (OSReconstructionProgress.q_add_neg_self ((H).B (J (A p)) (J r))))

/-- A free-Haar-orthogonal vector cannot have its Haar square reduced by
subtracting an exterior probe. -/
private theorem orthogonal_sub_lower (f : (H).V) (r : (G).V)
    (horth : (H).B f (J r) ≈ 0) :
    (H).B f f ≤ (H).B ((H).sub f (J r)) ((H).sub f (J r)) := by
  have hz : -((H).B f (J r)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ horth)
      (by decide : Q'.eqv (-(0 : Q')) 0)
  have he : (H).B ((H).sub f (J r)) ((H).sub f (J r)) ≈
      (H).B f f + (H).B (J r) (J r) :=
    Q'.eqv_trans _ _ _ ((H).B_sub_diag_expand f (J r))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
          (Q'.add_eqv_congr' hz (Q'.eqv_refl _)))
        (Q'.eqv_of_eq (by rw [Q'.add_zero', Q'.zero_add'])))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ ((H).self_nonneg (J r))) (Q'.ge_of_eqv he)

/-- The literal free average is the least ordinary-Haar exterior
approximation. The statement is on the original supported carrier. -/
theorem freeResidual_haar_minimal (p : (F).V) (r : (G).V) :
    (H).B (freeResidual hw0 hw1 K extent hK i.val i.property p)
      (freeResidual hw0 hw1 K extent hK i.val i.property p) ≤
      (H).distSqQ p (J r) := by
  let a := A p
  let f := freeResidual hw0 hw1 K extent hK i.val i.property p
  let d := (G).sub r a
  have hj : (H).veq (J d) ((H).sub (J r) (J a)) :=
    probeMap_sub hw0 hw1 K extent hK i.val i.property r a
  have hfirst : (H).veq ((H).sub f (J d))
      ((H).sub f ((H).sub (J r) (J a))) :=
    (H).add_congr ((H).veq_refl f) ((H).neg_congr hj)
  have hsecond : (H).veq ((H).sub f ((H).sub (J r) (J a)))
      ((H).sub p (J r)) := by
    change (H).veq ((H).sub ((H).sub p (J a)) ((H).sub (J r) (J a)))
      ((H).sub p (J r))
    have hneg : (H).veq ((H).neg ((H).sub (J r) (J a)))
        ((H).add ((H).neg (J r)) (J a)) :=
      (H).veq_trans ((H).neg_add_distrib (J r) ((H).neg (J a)))
        ((H).add_congr ((H).veq_refl _) ((H).neg_neg (J a)))
    exact (H).veq_trans
      ((H).add_congr ((H).veq_refl _) hneg)
      ((H).veq_trans
        ((H).add_congr ((H).veq_refl _) ((H).add_comm ((H).neg (J r)) (J a)))
        ((H).sub_add_sub p (J a) (J r)))
  exact Q'.le_trans' _ _ _
    (orthogonal_sub_lower hw0 hw1 K extent hK i f d
      (freeResidual_haar_orthogonal hw0 hw1 K extent hK i p d))
    (Q'.le_of_eqv ((H).B_diag_congr ((H).veq_trans hfirst hsecond)))

/-- The swap/head average is the in-place selected-block Haar projection
after the repository's explicit zero-padding transport. -/
theorem freeResidual_fluctuation_padded (p : (F).V) :
    PaddedPolynomialCoeffEqv (blocks extent)
      (freeResidual hw0 hw1 K extent hK i.val i.property p).val
      (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val) := by
  let block := (boundaryCompleteSlabLinks extent).idxOf i.val
  have hi : block < blocks extent := List.idxOf_lt_length_of_mem i.property
  have hp : PaddedPolynomialCoeffEqv (blocks extent) (J (A p)).val
      (project block p.val) :=
    PaddedPolynomialCoeffEqv.of_prefix
      (restored_prefix (blocks extent) block hi p.val)
  change PaddedPolynomialCoeffEqv (blocks extent)
    (polyAdd p.val (polySmul (-1) (J (A p)).val))
    (polyAdd p.val (polyNeg (project block p.val)))
  exact ((PaddedPolynomialCoeffEqv.refl _ p.val).add (hp.smul (-1))).trans
    ((PaddedPolynomialCoeffEqv.refl _ p.val).add
      (PaddedPolynomialCoeffEqv.of_coeff (smul_neg (project block p.val))))

/-- The ordinary Haar energy of the computed residual is exactly the
ordinary Haar energy of the selected coordinate fluctuation. -/
theorem freeResidual_fluctuation_square (p : (F).V) :
    quaternionHaar (blocks extent)
      (polyMul (freeResidual hw0 hw1 K extent hK i.val i.property p).val
        (freeResidual hw0 hw1 K extent hK i.val i.property p).val) ≈
      quaternionHaar (blocks extent)
        (polyMul (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val)
          (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val)) := by
  let f := freeResidual hw0 hw1 K extent hK i.val i.property p
  let block := (boundaryCompleteSlabLinks extent).idxOf i.val
  have he := freeResidual_fluctuation_padded hw0 hw1 K extent hK i p
  exact (he.mul he).haar
    (supported_polyMul f.property f.property)
    (supported_polyMul (fluctuation_supported block p.property)
      (fluctuation_supported block p.property))

/-- Every original face contributes its actual pointwise heat floor. -/
theorem full_square_haar_floor (p : (F).V) :
    (headFloor w)^(slabPhysicalFaceEdges extent).length *
      quaternionHaar (blocks extent) (polyMul p.val p.val) ≤ (F).B p p := by
  have h := headProduct_weighted_floor hw0 hw1 K extent hK
    (Certificate.square p.val p.property) (slabPhysicalFaceEdges extent)
    (fun _ hi => hi)
  exact h

/-- The sharp finite-volume coefficient applies uniformly to every
exterior probe before the conditional inverse is completed. -/
theorem probe_residual_haar_floor (p : (F).V) (r : (G).V) :
    (headFloor w)^(slabPhysicalFaceEdges extent).length *
      quaternionHaar (blocks extent)
        (polyMul (freeResidual hw0 hw1 K extent hK i.val i.property p).val
          (freeResidual hw0 hw1 K extent hK i.val i.property p).val) ≤
      (F).distSqQ p (J r) := by
  let f := freeResidual hw0 hw1 K extent hK i.val i.property p
  let q := (F).sub p (J r)
  have hm := freeResidual_haar_minimal hw0 hw1 K extent hK i p r
  have hscale :
      (headFloor w)^(slabPhysicalFaceEdges extent).length * (H).B f f ≤
        (headFloor w)^(slabPhysicalFaceEdges extent).length *
          (H).distSqQ p (J r) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hm
      (Q'.pow_nonneg (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))
        (slabPhysicalFaceEdges extent).length)
  have hq := full_square_haar_floor hw0 hw1 K extent hK q
  have hq' : (headFloor w)^(slabPhysicalFaceEdges extent).length *
      (H).distSqQ p (J r) ≤ (F).distSqQ p (J r) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_pair extent q q))) hq
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (haar_pair extent f f))))
      hscale)
    hq'

/-- The finite probe floor is now expressed in the in-place Haar
fluctuation consumed by the ordinary-coordinate Efron--Stein inequality. -/
theorem probe_residual_inplace_floor (p : (F).V) (r : (G).V) :
    (headFloor w)^(slabPhysicalFaceEdges extent).length *
      quaternionHaar (blocks extent)
        (polyMul (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val)
          (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val)) ≤
      (F).distSqQ p (J r) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (freeResidual_fluctuation_square hw0 hw1 K extent hK i p))))
    (probe_residual_haar_floor hw0 hw1 K extent hK i p r)

/-- The same Haar floor survives the actual constructed inverse Cauchy row.
The factor counts all original faces; no uniform-in-extent claim is made. -/
theorem conditional_residual_haar_floor (p : (F).V) :
    CReal.RCle
      (rat ((headFloor w)^(slabPhysicalFaceEdges extent).length *
        quaternionHaar (blocks extent)
          (polyMul (freeResidual hw0 hw1 K extent hK i.val i.property p).val
            (freeResidual hw0 hw1 K extent hK i.val i.property p).val)))
      (normSq ((P).residual i (embedV F p))) := by
  change CReal.RCle _ ((F).cinnerCompl
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p)))
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p))))
  rw [conditionalProjection_embed]
  change CReal.leEv (CReal.ofQ' _) ((F).cinnerRep
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p))))
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p)))))
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  exact probe_residual_haar_floor hw0 hw1 K extent hK i p _

/-- Same original completed residual, now with the literal selected-link
in-place Haar fluctuation. Its coefficient remains extent-dependent. -/
theorem conditional_residual_inplace_floor (p : (F).V) :
    CReal.RCle
      (rat ((headFloor w)^(slabPhysicalFaceEdges extent).length *
        quaternionHaar (blocks extent)
          (polyMul (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val)
            (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val))))
      (normSq ((P).residual i (embedV F p))) := by
  change CReal.RCle _ ((F).cinnerCompl
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p)))
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p))))
  rw [conditionalProjection_embed]
  change CReal.leEv (CReal.ofQ' _) ((F).cinnerRep
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p))))
    ((F).subCauchy (constCauchy F p)
      (probeCauchy hw0 hw1 K extent hK i.val i.property
        (inverseCauchy hw0 hw1 K extent hK i.val i.property
          (numeratorMap hw0 hw1 K extent hK i.val i.property p)))))
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  exact probe_residual_inplace_floor hw0 hw1 K extent hK i p _

end YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor

#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.probe_haar_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.probe_probe_haar_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.freeResidual_haar_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.freeResidual_haar_minimal
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.freeResidual_fluctuation_padded
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.freeResidual_fluctuation_square
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.full_square_haar_floor
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.probe_residual_haar_floor
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.probe_residual_inplace_floor
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.conditional_residual_haar_floor
#print axioms YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor.conditional_residual_inplace_floor
