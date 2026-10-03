/-
# Exact tested fundamental channel of the original six-face cube action

At cutoff one, each original face factor is 1+alpha*chi_1, with
alpha=coeffW(w,1). Literal subset expansion, computed odd-edge annihilation,
and the two original surviving Haar contractions give alpha/2+alpha^5/8.
The actual twelve-link cube action and original slice Haar carrier remain
unchanged. No transfer-matrix range, gain sign, cutoff guard, completed
response or scaling estimate is inferred.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_polySmul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeFaces cubeWeight bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity
  (singletonSelection complementSelection selectedBentInsertion selectedFaceProduct badSelection_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
  (singleton_selection_moment complement_selection_moment)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.FinitePolynomialSubsetExpansion (selections haar_expansion)
open YMGap.Continuum.FiniteSelectionMobius (sum_filter_zero)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarHeatCertificate
  (heatPrefix heatRemainder heatPrefix_split)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow qpow_succ)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks plaquette characterPolynomial
  bentObservable firstFaceTrace cubeWeight selectedBentInsertion selectedFaceProduct

private theorem fundamental_prefix (w : Q') (p : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w 1 p)
      (polyAdd polyOne (polySmul (coeffW w 1) (characterPolynomial p 1))) := by
  have hr : RatPolyCoeffEqv (heatRemainder w 1 p)
      (polySmul (coeffW w 1) (characterPolynomial p 1)) := by
    unfold heatRemainder
    change RatPolyCoeffEqv
      (polyAdd (polySmul (coeffW w 1) (characterPolynomial p 1)) polyZero)
      (polySmul (coeffW w 1) (characterPolynomial p 1))
    exact RatPolyCoeffEqv.add_zero _
  exact (heatPrefix_split w 1 p).trans ((RatPolyCoeffEqv.refl polyOne).add hr)

/-- Scalar extraction is structural; no actual face polynomial is expanded. -/
private theorem weighted_product (alpha : Q') (factor : Z4Plaq → RatPoly) :
    ∀ fs : List Z4Plaq,
    RatPolyCoeffEqv
      (polynomialProduct (fun face => polySmul alpha (factor face)) fs)
      (polySmul (qpow alpha fs.length) (polynomialProduct factor fs))
  | [] => (RatPolyCoeffEqv.one_smul polyOne).symm
  | face :: fs => by
      have hs := weighted_product alpha factor fs
      have h := (hs.mul_left (polySmul alpha (factor face))).trans
        ((RatPolyCoeffEqv.polyMul_smul_left alpha (factor face) _).trans
          (((RatPolyCoeffEqv.polyMul_smul_right (qpow alpha fs.length)
            (factor face) (polynomialProduct factor fs)).smul alpha).trans
            (RatPolyCoeffEqv.smul_assoc alpha (qpow alpha fs.length) _)))
      exact h.trans (by
        simpa only [List.length_cons, qpow_succ] using
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.mul_comm_eqv alpha (qpow alpha fs.length))
            (polynomialProduct factor (face :: fs))))

private def subsetTerm (w : Q') (fs : List Z4Plaq) : Q' :=
  quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable)
    (polynomialProduct (fun face => polySmul (coeffW w 1)
      (characterPolynomial (plaquette 2 face).scalar 1)) fs))

private theorem subsetTerm_weight (w : Q') (fs : List Z4Plaq) :
    subsetTerm w fs ≈ qpow (coeffW w 1) fs.length *
      quaternionHaar N (selectedBentInsertion fs) := by
  have hs := weighted_product (coeffW w 1)
    (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs
  unfold subsetTerm
  have hc := (hs.mul_left (polyMul firstFaceTrace bentObservable)).trans
    (RatPolyCoeffEqv.polyMul_smul_right (qpow (coeffW w 1) fs.length)
      (polyMul firstFaceTrace bentObservable)
      (polynomialProduct (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs))
  have hh := Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (quaternionHaar_polySmul N (qpow (coeffW w 1) fs.length) _)
  simpa only [selectedBentInsertion, selectedFaceProduct] using hh

attribute [local irreducible] subsetTerm

private def keepSurvivor (fs : List Z4Plaq) : Bool :=
  decide (fs = singletonSelection ∨ fs = complementSelection)

/-- This check is solely the order of two rows in the literal six-face selection list. -/
theorem survivor_filter :
    (selections cubeFaces).filter keepSurvivor =
      [singletonSelection, complementSelection] := by
  decide

/-- The complete actual action channel, at every rational nome. -/
theorem tested_bent_action_channel (w : Q') :
    quaternionHaar N
      (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w 1)) ≈
      (coeffW w 1) * HalfPow.half +
        qpow (coeffW w 1) 5 * (Q'.mkPos 1 8 (by decide)) := by
  have hexp := haar_expansion N
    (fun face => heatPrefix w 1 (plaquette 2 face).scalar)
    (fun face => polySmul (coeffW w 1)
      (characterPolynomial (plaquette 2 face).scalar 1))
    (fun face => fundamental_prefix w (plaquette 2 face).scalar)
    (polyMul firstFaceTrace bentObservable) cubeFaces
  have hsum :
      quaternionHaar N
        (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w 1)) ≈
      listQSum (subsetTerm w) (selections cubeFaces) := by
    unfold cubeWeight subsetTerm
    exact hexp
  have hfilter := sum_filter_zero (subsetTerm w) keepSurvivor (selections cubeFaces)
    (fun fs hfs hk => by
      have hn : ¬(fs = singletonSelection ∨ fs = complementSelection) :=
        of_decide_eq_false hk
      have hz := badSelection_haar_zero fs hfs
        (fun hs => hn (Or.inl hs)) (fun hc => hn (Or.inr hc))
      exact Q'.eqv_trans _ _ _ (subsetTerm_weight w fs)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz)
          (Q'.mul_zero_eqv _)))
  rw [survivor_filter] at hfilter
  have hsingle : subsetTerm w singletonSelection ≈ (coeffW w 1) * HalfPow.half := by
    have ha : qpow (coeffW w 1) 1 ≈ coeffW w 1 := Q'.one_mul_eqv _
    exact Q'.eqv_trans _ _ _ (subsetTerm_weight w singletonSelection)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
        (Q'.mul_eqv_congr_left _ _ _ singleton_selection_moment))
  have hcomplement : subsetTerm w complementSelection ≈
      qpow (coeffW w 1) 5 * (Q'.mkPos 1 8 (by decide)) :=
    Q'.eqv_trans _ _ _ (subsetTerm_weight w complementSelection)
      (Q'.mul_eqv_congr_left _ _ _ complement_selection_moment)
  have htwo : listQSum (subsetTerm w) [singletonSelection, complementSelection] ≈
      (coeffW w 1) * HalfPow.half +
        qpow (coeffW w 1) 5 * (Q'.mkPos 1 8 (by decide)) := by
    change subsetTerm w singletonSelection + (subsetTerm w complementSelection + 0) ≈ _
    exact Q'.add_eqv_congr' hsingle
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) hcomplement)
  exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_trans _ _ _ hfilter htwo)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment.survivor_filter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment.tested_bent_action_channel
