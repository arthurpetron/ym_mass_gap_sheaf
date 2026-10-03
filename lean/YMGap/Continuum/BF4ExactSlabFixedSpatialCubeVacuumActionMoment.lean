/-
# Exact vacuum test of the original cutoff-one cube action

The literal six-face subset expansion tested by the original first face P
has only two survivors. Its singleton gives H[P^2]=1 and its five-face
complement gives the closed original cube surface moment 1/16. Thus the
SAME action has H[P*V]=alpha+alpha^5/16, alpha=coeffW(w,1).

This is a finite original-source Haar identity, not a kinetic projection,
an OWN-centered gain bound or a changing-family/continuum estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_polySmul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeFaces cubeWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace thirdFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity
  (singletonSelection complementSelection selectedVacuumInsertion badSelection_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity (selectedFaceProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
  (remainingFourFaceProduct first_face_square_haar closed_cube_surface_moment)
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
  firstFaceTrace thirdFaceTrace cubeWeight selectedVacuumInsertion selectedFaceProduct

private theorem five_product (factor : Z4Plaq → RatPoly) (a b c d e : Z4Plaq) :
    RatPolyCoeffEqv (polynomialProduct factor [a,b,c,d,e])
      (polyMul (factor a) (polyMul (factor b) (polyMul (factor c) (polyMul (factor d) (factor e))))) :=
  (RatPolyCoeffEqv.refl (factor a)).mul ((RatPolyCoeffEqv.refl (factor b)).mul
    ((RatPolyCoeffEqv.refl (factor c)).mul ((RatPolyCoeffEqv.refl (factor d)).mul
      (RatPolyCoeffEqv.mul_one (factor e)))))

private theorem gather_six (p a q b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyMul a (polyMul q (polyMul b (polyMul c d)))))
      (polyMul (polyMul p q) (polyMul a (polyMul b (polyMul c d)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.var 5))))))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.var 5)))))
    (by decide) (fun | 0 => p | 1 => a | 2 => q | 3 => b | 4 => c | _ => d)

/-- The original first-face singleton contracts to its Haar square norm. -/
theorem singleton_selection_moment :
    quaternionHaar N (selectedVacuumInsertion singletonSelection) ≈ 1 := by
  have hp : RatPolyCoeffEqv (selectedFaceProduct singletonSelection) firstFaceTrace := by
    unfold selectedFaceProduct singletonSelection firstFaceTrace
    exact RatPolyCoeffEqv.mul_one _
  unfold selectedVacuumInsertion
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl firstFaceTrace).mul hp))
    first_face_square_haar

/-- The literal five-face complement closes with P, without dropping any face. -/
theorem complement_selection_moment :
    quaternionHaar N (selectedVacuumInsertion complementSelection) ≈ Q'.mkPos 1 16 (by decide) := by
  let C := fun face : Z4Plaq => characterPolynomial (plaquette 2 face).scalar 1
  have hp := five_product C ((0,0,1,0),.p01) ((0,0,0,0),.p02)
    ((0,1,0,0),.p02) ((0,0,0,0),.p12) ((1,0,0,0),.p12)
  have hg := gather_six firstFaceTrace (C ((0,0,1,0),.p01))
    (C ((0,0,0,0),.p02)) (C ((0,1,0,0),.p02))
    (C ((0,0,0,0),.p12)) (C ((1,0,0,0),.p12))
  have h : RatPolyCoeffEqv (selectedVacuumInsertion complementSelection)
      (polyMul (polyMul firstFaceTrace thirdFaceTrace) remainingFourFaceProduct) := by
    unfold selectedVacuumInsertion selectedFaceProduct complementSelection
      thirdFaceTrace remainingFourFaceProduct
    exact (hp.mul_left firstFaceTrace).trans hg
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h) closed_cube_surface_moment

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
  quaternionHaar N (polyMul firstFaceTrace
    (polynomialProduct (fun face => polySmul (coeffW w 1)
      (characterPolynomial (plaquette 2 face).scalar 1)) fs))

private theorem subsetTerm_weight (w : Q') (fs : List Z4Plaq) :
    subsetTerm w fs ≈ qpow (coeffW w 1) fs.length *
      quaternionHaar N (selectedVacuumInsertion fs) := by
  have hs := weighted_product (coeffW w 1)
    (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs
  unfold subsetTerm
  have hc := (hs.mul_left firstFaceTrace).trans
    (RatPolyCoeffEqv.polyMul_smul_right (qpow (coeffW w 1) fs.length)
      firstFaceTrace
      (polynomialProduct (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs))
  have hh := Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (quaternionHaar_polySmul N (qpow (coeffW w 1) fs.length) _)
  simpa only [selectedVacuumInsertion, selectedFaceProduct] using hh

attribute [local irreducible] subsetTerm

private def keepSurvivor (fs : List Z4Plaq) : Bool :=
  decide (fs = singletonSelection ∨ fs = complementSelection)

/-- Only the order of two rows in the original finite selection list is checked. -/
theorem survivor_filter :
    (selections cubeFaces).filter keepSurvivor =
      [complementSelection, singletonSelection] := by
  decide

/-- Exact vacuum source channel at every rational nome, on the original slice. -/
theorem tested_vacuum_action_channel (w : Q') :
    quaternionHaar N (polyMul firstFaceTrace (cubeWeight w 1)) ≈
      coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide) := by
  have hexp := haar_expansion N
    (fun face => heatPrefix w 1 (plaquette 2 face).scalar)
    (fun face => polySmul (coeffW w 1)
      (characterPolynomial (plaquette 2 face).scalar 1))
    (fun face => fundamental_prefix w (plaquette 2 face).scalar)
    firstFaceTrace cubeFaces
  have hsum : quaternionHaar N (polyMul firstFaceTrace (cubeWeight w 1)) ≈
      listQSum (subsetTerm w) (selections cubeFaces) := by
    unfold cubeWeight subsetTerm
    exact hexp
  have hfilter := sum_filter_zero (subsetTerm w) keepSurvivor (selections cubeFaces)
    (fun fs hfs hk => by
      have hn : ¬(fs = singletonSelection ∨ fs = complementSelection) := of_decide_eq_false hk
      have hz := badSelection_haar_zero fs hfs
        (fun hs => hn (Or.inl hs)) (fun hc => hn (Or.inr hc))
      exact Q'.eqv_trans _ _ _ (subsetTerm_weight w fs)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)))
  rw [survivor_filter] at hfilter
  have hsingle : subsetTerm w singletonSelection ≈ coeffW w 1 :=
    Q'.eqv_trans _ _ _ (subsetTerm_weight w singletonSelection)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ singleton_selection_moment)
          (Q'.mul_one_eqv _)))
  have hcomplement : subsetTerm w complementSelection ≈
      qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide) :=
    Q'.eqv_trans _ _ _ (subsetTerm_weight w complementSelection)
      (Q'.mul_eqv_congr_left _ _ _ complement_selection_moment)
  have htwo : listQSum (subsetTerm w) [complementSelection, singletonSelection] ≈
      coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide) := by
    change subsetTerm w complementSelection + (subsetTerm w singletonSelection + 0) ≈ _
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hcomplement
        (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) hsingle))
      (Q'.add_comm_eqv _ _)
  exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_trans _ _ _ hfilter htwo)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment.singleton_selection_moment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment.complement_selection_moment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment.survivor_filter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment.tested_vacuum_action_channel
