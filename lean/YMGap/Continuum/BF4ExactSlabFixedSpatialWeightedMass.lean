/-
# The actual V-weighted mass is linear and positive along transfer iterates

The functional is exactly H[V_K*f], with one original spatial potential.
Signed rational linearity is unconditional. At the existing late cutoff,
the spatial product floor proves positive mass of one. The actual transfer
lower certificate then preserves positive mass of a supported certified
input, with its input mass as the only supplied strict-positivity premise.

All constants retain their nome and width dependence. This finite-cutoff
statement introduces no normalization, stationary law or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Coefficient equality is retained under the actual spatial insertion. -/
theorem weightedMass_congr (w : Q') (K width : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) : weightedMass w K width f ≈ weightedMass w K width g :=
  haar_of_coeff ((RatPolyCoeffEqv.refl (spatialWeight w K width)).mul h)

/-- Exact additivity with the same original spatial weight in both terms. -/
theorem weightedMass_add (w : Q') (K width : Nat) (f g : RatPoly) :
    weightedMass w K width (polyAdd f g) ≈
      weightedMass w K width f + weightedMass w K width g :=
  quaternionHaar_polyMul_add_right (N width) (spatialWeight w K width) f g

/-- Signed rational homogeneity; the coefficient need not be nonnegative. -/
theorem weightedMass_smul (w : Q') (K width : Nat) (c : Q') (f : RatPoly) :
    weightedMass w K width (polySmul c f) ≈ c * weightedMass w K width f :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c (spatialWeight w K width) f))
    (quaternionHaar_polySmul (N width) c _)

private def productCertificate {A : Type} {blocks : Nat} (f : A → RatPoly)
    (F : ∀ i, Certificate blocks (f i)) :
    (ids : List A) → Certificate blocks (polynomialProduct f ids)
  | [] => .one _
  | i::ids => (F i).mul (productCertificate f F ids)

private def productFloorCertificate {A : Type} {blocks : Nat} (f : A → RatPoly)
    (F : ∀ i, Certificate blocks (f i)) (c : Q') (hc : (0 : Q') ≤ c)
    (L : ∀ i, Certificate blocks (polyAdd (f i) (polyNeg (cap c)))) :
    (ids : List A) → Certificate blocks
      (polyAdd (polynomialProduct f ids) (polyNeg (cap (c^ids.length))))
  | [] => .ofCoeff
      (((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
          (by decide) (fun _ => cap 1))) (.constant _ 0 (Q'.le_refl' _))
  | i::ids => .ofCoeff
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul c (c^ids.length)).symm)).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
          (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
            (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
          (by decide) (fun
            | 0 => f i
            | 1 => polynomialProduct f ids
            | 2 => cap c
            | _ => cap (c^ids.length))).trans
          ((RatPolyCoeffEqv.refl _).add
            (cap_mul_left c (polyAdd (polynomialProduct f ids) (polyNeg (cap (c^ids.length))))))))
      (((L i).mul (productCertificate f F ids)).add
        (.smul c hc (productFloorCertificate f F c hc L ids)))

private def spatialFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width) (polyAdd (spatialWeight w K width)
      (polyNeg (cap ((headFloor w)^(spatialFaces width).length)))) :=
  productFloorCertificate (fun face => heatPrefix w K (plaquette width face).scalar)
    (fun face => faceCertificate hw0 hw1 K width (N width) (Nat.le_refl _) face hK)
    (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))
    (fun face => QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
      (plaquette_supported width (N width) (Nat.le_refl _) face)
      (plaquette_unit width (N width) (Nat.le_refl _) face) K hK)
    (spatialFaces width)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem weighted_floor {blocks : Nat} {p h : RatPoly} {c : Q'}
    (P : Certificate blocks p) (C : Certificate blocks (polyAdd h (polyNeg (cap c)))) :
    c * quaternionHaar blocks p ≤ quaternionHaar blocks (polyMul p h) := by
  have hpos := (P.mul C).haar_nonnegative
  have hc : quaternionHaar blocks (polyMul p (cap c)) ≈ c * quaternionHaar blocks p :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (quaternionHaar_polySmul blocks c p)
  have he : quaternionHaar blocks (polyMul p (polyAdd h (polyNeg (cap c)))) ≈
      quaternionHaar blocks (polyMul p h) + -(c * quaternionHaar blocks p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => h | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_neg blocks _) (Q'.neg_eqv_congr _ _ hc))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

/-- The finite original spatial product supplies a computed positive mass floor. -/
theorem weightedMass_one_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (headFloor w)^(spatialFaces width).length ≤ weightedMass w K width polyOne := by
  let c := (headFloor w)^(spatialFaces width).length
  have h := weighted_floor (Certificate.one (N width)) (spatialFloorCertificate hw0 hw1 K width hK)
  have hl : (c * quaternionHaar (N width) polyOne) ≈ c :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one (N width))) (Q'.mul_one_eqv c)
  have hr : quaternionHaar (N width) (polyMul polyOne (spatialWeight w K width)) ≈
      weightedMass w K width polyOne :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm polyOne (spatialWeight w K width))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

theorem weightedMass_one_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (0 : Q') < weightedMass w K width polyOne :=
  HeatKernelRGStep.lt_of_lt_of_le (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
    (weightedMass_one_floor hw0 hw1 K width hK)

/-- One actual V occurs in each mass. The transfer's certified floor gives
the displayed quantitative lower bound without dividing by the input mass. -/
theorem weightedMass_transfer_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (F : Certificate (N width) f) :
    (kineticFloor w width * weightedMass w K width f) * weightedMass w K width polyOne ≤
      weightedMass w K width (transferStep w K width f) := by
  have h := weighted_floor
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
    (transferStepLowerCertificate hw0 hw1 K width hK hf F)
  have he : weightedMass w K width polyOne ≈ quaternionHaar (N width) (spatialWeight w K width) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one (spatialWeight w K width))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he)) h

/-- Strict mass positivity is preserved for the supplied supported certified
input. Its strict input mass is the only additional positivity premise. -/
theorem weightedMass_transfer_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (F : Certificate (N width) f)
    (hmass : (0 : Q') < weightedMass w K width f) :
    (0 : Q') < weightedMass w K width (transferStep w K width f) :=
  HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (kineticFloor_positive hw0 hw1 width) hmass)
      (weightedMass_one_positive hw0 hw1 K width hK))
    (weightedMass_transfer_floor hw0 hw1 K width hK hf F)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_one_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_one_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_transfer_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass.weightedMass_transfer_positive
