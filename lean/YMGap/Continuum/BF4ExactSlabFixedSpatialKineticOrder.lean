/-
# Positive order bounds for the actual compact kinetic polynomial

The original lower-times-inverse-upper quaternion has unit norm on the
SAME N+N product-Haar carrier. The all-nome heat-prefix compiler therefore
gives each actual finite heat factor the existing headFloor after the
existing headCutoff. Its absolute cap is prefixCap, independently of K.

Products retain every temporal face and all source coordinates. The
resulting bounds hold in any certificate-positive polynomial background,
not just for the bare integral. Constants depend on the nome and the
width-only temporal-face count. No layer normalization, stationary vacuum,
completed OS operator, spatially uniform contraction or gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (temporalFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Support of the literal source word, including its defined identity fallback. -/
theorem relative_supported (width : Nat) (face : Z4Plaq) :
    Supported (N width+N width) (relative width face) := by
  have hl (link : Z4Link) : Supported (N width+N width) (lowerLink width link) := by
    unfold lowerLink
    split
    · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
      exact Supported.coordinate (by omega)
    · exact Supported.one _
  have hu (link : Z4Link) : Supported (N width+N width) (upperLink width link) := by
    unfold upperLink
    split
    · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
      exact Supported.coordinate (by omega)
    · exact Supported.one _
  exact (hl _).mul (hu _).conj

/-- Unit norm holds under every source Haar insertion, not merely after one integral. -/
theorem relative_unit (width : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (relative width face)) polyOne := by
  have hl (link : Z4Link) : HaarCarrierEqv (N width+N width)
      (polyQuaternionNorm (lowerLink width link)) polyOne := by
    unfold lowerLink
    split
    · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
      exact haarNorm_coordinate (by omega)
    · exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  have hu (link : Z4Link) : HaarCarrierEqv (N width+N width)
      (polyQuaternionNorm (upperLink width link)) polyOne := by
    unfold upperLink
    split
    · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
      exact haarNorm_coordinate (by omega)
    · exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  exact haarNorm_mul (hl _)
    (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) (hu _))

private theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

private theorem sum_congr {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → f a = g a) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | a::xs, h => by
      simp only [finitePolySum, h a List.mem_cons_self,
        sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- Literal equality keeps every signed packet term and the original quaternion order. -/
theorem heatFace_eq_prefix (w : Q') (K width : Nat) (face : Z4Plaq) :
    factor (fun f spin => characterPolynomial (relative width f).scalar spin)
      (face, heatWeights w K) = heatPrefix w K (relative width face).scalar := by
  simp only [factor, heatWeights, sum_map, heatPrefix]
  apply sum_congr
  intro spin hs
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hs)]

/-- Each actual source factor has the SAME positive floor at every late cutoff. -/
def faceFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (face : Z4Plaq) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width)
      (polyAdd (factor (fun f spin => characterPolynomial (relative width f).scalar spin)
        (face, heatWeights w K)) (polyNeg (cap (headFloor w)))) := by
  rw [heatFace_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (relative_supported width face) (relative_unit width face) K hK

def faceCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (face : Z4Plaq) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width)
      (factor (fun f spin => characterPolynomial (relative width f).scalar spin)
        (face, heatWeights w K)) := by
  rw [heatFace_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixCertificate hw0 hw1
    (relative_supported width face) (relative_unit width face) K hK

/-- The absolute factor cap needs no late-cutoff assumption. -/
def faceInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (face : Z4Plaq) :
    Interval (N width+N width)
      (factor (fun f spin => characterPolynomial (relative width f).scalar spin)
        (face, heatWeights w K)) (prefixCap w) := by
  rw [heatFace_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1
    (SquareBound.scalar (relative_supported width face) (relative_unit width face)) K

private def productCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) : (faces : List Z4Plaq) →
    Certificate (N width+N width)
      (polynomialProduct (fun face => factor
        (fun f spin => characterPolynomial (relative width f).scalar spin)
        (face, heatWeights w K)) faces)
  | [] => .one _
  | face::faces => (faceCertificate hw0 hw1 K width face hK).mul
      (productCertificate hw0 hw1 K width hK faces)

/-- Certificate for the complete original compact kinetic layer. -/
def kineticCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width) (kineticWeight w K width) :=
  productCertificate hw0 hw1 K width hK (temporalFaces width)

/-- Cutoff-independent cap with the literal width-only temporal-face count. -/
def kineticInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) :
    Interval (N width+N width) (kineticWeight w K width)
      ((prefixCap w)^(temporalFaces width).length) :=
  Interval.productUniform _ (prefixCap w) (temporalFaces width)
    (fun face _ => faceInterval hw0 hw1 K width face)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_floor {n : Nat} {p h : RatPoly} {c : Q'}
    (P : Certificate n p) (C : Certificate n (polyAdd h (polyNeg (cap c)))) :
    c*quaternionHaar n p ≤ quaternionHaar n (polyMul p h) := by
  have hpos := (P.mul C).haar_nonnegative
  have hc : quaternionHaar n (polyMul p (cap c)) ≈ c*quaternionHaar n p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (quaternionHaar_polySmul n c p)
  have he : quaternionHaar n (polyMul p (polyAdd h (polyNeg (cap c)))) ≈
      quaternionHaar n (polyMul p h) + -(c*quaternionHaar n p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => h | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ hc))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

/-- Lower comparison in ANY certificate-positive source background, retaining all factors. -/
theorem kinetic_weighted_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly}
    (P : Certificate (N width+N width) p) :
    (headFloor w)^(temporalFaces width).length * quaternionHaar (N width+N width) p ≤
      quaternionHaar (N width+N width) (polyMul p (kineticWeight w K width)) := by
  unfold kineticWeight
  induction temporalFaces width with
  | nil =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
        (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))
  | cons face faces ih =>
      have h := weighted_floor (P.mul (productCertificate hw0 hw1 K width hK faces))
        (faceFloorCertificate hw0 hw1 K width face hK)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih
          (Q'.le_of_lt (headFloor_positive hw0 hw1)))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
            ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
              ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)))))))

/-- Upper comparison in the SAME positive background, uniformly in the heat cutoff. -/
theorem kinetic_weighted_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) {p : RatPoly} (P : Certificate (N width+N width) p) :
    quaternionHaar (N width+N width) (polyMul p (kineticWeight w K width)) ≤
      (prefixCap w)^(temporalFaces width).length * quaternionHaar (N width+N width) p :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    ((kineticInterval hw0 hw1 K width).weighted_haar_bound P)

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.relative_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.relative_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.heatFace_eq_prefix
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.faceFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.faceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.faceInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.kineticCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.kineticInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.kinetic_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder.kinetic_weighted_upper
