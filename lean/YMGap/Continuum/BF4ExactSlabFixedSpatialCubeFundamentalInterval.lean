/-
# Original cutoff-one cube action interval on shared coordinates

The six actual fundamental face remainders each have cap 2*coeffW(w,1).
Their structural telescope constructs an interval for cubeWeight(w,1)-1
with cap (1+2*coeffW(w,1))^6-1. All shared link variables are retained.
Smallness of this explicit cap constructs the original positive action,
or its half-floor certificate, without a headCutoff hypothesis.

This is a finite source certificate. No OWN gain sign, parameter-uniform
estimate, transfer range, completed response or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
import YMGap.Continuum.PolynomialProductRemainder
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatFace_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeFaces cubeWeight)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.PolynomialProductRemainder
  (productRemainder polynomialProduct_remainder)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarHeatCertificate
  (heatPrefix heatRemainder heatPrefix_split)
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks plaquette characterPolynomial cubeWeight

def cubeFundamentalDelta (w : Q') : Q' := (1 + 2 * coeffW w 1)^6 - 1

def cubeFundamentalRemainder (w : Q') : RatPoly :=
  polyAdd (cubeWeight w 1) (polyNeg polyOne)

private def faceRemainder (w : Q') (face : Z4Plaq) : RatPoly :=
  polySmul (coeffW w 1) (characterPolynomial (plaquette 2 face).scalar 1)

private theorem fundamental_prefix (w : Q') (face : Z4Plaq) :
    RatPolyCoeffEqv (heatPrefix w 1 (plaquette 2 face).scalar)
      (polyAdd polyOne (faceRemainder w face)) := by
  have hr : RatPolyCoeffEqv (heatRemainder w 1 (plaquette 2 face).scalar)
      (faceRemainder w face) := by
    unfold heatRemainder faceRemainder
    change RatPolyCoeffEqv
      (polyAdd (polySmul (coeffW w 1)
        (characterPolynomial (plaquette 2 face).scalar 1)) polyZero)
      (polySmul (coeffW w 1) (characterPolynomial (plaquette 2 face).scalar 1))
    exact RatPolyCoeffEqv.add_zero _
  exact (heatPrefix_split w 1 (plaquette 2 face).scalar).trans
    ((RatPolyCoeffEqv.refl polyOne).add hr)

private def faceRemainderInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (face : Z4Plaq) : Interval N (faceRemainder w face) (2 * coeffW w 1) :=
  Interval.changeCap (Q'.mul_comm_eqv (coeffW w 1) 2)
    ((sharpCharacterInterval
      (SquareBound.scalar (plaquette_supported 2 N (Nat.le_refl _) face)
        (plaquette_unit 2 N (Nat.le_refl _) face)) 1).smul (coeffW w 1) ha)

private def faceInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (face : Z4Plaq) :
    Interval N (heatPrefix w 1 (plaquette 2 face).scalar) (1 + 2 * coeffW w 1) :=
  Interval.ofCoeff (heatFace_supported w 1 2 face) (fundamental_prefix w face)
    ((Interval.one N).add (faceRemainderInterval w ha face))

private theorem cap_step (tau : Q') (n : Nat) :
    (1 : Q') * ((1+tau)^n-1) + tau*(1+tau)^n ≈ (1+tau)^(n+1)-1 := by
  rw [Q'.pow_succ]
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 1) (.add (.var 1) (.neg (.const 1)))) (.mul (.var 0) (.var 1)))
    (.add (.mul (.add (.const 1) (.var 0)) (.var 1)) (.neg (.const 1)))
    (by decide) (fun | 0 => tau | _ => (1+tau)^n)

private def telescopingInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1) :
    (fs : List Z4Plaq) →
    Interval N
      (productRemainder (fun _ => polyOne)
        (fun face => heatPrefix w 1 (plaquette 2 face).scalar) (faceRemainder w) fs)
      ((1 + 2 * coeffW w 1)^fs.length - 1)
  | [] => Interval.changeCap (by change (0 : Q') ≈ 1-1; decide) (Interval.zero N)
  | face :: fs => by
      let Pt := telescopingInterval w ha fs
      let Pg := Interval.productUniform
        (fun face => heatPrefix w 1 (plaquette 2 face).scalar)
        (1 + 2 * coeffW w 1) fs (fun face _ => faceInterval w ha face)
      exact Interval.changeCap (cap_step (2 * coeffW w 1) fs.length)
        (((Interval.one N).mul Pt).add ((faceRemainderInterval w ha face).mul Pg))

private theorem one_product : ∀ fs : List Z4Plaq,
    RatPolyCoeffEqv (polynomialProduct (fun _ => polyOne) fs) polyOne
  | [] => RatPolyCoeffEqv.refl _
  | _ :: fs => ((one_product fs).mul_left polyOne).trans (RatPolyCoeffEqv.one_mul polyOne)

private theorem cube_remainder_pin (w : Q') :
    RatPolyCoeffEqv (cubeFundamentalRemainder w)
      (productRemainder (fun _ => polyOne)
        (fun face => heatPrefix w 1 (plaquette 2 face).scalar) (faceRemainder w) cubeFaces) := by
  have he := polynomialProduct_remainder (fun _ => polyOne)
    (fun face => heatPrefix w 1 (plaquette 2 face).scalar) (faceRemainder w)
    (fundamental_prefix w) cubeFaces
  have hv : RatPolyCoeffEqv (cubeWeight w 1)
      (polyAdd polyOne (productRemainder (fun _ => polyOne)
        (fun face => heatPrefix w 1 (plaquette 2 face).scalar) (faceRemainder w) cubeFaces)) := by
    unfold cubeWeight
    exact he.trans ((one_product cubeFaces).add (RatPolyCoeffEqv.refl _))
  unfold cubeFundamentalRemainder
  let remainder := productRemainder (fun _ => polyOne)
    (fun face => heatPrefix w 1 (plaquette 2 face).scalar) (faceRemainder w) cubeFaces
  exact (hv.add (RatPolyCoeffEqv.refl (polyNeg polyOne))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => polyOne | _ => remainder))

private theorem neg_one_supported : SupportedQuaternionBlocks N (polyNeg polyOne) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one N source hs

/-- Constructed endpoints under arbitrary original Haar insertions, with all six factors shared. -/
def cubeFundamentalInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1) :
    Interval N (cubeFundamentalRemainder w) (cubeFundamentalDelta w) := by
  have hp := Interval.productUniform
    (fun face => heatPrefix w 1 (plaquette 2 face).scalar)
    (1 + 2 * coeffW w 1) cubeFaces (fun face _ => faceInterval w ha face)
  have hv : SupportedQuaternionBlocks N (cubeWeight w 1) := by
    unfold cubeWeight
    exact hp.support
  have hs : SupportedQuaternionBlocks N (cubeFundamentalRemainder w) := by
    unfold cubeFundamentalRemainder
    exact supported_add hv neg_one_supported
  exact Interval.ofCoeff hs (cube_remainder_pin w) (telescopingInterval w ha cubeFaces)

theorem cubeFundamentalDelta_nonnegative (w : Q') (ha : (0 : Q') ≤ coeffW w 1) :
    (0 : Q') ≤ cubeFundamentalDelta w := (cubeFundamentalInterval w ha).nonnegative

private theorem unit_lower_cancel (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (cap 1) (polyAdd p (polyNeg polyOne))) p :=
  ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => p | _ => polyOne))

/-- Positivity at this actual cutoff follows from the computed remainder cap, not headCutoff. -/
def cubeFundamentalCertificate (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hdelta : cubeFundamentalDelta w ≤ 1) : Certificate N (cubeWeight w 1) := by
  have P := ((cubeFundamentalInterval w ha).weaken hdelta).lower
  unfold cubeFundamentalRemainder at P
  exact Certificate.ofCoeff (unit_lower_cancel (cubeWeight w 1)).symm P

/-- A literal half-floor certificate on the SAME original cube action. -/
def cubeFundamentalHalfCertificate (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hdelta : cubeFundamentalDelta w ≤ HalfPow.half) :
    Certificate N (polyAdd (cubeWeight w 1) (polyNeg (cap HalfPow.half))) := by
  have P := ((cubeFundamentalInterval w ha).weaken hdelta).lower
  have hone : RatPolyCoeffEqv polyOne (polyAdd (cap HalfPow.half) (cap HalfPow.half)) :=
    ((cap_add HalfPow.half HalfPow.half).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide) polyOne).trans
        (RatPolyCoeffEqv.one_smul polyOne))).symm
  have he : RatPolyCoeffEqv
      (polyAdd (cap HalfPow.half) (cubeFundamentalRemainder w))
      (polyAdd (cubeWeight w 1) (polyNeg (cap HalfPow.half))) := by
    unfold cubeFundamentalRemainder
    exact ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hone))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 1) (.add (.var 0) (.neg (.add (.var 1) (.var 1)))))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => cubeWeight w 1 | _ => cap HalfPow.half))
  exact Certificate.ofCoeff he.symm P

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalDelta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalDelta_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalHalfCertificate
