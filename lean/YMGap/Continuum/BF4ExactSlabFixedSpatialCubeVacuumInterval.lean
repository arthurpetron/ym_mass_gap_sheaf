/-
# Original cutoff-one cube vacuum-message interval

The constructed cube action interval is integrated against the actual
positive cutoff-one kinetic kernel. Its normalization and the original
vacuum-message pin are upgraded only with explicit support on both sides.
The result bounds the literal U=T1 minus one on the full original carrier.
No headCutoff, OWN variance, gain sign, or changing-family estimate is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
import YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate (productMap_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks cubeWeight transferStep

/-- The actual original vacuum message, not its reduced representative. -/
def cubeVacuumRemainder (w : Q') : RatPoly :=
  polyAdd (transferStep w 1 2 polyOne) (polyNeg polyOne)

private theorem ids_lt (i : Nat) (hi : i ∈ cubeIndices) : i < N :=
  activeBlocks_lt 2 i (cubeIndices_active i hi)

private def M (w : Q') (p : RatPoly) : RatPoly := productMap N w 1 cubeIndices p

private theorem M_supported (w : Q') {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    SupportedQuaternionBlocks N (M w p) := productMap_supported N w 1 cubeIndices ids_lt hp

private theorem neg_supported {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    SupportedQuaternionBlocks N (polyNeg p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

private theorem neg_smul (p : RatPoly) : RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
    (by decide) (fun _ => p)).trans (cap_mul_left (-1) p)

private theorem neg_test {p q : RatPoly} (h : SupportedHaarEqv N p q) :
    SupportedHaarEqv N (polyNeg p) (polyNeg q) :=
  (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (neg_smul p))).trans
    ((h.smul (-1)).trans
      (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (neg_smul q).symm)))

private theorem vacuum_pin (w : Q') :
    SupportedHaarEqv N (transferStep w 1 2 polyOne) (M w (cubeWeight w 1)) := by
  have hc := productMap_congr N w 1 cubeIndices (RatPolyCoeffEqv.mul_one (cubeWeight w 1))
  exact (original_vacuum_message_cube w 1).trans
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hc))

private theorem remainder_pin (w : Q') :
    SupportedHaarEqv N (cubeVacuumRemainder w) (M w (cubeFundamentalRemainder w)) := by
  have hone : SupportedHaarEqv N (M w polyOne) polyOne :=
    productMap_one N w 1 cubeIndices cubeIndices_nodup ids_lt
  have hc : RatPolyCoeffEqv (M w (cubeFundamentalRemainder w))
      (polyAdd (M w (cubeWeight w 1)) (polyNeg (M w polyOne))) :=
    (productMap_add N w 1 cubeIndices (cubeWeight w 1) (polyNeg polyOne)).trans
      ((RatPolyCoeffEqv.refl _).add (productMap_neg N w 1 cubeIndices polyOne))
  exact ((vacuum_pin w).add (neg_test hone.symm)).trans
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hc).symm)

private theorem remainder_supported (w : Q') :
    SupportedQuaternionBlocks N (cubeVacuumRemainder w) :=
  supported_add (transferStep_supported w 1 2 (supported_one N))
    (neg_supported (supported_one N))

private theorem cap_supported (d : Q') : SupportedQuaternionBlocks N (cap d) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one N source hs

/-- Both endpoints of U-1 retain the entire original carrier. The only kernel
guard is direct fundamental-prefix positivity, not the all-nome late guard. -/
def cubeVacuumInterval (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1 * 2 ≤ 1) :
    Interval N (cubeVacuumRemainder w) (cubeFundamentalDelta w) := by
  let P := cubeFundamentalInterval w ha
  let d := cubeFundamentalDelta w
  let p := cubeFundamentalRemainder w
  let u := cubeVacuumRemainder w
  have hp : SupportedQuaternionBlocks N p := P.support
  have hu : SupportedQuaternionBlocks N u := remainder_supported w
  have hd : SupportedQuaternionBlocks N (cap d) := cap_supported d
  have hnorm : SupportedHaarEqv N (M w (cap d)) (cap d) :=
    productMap_cap N w 1 cubeIndices cubeIndices_nodup ids_lt d
  have hrem : SupportedHaarEqv N (M w p) u := (remainder_pin w).symm
  have hlo : SupportedHaarEqv N (M w (polyAdd (cap d) p)) (polyAdd (cap d) u) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_add N w 1 cubeIndices (cap d) p))).trans (hnorm.add hrem)
  have hhi : SupportedHaarEqv N (M w (polyAdd (cap d) (polyNeg p)))
      (polyAdd (cap d) (polyNeg u)) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      ((productMap_add N w 1 cubeIndices (cap d) (polyNeg p)).trans
        ((RatPolyCoeffEqv.refl _).add (productMap_neg N w 1 cubeIndices p))))).trans
      (hnorm.add (neg_test hrem))
  have hls := supported_add hd hp
  have hus := supported_add hd (neg_supported hp)
  exact ⟨hu, P.nonnegative,
    Certificate.transport
      (carrier_of_supported (M_supported w hus) (supported_add hd (neg_supported hu)) hhi).symm
      (productMap_certificate N w ha hcap cubeIndices ids_lt hus P.upper),
    Certificate.transport
      (carrier_of_supported (M_supported w hls) (supported_add hd hu) hlo).symm
      (productMap_certificate N w ha hcap cubeIndices ids_lt hls P.lower)⟩

private theorem unit_lower_cancel (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (cap 1) (polyAdd p (polyNeg polyOne))) p :=
  ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => p | _ => polyOne))

/-- Constructed positivity of the literal original vacuum message. -/
def cubeVacuumCertificate (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1 * 2 ≤ 1) (hdelta : cubeFundamentalDelta w ≤ 1) :
    Certificate N (transferStep w 1 2 polyOne) :=
  Certificate.ofCoeff (unit_lower_cancel (transferStep w 1 2 polyOne)).symm
    ((cubeVacuumInterval w ha hcap).weaken hdelta).lower

/-- A half-floor for the same original U, without replacing it by a cube source. -/
def cubeVacuumHalfCertificate (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1 * 2 ≤ 1) (hdelta : cubeFundamentalDelta w ≤ HalfPow.half) :
    Certificate N (polyAdd (transferStep w 1 2 polyOne) (polyNeg (cap HalfPow.half))) := by
  have P := ((cubeVacuumInterval w ha hcap).weaken hdelta).lower
  have hone : RatPolyCoeffEqv polyOne (polyAdd (cap HalfPow.half) (cap HalfPow.half)) :=
    ((cap_add HalfPow.half HalfPow.half).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide) polyOne).trans
        (RatPolyCoeffEqv.one_smul polyOne))).symm
  have he : RatPolyCoeffEqv (polyAdd (cap HalfPow.half) (cubeVacuumRemainder w))
      (polyAdd (transferStep w 1 2 polyOne) (polyNeg (cap HalfPow.half))) := by
    unfold cubeVacuumRemainder
    exact ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hone))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 1) (.add (.var 0) (.neg (.add (.var 1) (.var 1)))))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => transferStep w 1 2 polyOne | _ => cap HalfPow.half))
  exact Certificate.ofCoeff he.symm P

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval.cubeVacuumRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval.cubeVacuumInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval.cubeVacuumCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval.cubeVacuumHalfCertificate
