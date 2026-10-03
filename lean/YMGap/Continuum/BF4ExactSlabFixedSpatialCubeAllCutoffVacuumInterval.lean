/-
# Original all-cutoff cube vacuum-message interval

The all-cutoff cube action interval is integrated against the actual
positive original kinetic kernel. Its normalization and the original vacuum
message pin are upgraded only with explicit support on both sides. The
result bounds the literal `T_K 1 - 1` on the full original carrier for every
cutoff satisfying both the prefix and head guards. No OWN variance, gain
sign, or changing-family estimate is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
import YMGap.Continuum.SU2QuaternionProductHeatLocalBand
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_neg productMap_one productMap_cap)
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand (erasedCertificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks cubeWeight transferStep

/-- The actual original vacuum message, not its reduced representative. -/
def cubeVacuumRemainder (K : Nat) : RatPoly :=
  polyAdd (transferStep smallNome K 2 polyOne) (polyNeg polyOne)

private theorem ids_lt (i : Nat) (hi : i ∈ cubeIndices) : i < N :=
  activeBlocks_lt 2 i (cubeIndices_active i hi)

private def M (K : Nat) (p : RatPoly) : RatPoly :=
  productMap N smallNome K cubeIndices p

private theorem M_supported (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    SupportedQuaternionBlocks N (M K p) :=
  productMap_supported N smallNome K cubeIndices ids_lt hp

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

private theorem vacuum_pin (K : Nat) :
    SupportedHaarEqv N (transferStep smallNome K 2 polyOne) (M K (cubeWeight smallNome K)) := by
  have hc := productMap_congr N smallNome K cubeIndices
    (RatPolyCoeffEqv.mul_one (cubeWeight smallNome K))
  exact (original_vacuum_message_cube smallNome K).trans
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hc))

private theorem remainder_pin (K : Nat) :
    SupportedHaarEqv N
      (cubeVacuumRemainder K)
      (M K (polyAdd (cubeWeight smallNome K) (polyNeg polyOne))) := by
  have hone : SupportedHaarEqv N (M K polyOne) polyOne :=
    productMap_one N smallNome K cubeIndices cubeIndices_nodup ids_lt
  have hc : RatPolyCoeffEqv (M K (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)))
      (polyAdd (M K (cubeWeight smallNome K)) (polyNeg (M K polyOne))) :=
    (productMap_add N smallNome K cubeIndices (cubeWeight smallNome K) (polyNeg polyOne)).trans
      ((RatPolyCoeffEqv.refl _).add (productMap_neg N smallNome K cubeIndices polyOne))
  exact ((vacuum_pin K).add (neg_test hone.symm)).trans
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hc).symm)

private theorem remainder_supported (K : Nat) :
    SupportedQuaternionBlocks N (cubeVacuumRemainder K) :=
  supported_add (transferStep_supported smallNome K 2 (supported_one N))
    (neg_supported (supported_one N))

private theorem cap_supported (d : Q') : SupportedQuaternionBlocks N (cap d) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one N source hs

/-- Both endpoints of `T_K 1 - 1` retain the entire original carrier.
The cutoff obeys both the finite heat-prefix guard and the original head
guard; positivity is constructed by the all-nome erased-certificate API. -/
def cubeVacuumInterval (K : Nat) (hK1 : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) :
    Interval N (cubeVacuumRemainder K) deltaCap := by
  let P := cubeRemainderInterval K hK1
  let d := deltaCap
  let p := polyAdd (cubeWeight smallNome K) (polyNeg polyOne)
  let u := cubeVacuumRemainder K
  have hp : SupportedQuaternionBlocks N p := P.support
  have hu : SupportedQuaternionBlocks N u := remainder_supported K
  have hd : SupportedQuaternionBlocks N (cap d) := cap_supported d
  have hnorm : SupportedHaarEqv N (M K (cap d)) (cap d) :=
    productMap_cap N smallNome K cubeIndices cubeIndices_nodup ids_lt d
  have hrem : SupportedHaarEqv N (M K p) u := (remainder_pin K).symm
  have hlo : SupportedHaarEqv N (M K (polyAdd (cap d) p)) (polyAdd (cap d) u) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_add N smallNome K cubeIndices (cap d) p))).trans (hnorm.add hrem)
  have hhi : SupportedHaarEqv N (M K (polyAdd (cap d) (polyNeg p)))
      (polyAdd (cap d) (polyNeg u)) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      ((productMap_add N smallNome K cubeIndices (cap d) (polyNeg p)).trans
        ((RatPolyCoeffEqv.refl _).add (productMap_neg N smallNome K cubeIndices p))))).trans
      (hnorm.add (neg_test hrem))
  have hls := supported_add hd hp
  have hus := supported_add hd (neg_supported hp)
  have hw0 : (0 : Q') < smallNome := smallNome_pos
  have hw1 : smallNome < (1 : Q') := by decide
  exact ⟨hu, P.nonnegative,
    Certificate.transport
      (carrier_of_supported (M_supported K hus) (supported_add hd (neg_supported hu)) hhi).symm
      (erasedCertificate N (w := smallNome) hw0 hw1 K hhead cubeIndices ids_lt hus P.upper),
    Certificate.transport
      (carrier_of_supported (M_supported K hls) (supported_add hd hu) hlo).symm
      (erasedCertificate N (w := smallNome) hw0 hw1 K hhead cubeIndices ids_lt hls P.lower)⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval.cubeVacuumRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval.cubeVacuumInterval
