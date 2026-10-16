/-
# Constructive sixteen-chart partition for the global Cayley clearing

Each of the four oriented plaquette links is assigned either its normalized
north base or the normalized north base of its central sign flip.  The sixteen
products are separately sum-of-squares positive on the unchanged ORIGINAL
Haar carrier and sum coefficientwise to one.  For each Boolean chart, the
product of the four signed Cayley denominators is exactly `2^4` times the
corresponding partition weight.

This is the polynomial partition and fixed-chart denominator interface.  It
does not yet reassemble the chartwise vector-jet numerators, estimate any
centered remainder, remove a cutoff, construct a continuum Hamiltonian, or
prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate
import YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem supported_neg_local {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

/-- Central sign action on all four polynomial quaternion coordinates. -/
def signedChartQuaternion (south : Bool) (q : PolyQuaternion) : PolyQuaternion :=
  if south then
    ⟨polyNeg q.scalar, polyNeg q.iPart, polyNeg q.jPart, polyNeg q.kPart⟩
  else q

theorem supported_signedChartQuaternion {blocks : Nat} (south : Bool)
    {q : PolyQuaternion} (hq : Supported blocks q) :
    Supported blocks (signedChartQuaternion south q) := by
  cases south
  · exact hq
  · exact ⟨supported_neg_local hq.scalar,
      supported_neg_local hq.iPart,
      supported_neg_local hq.jPart,
      supported_neg_local hq.kPart⟩

theorem polyQuaternionNorm_signedChartQuaternion
    (south : Bool) (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyQuaternionNorm (signedChartQuaternion south q))
      (polyQuaternionNorm q) := by
  cases south
  · exact RatPolyCoeffEqv.refl _
  · unfold signedChartQuaternion polyQuaternionNorm
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.neg (.var 0)) (.neg (.var 0)))
        (.add (.mul (.neg (.var 1)) (.neg (.var 1)))
          (.add (.mul (.neg (.var 2)) (.neg (.var 2)))
            (.mul (.neg (.var 3)) (.neg (.var 3))))))
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2))
            (.mul (.var 3) (.var 3)))))
      (by decide)
      (fun | 0 => q.scalar | 1 => q.iPart | 2 => q.jPart | _ => q.kPart)

theorem haarNorm_signedChartQuaternion {blocks : Nat}
    (south : Bool) {q : PolyQuaternion}
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv blocks
      (polyQuaternionNorm (signedChartQuaternion south q)) polyOne :=
  (RatPolyCoeffEqv.haarCarrier
    (polyQuaternionNorm_signedChartQuaternion south q)).trans hnorm

/-- North base after the selected central sign; `true` is the south base of
the original quaternion. -/
def cayleyChartBasePolynomial
    (south : Bool) (q : PolyQuaternion) : RatPoly :=
  northCayleyBasePolynomial (signedChartQuaternion south q)

def cayleyChartBasePolynomial_certificate {blocks : Nat}
    (south : Bool) {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (cayleyChartBasePolynomial south q) :=
  northCayleyBasePolynomial_certificate
    (supported_signedChartQuaternion south hq)
    (haarNorm_signedChartQuaternion south hnorm)

private theorem smul_neg_coeff (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polyNeg p))
      (polyNeg (polySmul c p)) := by
  have hring : RatPolyCoeffEqv
      (polyMul (cap c) (polyNeg p))
      (polyNeg (polyMul (cap c) p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1)))
      (by decide)
      (fun | 0 => cap c | _ => p)
  exact (cap_mul_left c (polyNeg p)).symm.trans
    (hring.trans (RatPolyCoeffEqv.neg (cap_mul_left c p)))

private theorem northBase_coeff_affine (q : PolyQuaternion) :
    RatPolyCoeffEqv (northCayleyBasePolynomial q)
      (polyAdd (cap half) (polySmul half q.scalar)) := by
  unfold northCayleyBasePolynomial cayleyChartDenominatorPolynomial cap
  exact RatPolyCoeffEqv.smul_add half polyOne q.scalar

/-- The north and south normalized bases of one quaternion sum exactly to
one coefficientwise. -/
theorem cayleyChartBasePolynomial_pair_coeff_one (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyAdd (cayleyChartBasePolynomial false q)
        (cayleyChartBasePolynomial true q))
      polyOne := by
  have hnorth := northBase_coeff_affine q
  have hsouth0 := northBase_coeff_affine (signedChartQuaternion true q)
  have hsouth : RatPolyCoeffEqv
      (cayleyChartBasePolynomial true q)
      (polyAdd (cap half) (polyNeg (polySmul half q.scalar))) := by
    exact hsouth0.trans
      ((RatPolyCoeffEqv.refl (cap half)).add
        (smul_neg_coeff half q.scalar))
  have hcancel : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (cap half) (polySmul half q.scalar))
        (polyAdd (cap half) (polyNeg (polySmul half q.scalar))))
      (polyAdd (cap half) (cap half)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1))
        (.add (.var 0) (.neg (.var 1))))
      (.add (.var 0) (.var 0))
      (by decide)
      (fun | 0 => cap half | _ => polySmul half q.scalar)
  have hhalves : RatPolyCoeffEqv
      (polyAdd (cap half) (cap half)) polyOne :=
    (RatPolyCoeffEqv.add_smul_same half half polyOne).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (by decide : half + half ≈ (1 : Q')) polyOne).trans
        (RatPolyCoeffEqv.one_smul polyOne))
  exact (hnorth.add hsouth).trans (hcancel.trans hhalves)

structure FourCayleyChart : Type where
  south0 : Bool
  south1 : Bool
  south2 : Bool
  south3 : Bool
deriving DecidableEq

/-- The sixteen fixed central-sign charts. -/
def fourCayleyChartTable : List FourCayleyChart :=
  [ ⟨false, false, false, false⟩,
    ⟨false, false, false, true⟩,
    ⟨false, false, true, false⟩,
    ⟨false, false, true, true⟩,
    ⟨false, true, false, false⟩,
    ⟨false, true, false, true⟩,
    ⟨false, true, true, false⟩,
    ⟨false, true, true, true⟩,
    ⟨true, false, false, false⟩,
    ⟨true, false, false, true⟩,
    ⟨true, false, true, false⟩,
    ⟨true, false, true, true⟩,
    ⟨true, true, false, false⟩,
    ⟨true, true, false, true⟩,
    ⟨true, true, true, false⟩,
    ⟨true, true, true, true⟩ ]

def FourCayleyChart.sector (chart : FourCayleyChart) : Bool :=
  plaquetteSign chart.south0 chart.south1 chart.south2 chart.south3

/-- Product partition weight for one fixed four-link chart. -/
def globalCayleyChartWeightPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul
      (cayleyChartBasePolynomial chart.south0
        (faceCayleyQuaternion0 extent face))
      (cayleyChartBasePolynomial chart.south1
        (faceCayleyQuaternion1 extent face)))
    (polyMul
      (cayleyChartBasePolynomial chart.south2
        (faceCayleyQuaternion2 extent face))
      (cayleyChartBasePolynomial chart.south3
        (faceCayleyQuaternion3 extent face)))

/-- Every one of the sixteen chart weights is sum-of-squares positive on the
complete ORIGINAL slab Haar carrier. -/
def globalCayleyChartWeight_certificate
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyChartWeightPolynomial extent face chart) := by
  let C0 := cayleyChartBasePolynomial_certificate chart.south0
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
  let C1 := cayleyChartBasePolynomial_certificate chart.south1
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
  let C2 := cayleyChartBasePolynomial_certificate chart.south2
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
  let C3 := cayleyChartBasePolynomial_certificate chart.south3
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
  exact (C0.mul C1).mul (C2.mul C3)

/-- Sum of all sixteen chart weights. -/
def globalCayleyChartPartitionPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleyChartWeightPolynomial extent face)
    fourCayleyChartTable

private def chartBaseExpr (slot : Nat) (south : Bool) : PolyExpr :=
  .var (2 * slot + if south then 1 else 0)

private def chartWeightExpr (chart : FourCayleyChart) : PolyExpr :=
  .mul
    (.mul (chartBaseExpr 0 chart.south0)
      (chartBaseExpr 1 chart.south1))
    (.mul (chartBaseExpr 2 chart.south2)
      (chartBaseExpr 3 chart.south3))

private def chartSumExpr : PolyExpr :=
  fourCayleyChartTable.foldr
    (fun chart total => .add (chartWeightExpr chart) total) (.var 8)

private def chartPairProductExpr : PolyExpr :=
  .add
    (.mul
      (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.mul (.add (.var 4) (.var 5)) (.add (.var 6) (.var 7))))
    (.var 8)

private theorem chartSum_normalized :
    normalize chartSumExpr = normalize chartPairProductExpr := by
  decide

private def chartEnvironment
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => cayleyChartBasePolynomial false
      (faceCayleyQuaternion0 extent face)
  | 1 => cayleyChartBasePolynomial true
      (faceCayleyQuaternion0 extent face)
  | 2 => cayleyChartBasePolynomial false
      (faceCayleyQuaternion1 extent face)
  | 3 => cayleyChartBasePolynomial true
      (faceCayleyQuaternion1 extent face)
  | 4 => cayleyChartBasePolynomial false
      (faceCayleyQuaternion2 extent face)
  | 5 => cayleyChartBasePolynomial true
      (faceCayleyQuaternion2 extent face)
  | 6 => cayleyChartBasePolynomial false
      (faceCayleyQuaternion3 extent face)
  | 7 => cayleyChartBasePolynomial true
      (faceCayleyQuaternion3 extent face)
  | _ => polyZero

private def globalCayleyChartPairProductPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul
      (polyAdd
        (cayleyChartBasePolynomial false
          (faceCayleyQuaternion0 extent face))
        (cayleyChartBasePolynomial true
          (faceCayleyQuaternion0 extent face)))
      (polyAdd
        (cayleyChartBasePolynomial false
          (faceCayleyQuaternion1 extent face))
        (cayleyChartBasePolynomial true
          (faceCayleyQuaternion1 extent face))))
    (polyMul
      (polyAdd
        (cayleyChartBasePolynomial false
          (faceCayleyQuaternion2 extent face))
        (cayleyChartBasePolynomial true
          (faceCayleyQuaternion2 extent face)))
      (polyAdd
        (cayleyChartBasePolynomial false
          (faceCayleyQuaternion3 extent face))
        (cayleyChartBasePolynomial true
          (faceCayleyQuaternion3 extent face))))

private theorem globalCayleyChartPartition_coeff_pairProduct
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyChartPartitionPolynomial extent face)
      (globalCayleyChartPairProductPolynomial extent face) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    chartSumExpr chartPairProductExpr chartSum_normalized
    (chartEnvironment extent face)
  have hshape : RatPolyCoeffEqv
      (globalCayleyChartPartitionPolynomial extent face)
      (polyAdd
        (globalCayleyChartPairProductPolynomial extent face) polyZero) := by
    simpa [globalCayleyChartPartitionPolynomial,
      globalCayleyChartPairProductPolynomial, finitePolySum,
      chartSumExpr, chartPairProductExpr, chartWeightExpr, chartBaseExpr,
      fourCayleyChartTable, chartEnvironment,
      globalCayleyChartWeightPolynomial] using h
  exact hshape.trans
    (RatPolyCoeffEqv.add_zero
      (globalCayleyChartPairProductPolynomial extent face))

/-- The sixteen positive chart weights form an exact coefficientwise
partition of one. -/
theorem globalCayleyChartPartition_coeff_one
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyChartPartitionPolynomial extent face) polyOne := by
  have h0 := cayleyChartBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion0 extent face)
  have h1 := cayleyChartBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion1 extent face)
  have h2 := cayleyChartBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion2 extent face)
  have h3 := cayleyChartBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion3 extent face)
  have h01 := (h0.mul h1).trans (RatPolyCoeffEqv.one_mul polyOne)
  have h23 := (h2.mul h3).trans (RatPolyCoeffEqv.one_mul polyOne)
  exact (globalCayleyChartPartition_coeff_pairProduct extent face).trans
    ((h01.mul h23).trans (RatPolyCoeffEqv.one_mul polyOne))

private def finiteCertificateSum {Index : Type} {blocks : Nat}
    (polynomial : Index → RatPoly)
    (certificate : ∀ index, Certificate blocks (polynomial index)) :
    ∀ items : List Index,
      Certificate blocks (finitePolySum polynomial items)
  | [] => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | index :: items =>
      (certificate index).add
        (finiteCertificateSum polynomial certificate items)

/-- The full partition polynomial is itself certificate-positive before its
coefficientwise normalization to one is used. -/
def globalCayleyChartPartition_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyChartPartitionPolynomial extent face) :=
  finiteCertificateSum
    (globalCayleyChartWeightPolynomial extent face)
    (globalCayleyChartWeight_certificate extent face)
    fourCayleyChartTable

/-- Under the unchanged normalized ORIGINAL action the sixteen-chart
partition has expectation exactly one. -/
theorem globalCayleyChartPartition_expectation_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (halfTime : Nat) (face : Z4Plaq) :
    CReal.Equiv
      (expectation w hw0 hw1 halfTime
        (globalCayleyChartPartitionPolynomial
          (centralExtent halfTime) face))
      CReal.cone :=
  (expectation_congr w hw0 hw1 halfTime
    (globalCayleyChartPartition_coeff_one
      (centralExtent halfTime) face)).trans
    (expectation_one w hw0 hw1 halfTime)

/-- Product of the four Cayley denominators after applying one fixed central
sign chart. -/
def globalCayleySignedChartDenominatorProduct
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul
      (cayleyChartDenominatorPolynomial
        (signedChartQuaternion chart.south0
          (faceCayleyQuaternion0 extent face)))
      (cayleyChartDenominatorPolynomial
        (signedChartQuaternion chart.south1
          (faceCayleyQuaternion1 extent face))))
    (polyMul
      (cayleyChartDenominatorPolynomial
        (signedChartQuaternion chart.south2
          (faceCayleyQuaternion2 extent face)))
      (cayleyChartDenominatorPolynomial
        (signedChartQuaternion chart.south3
          (faceCayleyQuaternion3 extent face))))

private theorem polyConst_coeff_smul (coefficient : Q') :
    RatPolyCoeffEqv (polyConst coefficient)
      (polySmul coefficient polyOne) := by
  intro weight
  change coefficient * weight [] + 0 ≈
    (coefficient * 1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv coefficient)))
    (Q'.eqv_refl 0)

/-- Every fixed signed common denominator product is exactly `16` times its
positive chart weight.  This is the polynomial interface consumed by the
existing fixed-sign Cayley clearing theorem. -/
theorem globalCayleySignedChartDenominatorProduct_coeff_weight
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySignedChartDenominatorProduct extent face chart)
      (polyMul (polySmul 16 polyOne)
        (globalCayleyChartWeightPolynomial extent face chart)) := by
  let q0 := faceCayleyQuaternion0 extent face
  let q1 := faceCayleyQuaternion1 extent face
  let q2 := faceCayleyQuaternion2 extent face
  let q3 := faceCayleyQuaternion3 extent face
  let b0 := cayleyChartBasePolynomial chart.south0 q0
  let b1 := cayleyChartBasePolynomial chart.south1 q1
  let b2 := cayleyChartBasePolynomial chart.south2 q2
  let b3 := cayleyChartBasePolynomial chart.south3 q3
  have h0 := cayleyChartDenominatorPolynomial_coeff_double_base
    (signedChartQuaternion chart.south0 q0)
  have h1 := cayleyChartDenominatorPolynomial_coeff_double_base
    (signedChartQuaternion chart.south1 q1)
  have h2 := cayleyChartDenominatorPolynomial_coeff_double_base
    (signedChartQuaternion chart.south2 q2)
  have h3 := cayleyChartDenominatorPolynomial_coeff_double_base
    (signedChartQuaternion chart.south3 q3)
  have hconst : RatPolyCoeffEqv
      (polySmul 2 polyOne) (polyConst 2) :=
    (polyConst_coeff_smul 2).symm
  have hd0 := h0.trans (hconst.mul (RatPolyCoeffEqv.refl b0))
  have hd1 := h1.trans (hconst.mul (RatPolyCoeffEqv.refl b1))
  have hd2 := h2.trans (hconst.mul (RatPolyCoeffEqv.refl b2))
  have hd3 := h3.trans (hconst.mul (RatPolyCoeffEqv.refl b3))
  have hnormalized : RatPolyCoeffEqv
      (polyMul
        (polyMul (polyMul (polyConst 2) b0) (polyMul (polyConst 2) b1))
        (polyMul (polyMul (polyConst 2) b2) (polyMul (polyConst 2) b3)))
      (polyMul (polyConst 16)
        (polyMul (polyMul b0 b1) (polyMul b2 b3))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul
        (.mul (.mul (.const 2) (.var 0))
          (.mul (.const 2) (.var 1)))
        (.mul (.mul (.const 2) (.var 2))
          (.mul (.const 2) (.var 3))))
      (.mul (.const 16)
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.var 3))))
      (by decide)
      (fun | 0 => b0 | 1 => b1 | 2 => b2 | _ => b3)
  have hright : RatPolyCoeffEqv
      (polyMul (polyConst 16)
        (polyMul (polyMul b0 b1) (polyMul b2 b3)))
      (polyMul (polySmul 16 polyOne)
        (polyMul (polyMul b0 b1) (polyMul b2 b3))) :=
    (polyConst_coeff_smul 16).mul (RatPolyCoeffEqv.refl _)
  simpa [globalCayleySignedChartDenominatorProduct,
    globalCayleyChartWeightPolynomial, cayleyChartBasePolynomial,
    q0, q1, q2, q3, b0, b1, b2, b3] using
    ((hd0.mul hd1).mul (hd2.mul hd3)).trans
      (hnormalized.trans hright)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.supported_signedChartQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.haarNorm_signedChartQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.cayleyChartBasePolynomial_pair_coeff_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.globalCayleyChartWeight_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.globalCayleyChartPartition_coeff_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.globalCayleyChartPartition_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.globalCayleyChartPartition_expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition.globalCayleySignedChartDenominatorProduct_coeff_weight
