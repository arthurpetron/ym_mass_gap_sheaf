/-
# A global square remainder for the bounded ORIGINAL bulk deficit

For every literal plaquette quaternion `q = (r,i,j,k)`, unit radius gives the
division-free identity

  2 * (1 - r) = (i^2 + j^2 + k^2) + (1 - r)^2.

The first term is the global vector-coordinate quadratic jet and the second
is an explicit scalar-square remainder.  This file sums that identity with
the existing positive bulk coefficients on the SAME ORIGINAL Haar carrier.
Both summands receive constructive square certificates, so their actual
finite middle ratios are nonnegative and bounded above by the full bounded
deficit ratio.  In particular, the actual finite OWN center splits into the
jet center plus a nonnegative remainder center.

No chart denominator, pointwise substitution, FREE Gaussian comparison,
cutoff removal, continuum limit, Hamiltonian gap, or Clay mass gap is claimed.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.QuaternionHaarGammaFiniteSum

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
  (middleRatio_add middleRatio_carrier_congr middleRatio_congr
    middleRatio_certificate_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add finitePolySum_coeff_congr finitePolySum_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkBoundedSource
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem supported_neg_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

/-- The scalar half-deficit `1-r` of one literal plaquette quaternion. -/
def plaquetteScalarDeficit (width : Nat) (face : Z4Plaq) : RatPoly :=
  polyAdd polyOne (polyNeg (plaquette width face).scalar)

/-- The sum of squares of the three vector coordinates of one plaquette. -/
def plaquetteVectorQuadraticJet (width : Nat) (face : Z4Plaq) : RatPoly :=
  let q := plaquette width face
  polyAdd (polyMul q.iPart q.iPart)
    (polyAdd (polyMul q.jPart q.jPart) (polyMul q.kPart q.kPart))

/-- The explicit square remainder `(1-r)^2`. -/
def plaquetteScalarSquareRemainder (width : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul (plaquetteScalarDeficit width face) (plaquetteScalarDeficit width face)

/-- The full bounded fundamental trace deficit `2-chi_1 = 2(1-r)`. -/
def plaquetteTraceDeficit (width : Nat) (face : Z4Plaq) : RatPoly :=
  polyAdd (polySmul 2 polyOne)
    (polySmul (-1) (characterPolynomial (plaquette width face).scalar 1))

theorem plaquetteScalarDeficit_supported
    (width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq) :
    SupportedQuaternionBlocks blocks (plaquetteScalarDeficit width face) := by
  exact supported_add (supported_one blocks)
    (supported_neg_local (plaquette_supported width blocks hroom face).scalar)

private theorem smul_neg_local (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) polynomial) (polyNeg polynomial) :=
  (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left (-1) polynomial).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => polynomial))

private theorem two_smul_add (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul 2 polynomial) (polyAdd polynomial polynomial) :=
  (RatPolyCoeffEqv.smul_coefficient (by decide : (2 : Q') ≈ 1 + 1) polynomial).trans
    ((RatPolyCoeffEqv.add_smul_same 1 1 polynomial).symm.trans
      ((RatPolyCoeffEqv.one_smul polynomial).add
        (RatPolyCoeffEqv.one_smul polynomial)))

private theorem traceDeficit_algebra (scalar : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul 2 polyOne) (polySmul (-1) (polySmul 2 scalar)))
      (polyAdd polyOne
        (polyAdd polyOne (polyAdd (polyNeg scalar) (polyNeg scalar)))) := by
  have hnegative : RatPolyCoeffEqv
      (polySmul (-1) (polySmul 2 scalar))
      (polyAdd (polyNeg scalar) (polyNeg scalar)) :=
    ((two_smul_add scalar).smul (-1)).trans
      ((RatPolyCoeffEqv.smul_add (-1) scalar scalar).trans
        ((smul_neg_local scalar).add (smul_neg_local scalar)))
  exact ((two_smul_add polyOne).add hnegative).trans
    (RatPolyCoeffEqv.add_assoc polyOne polyOne
      (polyAdd (polyNeg scalar) (polyNeg scalar)))

private theorem vectorSquareRemainder_algebra
    (scalar iPart jPart kPart : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul iPart iPart)
          (polyAdd (polyMul jPart jPart) (polyMul kPart kPart)))
        (polyMul (polyAdd polyOne (polyNeg scalar))
          (polyAdd polyOne (polyNeg scalar))))
      (polyAdd
        (polyAdd (polyMul scalar scalar)
          (polyAdd (polyMul iPart iPart)
            (polyAdd (polyMul jPart jPart) (polyMul kPart kPart))))
        (polyAdd polyOne (polyAdd (polyNeg scalar) (polyNeg scalar)))) := by
  have hring : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul iPart iPart)
          (polyAdd (polyMul jPart jPart) (polyMul kPart kPart)))
        (polyMul (polyAdd polyOne (polyNeg scalar))
          (polyAdd polyOne (polyNeg scalar))))
      (polyAdd
        (polyAdd (polyMul scalar scalar)
          (polyAdd (polyMul iPart iPart)
            (polyAdd (polyMul jPart jPart) (polyMul kPart kPart))))
        (polyAdd (polyMul polyOne polyOne)
          (polyAdd (polyNeg (polyMul polyOne scalar))
            (polyNeg (polyMul scalar polyOne))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
        (.mul (.add (.var 4) (.neg (.var 0)))
          (.add (.var 4) (.neg (.var 0)))))
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.add (.mul (.var 4) (.var 4))
          (.add (.neg (.mul (.var 4) (.var 0)))
            (.neg (.mul (.var 0) (.var 4))))))
      (by decide)
      (fun | 0 => scalar | 1 => iPart | 2 => jPart | 3 => kPart | _ => polyOne)
  exact hring.trans ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.mul_one polyOne).add
      ((RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_mul scalar)).add
        (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_one scalar)))))

/-- Unit radius converts the full bounded deficit into a vector quadratic
plus a literal scalar square under every later Haar insertion. -/
theorem plaquetteTraceDeficit_decomposition
    (width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq) :
    HaarCarrierEqv blocks
      (plaquetteTraceDeficit width face)
      (polyAdd (plaquetteVectorQuadraticJet width face)
        (plaquetteScalarSquareRemainder width face)) := by
  let q := plaquette width face
  let rest := polyAdd polyOne (polyAdd (polyNeg q.scalar) (polyNeg q.scalar))
  have hleft : RatPolyCoeffEqv
      (plaquetteTraceDeficit width face) (polyAdd polyOne rest) := by
    change RatPolyCoeffEqv
      (polyAdd (polySmul 2 polyOne)
        (polySmul (-1) (polySmul 2 (plaquette width face).scalar)))
      (polyAdd polyOne
        (polyAdd polyOne
          (polyAdd (polyNeg (plaquette width face).scalar)
            (polyNeg (plaquette width face).scalar))))
    exact traceDeficit_algebra (plaquette width face).scalar
  have hright : RatPolyCoeffEqv
      (polyAdd (plaquetteVectorQuadraticJet width face)
        (plaquetteScalarSquareRemainder width face))
      (polyAdd (polyQuaternionNorm q) rest) := by
    unfold plaquetteVectorQuadraticJet plaquetteScalarSquareRemainder
      plaquetteScalarDeficit polyQuaternionNorm rest q
    exact vectorSquareRemainder_algebra
      (plaquette width face).scalar (plaquette width face).iPart
      (plaquette width face).jPart (plaquette width face).kPart
  exact (RatPolyCoeffEqv.haarCarrier hleft).trans
    ((HaarCarrierEqv.add (plaquette_unit width blocks hroom face)
        (HaarCarrierEqv.refl blocks rest)).symm.trans
      (RatPolyCoeffEqv.haarCarrier hright).symm)

def originalBulkTraceDeficit (s : Nat) (hs : 0 < s) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (plaquetteTraceDeficit (s * s) face))
    (bulkSourceFaces s)

def originalBulkVectorQuadraticJet (s : Nat) (hs : 0 < s) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (plaquetteVectorQuadraticJet (s * s) face))
    (bulkSourceFaces s)

def originalBulkScalarSquareRemainder (s : Nat) (hs : 0 < s) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (plaquetteScalarSquareRemainder (s * s) face))
    (bulkSourceFaces s)

private theorem finiteSum_carrier {Index : Type} (blocks : Nat)
    (left right : Index → RatPoly) :
    ∀ items : List Index,
      (∀ index, index ∈ items → HaarCarrierEqv blocks (left index) (right index)) →
      HaarCarrierEqv blocks (finitePolySum left items) (finitePolySum right items)
  | [], _ => .refl _ _
  | index :: items, h =>
      HaarCarrierEqv.add (h index List.mem_cons_self)
        (finiteSum_carrier blocks left right items
          (fun next hnext => h next (List.mem_cons_of_mem index hnext)))

/-- The positively weighted bulk deficit is exactly the sum of its vector jet
and scalar-square remainder on the same ORIGINAL carrier. -/
theorem originalBulkTraceDeficit_decomposition (s : Nat) (hs : 0 < s) :
    HaarCarrierEqv (N (s * s))
      (originalBulkTraceDeficit s hs)
      (polyAdd (originalBulkVectorQuadraticJet s hs)
        (originalBulkScalarSquareRemainder s hs)) := by
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      HaarCarrierEqv (N (s * s))
        (polySmul (bulkSourceCoefficient s hs face)
          (plaquetteTraceDeficit (s * s) face))
        (polySmul (bulkSourceCoefficient s hs face)
          (polyAdd (plaquetteVectorQuadraticJet (s * s) face)
            (plaquetteScalarSquareRemainder (s * s) face))) := by
    intro face _
    exact HaarCarrierEqv.smul (bulkSourceCoefficient s hs face)
      (plaquetteTraceDeficit_decomposition (s * s) (N (s * s))
        (Nat.le_refl _) face)
  have hsum := finiteSum_carrier (N (s * s)) _ _ (bulkSourceFaces s) hpoint
  have hdistribute := finitePolySum_coeff_congr
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (polyAdd (plaquetteVectorQuadraticJet (s * s) face)
        (plaquetteScalarSquareRemainder (s * s) face)))
    (fun face => polyAdd
      (polySmul (bulkSourceCoefficient s hs face)
        (plaquetteVectorQuadraticJet (s * s) face))
      (polySmul (bulkSourceCoefficient s hs face)
        (plaquetteScalarSquareRemainder (s * s) face)))
    (fun face => RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face) _ _)
    (bulkSourceFaces s)
  exact hsum.trans
    ((RatPolyCoeffEqv.haarCarrier hdistribute).trans
      (RatPolyCoeffEqv.haarCarrier
        (finitePolySum_add
          (fun face => polySmul (bulkSourceCoefficient s hs face)
            (plaquetteVectorQuadraticJet (s * s) face))
          (fun face => polySmul (bulkSourceCoefficient s hs face)
            (plaquetteScalarSquareRemainder (s * s) face))
          (bulkSourceFaces s))))

private theorem two_mul_add (left right : Q') :
    2 * (left + right) ≈ 2 * left + 2 * right := by
  exact poly_identity_of_normal_eq
    (.mul (.const 2) (.add (.var 0) (.var 1)))
    (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
    (by decide) (fun | 0 => left | _ => right)

private theorem finitePolySum_two_coefficients {Index : Type}
    (coefficient : Index → Q') : ∀ items : List Index,
    RatPolyCoeffEqv
      (finitePolySum (fun index => polySmul (2 * coefficient index) polyOne) items)
      (polySmul (2 * listQSum coefficient items) polyOne)
  | [] => (RatPolyCoeffEqv.zero_smul polyOne).symm
  | index :: items => by
      exact ((RatPolyCoeffEqv.refl _).add
          (finitePolySum_two_coefficients coefficient items)).trans
        ((RatPolyCoeffEqv.add_smul_same
            (2 * coefficient index) (2 * listQSum coefficient items) polyOne).trans
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.eqv_symm (two_mul_add (coefficient index)
              (listQSum coefficient items))) polyOne))

private theorem weighted_trace_split
    (width : Nat) (coefficient : Q') (face : Z4Plaq) :
    RatPolyCoeffEqv
      (polySmul coefficient (plaquetteTraceDeficit width face))
      (polyAdd
        (polySmul (2 * coefficient) polyOne)
        (polySmul (-1)
          (polySmul coefficient
            (characterPolynomial (plaquette width face).scalar 1)))) := by
  unfold plaquetteTraceDeficit
  refine (RatPolyCoeffEqv.smul_add coefficient _ _).trans ?_
  apply RatPolyCoeffEqv.add
  · exact (RatPolyCoeffEqv.smul_assoc coefficient 2 polyOne).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv coefficient 2) polyOne)
  · exact (RatPolyCoeffEqv.smul_assoc coefficient (-1) _).trans
      ((RatPolyCoeffEqv.smul_coefficient
          (Q'.mul_comm_eqv coefficient (-1)) _).trans
        (RatPolyCoeffEqv.smul_assoc (-1) coefficient _).symm)

private theorem originalBulkTraceDeficit_affine_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv (originalBulkTraceDeficit s hs)
      (polyAdd
        (polySmul (2 * originalBulkCoefficientSum s hs) polyOne)
        (polySmul (-1)
          (spatialSpan (s * s) (bulkSourceCoefficient s hs)
            (bulkSourceFaces s)))) := by
  have hsplit := finitePolySum_coeff_congr
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (plaquetteTraceDeficit (s * s) face))
    (fun face => polyAdd
      (polySmul (2 * bulkSourceCoefficient s hs face) polyOne)
      (polySmul (-1)
        (polySmul (bulkSourceCoefficient s hs face)
          (characterPolynomial (plaquette (s * s) face).scalar 1))))
    (fun face => weighted_trace_split (s * s) (bulkSourceCoefficient s hs face) face)
    (bulkSourceFaces s)
  refine hsplit.trans ((finitePolySum_add _ _ (bulkSourceFaces s)).trans ?_)
  exact (finitePolySum_two_coefficients (bulkSourceCoefficient s hs)
      (bulkSourceFaces s)).add
    (by
      unfold spatialSpan
      exact finitePolySum_smul (-1)
        (fun face => polySmul (bulkSourceCoefficient s hs face)
          (characterPolynomial (plaquette (s * s) face).scalar 1))
        (bulkSourceFaces s))

/-- The new finite trace-deficit sum is coefficientwise the already compiled
bounded physical deficit source. -/
theorem originalBulkDeficitExpression_jet_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv
      (sourcePolynomial (originalBulkDeficitExpression s hs))
      (originalBulkTraceDeficit s hs) :=
  (originalBulkDeficitExpression_source_pin s hs).trans
    (originalBulkTraceDeficit_affine_pin s hs).symm

private def finiteWeightedCertificate {Index : Type} {blocks : Nat}
    (coefficient : Index → Q') (polynomial : Index → RatPoly)
    (certificate : ∀ index, Certificate blocks (polynomial index)) :
    ∀ items : List Index,
      (∀ index, index ∈ items → (0 : Q') ≤ coefficient index) →
      Certificate blocks
        (finitePolySum (fun index => polySmul (coefficient index) (polynomial index)) items)
  | [], _ => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | index :: items, hnonnegative =>
      (Certificate.smul (coefficient index)
        (hnonnegative index List.mem_cons_self) (certificate index)).add
      (finiteWeightedCertificate coefficient polynomial certificate items
        (fun next hnext => hnonnegative next (List.mem_cons_of_mem index hnext)))

def originalBulkVectorQuadraticJet_certificate (s : Nat) (hs : 0 < s) :
    Certificate (N (s * s)) (originalBulkVectorQuadraticJet s hs) := by
  apply finiteWeightedCertificate
  · intro face
    have hsupport := plaquette_supported (s * s) (N (s * s)) (Nat.le_refl _) face
    exact (Certificate.square _ hsupport.iPart).add
      ((Certificate.square _ hsupport.jPart).add
        (Certificate.square _ hsupport.kPart))
  · intro face hface
    exact Q'.le_of_lt (bulkSourceCoefficient_pos hs hface)

def originalBulkScalarSquareRemainder_certificate (s : Nat) (hs : 0 < s) :
    Certificate (N (s * s)) (originalBulkScalarSquareRemainder s hs) := by
  apply finiteWeightedCertificate
  · intro face
    exact Certificate.square _
      (plaquetteScalarDeficit_supported (s * s) (N (s * s)) (Nat.le_refl _) face)
  · intro face hface
    exact Q'.le_of_lt (bulkSourceCoefficient_pos hs hface)

theorem originalBulkVectorQuadraticJet_middleRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    (0 : Q') ≤ middleRatio hw0 hw1 K (s * s) hK m n
      (originalBulkVectorQuadraticJet s hs) :=
  middleRatio_certificate_nonnegative hw0 hw1 K (s * s) hK m n
    (originalBulkVectorQuadraticJet_certificate s hs)

theorem originalBulkScalarSquareRemainder_middleRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    (0 : Q') ≤ middleRatio hw0 hw1 K (s * s) hK m n
      (originalBulkScalarSquareRemainder s hs) :=
  middleRatio_certificate_nonnegative hw0 hw1 K (s * s) hK m n
    (originalBulkScalarSquareRemainder_certificate s hs)

theorem originalBulkTraceDeficit_middleRatio_split {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    middleRatio hw0 hw1 K (s * s) hK m n (originalBulkTraceDeficit s hs) ≈
      middleRatio hw0 hw1 K (s * s) hK m n
          (originalBulkVectorQuadraticJet s hs) +
        middleRatio hw0 hw1 K (s * s) hK m n
          (originalBulkScalarSquareRemainder s hs) :=
  Q'.eqv_trans _ _ _
    (middleRatio_carrier_congr hw0 hw1 K (s * s) hK m n
      (originalBulkTraceDeficit_decomposition s hs))
    (middleRatio_add hw0 hw1 K (s * s) hK m n _ _)

theorem originalBulkScalarSquareRemainder_middleRatio_le_traceDeficit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    middleRatio hw0 hw1 K (s * s) hK m n
        (originalBulkScalarSquareRemainder s hs) ≤
      middleRatio hw0 hw1 K (s * s) hK m n
        (originalBulkTraceDeficit s hs) := by
  let jet := middleRatio hw0 hw1 K (s * s) hK m n
    (originalBulkVectorQuadraticJet s hs)
  let remainder := middleRatio hw0 hw1 K (s * s) hK m n
    (originalBulkScalarSquareRemainder s hs)
  have hjet : (0 : Q') ≤ jet :=
    originalBulkVectorQuadraticJet_middleRatio_nonnegative
      hw0 hw1 s hs K hK m n
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg remainder jet hjet)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv remainder jet))
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (originalBulkTraceDeficit_middleRatio_split
            hw0 hw1 s hs K hK m n))))

def originalBulkVectorQuadraticJetOwnMean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : Q' :=
  middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    (n + 1) n (originalBulkVectorQuadraticJet s hs)

def originalBulkScalarSquareRemainderOwnMean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : Q' :=
  middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    (n + 1) n (originalBulkScalarSquareRemainder s hs)

/-- The actual finite OWN center of the bounded deficit is exactly the jet
center plus the scalar-square remainder center. -/
theorem originalBulkDeficitOwnMean_jet_remainder_split {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkDeficitOwnMean hw0 hw1 s hs stage n ≈
      originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n +
        originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n := by
  unfold originalBulkDeficitOwnMean
    YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.expressionOwnMean
    originalBulkVectorQuadraticJetOwnMean originalBulkScalarSquareRemainderOwnMean
  exact Q'.eqv_trans _ _ _
    (middleRatio_congr hw0 hw1 _ _ _ _ _
      (originalBulkDeficitExpression_jet_source_pin s hs))
    (originalBulkTraceDeficit_middleRatio_split hw0 hw1 s hs _ _ _ _)

theorem originalBulkScalarSquareRemainderOwnMean_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n :=
  originalBulkScalarSquareRemainder_middleRatio_nonnegative
    hw0 hw1 s hs _ _ _ _

theorem originalBulkScalarSquareRemainderOwnMean_le_deficit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n ≤
      originalBulkDeficitOwnMean hw0 hw1 s hs stage n := by
  unfold originalBulkScalarSquareRemainderOwnMean originalBulkDeficitOwnMean
    YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.expressionOwnMean
  exact Q'.le_trans' _ _ _
    (originalBulkScalarSquareRemainder_middleRatio_le_traceDeficit
      hw0 hw1 s hs _ _ _ _)
    (Q'.le_of_eqv (Q'.eqv_symm
      (middleRatio_congr hw0 hw1 _ _ _ _ _
        (originalBulkDeficitExpression_jet_source_pin s hs))))

#print axioms plaquetteTraceDeficit_decomposition
#print axioms originalBulkTraceDeficit_decomposition
#print axioms originalBulkDeficitExpression_jet_source_pin
#print axioms originalBulkVectorQuadraticJet_certificate
#print axioms originalBulkScalarSquareRemainder_certificate
#print axioms originalBulkTraceDeficit_middleRatio_split
#print axioms originalBulkScalarSquareRemainder_middleRatio_le_traceDeficit
#print axioms originalBulkDeficitOwnMean_jet_remainder_split
#print axioms originalBulkScalarSquareRemainderOwnMean_nonnegative
#print axioms originalBulkScalarSquareRemainderOwnMean_le_deficit

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
