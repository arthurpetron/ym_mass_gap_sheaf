/-
The one-block, shared-coordinate cube norm-defect certificate.

For any four rational cube coordinates (including zero and corners), the
six-square Gram identity below constructs a positive certificate on the
ORIGINAL Haar carrier. Carrier equalities hold under arbitrary polynomial
insertions; positivity is preserved under supported square or Certificate-
positive insertions, not arbitrary signed insertions. This is not a
pointwise-to-Haar axiom and does not yet perform the joint Bernstein average.
-/

import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

namespace YMGap.Continuum.QuaternionHaarCubeNormDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

private def sq (p : RatPoly) : RatPoly := polyMul p p
private def sum4 (a b c d : RatPoly) : RatPoly :=
  polyAdd a (polyAdd b (polyAdd c d))
private def diff (a b : RatPoly) : RatPoly := polyAdd a (polyNeg b)

private def esq (p : PolyExpr) : PolyExpr := .mul p p
private def esum4 (a b c d : PolyExpr) : PolyExpr :=
  .add a (.add b (.add c d))
private def ediff (a b : PolyExpr) : PolyExpr := .add a (.neg b)

/-- Four raw rational coordinates, with no normalization or nonzero guard. -/
abbrev CubeNode := Fin 4 → Q'

def nodeCoord (r : CubeNode) (i : Fin 4) : RatPoly := cap (r i)
def sphereCoord (i : Fin 4) : RatPoly := polyVar i.val
def coordDifference (r : CubeNode) (i : Fin 4) : RatPoly :=
  diff (nodeCoord r i) (sphereCoord i)
def coordSum (r : CubeNode) (i : Fin 4) : RatPoly :=
  polyAdd (nodeCoord r i) (sphereCoord i)

private def i0 : Fin 4 := ⟨0, by decide⟩
private def i1 : Fin 4 := ⟨1, by decide⟩
private def i2 : Fin 4 := ⟨2, by decide⟩
private def i3 : Fin 4 := ⟨3, by decide⟩

/-- The raw cube-to-sphere squared discrepancy, before any averaging. -/
def discrepancy (r : CubeNode) : RatPoly :=
  sum4 (sq (coordDifference r i0)) (sq (coordDifference r i1))
    (sq (coordDifference r i2)) (sq (coordDifference r i3))

def nodeNorm (r : CubeNode) : RatPoly :=
  sum4 (sq (nodeCoord r i0)) (sq (nodeCoord r i1))
    (sq (nodeCoord r i2)) (sq (nodeCoord r i3))

/-- The exact rational squared norm of the raw, possibly zero, cube node. -/
def nodeNormScalar (r : CubeNode) : Q' :=
  r i0 * r i0 + (r i1 * r i1 + (r i2 * r i2 + r i3 * r i3))

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change Q'.eqv ((-(a*1))*weight []+0) (((-a)*1)*weight []+0)
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1)))
    (Q'.eqv_refl _)

private theorem cap_sum4 (a b c d : Q') :
    RatPolyCoeffEqv (sum4 (cap a) (cap b) (cap c) (cap d))
      (cap (a + (b + (c + d)))) := by
  exact (((RatPolyCoeffEqv.refl (cap a)).add
      ((RatPolyCoeffEqv.refl (cap b)).add (cap_add c d))).trans
    (((RatPolyCoeffEqv.refl (cap a)).add (cap_add b (c+d))).trans
      (cap_add a (b+(c+d)))))

/-- The literal polynomial node norm is exactly the rational scalar node norm. -/
theorem nodeNorm_cap (r : CubeNode) :
    RatPolyCoeffEqv (nodeNorm r) (cap (nodeNormScalar r)) := by
  exact ((cap_mul (r i0) (r i0)).add
    ((cap_mul (r i1) (r i1)).add
      ((cap_mul (r i2) (r i2)).add (cap_mul (r i3) (r i3))))).trans
    (cap_sum4 _ _ _ _)

private def sphereNorm : RatPoly :=
  sum4 (sq (sphereCoord i0)) (sq (sphereCoord i1))
    (sq (sphereCoord i2)) (sq (sphereCoord i3))

/-- Squared defect of the actual raw node, without repairing it to the sphere. -/
def normDefect (r : CubeNode) : RatPoly :=
  sq (diff (nodeNorm r) polyOne)

/-- In particular, the defect is the requested constant cap
`cap ((‖r‖²-1)^2)`; no normalization of `r` is presumed. -/
theorem normDefect_cap (r : CubeNode) :
    RatPolyCoeffEqv (normDefect r)
      (cap ((nodeNormScalar r + -(1 : Q')) *
        (nodeNormScalar r + -(1 : Q')))) := by
  have hfirst : RatPolyCoeffEqv (diff (nodeNorm r) polyOne)
      (diff (cap (nodeNormScalar r)) (cap 1)) :=
    (nodeNorm_cap r).add
      (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.one_smul polyOne).symm))
  have hsecond : RatPolyCoeffEqv
      (diff (cap (nodeNormScalar r)) (cap 1))
      (cap (nodeNormScalar r + -(1 : Q'))) :=
    ((RatPolyCoeffEqv.refl _).add (cap_neg 1)).trans
      (cap_add (nodeNormScalar r) (-1))
  have hbase := hfirst.trans hsecond
  exact (hbase.mul hbase).trans
    (cap_mul (nodeNormScalar r + -1) (nodeNormScalar r + -1))

/-- The target positive polynomial: `16 Σ_i (r_i-x_i)^2-(‖r‖²-1)^2`. -/
def defectDiscrepancy (r : CubeNode) : RatPoly :=
  diff (polyMul (cap 16) (discrepancy r)) (normDefect r)

private def dot4 (d0 d1 d2 d3 s0 s1 s2 s3 : RatPoly) : RatPoly :=
  sum4 (polyMul d0 s0) (polyMul d1 s1) (polyMul d2 s2) (polyMul d3 s3)

private def pair (a b : RatPoly) : RatPoly := sq (diff a b)

private def pairSum (a b c d : RatPoly) : RatPoly :=
  polyAdd (pair a b) (polyAdd (pair a c) (polyAdd (pair a d)
    (polyAdd (pair b c) (polyAdd (pair b d) (pair c d)))))

private def gramRight (d0 d1 d2 d3 s0 s1 s2 s3 : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (cap 4)
      (sum4 (polyMul (sq d0) (gap 4 s0))
        (polyMul (sq d1) (gap 4 s1))
        (polyMul (sq d2) (gap 4 s2))
        (polyMul (sq d3) (gap 4 s3))))
    (pairSum (polyMul d0 s0) (polyMul d1 s1)
      (polyMul d2 s2) (polyMul d3 s3))

private def edot4 (d0 d1 d2 d3 s0 s1 s2 s3 : PolyExpr) : PolyExpr :=
  esum4 (.mul d0 s0) (.mul d1 s1) (.mul d2 s2) (.mul d3 s3)
private def epair (a b : PolyExpr) : PolyExpr := esq (ediff a b)
private def epairSum (a b c d : PolyExpr) : PolyExpr :=
  .add (epair a b) (.add (epair a c) (.add (epair a d)
    (.add (epair b c) (.add (epair b d) (epair c d)))))
private def egap4 (s : PolyExpr) : PolyExpr := ediff (.const 4) (esq s)
private def egramRight (d0 d1 d2 d3 s0 s1 s2 s3 : PolyExpr) : PolyExpr :=
  .add
    (.mul (.const 4)
      (esum4 (.mul (esq d0) (egap4 s0)) (.mul (esq d1) (egap4 s1))
        (.mul (esq d2) (egap4 s2)) (.mul (esq d3) (egap4 s3))))
    (epairSum (.mul d0 s0) (.mul d1 s1) (.mul d2 s2) (.mul d3 s3))

/-- The exact four-term Gram decomposition; all six pair squares are retained. -/
private theorem gram_identity (d0 d1 d2 d3 s0 s1 s2 s3 : RatPoly) :
    RatPolyCoeffEqv
      (diff (polyMul (cap 16) (sum4 (sq d0) (sq d1) (sq d2) (sq d3)))
        (sq (dot4 d0 d1 d2 d3 s0 s1 s2 s3)))
      (gramRight d0 d1 d2 d3 s0 s1 s2 s3) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (ediff (.mul (.const 16)
      (esum4 (esq (.var 0)) (esq (.var 1)) (esq (.var 2)) (esq (.var 3))))
      (esq (edot4 (.var 0) (.var 1) (.var 2) (.var 3)
        (.var 4) (.var 5) (.var 6) (.var 7))))
    (egramRight (.var 0) (.var 1) (.var 2) (.var 3)
      (.var 4) (.var 5) (.var 6) (.var 7))
    (by decide)
    (fun | 0 => d0 | 1 => d1 | 2 => d2 | 3 => d3
         | 4 => s0 | 5 => s1 | 6 => s2 | _ => s3)

private theorem supported_neg {p : RatPoly}
    (hp : SupportedQuaternionBlocks 1 p) : SupportedQuaternionBlocks 1 (polyNeg p) := by
  intro t ht
  obtain ⟨u, hu, he⟩ := List.mem_map.mp ht
  rw [← he]
  exact hp u hu

private def differenceSupported (r : CubeNode) (i : Fin 4) :
    SupportedQuaternionBlocks 1 (coordDifference r i) :=
  supported_add (SquareBound.constant 1 (r i)).support
    (supported_neg (coordinateSquareBound 1 i.val (by omega)).support)

private theorem cap_four (r : CubeNode) (i : Fin 4)
    (hr : r i * r i ≤ (1 : Q')) :
    sumBound (r i * r i) 1 ≤ (4 : Q') := by
  have h := Q'.add_le_add
    (Q'.add_le_add hr hr)
    (Q'.add_le_add (Q'.le_refl' (1 : Q')) (Q'.le_refl' (1 : Q')))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide :
    Q'.eqv (sumBound (1 : Q') 1) 4))

/-- Actual coordinate cap `4-(r_i+x_i)^2`, with no disjointness premise. -/
def coordSumBound (r : CubeNode) (i : Fin 4)
    (hr : r i * r i ≤ (1 : Q')) : SquareBound 1 (coordSum r i) 4 := by
  let P := (SquareBound.constant 1 (r i)).add
    (coordinateSquareBound 1 i.val (by omega))
  have hcap := cap_four r i hr
  have hdelta : (0 : Q') ≤ 4 + -(sumBound (r i * r i) 1) :=
    Q'.sub_nonneg_of_le hcap
  have he : Q'.eqv (sumBound (r i * r i) 1 +
      (4 + -(sumBound (r i * r i) 1))) 4 :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 4) (.neg (.var 0))))
      (.const 4) (by decide) (fun _ => sumBound (r i * r i) 1)
  exact (P.raise _ hdelta).changeCap he

private def pairCertificate (a b : RatPoly)
    (ha : SupportedQuaternionBlocks 1 a)
    (hb : SupportedQuaternionBlocks 1 b) : Certificate 1 (pair a b) :=
  .square (diff a b) (supported_add ha (supported_neg hb))

private def gramCertificate (d0 d1 d2 d3 s0 s1 s2 s3 : RatPoly)
    (hd0 : SupportedQuaternionBlocks 1 d0)
    (hd1 : SupportedQuaternionBlocks 1 d1)
    (hd2 : SupportedQuaternionBlocks 1 d2)
    (hd3 : SupportedQuaternionBlocks 1 d3)
    (S0 : SquareBound 1 s0 4) (S1 : SquareBound 1 s1 4)
    (S2 : SquareBound 1 s2 4) (S3 : SquareBound 1 s3 4) :
    Certificate 1
      (diff (polyMul (cap 16) (sum4 (sq d0) (sq d1) (sq d2) (sq d3)))
        (sq (dot4 d0 d1 d2 d3 s0 s1 s2 s3))) := by
  let a := polyMul d0 s0
  let b := polyMul d1 s1
  let c := polyMul d2 s2
  let d := polyMul d3 s3
  have ha : SupportedQuaternionBlocks 1 a := supported_polyMul hd0 S0.support
  have hb : SupportedQuaternionBlocks 1 b := supported_polyMul hd1 S1.support
  have hc : SupportedQuaternionBlocks 1 c := supported_polyMul hd2 S2.support
  have hd : SupportedQuaternionBlocks 1 d := supported_polyMul hd3 S3.support
  have hgap : Certificate 1 (gramRight d0 d1 d2 d3 s0 s1 s2 s3) :=
    .add
      (.ofCoeff (cap_mul_left 4 _)
        (.smul 4 (by decide)
          (.add (Certificate.multiplySquare d0 hd0 S0.certificate)
            (.add (Certificate.multiplySquare d1 hd1 S1.certificate)
              (.add (Certificate.multiplySquare d2 hd2 S2.certificate)
                (Certificate.multiplySquare d3 hd3 S3.certificate))))))
      (.add (pairCertificate a b ha hb)
        (.add (pairCertificate a c ha hc)
          (.add (pairCertificate a d ha hd)
            (.add (pairCertificate b c hb hc)
              (.add (pairCertificate b d hb hd)
                (pairCertificate c d hc hd))))))
  exact .ofCoeff (gram_identity d0 d1 d2 d3 s0 s1 s2 s3) hgap

private theorem dot_node_sphere (r : CubeNode) :
    RatPolyCoeffEqv
      (dot4 (coordDifference r i0) (coordDifference r i1)
        (coordDifference r i2) (coordDifference r i3)
        (coordSum r i0) (coordSum r i1) (coordSum r i2) (coordSum r i3))
      (diff (nodeNorm r) sphereNorm) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (edot4 (ediff (.var 0) (.var 4)) (ediff (.var 1) (.var 5))
      (ediff (.var 2) (.var 6)) (ediff (.var 3) (.var 7))
      (.add (.var 0) (.var 4)) (.add (.var 1) (.var 5))
      (.add (.var 2) (.var 6)) (.add (.var 3) (.var 7)))
    (ediff (esum4 (esq (.var 0)) (esq (.var 1)) (esq (.var 2)) (esq (.var 3)))
      (esum4 (esq (.var 4)) (esq (.var 5)) (esq (.var 6)) (esq (.var 7))))
    (by decide)
    (fun | 0 => nodeCoord r i0 | 1 => nodeCoord r i1
         | 2 => nodeCoord r i2 | 3 => nodeCoord r i3
         | 4 => sphereCoord i0 | 5 => sphereCoord i1
         | 6 => sphereCoord i2 | _ => sphereCoord i3)

private theorem sphereNorm_one : HaarCarrierEqv 1 sphereNorm polyOne := by
  change HaarCarrierEqv 1
    (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0)) polyOne
  exact haarNorm_coordinate (by decide : 0 < 1)

private theorem dot_normDefect (r : CubeNode) :
    HaarCarrierEqv 1
      (sq (dot4 (coordDifference r i0) (coordDifference r i1)
        (coordDifference r i2) (coordDifference r i3)
        (coordSum r i0) (coordSum r i1) (coordSum r i2) (coordSum r i3)))
      (normDefect r) := by
  have hd : HaarCarrierEqv 1
      (dot4 (coordDifference r i0) (coordDifference r i1)
        (coordDifference r i2) (coordDifference r i3)
        (coordSum r i0) (coordSum r i1) (coordSum r i2) (coordSum r i3))
      (diff (nodeNorm r) polyOne) :=
    HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (dot_node_sphere r))
      (HaarCarrierEqv.add (HaarCarrierEqv.refl 1 (nodeNorm r))
        (HaarCarrierEqv.neg sphereNorm_one))
  exact HaarCarrierEqv.mul hd hd

/-- Constructed one-block certificate for every rational cube node. The four
coordinates share the SAME Haar block; zero and all cube corners are included.
Only the explicit guards `r_i²≤1` are used. -/
def defectCertificate (r : CubeNode)
    (hr : ∀ i : Fin 4, r i * r i ≤ (1 : Q')) :
    Certificate 1 (defectDiscrepancy r) := by
  let d0 := coordDifference r i0
  let d1 := coordDifference r i1
  let d2 := coordDifference r i2
  let d3 := coordDifference r i3
  let s0 := coordSum r i0
  let s1 := coordSum r i1
  let s2 := coordSum r i2
  let s3 := coordSum r i3
  have G := gramCertificate d0 d1 d2 d3 s0 s1 s2 s3
    (differenceSupported r i0) (differenceSupported r i1)
    (differenceSupported r i2) (differenceSupported r i3)
    (coordSumBound r i0 (hr i0)) (coordSumBound r i1 (hr i1))
    (coordSumBound r i2 (hr i2)) (coordSumBound r i3 (hr i3))
  exact .transport
    (HaarCarrierEqv.add (HaarCarrierEqv.refl 1 (polyMul (cap 16) (discrepancy r)))
      (HaarCarrierEqv.symm (HaarCarrierEqv.neg (dot_normDefect r)))) G

/-- The produced certificate gives the original rational Haar inequality;
the joint Bernstein average is a separate, still-open finite algebra step. -/
theorem defect_haar_nonnegative (r : CubeNode)
    (hr : ∀ i : Fin 4, r i * r i ≤ (1 : Q')) :
    (0 : Q') ≤ quaternionHaar 1 (defectDiscrepancy r) :=
  (defectCertificate r hr).haar_nonnegative

end YMGap.Continuum.QuaternionHaarCubeNormDefect

#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.CubeNode
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.nodeCoord
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.sphereCoord
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.coordDifference
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.coordSum
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.discrepancy
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.nodeNorm
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.nodeNormScalar
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.nodeNorm_cap
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.normDefect
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.normDefect_cap
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.defectDiscrepancy
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.coordSumBound
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.defectCertificate
#print axioms YMGap.Continuum.QuaternionHaarCubeNormDefect.defect_haar_nonnegative
