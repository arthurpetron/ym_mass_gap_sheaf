/-
# The original plaquette's own gradient in its common frame

At EVERY physical boundary slot the three actual LEFT scalar derivatives,
contracted with their signed common-frame vectors, synthesize -Im(P).
Only the prefix is Haar-unit; no unit-P hypothesis is needed. For a scalar
source c*X this velocity is -c*Im(P); the fundamental character is chi_1=2X,
so its source velocity is -2c*Im(P). A bracket diagnostic with TWO such
velocities scales by FOUR, not two. This finite synthesis does not supply
the original weighted mixed Hessian or its changing-family payment.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOwnVector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction

local instance : Mul PolyQuaternion := ⟨PolyQuaternion.mul⟩

def polynomialScale (a : RatPoly) (q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyMul a q.scalar, polyMul a q.iPart, polyMul a q.jPart, polyMul a q.kPart⟩

def quaternionAdd (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart, polyAdd p.kPart q.kPart⟩

def sum3 (a b c : PolyQuaternion) : PolyQuaternion := quaternionAdd a (quaternionAdd b c)

def negativeImaginary (q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyZero, polyNeg q.iPart, polyNeg q.jPart, polyNeg q.kPart⟩

private def component (q : PolyQuaternion) (i : Fin 3) : RatPoly :=
  match i.val with | 0 => q.iPart | 1 => q.jPart | _ => q.kPart
private theorem cases3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega
private def dot3 (a b c x y z : RatPoly) : RatPoly :=
  polyAdd (polyMul a x) (polyAdd (polyMul b y) (polyMul c z))
private def dotExpr (a b c x y z : PolyExpr) : PolyExpr :=
  .add (.mul a x) (.add (.mul b y) (.mul c z))
private def fEnv (f : PolyQuaternion) : Nat → RatPoly
  | 0 => f.scalar | 1 => f.iPart | 2 => f.jPart | 3 => f.kPart | _ => polyZero
private def square (x : Nat) : PolyExpr := .mul (.var x) (.var x)
private def twice (p : PolyExpr) : PolyExpr := .add p p

/- Columns of Hamilton conjugation by f, without imposing norm(f)=1. -/
private def rowExpr (i j : Fin 3) : PolyExpr :=
  match i.val, j.val with
  | 0, 0 => .add (.add (square 0) (square 1)) (.neg (.add (square 2) (square 3)))
  | 0, 1 => twice (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
  | 0, _ => twice (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 0) (.var 2))))
  | 1, 0 => twice (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
  | 1, 1 => .add (.add (square 0) (square 2)) (.neg (.add (square 1) (square 3)))
  | 1, _ => twice (.add (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 1)))
  | _, 0 => twice (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2)))
  | _, 1 => twice (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 1))))
  | _, _ => .add (.add (square 0) (square 3)) (.neg (.add (square 1) (square 2)))
private def rowEntry (f : PolyQuaternion) (i j : Fin 3) : RatPoly :=
  coeffEvalExpr (fEnv f) (rowExpr i j)
private def rowQuaternion (f : PolyQuaternion) (i : Fin 3) : PolyQuaternion :=
  ⟨polyZero, rowEntry f i 0, rowEntry f i 1, rowEntry f i 2⟩
private def basisExpr (i : Fin 3) : PolyQuaternionExpr :=
  ⟨.const 0, .const (if i.val=0 then 1 else 0),
    .const (if i.val=1 then 1 else 0), .const (if i.val=2 then 1 else 0)⟩
private def conjugatedExpr (i : Fin 3) : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (basisExpr i))
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))

private theorem conjugated_rows (f : PolyQuaternion) (i : Fin 3) :
    PolyQuaternionCoeffEqv ((f*imaginaryBasis i)*PolyQuaternion.conj f) (rowQuaternion f i) := by
  constructor
  · exact (coeffEvalExpr_eqv_of_normalize_eq (conjugatedExpr i).scalar (.const 0)
      (by rcases cases3 i with rfl | rfl | rfl <;> decide) (fEnv f)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)
  · exact coeffEvalExpr_eqv_of_normalize_eq (conjugatedExpr i).iPart (rowExpr i 0)
      (by rcases cases3 i with rfl | rfl | rfl <;> decide) (fEnv f)
  · exact coeffEvalExpr_eqv_of_normalize_eq (conjugatedExpr i).jPart (rowExpr i 1)
      (by rcases cases3 i with rfl | rfl | rfl <;> decide) (fEnv f)
  · exact coeffEvalExpr_eqv_of_normalize_eq (conjugatedExpr i).kPart (rowExpr i 2)
      (by rcases cases3 i with rfl | rfl | rfl <;> decide) (fEnv f)

private def gram (f : PolyQuaternion) (j k : Fin 3) : RatPoly :=
  dot3 (rowEntry f 0 j) (rowEntry f 1 j) (rowEntry f 2 j)
    (rowEntry f 0 k) (rowEntry f 1 k) (rowEntry f 2 k)
private def gramExpr (j k : Fin 3) : PolyExpr :=
  dotExpr (rowExpr 0 j) (rowExpr 1 j) (rowExpr 2 j)
    (rowExpr 0 k) (rowExpr 1 k) (rowExpr 2 k)
private def normSquaredExpr : PolyExpr :=
  .mul (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))
private theorem gram_exact (f : PolyQuaternion) (j k : Fin 3) :
    RatPolyCoeffEqv (gram f j k)
      (if j=k then polyMul (polyQuaternionNorm f) (polyQuaternionNorm f) else polyZero) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq (gramExpr j k)
    (if j=k then normSquaredExpr else .const 0)
    (by rcases cases3 j with rfl | rfl | rfl <;> rcases cases3 k with rfl | rfl | rfl <;> decide)
    (fEnv f)
  by_cases hjk : j=k
  · simpa only [if_pos hjk] using h
  · simp only [if_neg hjk]
    have h0 : RatPolyCoeffEqv (gram f j k) (coeffEvalExpr (fEnv f) (.const 0)) := by
      simpa only [if_neg hjk] using h
    exact h0.trans (RatPolyCoeffEqv.zero_smul polyOne)

private theorem column_synthesis (a b c d e f g h j u v w x y z : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyNeg (dot3 a b c x y z)) u)
        (polyAdd (polyMul (polyNeg (dot3 d e f x y z)) v)
          (polyMul (polyNeg (dot3 g h j x y z)) w)))
      (polyNeg (dot3 (dot3 a d g u v w) (dot3 b e h u v w) (dot3 c f j u v w) x y z)) := by
  let env : Nat → RatPoly
    | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | 7 => h
    | 8 => j | 9 => u | 10 => v | 11 => w | 12 => x | 13 => y | 14 => z | _ => polyZero
  exact coeffEvalExpr_eqv_of_normalize_eq
    (dotExpr (.neg (dotExpr (.var 0) (.var 1) (.var 2) (.var 12) (.var 13) (.var 14)))
      (.neg (dotExpr (.var 3) (.var 4) (.var 5) (.var 12) (.var 13) (.var 14)))
      (.neg (dotExpr (.var 6) (.var 7) (.var 8) (.var 12) (.var 13) (.var 14)))
      (.var 9) (.var 10) (.var 11))
    (.neg (dotExpr (dotExpr (.var 0) (.var 3) (.var 6) (.var 9) (.var 10) (.var 11))
      (dotExpr (.var 1) (.var 4) (.var 7) (.var 9) (.var 10) (.var 11))
      (dotExpr (.var 2) (.var 5) (.var 8) (.var 9) (.var 10) (.var 11))
      (.var 12) (.var 13) (.var 14))) (by decide) env

private theorem dot_congr {a a' b b' c c' : RatPoly} (x y z : RatPoly)
    (ha : RatPolyCoeffEqv a a') (hb : RatPolyCoeffEqv b b') (hc : RatPolyCoeffEqv c c') :
    RatPolyCoeffEqv (dot3 a b c x y z) (dot3 a' b' c' x y z) :=
  (RatPolyCoeffEqv.mul_right ha x).add
    ((RatPolyCoeffEqv.mul_right hb y).add (RatPolyCoeffEqv.mul_right hc z))
private theorem diagonal_dot (n : RatPoly) (p : PolyQuaternion) (k : Fin 3) :
    RatPolyCoeffEqv (dot3 (if (0:Fin 3)=k then n else polyZero)
      (if (1:Fin 3)=k then n else polyZero) (if (2:Fin 3)=k then n else polyZero)
      p.iPart p.jPart p.kPart) (polyMul n (component p k)) := by
  rcases cases3 k with rfl | rfl | rfl
  · exact RatPolyCoeffEqv.add_zero _
  · exact (RatPolyCoeffEqv.zero_add _).trans (RatPolyCoeffEqv.add_zero _)
  · exact (RatPolyCoeffEqv.zero_add _).trans (RatPolyCoeffEqv.zero_add _)

private theorem row_scalar (f p : PolyQuaternion) (i : Fin 3) :
    RatPolyCoeffEqv (rowQuaternion f i * p).scalar
      (polyNeg (dot3 (rowEntry f i 0) (rowEntry f i 1) (rowEntry f i 2) p.iPart p.jPart p.kPart)) :=
  RatPolyCoeffEqv.zero_add _
private theorem row_component_synthesis (f p : PolyQuaternion) (k : Fin 3) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (rowQuaternion f 0*p).scalar (rowEntry f 0 k))
        (polyAdd (polyMul (rowQuaternion f 1*p).scalar (rowEntry f 1 k))
          (polyMul (rowQuaternion f 2*p).scalar (rowEntry f 2 k))))
      (polyNeg (polyMul (polyMul (polyQuaternionNorm f) (polyQuaternionNorm f)) (component p k))) := by
  exact ((RatPolyCoeffEqv.mul_right (row_scalar f p 0) (rowEntry f 0 k)).add
    ((RatPolyCoeffEqv.mul_right (row_scalar f p 1) (rowEntry f 1 k)).add
      (RatPolyCoeffEqv.mul_right (row_scalar f p 2) (rowEntry f 2 k)))).trans
    ((column_synthesis (rowEntry f 0 0) (rowEntry f 0 1) (rowEntry f 0 2)
      (rowEntry f 1 0) (rowEntry f 1 1) (rowEntry f 1 2)
      (rowEntry f 2 0) (rowEntry f 2 1) (rowEntry f 2 2)
      (rowEntry f 0 k) (rowEntry f 1 k) (rowEntry f 2 k) p.iPart p.jPart p.kPart).trans
      (RatPolyCoeffEqv.neg ((dot_congr p.iPart p.jPart p.kPart
        (gram_exact f 0 k) (gram_exact f 1 k) (gram_exact f 2 k)).trans
        (diagonal_dot _ p k))))

private theorem scale_coeff {a b : RatPoly} {p q : PolyQuaternion}
    (ha : RatPolyCoeffEqv a b) (hq : PolyQuaternionCoeffEqv p q) :
    PolyQuaternionCoeffEqv (polynomialScale a p) (polynomialScale b q) :=
  ⟨ha.mul hq.scalar, ha.mul hq.iPart, ha.mul hq.jPart, ha.mul hq.kPart⟩
private theorem sum_coeff {a a' b b' c c' : PolyQuaternion}
    (ha : PolyQuaternionCoeffEqv a a') (hb : PolyQuaternionCoeffEqv b b')
    (hc : PolyQuaternionCoeffEqv c c') : PolyQuaternionCoeffEqv (sum3 a b c) (sum3 a' b' c') :=
  ⟨ha.scalar.add (hb.scalar.add hc.scalar), ha.iPart.add (hb.iPart.add hc.iPart),
    ha.jPart.add (hb.jPart.add hc.jPart), ha.kPart.add (hb.kPart.add hc.kPart)⟩
private def clearedNegativeImaginary (n : RatPoly) (p : PolyQuaternion) : PolyQuaternion :=
  ⟨polyZero, polyNeg (polyMul n p.iPart), polyNeg (polyMul n p.jPart), polyNeg (polyMul n p.kPart)⟩
private def conjugatedBasis (f : PolyQuaternion) (i : Fin 3) : PolyQuaternion :=
  (f*imaginaryBasis i)*PolyQuaternion.conj f
private def contraction (p : PolyQuaternion) (v : Fin 3 → PolyQuaternion) : PolyQuaternion :=
  sum3 (polynomialScale (v 0*p).scalar (v 0))
    (polynomialScale (v 1*p).scalar (v 1)) (polynomialScale (v 2*p).scalar (v 2))

/-- Cleared finite identity for arbitrary f,P. Its only later unit input
is norm(f)=1 in the original arbitrary-insertion Haar carrier. -/
theorem conjugated_basis_contraction_cleared (f p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (contraction p (conjugatedBasis f))
      (clearedNegativeImaginary (polyMul (polyQuaternionNorm f) (polyQuaternionNorm f)) p) := by
  have ht (i : Fin 3) := scale_coeff
    ((conjugated_rows f i).mul (PolyQuaternionCoeffEqv.refl p)).scalar (conjugated_rows f i)
  apply (sum_coeff (ht 0) (ht 1) (ht 2)).trans
  constructor
  · exact (RatPolyCoeffEqv.mul_zero_right _).add
      ((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_zero_right _))
  · exact row_component_synthesis f p 0
  · exact row_component_synthesis f p 1
  · exact row_component_synthesis f p 2

private theorem scale_carrier {B : Nat} {a b : RatPoly} {p q : PolyQuaternion}
    (ha : HaarCarrierEqv B a b) (hq : PolyQuaternionHaarCarrierEqv B p q) :
    PolyQuaternionHaarCarrierEqv B (polynomialScale a p) (polynomialScale b q) :=
  ⟨HaarCarrierEqv.mul ha hq.scalar, HaarCarrierEqv.mul ha hq.iPart,
    HaarCarrierEqv.mul ha hq.jPart, HaarCarrierEqv.mul ha hq.kPart⟩
private theorem sum_carrier {B : Nat} {a a' b b' c c' : PolyQuaternion}
    (ha : PolyQuaternionHaarCarrierEqv B a a') (hb : PolyQuaternionHaarCarrierEqv B b b')
    (hc : PolyQuaternionHaarCarrierEqv B c c') :
    PolyQuaternionHaarCarrierEqv B (sum3 a b c) (sum3 a' b' c') :=
  ⟨HaarCarrierEqv.add ha.scalar (HaarCarrierEqv.add hb.scalar hc.scalar),
    HaarCarrierEqv.add ha.iPart (HaarCarrierEqv.add hb.iPart hc.iPart),
    HaarCarrierEqv.add ha.jPart (HaarCarrierEqv.add hb.jPart hc.jPart),
    HaarCarrierEqv.add ha.kPart (HaarCarrierEqv.add hb.kPart hc.kPart)⟩
private theorem unit_contraction {B : Nat} {f : PolyQuaternion}
    (hf : HaarCarrierEqv B (polyQuaternionNorm f) polyOne) (p : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv B (contraction p (conjugatedBasis f)) (negativeImaginary p) := by
  have hn := HaarCarrierEqv.trans (HaarCarrierEqv.mul hf hf)
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one polyOne))
  have hc (q : RatPoly) := HaarCarrierEqv.neg
    (HaarCarrierEqv.trans (HaarCarrierEqv.mul_right q hn)
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul q)))
  exact (PolyQuaternionHaarCarrierEqv.of_coeff (conjugated_basis_contraction_cleared f p)).trans
    ⟨HaarCarrierEqv.refl B polyZero, hc p.iPart, hc p.jPart, hc p.kPart⟩

private theorem neg_mul_neg (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyNeg p) (polyNeg q)) (polyMul p q) :=
  coeffEvalExpr_eqv_of_normalize_eq (.mul (.neg (.var 0)) (.neg (.var 1)))
    (.mul (.var 0) (.var 1)) (by decide) (fun n => if n=0 then p else q)
private theorem sign_squared (s : Fin 4) (v p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (polynomialScale (signed s v*p).scalar (signed s v))
      (polynomialScale (v*p).scalar v) := by
  unfold signed
  split
  · have hm : PolyQuaternionCoeffEqv (negQuaternion v*p) (negQuaternion (v*p)) := by
      let env : Nat → RatPoly
        | 0 => v.scalar | 1 => v.iPart | 2 => v.jPart | 3 => v.kPart
        | 4 => p.scalar | 5 => p.iPart | 6 => p.jPart | 7 => p.kPart | _ => polyZero
      let exprNeg (q : PolyQuaternionExpr) : PolyQuaternionExpr :=
        ⟨.neg q.scalar, .neg q.iPart, .neg q.jPart, .neg q.kPart⟩
      let left := PolyQuaternionExpr.mul (exprNeg (PolyQuaternionExpr.coordinate 0))
        (PolyQuaternionExpr.coordinate 4)
      let right := exprNeg (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.coordinate 4))
      exact ⟨coeffEvalExpr_eqv_of_normalize_eq left.scalar right.scalar (by decide) env,
        coeffEvalExpr_eqv_of_normalize_eq left.iPart right.iPart (by decide) env,
        coeffEvalExpr_eqv_of_normalize_eq left.jPart right.jPart (by decide) env,
        coeffEvalExpr_eqv_of_normalize_eq left.kPart right.kPart (by decide) env⟩
    exact (scale_coeff hm.scalar (PolyQuaternionCoeffEqv.refl (negQuaternion v))).trans
      ⟨neg_mul_neg _ _, neg_mul_neg _ _, neg_mul_neg _ _, neg_mul_neg _ _⟩
  · exact PolyQuaternionCoeffEqv.refl _

/-- Literal three-direction own-gradient vector at a physical face slot. -/
def ownVector (width : Nat) (p : Z4Plaq) (s : Fin 4) : PolyQuaternion :=
  sum3
    (polynomialScale (pairedDerivativeAt (slotIndex width p s) 0 (plaquette width p).scalar)
      (commonVector width p s 0))
    (polynomialScale (pairedDerivativeAt (slotIndex width p s) 1 (plaquette width p).scalar)
      (commonVector width p s 1))
    (polynomialScale (pairedDerivativeAt (slotIndex width p s) 2 (plaquette width p).scalar)
      (commonVector width p s 2))

/-- Produced own-gradient synthesis on the SAME original Haar carrier,
for every physical slot. It is not a weighted Hessian estimate. -/
theorem ownVector_exact {width : Nat} {p : Z4Plaq} (hp : p ∈ spatialFaces width) (s : Fin 4) :
    PolyQuaternionHaarCarrierEqv (baseLinks width).length (ownVector width p s)
      (negativeImaginary (plaquette width p)) := by
  have hj (i : Fin 3) := scale_carrier (original_paired_first_jet hp s i)
    (PolyQuaternionHaarCarrierEqv.refl (baseLinks width).length (commonVector width p s i))
  have hs (i : Fin 3) := sign_squared s (conjugatedBasis (commonPrefix width p s) i) (plaquette width p)
  exact (sum_carrier (hj 0) (hj 1) (hj 2)).trans
    ((PolyQuaternionHaarCarrierEqv.of_coeff (sum_coeff (hs 0) (hs 1) (hs 2))).trans
      (unit_contraction (prefix_unit hp s) (plaquette width p)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOwnVector

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOwnVector.conjugated_basis_contraction_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOwnVector.ownVector_exact
