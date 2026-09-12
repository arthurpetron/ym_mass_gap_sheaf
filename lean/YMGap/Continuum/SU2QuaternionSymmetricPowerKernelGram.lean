/-
# Actual all-degree polynomial trace kernel as a positive-weighted Gram kernel

Hamilton multiplication and conjugation give the actual fundamental matrix
product and adjoint at coefficient-probe strength. Tensor functoriality,
the Hermitian adjoint law, and the explicit binomial dual basis identify
the ORIGINAL polynomial trace with weighted representation-column pairings.
The coefficients are explicit positive rationals, without square roots.

All statements retain every spectator coefficient. The Haar character
consumer requires a proved radius relation, not pointwise unit norm.
This does not glue reflected channels on the physical slab or prove its
reflection positivity, transfer gap, or continuum construction.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
import YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈c " => ComplexCoeffEqv
private abbrev A := fundamentalMatrixCoefficient
private abbrev CExpr := PolyExpr × PolyExpr
private def plus (x y : CExpr) : CExpr := (.add x.1 y.1, .add x.2 y.2)
private def times (x y : CExpr) : CExpr :=
  (.add (.mul x.1 y.1) (.neg (.mul x.2 y.2)), .add (.mul x.1 y.2) (.mul x.2 y.1))
private def matrixExpr (p : PolyQuaternionExpr) : Bool → Bool → CExpr
  | false, false => (p.scalar, p.iPart)
  | false, true => (p.jPart, p.kPart)
  | true, false => (.neg p.jPart, p.kPart)
  | true, true => (p.scalar, .neg p.iPart)
private def four (a b c d : PolyExpr) : PolyExpr := .add (.add a b) (.add c d)
private def hamiltonExpr (p q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨four (.mul p.scalar q.scalar) (.neg (.mul p.iPart q.iPart))
      (.neg (.mul p.jPart q.jPart)) (.neg (.mul p.kPart q.kPart)),
    four (.mul p.scalar q.iPart) (.mul p.iPart q.scalar)
      (.mul p.jPart q.kPart) (.neg (.mul p.kPart q.jPart)),
    four (.mul p.scalar q.jPart) (.neg (.mul p.iPart q.kPart))
      (.mul p.jPart q.scalar) (.mul p.kPart q.iPart),
    four (.mul p.scalar q.kPart) (.mul p.iPart q.jPart)
      (.neg (.mul p.jPart q.iPart)) (.mul p.kPart q.scalar)⟩
private def leftExpr (row column : Bool) : CExpr := matrixExpr
  (hamiltonExpr (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)) row column
private def rightExpr (row column : Bool) : CExpr :=
  plus (times (matrixExpr (PolyQuaternionExpr.coordinate 0) row false)
      (matrixExpr (PolyQuaternionExpr.coordinate 4) false column))
    (times (matrixExpr (PolyQuaternionExpr.coordinate 0) row true)
      (matrixExpr (PolyQuaternionExpr.coordinate 4) true column))
private def env (p q : RatPolyQuaternion) : Nat → RatPoly
  | 0 => p.r | 1 => p.i | 2 => p.j | 3 => p.k
  | 4 => q.r | 5 => q.i | 6 => q.j | 7 => q.k | _ => polyZero
private theorem cert (l r : CExpr)
    (hr : normalize l.1 = normalize r.1) (hi : normalize l.2 = normalize r.2)
    (environment : Nat → RatPoly) :
    (coeffEvalExpr environment l.1, coeffEvalExpr environment l.2) ≈c
      (coeffEvalExpr environment r.1, coeffEvalExpr environment r.2) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ hr environment,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hi environment⟩

/-- The actual polynomial Hamilton product, not merely its evaluation. -/
theorem fundamental_coeff_mul (p q : RatPolyQuaternion) (row column : Bool) :
    A (RationalQuaternionRatPoly.mul p q) row column ≈c polynomialMatrixMul (A p) (A q) row column := by
  cases row <;> cases column
  · exact cert (leftExpr false false) (rightExpr false false) (by decide) (by decide) (env p q)
  · exact cert (leftExpr false true) (rightExpr false true) (by decide) (by decide) (env p q)
  · exact cert (leftExpr true false) (rightExpr true false) (by decide) (by decide) (env p q)
  · exact cert (leftExpr true true) (rightExpr true true) (by decide) (by decide) (env p q)

theorem fundamental_coeff_conj (q : RatPolyQuaternion) (row column : Bool) :
    A (RationalQuaternionRatPoly.conj q) row column ≈c polynomialMatrixAdjoint (A q) row column := by
  cases row <;> cases column
  · exact ComplexCoeffEqv.refl _
  · exact ComplexCoeffEqv.refl _
  · exact ⟨coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 2))) (.var 2)
      (by decide) (env q q), RatPolyCoeffEqv.refl _⟩
  · exact ComplexCoeffEqv.refl _

/-- The actual raw Hamilton norm is multiplicative, coefficientwise. -/
theorem radius_mul (p q : RatPolyQuaternion) :
    RatPolyCoeffEqv (radiusPolynomial (RationalQuaternionRatPoly.mul p q))
      (polyMul (radiusPolynomial p) (radiusPolynomial q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm (hamiltonExpr (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
    (.mul (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))
      (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 4))) (by decide) (env p q)

theorem radius_conj (p : RatPolyQuaternion) :
    RatPolyCoeffEqv (radiusPolynomial (RationalQuaternionRatPoly.conj p)) (radiusPolynomial p) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0)))
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0)) (by decide) (env p p)

/-- Individual Haar-unit radii imply the conjugate-product radius relation
on the SAME carrier, even when the two words share link variables. -/
theorem haarRadius_conj_mul {blocks : Nat} {p q : RatPolyQuaternion}
    (hp : QuaternionHaarCarrierEqv blocks (radiusPolynomial p) polyOne)
    (hq : QuaternionHaarCarrierEqv blocks (radiusPolynomial q) polyOne) :
    QuaternionHaarCarrierEqv blocks
      (radiusPolynomial (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q)) polyOne :=
  QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (radius_mul _ _))
    (QuaternionHaarCarrierEqv.trans
      (QuaternionHaarCarrierEqv.mul
        (QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (radius_conj p)) hp) hq)
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one polyOne)))

/-- The actual degree-n representation column, retained as a symmetric
polynomial tensor. Its coefficient window is the original matrix column. -/
def polynomialColumn (q : RatPolyQuaternion) (n k : Nat) : PolyTensor n :=
  polyMatrixAction n (A q) (polyEmbed n (polynomialBasis k))

theorem polynomialColumn_eq_entries (q : RatPolyQuaternion) (n k : Nat) :
    PolyTensorEqv n (polynomialColumn q n k)
      (polyEmbed n (fun j => polynomialMatrixCoefficient q n j k)) := polyMatrixAction_embed q n _

/-- Every diagonal entry of the product is its explicit weighted column
pairing. No unit-norm or Haar assumption is needed for this algebraic law. -/
theorem diagonal_eq_column_pair (p q : RatPolyQuaternion) (n k : Nat) (hk : k ≤ n) :
    polynomialMatrixCoefficient (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q) n k k ≈c
      polyRealScale (basisInverseWeight n k)
        (polyTensorInner n (polynomialColumn p n k) (polynomialColumn q n k)) := by
  let e := polyEmbed n (polynomialBasis k)
  let product := RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q
  have hprod : PolyTensorEqv n (polyMatrixAction n (A product) e)
      (polyMatrixAction n (polynomialMatrixAdjoint (A p)) (polynomialColumn q n k)) :=
    (polyMatrixAction_congr (fundamental_coeff_mul (RationalQuaternionRatPoly.conj p) q)
      (PolyTensorEqv.refl n e)).trans
      ((polyMatrixAction_mul _ _ n e).trans
        (polyMatrixAction_congr (fundamental_coeff_conj p) (PolyTensorEqv.refl n _)))
  have hinner : polyTensorInner n (polynomialColumn p n k) (polynomialColumn q n k) ≈c
      polyTensorInner n e (polyEmbed n (fun j => polynomialMatrixCoefficient product n j k)) :=
    (polyTensorInner_matrixAction (A p) n e (polynomialColumn q n k)).trans
      ((polyTensorInner_congr (PolyTensorEqv.refl n e) hprod.symm).trans
        (polyTensorInner_congr (PolyTensorEqv.refl n e) (polynomialColumn_eq_entries product n k)))
  exact ((polyRealScale_congr (Q'.eqv_refl _) hinner).trans
    (polyTensorInner_basis_extract n _ k hk)).symm

/-- Positive-weighted Gram kernel built from the ACTUAL columns. The
weights `basisInverseWeight n k` are explicit and proved strictly positive. -/
def polynomialGramKernel (p q : RatPolyQuaternion) (n : Nat) : ComplexRatPoly :=
  polynomialSum (n + 1) (fun k => polyRealScale (basisInverseWeight n k)
    (polyTensorInner n (polynomialColumn p n k) (polynomialColumn q n k)))

/-- Exact coefficient-level Gram decomposition of the ORIGINAL all-degree
trace kernel. It can be multiplied by arbitrary spectators before Haar. -/
theorem polynomialTrace_conj_mul_eq_gram (p q : RatPolyQuaternion) (n : Nat) :
    polynomialTrace (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q) n ≈c
      polynomialGramKernel p q n :=
  sum_congr (n + 1) (fun k hk => diagonal_eq_column_pair p q n k (by omega))

/-- Character-kernel consumer on the SAME Haar carrier. The explicit norm
premise is a polynomial sphere-ideal relation under arbitrary insertions. -/
theorem character_haar_gram {blocks : Nat} (p q : RatPolyQuaternion)
    (hradius : QuaternionHaarCarrierEqv blocks
      (radiusPolynomial (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q)) polyOne)
    (n : Nat) :
    QuaternionHaarCarrierEqv blocks
      (characterPolynomial (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q).r n)
      (polynomialGramKernel p q n).1 ∧
    QuaternionHaarCarrierEqv blocks (polynomialGramKernel p q n).2 polyZero := by
  have h := polynomialTrace_haar_character
    (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q) hradius n
  have hg := polynomialTrace_conj_mul_eq_gram p q n
  exact ⟨QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm h.1)
      (RatPolyCoeffEqv.haarCarrier hg.1),
    QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm (RatPolyCoeffEqv.haarCarrier hg.2)) h.2⟩

/-- The local character channels consume only the two individual proved
Haar-unit radius relations; no pairwise radius or character identity is assumed. -/
theorem character_haar_gram_of_unit_radii {blocks : Nat} (p q : RatPolyQuaternion)
    (hp : QuaternionHaarCarrierEqv blocks (radiusPolynomial p) polyOne)
    (hq : QuaternionHaarCarrierEqv blocks (radiusPolynomial q) polyOne) (n : Nat) :
    QuaternionHaarCarrierEqv blocks
      (characterPolynomial (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj p) q).r n)
      (polynomialGramKernel p q n).1 ∧
    QuaternionHaarCarrierEqv blocks (polynomialGramKernel p q n).2 polyZero :=
  character_haar_gram p q (haarRadius_conj_mul hp hq) n

end YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.fundamental_coeff_mul
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.fundamental_coeff_conj
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.radius_mul
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.radius_conj
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.haarRadius_conj_mul
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.polynomialColumn
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.polynomialColumn_eq_entries
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.diagonal_eq_column_pair
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.polynomialGramKernel
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.polynomialTrace_conj_mul_eq_gram
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.character_haar_gram
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram.character_haar_gram_of_unit_radii
