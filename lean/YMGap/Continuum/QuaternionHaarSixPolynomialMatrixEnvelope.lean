/-
# Six-column envelopes with genuine polynomial coefficients

Both signs of all 36 ORDERED matrix entries are retained. Pairwise square
completion constructs the local matrix bound with coefficient six, with no
symmetry, positivity or scalar-only restriction on the coefficient family.

The consumer is the adaptive local heat-curvature Gram construction. This
algebraic certificate does not itself supply the conditional Fisher join,
an ORIGINAL normalized energy estimate or a completed OS comparison.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

private def slot (n : Nat) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by decide)⟩

/-- Fixed six-column sum, with no hidden omission of an ordered entry. -/
def sixSum (f : Fin 6 → RatPoly) : RatPoly :=
  polyAdd (f (slot 0)) (polyAdd (f (slot 1)) (polyAdd (f (slot 2))
    (polyAdd (f (slot 3)) (polyAdd (f (slot 4)) (f (slot 5))))))

/-- The six literal coefficient squares. -/
def squareSum (u : Fin 6 → RatPoly) : RatPoly :=
  sixSum (fun i => polyMul (u i) (u i))

/-- All ordered mixed entries, without a symmetry assumption. -/
def quadraticForm (u : Fin 6 → RatPoly) (M : Fin 6 → Fin 6 → RatPoly) : RatPoly :=
  sixSum (fun i => sixSum (fun j => polyMul (polyMul (u i) (u j)) (M i j)))

def matrixEnvelope (U : RatPoly) (u : Fin 6 → RatPoly)
    (M : Fin 6 → Fin 6 → RatPoly) : RatPoly :=
  polyAdd (polyMul (polyMul (cap 6) U) (squareSum u)) (quadraticForm u M)

private def sixCertificate {blocks : Nat} (f : Fin 6 → RatPoly)
    (P : ∀ i, Certificate blocks (f i)) : Certificate blocks (sixSum f) :=
  (P (slot 0)).add ((P (slot 1)).add ((P (slot 2)).add
    ((P (slot 3)).add ((P (slot 4)).add (P (slot 5))))))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

private def halveCertificate {blocks : Nat} {p : RatPoly}
    (P : Certificate blocks (polySmul 2 p)) : Certificate blocks p :=
  Certificate.ofCoeff
    (((RatPolyCoeffEqv.smul_assoc HalfPow.half 2 p).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (HalfPow.half*2) 1) p)).trans
      (RatPolyCoeffEqv.one_smul p)).symm
    (P.smul HalfPow.half HalfPow.half_nonneg)

private def pairEnvelope (U M v w : RatPoly) : RatPoly :=
  polyAdd (polyMul U (polyAdd (polyMul v v) (polyMul w w)))
    (polyMul (cap 2) (polyMul (polyMul v w) M))

/-- Exact two-column square completion, with polynomial v and w. -/
def two_polynomial_envelope_certificate {blocks : Nat}
    (U M v w : RatPoly)
    (hv : SupportedQuaternionBlocks blocks v)
    (hw : SupportedQuaternionBlocks blocks w)
    (P : Certificate blocks (polyAdd U M))
    (N : Certificate blocks (polyAdd U (polyNeg M))) :
    Certificate blocks (pairEnvelope U M v w) := by
  have source := (Certificate.multiplySquare (polyAdd v w) (supported_add hv hw) P).add
    (Certificate.multiplySquare (polyAdd v (polyNeg w))
      (supported_add hv (support_neg hw)) N)
  apply halveCertificate
  exact Certificate.ofCoeff
    ((cap_mul_left 2 (pairEnvelope U M v w)).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.const 2)
          (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
            (.mul (.const 2) (.mul (.mul (.var 2) (.var 3)) (.var 1)))))
        (.add
          (.mul (.mul (.add (.var 2) (.var 3)) (.add (.var 2) (.var 3)))
            (.add (.var 0) (.var 1)))
          (.mul (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 2) (.neg (.var 3))))
            (.add (.var 0) (.neg (.var 1)))))
        (by decide) (fun | 0 => U | 1 => M | 2 => v | _ => w))) source

private def exprSix (f : Fin 6 → PolyExpr) : PolyExpr :=
  .add (f (slot 0)) (.add (f (slot 1)) (.add (f (slot 2))
    (.add (f (slot 3)) (.add (f (slot 4)) (f (slot 5))))))

private def coefficientExpr (i : Fin 6) : PolyExpr := .var (1+i.val)
private def entryExpr (i j : Fin 6) : PolyExpr := .var (7+6*i.val+j.val)
private def envelopeExpr : PolyExpr :=
  .add
    (.mul (.mul (.const 6) (.var 0))
      (exprSix (fun i => .mul (coefficientExpr i) (coefficientExpr i))))
    (exprSix (fun i => exprSix (fun j =>
      .mul (.mul (coefficientExpr i) (coefficientExpr j)) (entryExpr i j))))
private def pairsExpr : PolyExpr :=
  exprSix (fun i => exprSix (fun j =>
    .add (.mul (.var 0)
      (.add (.mul (coefficientExpr i) (coefficientExpr i))
        (.mul (coefficientExpr j) (coefficientExpr j))))
      (.mul (.const 2)
        (.mul (.mul (coefficientExpr i) (coefficientExpr j)) (entryExpr i j)))))

private theorem orderedPairs_pin (U : RatPoly) (u : Fin 6 → RatPoly)
    (M : Fin 6 → Fin 6 → RatPoly) :
    RatPolyCoeffEqv (polySmul 2 (matrixEnvelope U u M))
      (sixSum (fun i => sixSum (fun j => pairEnvelope U (M i j) (u i) (u j)))) := by
  let environment : Nat → RatPoly := fun k =>
    if k = 0 then U else if k ≤ 6 then u (slot (k-1))
    else M (slot ((k-7)/6)) (slot (k-7))
  have h := coeffEvalExpr_eqv_of_normalize_eq (.mul (.const 2) envelopeExpr) pairsExpr
    (by decide) environment
  apply (cap_mul_left 2 (matrixEnvelope U u M)).symm.trans
  simpa only [envelopeExpr, pairsExpr, exprSix, coefficientExpr, entryExpr,
    coeffEvalExpr, environment, matrixEnvelope, squareSum, quadraticForm, sixSum,
    pairEnvelope, slot] using h

/-- Six-column polynomial matrix certificate. All ordered entries retain
their original signs; coefficients are supported polynomials, not rationals. -/
def six_polynomial_matrix_envelope_certificate {blocks : Nat}
    (U : RatPoly) (u : Fin 6 → RatPoly) (M : Fin 6 → Fin 6 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (P : ∀ i j, Certificate blocks (polyAdd U (M i j)))
    (N : ∀ i j, Certificate blocks (polyAdd U (polyNeg (M i j)))) :
    Certificate blocks (matrixEnvelope U u M) :=
  halveCertificate (Certificate.ofCoeff (orderedPairs_pin U u M)
    (sixCertificate _ (fun i => sixCertificate _ (fun j =>
      two_polynomial_envelope_certificate U (M i j) (u i) (u j)
        (hu i) (hu j) (P i j) (N i j)))))

end YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope

#print axioms YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.two_polynomial_envelope_certificate
#print axioms YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.six_polynomial_matrix_envelope_certificate
