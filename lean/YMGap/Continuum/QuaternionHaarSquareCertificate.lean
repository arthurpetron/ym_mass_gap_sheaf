/-
# Constructive square certificates on the ORIGINAL polynomial Haar carrier

The data constructors are supported polynomial squares, addition,
nonnegative rational scaling, and equality under EVERY Haar insertion.
There is no constructor from pointwise positivity or an arbitrary claimed
Haar inequality. Products are compiled by distributing actual squares,
including all overlapping variables. No reflection operator is involved.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.QuaternionHaarSquareCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

local infix:50 " ≈ " => Q'.eqv

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by unfold quaternionHaar ratWeightedSum; rw [haar_eq_weighted blocks rest]

theorem haar_of_coeff {blocks : Nat} {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  rw [haar_eq_weighted, haar_eq_weighted]
  exact h _

/-- Specialize the existing arbitrary-insertion relation to Haar itself. -/
theorem haar_of_carrier {blocks : Nat} {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul p)))
    (Q'.eqv_trans _ _ _ (h polyOne) (haar_of_coeff (RatPolyCoeffEqv.one_mul q)))

theorem supported_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

theorem supported_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hp t h
  · exact hq t h

/-- Witness-bearing algebraic certificate; there is no analytic premise
asserting positivity of the represented polynomial. -/
inductive Certificate (blocks : Nat) : RatPoly → Type where
  | square (p : RatPoly) (support : SupportedQuaternionBlocks blocks p) :
      Certificate blocks (polyMul p p)
  | add {p q : RatPoly} : Certificate blocks p → Certificate blocks q → Certificate blocks (polyAdd p q)
  | smul (c : Q') (nonnegative : (0 : Q') ≤ c) {p : RatPoly} :
      Certificate blocks p → Certificate blocks (polySmul c p)
  | transport {p q : RatPoly} : HaarCarrierEqv blocks p q → Certificate blocks q → Certificate blocks p

namespace Certificate

def ofCoeff {blocks : Nat} {p q : RatPoly} (h : RatPolyCoeffEqv p q) (Q : Certificate blocks q) :
    Certificate blocks p := .transport (RatPolyCoeffEqv.haarCarrier h) Q

def one (blocks : Nat) : Certificate blocks polyOne :=
  ofCoeff (RatPolyCoeffEqv.one_mul polyOne).symm (.square polyOne (supported_one blocks))

def constant (blocks : Nat) (c : Q') (hc : (0 : Q') ≤ c) : Certificate blocks (polySmul c polyOne) :=
  .smul c hc (one blocks)

/-- Multiply by a supported square by explicitly multiplying every channel. -/
def multiplySquare {blocks : Nat} (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    {q : RatPoly} → Certificate blocks q → Certificate blocks (polyMul (polyMul p p) q)
  | _, .square q hq => ofCoeff (RatPolyCoeffEqv.mul_four_swap p p q q)
      (.square (polyMul p q) (supported_polyMul hp hq))
  | _, .add Q R => ofCoeff (RatPolyCoeffEqv.mul_add_right _ _ _)
      (.add (multiplySquare p hp Q) (multiplySquare p hp R))
  | _, .smul c hc Q => ofCoeff (RatPolyCoeffEqv.polyMul_smul_right c _ _)
      (.smul c hc (multiplySquare p hp Q))
  | _, .transport h Q => .transport (h.mul_left (polyMul p p)) (multiplySquare p hp Q)

/-- Product closure retains shared coordinates. It is proved from the
square constructors, not postulated as a positivity rule. -/
def mul {blocks : Nat} : {p q : RatPoly} → Certificate blocks p → Certificate blocks q →
    Certificate blocks (polyMul p q)
  | _, _, .square p hp, Q => multiplySquare p hp Q
  | _, _, .add P R, Q => by
      rw [polyMul_add_left_exact]
      exact .add (mul P Q) (mul R Q)
  | _, _, .smul c hc P, Q => ofCoeff (RatPolyCoeffEqv.polyMul_smul_left c _ _)
      (.smul c hc (mul P Q))
  | _, _, .transport h P, Q => .transport (HaarCarrierEqv.mul_right _ h) (mul P Q)

/-- Every certificate gives nonnegative ORIGINAL rational Haar value. -/
theorem haar_nonnegative {blocks : Nat} : {p : RatPoly} → Certificate blocks p →
    (0 : Q') ≤ quaternionHaar blocks p
  | _, .square p hp => quaternionHaar_square_nonnegative blocks p hp
  | _, .add P Q => Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ (haar_nonnegative P) (haar_nonnegative Q))
      (Q'.ge_of_eqv (quaternionHaar_append blocks _ _))
  | _, .smul c hc P => Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hc (haar_nonnegative P))
      (Q'.ge_of_eqv (quaternionHaar_polySmul blocks c _))
  | _, .transport h P => Q'.le_trans' _ _ _ (haar_nonnegative P) (Q'.ge_of_eqv (haar_of_carrier h))

/-- The same certificate remains positive after any supported square insertion. -/
theorem square_insertion_nonnegative {blocks : Nat} {p : RatPoly} (P : Certificate blocks p)
    (r : RatPoly) (hr : SupportedQuaternionBlocks blocks r) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul (polyMul r r) p) :=
  (multiplySquare r hr P).haar_nonnegative

end Certificate

end YMGap.Continuum.QuaternionHaarSquareCertificate

#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.haar_of_coeff
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.haar_of_carrier
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.supported_one
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.supported_add
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.ofCoeff
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.one
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.constant
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.multiplySquare
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.mul
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.haar_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.square_insertion_nonnegative
