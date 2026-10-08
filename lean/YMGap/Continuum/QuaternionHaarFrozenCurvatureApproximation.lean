/-
# Homogeneous full-matrix transport through actual finite jet errors

ALL nine ordered entries retain the two distinct signed cross terms.
Polynomial direction coefficients are frozen, supported, and never capped
by scalar magnitudes. The existing six-column envelope is zero-padded;
its factor SIX is paid by precision and the ORIGINAL positive floor.

This finite algebraic compiler supplies no heat estimate, interacting
conditional sign, OS passage, continuum construction or physical mass.
-/

import YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope
import YMGap.Continuum.QuaternionHaarCurvatureApproximation

namespace YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSignedInterval
open YMGap.Continuum.QuaternionHaarCurvatureApproximation (errorCap floor_square_payment)

def firstJet (u dp : Fin 3 → RatPoly) : RatPoly :=
  threeSum (fun i => polyMul (u i) (dp i))

/-- Literal homogeneous curvature of supplied jets, before any analytic join. -/
def jetCurvature (C : Q') (p : RatPoly) (dp : Fin 3 → RatPoly)
    (ddp : Fin 3 → Fin 3 → RatPoly) (u : Fin 3 → RatPoly) : RatPoly :=
  polyAdd (polyMul (cap C) (polyMul (threeSquare u) (polyMul p p)))
    (polyAdd (polyMul p (quadraticForm u ddp))
      (polyNeg (polyMul (firstJet u dp) (firstJet u dp))))

private def diagonal (i j : Fin 3) (p : RatPoly) : RatPoly :=
  if i=j then p else cap 0

/-- Literal entry error, not a symmetrized representative. -/
def errorEntry (C : Q') (p e : RatPoly) (dp de : Fin 3 → RatPoly)
    (ddp dde : Fin 3 → Fin 3 → RatPoly) (i j : Fin 3) : RatPoly :=
  polyAdd
    (polyAdd
      (diagonal i j (polyMul (cap C)
        (polyAdd (polyMul (cap 2) (polyMul p e)) (polyNeg (polyMul e e)))))
      (polyAdd (polyAdd (polyMul p (dde i j)) (polyMul e (ddp i j)))
        (polyNeg (polyMul e (dde i j)))))
    (polyAdd (polyNeg (polyAdd (polyMul (dp i) (de j)) (polyMul (de i) (dp j))))
      (polyMul (de i) (de j)))

private def exprThree (f : Fin 3 → PolyExpr) : PolyExpr :=
  .add (f 0) (.add (f 1) (f 2))
private def minus (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def exprQuadratic (u : Fin 3 → PolyExpr) (M : Fin 3 → Fin 3 → PolyExpr) : PolyExpr :=
  exprThree (fun i => exprThree (fun j => .mul (.mul (u i) (u j)) (M i j)))
private def exprCurvature (C p : PolyExpr) (dp : Fin 3 → PolyExpr)
    (ddp : Fin 3 → Fin 3 → PolyExpr) (u : Fin 3 → PolyExpr) : PolyExpr :=
  .add (.mul C (.mul (exprThree (fun i => .mul (u i) (u i))) (.mul p p)))
    (.add (.mul p (exprQuadratic u ddp))
      (.neg (.mul (exprThree (fun i => .mul (u i) (dp i)))
        (exprThree (fun i => .mul (u i) (dp i))))))
private def exprError (i j : Fin 3) : PolyExpr :=
  let dpi := .var (6+i.val)
  let dpj := .var (6+j.val)
  let dei := .var (9+i.val)
  let dej := .var (9+j.val)
  let dd := .var (12+3*i.val+j.val)
  let de := .var (21+3*i.val+j.val)
  .add
    (.add
      (if i=j then .mul (.var 0)
        (minus (.mul (.const 2) (.mul (.var 1) (.var 2))) (.mul (.var 2) (.var 2)))
        else .const 0)
      (minus (.add (.mul (.var 1) de) (.mul (.var 2) dd)) (.mul (.var 2) de)))
    (.add (.neg (.add (.mul dpi dej) (.mul dei dpj))) (.mul dei dej))
private def env (C : Q') (p e : RatPoly) (u dp de : Fin 3 → RatPoly)
    (ddp dde : Fin 3 → Fin 3 → RatPoly) : Nat → RatPoly
  | 0 => cap C | 1 => p | 2 => e
  | 3 => u 0 | 4 => u 1 | 5 => u 2
  | 6 => dp 0 | 7 => dp 1 | 8 => dp 2
  | 9 => de 0 | 10 => de 1 | 11 => de 2
  | 12 => ddp 0 0 | 13 => ddp 0 1 | 14 => ddp 0 2
  | 15 => ddp 1 0 | 16 => ddp 1 1 | 17 => ddp 1 2
  | 18 => ddp 2 0 | 19 => ddp 2 1 | 20 => ddp 2 2
  | 21 => dde 0 0 | 22 => dde 0 1 | 23 => dde 0 2
  | 24 => dde 1 0 | 25 => dde 1 1 | 26 => dde 1 2
  | 27 => dde 2 0 | 28 => dde 2 1 | _ => dde 2 2

private theorem curvature_congr {C : Q'} {p q : RatPoly}
    {dp dq : Fin 3 → RatPoly} {ddp ddq : Fin 3 → Fin 3 → RatPoly}
    (u : Fin 3 → RatPoly) (h : RatPolyCoeffEqv p q)
    (hd : ∀ i, RatPolyCoeffEqv (dp i) (dq i))
    (hdd : ∀ i j, RatPolyCoeffEqv (ddp i j) (ddq i j)) :
    RatPolyCoeffEqv (jetCurvature C p dp ddp u) (jetCurvature C q dq ddq u) :=
  ((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.refl _).mul (h.mul h))).add
    ((h.mul (threeSum_congr (fun i => threeSum_congr (fun j =>
      (RatPolyCoeffEqv.refl _).mul (hdd i j))))).add
      (RatPolyCoeffEqv.neg ((threeSum_congr (fun i => (hd i).mul_left (u i))).mul
        (threeSum_congr (fun i => (hd i).mul_left (u i))))))

/-- Coefficient pin for the full signed discrepancy; no jet symmetry is used. -/
theorem curvature_difference_pin (C : Q') {p f e : RatPoly}
    {dp df de : Fin 3 → RatPoly} {ddp ddf dde : Fin 3 → Fin 3 → RatPoly}
    (u : Fin 3 → RatPoly) (h0 : RatPolyCoeffEqv p (polyAdd f e))
    (h1 : ∀ i, RatPolyCoeffEqv (dp i) (polyAdd (df i) (de i)))
    (h2 : ∀ i j, RatPolyCoeffEqv (ddp i j) (polyAdd (ddf i j) (dde i j))) :
    RatPolyCoeffEqv
      (polyAdd (jetCurvature C p dp ddp u) (polyNeg (jetCurvature C f df ddf u)))
      (quadraticForm u (errorEntry C p e dp de ddp dde)) := by
  have recover {x y z : RatPoly} (h : RatPolyCoeffEqv x (polyAdd y z)) :
      RatPolyCoeffEqv y (polyAdd x (polyNeg z)) :=
    (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (minus (.add (.var 0) (.var 1)) (.var 1)) (by decide)
      (fun | 0 => y | _ => z)).trans (h.symm.add (.refl _))
  have hf := curvature_congr (C := C) u (recover h0)
    (fun i => recover (h1 i)) (fun i j => recover (h2 i j))
  refine ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hf)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (minus
      (exprCurvature (.var 0) (.var 1) (fun i => .var (6+i.val))
        (fun i j => .var (12+3*i.val+j.val)) (fun i => .var (3+i.val)))
      (exprCurvature (.var 0) (minus (.var 1) (.var 2))
        (fun i => minus (.var (6+i.val)) (.var (9+i.val)))
        (fun i j => minus (.var (12+3*i.val+j.val)) (.var (21+3*i.val+j.val)))
        (fun i => .var (3+i.val))))
    (exprQuadratic (fun i => .var (3+i.val)) exprError)
    (by decide) (env C p e u dp de ddp dde)

/-- Each literal entry has the same produced cap, including the diagonal value error. -/
def error_interval {blocks : Nat} {C U0 U1 U2 a b c : Q'} {p e : RatPoly}
    {dp de : Fin 3 → RatPoly} {ddp dde : Fin 3 → Fin 3 → RatPoly}
    (hC : (0 : Q') ≤ C) (P : Interval blocks p U0) (E : Interval blocks e a)
    (DP : ∀ i, Interval blocks (dp i) U1) (DE : ∀ i, Interval blocks (de i) b)
    (DDP : ∀ i j, Interval blocks (ddp i j) U2)
    (DDE : ∀ i j, Interval blocks (dde i j) c) (i j : Fin 3) :
    Interval blocks (errorEntry C p e dp de ddp dde i j) (errorCap C U0 U1 U2 a b c) := by
  let V := (Interval.constant blocks C hC).mul
    (((Interval.constant blocks 2 (by decide)).mul (P.mul E)).add (Interval.neg (E.mul E)))
  have D : Interval blocks
      (diagonal i j (polyMul (cap C)
        (polyAdd (polyMul (cap 2) (polyMul p e)) (polyNeg (polyMul e e)))))
      (C*(2*(U0*a)+a*a)) := by
    by_cases hij : i=j
    · simpa only [diagonal, if_pos hij] using V
    · simpa only [diagonal, if_neg hij] using
        (Interval.constant blocks 0 (Q'.le_refl' _)).weaken V.nonnegative
  let H := (D.add (((P.mul (DDE i j)).add (E.mul (DDP i j))).add
    (Interval.neg (E.mul (DDE i j))))).add
    ((Interval.neg (((DP i).mul (DE j)).add ((DE i).mul (DP j)))).add ((DE i).mul (DE j)))
  exact H.changeCap (poly_identity_of_normal_eq
    (.add
      (.add (.mul (.var 0) (.add (.mul (.const 2) (.mul (.var 1) (.var 4)))
        (.mul (.var 4) (.var 4))))
        (.add (.add (.mul (.var 1) (.var 6)) (.mul (.var 4) (.var 3)))
          (.mul (.var 4) (.var 6))))
      (.add (.add (.mul (.var 2) (.var 5)) (.mul (.var 5) (.var 2)))
        (.mul (.var 5) (.var 5))))
    (.add
      (.add (.mul (.var 0) (.add (.mul (.const 2) (.mul (.var 1) (.var 4)))
        (.mul (.var 4) (.var 4))))
        (.add (.add (.mul (.var 1) (.var 6)) (.mul (.var 4) (.var 3)))
          (.mul (.var 4) (.var 6))))
      (.add (.mul (.const 2) (.mul (.var 2) (.var 5))) (.mul (.var 5) (.var 5))))
    (by decide) (fun
      | 0 => C | 1 => U0 | 2 => U1 | 3 => U2
      | 4 => a | 5 => b | _ => c))

/-- Transfer the full frozen form; all error and floor witnesses remain explicit. -/
def curvature_approximation_certificate {blocks : Nat} {C m U0 U1 U2 a b c : Q'}
    {p f e : RatPoly} {dp df de : Fin 3 → RatPoly}
    {ddp ddf dde : Fin 3 → Fin 3 → RatPoly}
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (hC : (0 : Q') ≤ C) (hm : (0 : Q') ≤ m)
    (h0 : RatPolyCoeffEqv p (polyAdd f e))
    (h1 : ∀ i, RatPolyCoeffEqv (dp i) (polyAdd (df i) (de i)))
    (h2 : ∀ i j, RatPolyCoeffEqv (ddp i j) (polyAdd (ddf i j) (dde i j)))
    (P : Interval blocks p U0) (E : Interval blocks e a)
    (DP : ∀ i, Interval blocks (dp i) U1) (DE : ∀ i, Interval blocks (de i) b)
    (DDP : ∀ i j, Interval blocks (ddp i j) U2)
    (DDE : ∀ i j, Interval blocks (dde i j) c)
    (hbudget : 6*errorCap C U0 U1 U2 a b c ≤ m*m)
    (floor : Certificate blocks (polyAdd p (polyNeg (cap m))))
    (weighted : Certificate blocks (jetCurvature C f df ddf u)) :
    Certificate blocks (jetCurvature (C+1) p dp ddp u) := by
  let B := errorCap C U0 U1 U2 a b c
  let M := errorEntry C p e dp de ddp dde
  let Q := error_interval hC P E DP DE DDP DDE
  let direction : Certificate blocks (threeSquare u) :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let envelope := three_polynomial_matrix_envelope_certificate (cap B) u M hu
    (fun i j => (Q i j).lower) (fun i j => (Q i j).upper)
  have hcap : RatPolyCoeffEqv (polyMul (cap 6) (cap B)) (cap (6*B)) :=
    QuaternionHaarPolynomialSquareBound.cap_mul 6 B
  let discrepancy := Certificate.ofCoeff
    ((hcap.symm.mul (RatPolyCoeffEqv.refl _)).add
      (curvature_difference_pin C u h0 h1 h2)) envelope
  let payment := direction.mul (floor_square_payment hm hbudget floor)
  have hC1 : RatPolyCoeffEqv (cap (C+1)) (polyAdd (cap C) polyOne) :=
    (cap_add C 1).symm.trans ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul polyOne))
  exact Certificate.ofCoeff
    (((hC1.mul (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.const 1)) (.mul (.var 1) (.mul (.var 2) (.var 2))))
          (.var 3))
        (.add
          (.add (.var 4)
            (.add (.mul (.var 5) (.var 1))
              (minus (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
                (.var 3)) (.var 4))))
          (.mul (.var 1) (minus (.mul (.var 2) (.var 2)) (.var 5))))
        (by decide) (fun
          | 0 => cap C | 1 => threeSquare u | 2 => p
          | 3 => polyAdd (polyMul p (quadraticForm u ddp))
              (polyNeg (polyMul (firstJet u dp) (firstJet u dp)))
          | 4 => jetCurvature C f df ddf u | _ => cap (6*B))))
    ((weighted.add discrepancy).add payment)

end YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation

#print axioms YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation.curvature_difference_pin
#print axioms YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation.error_interval
#print axioms YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation.curvature_approximation_certificate
