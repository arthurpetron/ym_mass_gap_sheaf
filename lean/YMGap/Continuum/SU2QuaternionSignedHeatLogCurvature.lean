/-
# Signed mixed curvature of the actual relative heat

The double signed sum retains all mixed entries. Its cost is the product of
the two coefficient l1 budgets; block localization is a separate theorem.
This does not replace grouped coefficient-square control by a global l1 norm.
-/

import YMGap.Continuum.QuaternionHaarRelativePolynomialInterval
import YMGap.Continuum.SU2QuaternionHeatLogCurvature
import YMGap.Continuum.SU2QuaternionSignedAngularAlgebra

namespace YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionSignedAngularAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

def coefficientL1 {n : Nat} : List (AngularTerm n) → Q'
  | [] => 0
  | term :: terms => Q'.abs term.coefficient + coefficientL1 terms

def rawDirection {n : Nat} (term : AngularTerm n) : RatPoly → RatPoly :=
  angularDerivative (4*term.block.val+term.first.val) (4*term.block.val+term.second.val)

def jetNumerator (h x y z : RatPoly) : RatPoly :=
  polyAdd (polyMul h z) (polyNeg (polyMul x y))

def termNumerator {n : Nat} (h : RatPoly) (term : AngularTerm n)
    (terms : List (AngularTerm n)) : RatPoly :=
  jetNumerator h (rawDirection term h) (signedAngularDirection terms h)
    (rawDirection term (signedAngularDirection terms h))

def signedNumerator {n : Nat} (h : RatPoly) (outer inner : List (AngularTerm n)) : RatPoly :=
  jetNumerator h (signedAngularDirection outer h) (signedAngularDirection inner h)
    (signedAngularDirection outer (signedAngularDirection inner h))

private theorem jet_left (h x x' y z z' : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (jetNumerator h (polyAdd (polySmul c x) x') y (polyAdd (polySmul c z) z'))
      (polyAdd (polySmul c (jetNumerator h x y z)) (jetNumerator h x' y z')) := by
  refine (((((cap_mul_left c z).symm.add (.refl z')).mul_left h).add
    (RatPolyCoeffEqv.neg (((cap_mul_left c x).symm.add (.refl x')).mul_right y))).trans ?_)
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.mul (.var 6) (.var 4)) (.var 5)))
      (.neg (.mul (.add (.mul (.var 6) (.var 1)) (.var 2)) (.var 3))))
    (.add (.mul (.var 6) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))
      (.add (.mul (.var 0) (.var 5)) (.neg (.mul (.var 2) (.var 3)))))
    (by decide) (fun | 0 => h | 1 => x | 2 => x' | 3 => y | 4 => z | 5 => z' | _ => cap c)).trans ?_
  exact (cap_mul_left c _).add (.refl _)

private theorem jet_right (h x y y' z z' : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (jetNumerator h x (polyAdd (polySmul c y) y') (polyAdd (polySmul c z) z'))
      (polyAdd (polySmul c (jetNumerator h x y z)) (jetNumerator h x y' z')) := by
  refine (((((cap_mul_left c z).symm.add (.refl z')).mul_left h).add
    (RatPolyCoeffEqv.neg (((cap_mul_left c y).symm.add (.refl y')).mul_left x))).trans ?_)
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.mul (.var 6) (.var 4)) (.var 5)))
      (.neg (.mul (.var 1) (.add (.mul (.var 6) (.var 2)) (.var 3)))))
    (.add (.mul (.var 6) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 2)))))
      (.add (.mul (.var 0) (.var 5)) (.neg (.mul (.var 1) (.var 3)))))
    (by decide) (fun | 0 => h | 1 => x | 2 => y | 3 => y' | 4 => z | 5 => z' | _ => cap c)).trans ?_
  exact (cap_mul_left c _).add (.refl _)

theorem termNumerator_cons {n : Nat} (h : RatPoly) (outer inner : AngularTerm n)
    (terms : List (AngularTerm n)) :
    RatPolyCoeffEqv (termNumerator h outer (inner::terms))
      (polyAdd (polySmul inner.coefficient
        (jetNumerator h (rawDirection outer h) (rawDirection inner h)
          (rawDirection outer (rawDirection inner h)))) (termNumerator h outer terms)) := by
  have hd := (angularDerivative_add
    (4*outer.block.val+outer.first.val) (4*outer.block.val+outer.second.val)
    (applyAngularTerm inner h) (signedAngularDirection terms h)).trans
      ((angularDerivative_smul _ _ inner.coefficient (rawDirection inner h)).add (.refl _))
  exact ((hd.mul_left h).add (.refl _)).trans
    (jet_right h (rawDirection outer h) (rawDirection inner h)
      (signedAngularDirection terms h) (rawDirection outer (rawDirection inner h))
      (rawDirection outer (signedAngularDirection terms h)) inner.coefficient)

theorem signedNumerator_cons {n : Nat} (h : RatPoly) (term : AngularTerm n)
    (outer inner : List (AngularTerm n)) :
    RatPolyCoeffEqv (signedNumerator h (term::outer) inner)
      (polyAdd (polySmul term.coefficient (termNumerator h term inner))
        (signedNumerator h outer inner)) :=
  jet_left h (rawDirection term h) (signedAngularDirection outer h)
    (signedAngularDirection inner h) (rawDirection term (signedAngularDirection inner h))
    (signedAngularDirection outer (signedAngularDirection inner h)) term.coefficient

private theorem termNumerator_nil {n : Nat} (h : RatPoly) (term : AngularTerm n) :
    RatPolyCoeffEqv (termNumerator h term []) polyZero := by
  change RatPolyCoeffEqv
    (polyAdd (polyMul h polyZero) (polyNeg (polyMul (rawDirection term h) polyZero))) polyZero
  exact ((RatPolyCoeffEqv.mul_zero_right h).add
    (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_right _))).trans (.zero_add _)

private theorem signedNumerator_nil {n : Nat} (h : RatPoly) (inner : List (AngularTerm n)) :
    RatPolyCoeffEqv (signedNumerator h [] inner) polyZero := by
  exact ((RatPolyCoeffEqv.mul_zero_right h).add
    (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _))).trans (.zero_add _)

/-- All signed inner entries, before any locality simplification. -/
def termHeatCurvature {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) (outer : AngularTerm blocks) :
    (inner : List (AngularTerm blocks)) →
    RelativeInterval blocks (polyMul (heatAt a b w K) (heatAt a b w K))
      (termNumerator (heatAt a b w K) outer inner)
      (coefficientL1 inner * logCurvatureCap w hw0 hw1)
  | [] =>
    RelativeInterval.ofCoeff (termNumerator_nil _ _)
      ((RelativeInterval.zero blocks _).changeCap (Q'.zero_mul_eqv _).symm)
  | term::terms => by
    let bounds := heatLogHessianBounds ha hb outer.block.isLt term.block.isLt
      outer.first.isLt outer.second.isLt term.first.isLt term.second.isLt hw0 hw1 K hK
    let entry : RelativeInterval blocks (polyMul (heatAt a b w K) (heatAt a b w K))
        (jetNumerator (heatAt a b w K) (rawDirection outer (heatAt a b w K))
          (rawDirection term (heatAt a b w K))
          (rawDirection outer (rawDirection term (heatAt a b w K))))
        (logCurvatureCap w hw0 hw1) := ⟨bounds.1, bounds.2⟩
    let sum := (entry.smulSigned term.coefficient).add
      (termHeatCurvature ha hb hw0 hw1 K hK outer terms)
    exact RelativeInterval.ofCoeff (termNumerator_cons _ _ _ _)
      (sum.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => Q'.abs term.coefficient | 1 => coefficientL1 terms
             | _ => logCurvatureCap w hw0 hw1)))

/-- The complete signed mixed numerator, without dropping any cross term. -/
def signedHeatCurvature {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) (inner : List (AngularTerm blocks)) :
    (outer : List (AngularTerm blocks)) →
    RelativeInterval blocks (polyMul (heatAt a b w K) (heatAt a b w K))
      (signedNumerator (heatAt a b w K) outer inner)
      (coefficientL1 outer * (coefficientL1 inner * logCurvatureCap w hw0 hw1))
  | [] => RelativeInterval.ofCoeff (signedNumerator_nil _ _)
      ((RelativeInterval.zero blocks _).changeCap (Q'.zero_mul_eqv _).symm)
  | term::terms => by
    let sum := ((termHeatCurvature ha hb hw0 hw1 K hK term inner).smulSigned term.coefficient).add
      (signedHeatCurvature ha hb hw0 hw1 K hK inner terms)
    exact RelativeInterval.ofCoeff (signedNumerator_cons _ _ _ _)
      (sum.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => Q'.abs term.coefficient | 1 => coefficientL1 terms
             | _ => coefficientL1 inner * logCurvatureCap w hw0 hw1)))

end YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature

#print axioms YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature.termNumerator_cons
#print axioms YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature.signedNumerator_cons
#print axioms YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature.termHeatCurvature
#print axioms YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature.signedHeatCurvature
