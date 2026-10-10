/-
An actual polynomial presentation in the represented original-Haar domain.
The dense input is evaluation of the SAME rational polynomial on the actual
four quaternion coordinates. Its bound and continuity radius are produced from
finite coefficient data, without an assumed admissibility or Haar-value field.
The actual completed map recovers pointEval, and supported polynomials recover
their ORIGINAL Haar moments. Polynomial products are the same pointwise products
on every Point. The first coordinate supplies a nonconstant mean-zero member
whose same square has moment 1/4. This is not a continuum excitation, interacting
variance estimate, full continuous function algebra, or physical mass gap.
-/

import YMGap.Continuum.QuaternionRepresentedHaar
import YMGap.Continuum.RatPolyCubeLipschitz
import YMGap.Continuum.QuaternionCompletedPolynomialApproximation
import YMGap.Continuum.QuaternionPointPolynomialDenseEvaluation

namespace YMGap.Continuum.QuaternionRepresentedPolynomialHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RatPolyCubeLipschitz
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionRepresentedHaar
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.QuaternionDenseCRealHaarComparison
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionCompletedPolynomialApproximation
open YMGap.Continuum.QuaternionPointPolynomialDenseEvaluation
open YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

private theorem abs_square (a : Q') : Q'.abs a * Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => a)

private theorem abs_le_of_square_le {a delta : Q'}
    (hdelta : (0 : Q') < delta) (h : a*a ≤ delta*delta) :
    Q'.abs a ≤ delta :=
  CReal.le_of_sq_le_sq hdelta (Q'.abs_nonneg a)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square a)) h)

private theorem environment_cube (q : UnitNorm) :
    CompactCubeEnvironment (environmentOf q.val) := by
  intro index
  by_cases h : index < 4
  · have hs : coordinate q.val ⟨index,h⟩ * coordinate q.val ⟨index,h⟩ ≤ 1 :=
      Q'.le_trans' _ _ _ (coordinate_square_le q.val ⟨index,h⟩)
        (Q'.le_of_eqv q.unitNorm)
    have habs : Q'.abs (coordinate q.val ⟨index,h⟩) ≤ 1 :=
      abs_le_of_square_le (by decide : (0 : Q') < 1)
        (Q'.le_trans' _ _ _ hs
          (Q'.le_of_eqv (by decide : (1 : Q') ≈ 1*1)))
    simpa only [environmentOf, h, dite_true] using habs
  · simpa only [environmentOf, h, dite_false] using
      (by decide : Q'.abs (0 : Q') ≤ (1 : Q'))

private theorem environment_motion (q x : UnitNorm) (delta : Q')
    (hdelta : (0 : Q') < delta)
    (hd : distSq q.val x.val ≤ delta*delta) :
    ∀ index, Q'.abs (environmentOf q.val index +
      -(environmentOf x.val index)) ≤ delta := by
  intro index
  by_cases h : index < 4
  · have hs : (coordinate q.val ⟨index,h⟩ +
        -coordinate x.val ⟨index,h⟩) *
        (coordinate q.val ⟨index,h⟩ +
        -coordinate x.val ⟨index,h⟩) ≤ delta*delta :=
      Q'.le_trans' _ _ _
        (coordinate_difference_square_le q.val x.val ⟨index,h⟩) hd
    simpa only [environmentOf, h, dite_true] using
      (abs_le_of_square_le hdelta hs)
  · have hz : Q'.abs ((0 : Q') + -0) ≤ delta :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (by decide : Q'.abs ((0 : Q') + -0) ≈ 0))
        (Q'.le_of_lt hdelta)
    simpa only [environmentOf, h, dite_false] using hz

/-- Literal rational polynomial evaluation on the actual dense quaternion. -/
def polynomialInput (p : RatPoly) (q : UnitNorm) : CReal :=
  CReal.ofQ' (evalRatPoly (environmentOf q.val) p)

/-- Constant approximants have the computed zero Type-level output rate. -/
def polynomialInner (p : RatPoly) :
    ∀ q, InnerRegularity (polynomialInput p q) :=
  fun q => InnerRegularity.ofQ' (evalRatPoly (environmentOf q.val) p)

/-- A positive squared-chord radius, with no division by the polynomial
Lipschitz coefficient, including the zero-coefficient/constant case. -/
def polynomialRadius (p : RatPoly) (epsilon : Q') : Q' :=
  let delta := InnerRegularity.scaleTolerance (polynomialLipschitz p) epsilon
  delta*delta

theorem polynomialRadius_positive (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) : (0 : Q') < polynomialRadius p epsilon := by
  exact Q'.mul_pos
    (InnerRegularity.scaleTolerance_pos (polynomialLipschitz p) epsilon he)
    (InnerRegularity.scaleTolerance_pos (polynomialLipschitz p) epsilon he)

/-- Coefficient-L1 is a produced sound bound on the ACTUAL dense evaluation;
arbitrary signed terms, repeats, and empty polynomials are included. -/
theorem polynomial_bound (p : RatPoly) (q : UnitNorm) :
    leRat (CReal.abs (polynomialInput p q)) (polynomialCoefficientL1 p) :=
  CReal.leRat_ofQ'
    (evalRatPoly_abs_le_coefficientL1 (environmentOf q.val)
      (environment_cube q) p)

/-- Squared-chord continuity of the ACTUAL dense polynomial, with a computed
radius and no supplied modulus premise. -/
theorem polynomial_modulus (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ polynomialRadius p epsilon) :
    leRat (CReal.abs (CReal.add (polynomialInput p q)
      (CReal.neg (polynomialInput p x)))) epsilon := by
  let L := polynomialLipschitz p
  let delta := InnerRegularity.scaleTolerance L epsilon
  have hdelta : (0 : Q') < delta :=
    InnerRegularity.scaleTolerance_pos L epsilon he
  have hmotion : ∀ index, Q'.abs (environmentOf q.val index +
      -(environmentOf x.val index)) ≤ delta :=
    environment_motion q x delta hdelta hd
  have hpoly : Q'.abs (evalRatPoly (environmentOf q.val) p +
      -(evalRatPoly (environmentOf x.val) p)) ≤ L*delta :=
    polynomial_difference (environmentOf q.val) (environmentOf x.val)
      (environment_cube q) (environment_cube x) delta hmotion p
  exact CReal.leRat_ofQ' (Q'.le_trans' _ _ _ hpoly
    (InnerRegularity.mul_scaleTolerance_le L epsilon
      (polynomialLipschitz_nonnegative p) he))

/-- Produced admissibility data for every finite signed rational polynomial.
This constructor assumes neither a completed-map pin nor an integral value. -/
def polynomialData (p : RatPoly) : DenseData where
  values := polynomialInput p
  inner := polynomialInner p
  bound := polynomialCoefficientL1 p
  radius := polynomialRadius p
  radius_positive := polynomialRadius_positive p
  bounded := polynomial_bound p
  continuity := polynomial_modulus p

/-- A concrete member of the represented Haar domain, not a membership premise. -/
def polynomial (p : RatPoly) : Represented := classOf (polynomialData p)

private theorem polynomial_input_pin (p : RatPoly) (q : UnitNorm) :
    leRat (CReal.abs (CReal.add (polynomialInput p q)
      (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) 0 :=
  self_input_distance_zero (polynomialInput p q)

/-- The produced member is the SAME existing polynomial map on EVERY Point.
No support hypothesis is needed for this map identity. -/
theorem evaluate_polynomial (p : RatPoly) (x : Point) :
    evaluate (polynomial p) x = pointEval x p :=
  pointPolynomial_compatible (polynomialInput p) (polynomialInner p)
    (polynomialRadius p) (polynomialRadius_positive p) (polynomial_modulus p)
    p (polynomial_input_pin p) x

/-- The ACTUAL integral recovers the ORIGINAL moment. The syntactic support
condition belongs to this moment pin, not to admissibility or map evaluation. -/
theorem integral_polynomial (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    integral (polynomial p) = rational (quaternionHaar 1 p) := by
  apply Quotient.sound
  exact haarApproximation_polynomial_compatible
    (polynomialInput p) (polynomialInner p) (polynomialCoefficientL1 p)
    (polynomialRadius p) (polynomialRadius_positive p) (polynomial_bound p)
    (polynomial_modulus p) p hp (polynomial_input_pin p)

/-- Polynomial multiplication gives the SAME pointwise RC product on every
Point. This is polynomial-subfamily closure, not closure of all Represented. -/
theorem evaluate_polynomial_mul (p q : RatPoly) (x : Point) :
    evaluate (polynomial (polyMul p q)) x =
      RCmul (evaluate (polynomial p) x) (evaluate (polynomial q) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  change Quotient.mk crealSetoid
      (rowImage (polynomialInput (polyMul p q)) (polynomialInner (polyMul p q))
        (polynomialRadius (polyMul p q)) (polynomialRadius_positive (polyMul p q))
        (polynomial_modulus (polyMul p q)) X) =
    RCmul (Quotient.mk crealSetoid
      (rowImage (polynomialInput p) (polynomialInner p)
        (polynomialRadius p) (polynomialRadius_positive p) (polynomial_modulus p) X))
      (Quotient.mk crealSetoid
      (rowImage (polynomialInput q) (polynomialInner q)
        (polynomialRadius q) (polynomialRadius_positive q) (polynomial_modulus q) X))
  rw [RCmul_mk]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact evalRatPoly_mul (environmentOf (X.seq n).val) p q

/-- A concrete first-coordinate observable on the completed unit quaternion. -/
def coordinateObservable : Represented := polynomial (polyVar 0)

theorem coordinate_supported : SupportedQuaternionBlocks 1 (polyVar 0) := by
  intro term hterm
  have h : term = ([1], (1 : Q')) := by
    simpa [polyVar, varMono] using hterm
  subst term
  decide

theorem coordinate_square_supported :
    SupportedQuaternionBlocks 1 (polyMul (polyVar 0) (polyVar 0)) := by
  intro term hterm
  have h : term = ([2], (1 : Q') * 1) := by
    simpa [polyVar, varMono, polyMul, monoMul] using hterm
  subst term
  decide

/-- Exact mean zero for this concrete member under the ACTUAL integral. -/
theorem coordinate_mean_zero : integral coordinateObservable = rational 0 := by
  rw [coordinateObservable, integral_polynomial _ coordinate_supported]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

/-- The original second moment is 1/4. The product pin above identifies this
polynomial with the square of the SAME coordinate, rather than a proxy map. -/
theorem coordinate_second_moment :
    integral (polynomial (polyMul (polyVar 0) (polyVar 0))) =
      rational (HalfPow.half * HalfPow.half) := by
  rw [integral_polynomial _ coordinate_square_supported]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

theorem coordinate_square_pin (x : Point) :
    evaluate (polynomial (polyMul (polyVar 0) (polyVar 0))) x =
      RCmul (evaluate coordinateObservable x) (evaluate coordinateObservable x) :=
  evaluate_polynomial_mul (polyVar 0) (polyVar 0) x

theorem coordinate_second_moment_positive :
    (0 : Q') < HalfPow.half * HalfPow.half := by decide

theorem coordinate_at_one :
    evaluate coordinateObservable (embed unitOne) = rational 1 := by
  rw [coordinateObservable, evaluate_polynomial, pointEval_embed]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

theorem coordinate_at_negative_one :
    evaluate coordinateObservable (embed unitNegativeOne) = rational (-1) := by
  rw [coordinateObservable, evaluate_polynomial, pointEval_embed]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

/-- Nonconstancy is witnessed by the two concrete central units. This is Haar
domain nonconstancy only, not survival of a continuum Yang--Mills excitation. -/
theorem coordinate_nonconstant :
    evaluate coordinateObservable (embed unitOne) ≠
      evaluate coordinateObservable (embed unitNegativeOne) := by
  intro h
  rw [coordinate_at_one, coordinate_at_negative_one] at h
  have hE : Equiv (CReal.ofQ' 1) (CReal.ofQ' (-1)) := Quotient.exact h
  obtain ⟨N, hN⟩ := hE 1 (by decide)
  have hbad : (1 : Q') ≤ (-1) + 1 := (hN N (Nat.le_refl _)).1
  exact (by decide : ¬ ((1 : Q') ≤ (-1) + 1)) hbad

#print axioms polynomialInput
#print axioms polynomialInner
#print axioms polynomialRadius
#print axioms polynomialRadius_positive
#print axioms polynomial_bound
#print axioms polynomial_modulus
#print axioms polynomialData
#print axioms polynomial
#print axioms evaluate_polynomial
#print axioms integral_polynomial
#print axioms evaluate_polynomial_mul
#print axioms coordinateObservable
#print axioms coordinate_supported
#print axioms coordinate_square_supported
#print axioms coordinate_mean_zero
#print axioms coordinate_second_moment
#print axioms coordinate_square_pin
#print axioms coordinate_second_moment_positive
#print axioms coordinate_at_one
#print axioms coordinate_at_negative_one
#print axioms coordinate_nonconstant

end YMGap.Continuum.QuaternionRepresentedPolynomialHaar
