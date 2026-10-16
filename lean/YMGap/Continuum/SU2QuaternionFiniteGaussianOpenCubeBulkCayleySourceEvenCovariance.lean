/-
# Even source-source order-six Cayley covariance

For two trace-source insertions, two of the three source-only order-six terms
are

  Cov(A4(left), A2(right)) + Cov(A2(left), A4(right)).

This leaf reduces both terms to finite weighted sums of the checked six-row
Wick recursion on the exact open-cube Cayley source blocks.  Covariance
symmetry is proved from the literal evaluator rather than assumed, so the
same quadratic-before-quartic compiler serves both orientations.

The cubic-cubic covariance, mixed source/action cumulants, OWN normalization,
supplied OLD centers, higher remainder and ORIGINAL-law comparison remain
separate obligations.  No sign, uniform estimate or physical mass gap is
claimed here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem gaussian_zero (N : Nat) :
    finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (left right : RatPoly) :
    finiteProductGaussian N (polyAdd left right) ≈
      finiteProductGaussian N left + finiteProductGaussian N right := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe,
    finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) left right

private theorem gaussian_smul (N : Nat) (weight : Q')
    (polynomial : RatPoly) :
    finiteProductGaussian N (polySmul weight polynomial) ≈
      weight * finiteProductGaussian N polynomial := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) weight polynomial

/-- Covariance respects coefficientwise equality in both polynomial slots. -/
theorem finiteGaussianCovariance_coeffEqv
    (N : Nat) {left left' right right' : RatPoly}
    (hleft : RatPolyCoeffEqv left left')
    (hright : RatPolyCoeffEqv right right') :
    finiteGaussianCovariance N left right ≈
      finiteGaussianCovariance N left' right' := by
  unfold finiteGaussianCovariance
  exact Q'.add_eqv_congr'
    (finiteProductGaussian_coeffEqv N (hleft.mul hright))
    (Q'.neg_eqv_congr _ _
      (mul_congr
        (finiteProductGaussian_coeffEqv N hleft)
        (finiteProductGaussian_coeffEqv N hright)))

/-- Literal symmetry of the finite product-Gaussian covariance. -/
theorem finiteGaussianCovariance_comm
    (N : Nat) (left right : RatPoly) :
    finiteGaussianCovariance N left right ≈
      finiteGaussianCovariance N right left := by
  unfold finiteGaussianCovariance
  exact Q'.add_eqv_congr'
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.mul_comm left right))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_comm_eqv
        (finiteProductGaussian N left)
        (finiteProductGaussian N right)))

/-- Pull rational weights out of both finite Gaussian covariance slots. -/
theorem finiteGaussianCovariance_smul
    (N : Nat) (leftWeight rightWeight : Q')
    (left right : RatPoly) :
    finiteGaussianCovariance N
        (polySmul leftWeight left) (polySmul rightWeight right) ≈
      (leftWeight * rightWeight) *
        finiteGaussianCovariance N left right := by
  have product :
      finiteProductGaussian N
          (polyMul (polySmul leftWeight left)
            (polySmul rightWeight right)) ≈
        (leftWeight * rightWeight) *
          finiteProductGaussian N (polyMul left right) := by
    exact Q'.eqv_trans _ _ _
      (finiteProductGaussian_coeffEqv N
        ((RatPolyCoeffEqv.polyMul_smul_left
            leftWeight left (polySmul rightWeight right)).trans
          (((RatPolyCoeffEqv.polyMul_smul_right
              rightWeight left right).smul leftWeight).trans
            (RatPolyCoeffEqv.smul_assoc
              leftWeight rightWeight (polyMul left right)))))
      (gaussian_smul N (leftWeight * rightWeight) (polyMul left right))
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' product
      (Q'.neg_eqv_congr _ _
        (mul_congr
          (gaussian_smul N leftWeight left)
          (gaussian_smul N rightWeight right))))
    (poly_identity_of_normal_eq
      (.add
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg
          (.mul (.mul (.var 0) (.var 3))
            (.mul (.var 1) (.var 4)))))
      (.mul (.mul (.var 0) (.var 1))
        (.add (.var 2) (.neg (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => leftWeight
        | 1 => rightWeight
        | 2 => finiteProductGaussian N (polyMul left right)
        | 3 => finiteProductGaussian N left
        | _ => finiteProductGaussian N right))

private theorem covariance_add_left
    (N : Nat) (left₁ left₂ right : RatPoly) :
    finiteGaussianCovariance N (polyAdd left₁ left₂) right ≈
      finiteGaussianCovariance N left₁ right +
        finiteGaussianCovariance N left₂ right := by
  unfold finiteGaussianCovariance
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (gaussian_add N (polyMul left₁ right) (polyMul left₂ right))
      (Q'.neg_eqv_congr _ _
        (mul_congr (gaussian_add N left₁ left₂) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.add (.var 2) (.var 3)) (.var 4))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
        (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul left₁ right)
        | 1 => finiteProductGaussian N (polyMul left₂ right)
        | 2 => finiteProductGaussian N left₁
        | 3 => finiteProductGaussian N left₂
        | _ => finiteProductGaussian N right))

private theorem covariance_add_right
    (N : Nat) (left right₁ right₂ : RatPoly) :
    finiteGaussianCovariance N left (polyAdd right₁ right₂) ≈
      finiteGaussianCovariance N left right₁ +
        finiteGaussianCovariance N left right₂ := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_add_right left right₁ right₂))
        (gaussian_add N (polyMul left right₁) (polyMul left right₂)))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _) (gaussian_add N right₁ right₂))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
        (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul left right₁)
        | 1 => finiteProductGaussian N (polyMul left right₂)
        | 2 => finiteProductGaussian N left
        | 3 => finiteProductGaussian N right₁
        | _ => finiteProductGaussian N right₂))

private theorem covariance_zero_left (N : Nat) (right : RatPoly) :
    finiteGaussianCovariance N polyZero right ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (gaussian_zero N)
      (Q'.neg_eqv_congr _ _
        (mul_congr (gaussian_zero N) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.const 0) (.var 0))))
      (.const 0) (by decide)
      (fun _ => finiteProductGaussian N right))

private theorem covariance_zero_right (N : Nat) (left : RatPoly) :
    finiteGaussianCovariance N left polyZero ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_zero_right left))
        (gaussian_zero N))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _) (gaussian_zero N))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.var 0) (.const 0))))
      (.const 0) (by decide)
      (fun _ => finiteProductGaussian N left))

/-- Expand a finite polynomial sum in the left covariance slot. -/
theorem finiteGaussianCovariance_polySum_left
    (N : Nat) (right : RatPoly) : ∀ polynomials : List RatPoly,
    finiteGaussianCovariance N (polySum polynomials) right ≈
      qListSum (polynomials.map fun polynomial =>
        finiteGaussianCovariance N polynomial right)
  | [] => covariance_zero_left N right
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _
        (covariance_add_left N polynomial (polySum polynomials) right)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (finiteGaussianCovariance_polySum_left N right polynomials))

/-- Expand a finite polynomial sum in the right covariance slot. -/
theorem finiteGaussianCovariance_polySum_right
    (N : Nat) (left : RatPoly) : ∀ polynomials : List RatPoly,
    finiteGaussianCovariance N left (polySum polynomials) ≈
      qListSum (polynomials.map fun polynomial =>
        finiteGaussianCovariance N left polynomial)
  | [] => covariance_zero_right N left
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _
        (covariance_add_right N left polynomial (polySum polynomials))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (finiteGaussianCovariance_polySum_right N left polynomials))

/-- Termwise rational equivalence transports through one finite scalar sum. -/
theorem finiteGaussianCovariance_qListSum_congr {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (finiteGaussianCovariance_qListSum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

/-- Exact six-row Wick reduction of one quadratic/quartic covariance. -/
def finiteGaussianTwoFourCovarianceWickReduction
    (N : Nat) (a b c d e f : Nat → Q') : Q' :=
  finiteGaussianRowWickStep N a [b, c, d, e, f] -
    finiteRowGram N a b * finiteRowFourWickValue N c d e f

/-- One ordered quadratic row word covaried with one ordered quartic row word
reduces to the checked six-row Wick step and explicit lower moments. -/
theorem finiteGaussianCovariance_two_four_row_words_wick
    (N : Nat) (a b c d e f : Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d, e, f]) ≈
      finiteGaussianTwoFourCovarianceWickReduction N a b c d e f := by
  have productPolynomial : RatPolyCoeffEqv
      (polyMul
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d, e, f]))
      (finiteGaussianRowWord N [a, b, c, d, e, f]) :=
    finiteGaussianRowWord_append_nonempty N a c [b] [d, e, f]
  have productValue := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N productPolynomial)
    (finiteProductGaussian_six_rows_wick N a b c d e f)
  have quadraticValue := finiteProductGaussian_two_row_word N a b
  have quarticValue := finiteProductGaussian_four_row_word N c d e f
  unfold finiteGaussianCovariance
    finiteGaussianTwoFourCovarianceWickReduction finiteRowFourWickValue
  exact Q'.add_eqv_congr' productValue
    (Q'.neg_eqv_congr _ _ (mul_congr quadraticValue quarticValue))

/-- Explicit weighted double sum of the quadratic/quartic covariance Wick
reductions. -/
def finiteGaussianWeightedTwoFourCovarianceWickSum
    (N : Nat)
    (quadratics : List WeightedQuadraticRowBlock)
    (quartics : List WeightedQuarticRowBlock) : Q' :=
  qListSum (quadratics.map fun quadratic =>
    qListSum (quartics.map fun quartic =>
      (quadratic.weight * quartic.weight) *
        finiteGaussianTwoFourCovarianceWickReduction N
          quadratic.first quadratic.second
          quartic.first quartic.second quartic.third quartic.fourth))

/-- Covariance of finite weighted quadratic and quartic row-block sums is
the displayed finite double Wick sum. -/
theorem finiteGaussianCovariance_weighted_two_four_row_blocks_wick
    (N : Nat)
    (quadratics : List WeightedQuadraticRowBlock)
    (quartics : List WeightedQuarticRowBlock) :
    finiteGaussianCovariance N
        (weightedTermPolynomial
          (quadratics.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (quartics.map (weightedQuarticRowBlockTerm N))) ≈
      finiteGaussianWeightedTwoFourCovarianceWickSum
        N quadratics quartics := by
  let quadraticPolynomial := fun quadratic : WeightedQuadraticRowBlock =>
    polySmul quadratic.weight
      (finiteGaussianRowWord N [quadratic.first, quadratic.second])
  let quarticPolynomial := fun quartic : WeightedQuarticRowBlock =>
    polySmul quartic.weight
      (finiteGaussianRowWord N
        [quartic.first, quartic.second, quartic.third, quartic.fourth])
  let reduced := fun quadratic : WeightedQuadraticRowBlock =>
    fun quartic : WeightedQuarticRowBlock =>
      (quadratic.weight * quartic.weight) *
        finiteGaussianTwoFourCovarianceWickReduction N
          quadratic.first quadratic.second
          quartic.first quartic.second quartic.third quartic.fourth
  unfold weightedTermPolynomial
    weightedQuadraticRowBlockTerm weightedQuarticRowBlockTerm
    finiteGaussianWeightedTwoFourCovarianceWickSum
  simp only [List.map_map]
  change finiteGaussianCovariance N
      (polySum (quadratics.map quadraticPolynomial))
      (polySum (quartics.map quarticPolynomial)) ≈
    qListSum (quadratics.map fun quadratic =>
      qListSum (quartics.map (reduced quadratic)))
  have expandQuadratics :
      finiteGaussianCovariance N
          (polySum (quadratics.map quadraticPolynomial))
          (polySum (quartics.map quarticPolynomial)) ≈
        qListSum (quadratics.map fun quadratic =>
          finiteGaussianCovariance N (quadraticPolynomial quadratic)
            (polySum (quartics.map quarticPolynomial))) :=
    by
      simpa only [List.map_map, Function.comp_apply] using
        finiteGaussianCovariance_polySum_left N
          (polySum (quartics.map quarticPolynomial))
          (quadratics.map quadraticPolynomial)
  have reduceQuadratics :
      qListSum (quadratics.map fun quadratic =>
          finiteGaussianCovariance N (quadraticPolynomial quadratic)
            (polySum (quartics.map quarticPolynomial))) ≈
        qListSum (quadratics.map fun quadratic =>
          qListSum (quartics.map (reduced quadratic))) := by
    exact finiteGaussianCovariance_qListSum_congr _ _ quadratics (fun quadratic _ => by
      have expandQuartics :
          finiteGaussianCovariance N (quadraticPolynomial quadratic)
              (polySum (quartics.map quarticPolynomial)) ≈
            qListSum (quartics.map fun quartic =>
              finiteGaussianCovariance N (quadraticPolynomial quadratic)
                (quarticPolynomial quartic)) :=
        by
          simpa only [List.map_map, Function.comp_apply] using
            finiteGaussianCovariance_polySum_right N (quadraticPolynomial quadratic)
              (quartics.map quarticPolynomial)
      have reduceQuartics :
          qListSum (quartics.map fun quartic =>
              finiteGaussianCovariance N (quadraticPolynomial quadratic)
                (quarticPolynomial quartic)) ≈
            qListSum (quartics.map (reduced quadratic)) := by
        exact finiteGaussianCovariance_qListSum_congr _ _ quartics (fun quartic _ => by
          exact Q'.eqv_trans _ _ _
            (finiteGaussianCovariance_smul N quadratic.weight quartic.weight _ _)
            (Q'.mul_eqv_congr_left _ _ _
              (finiteGaussianCovariance_two_four_row_words_wick N
                quadratic.first quadratic.second
                quartic.first quartic.second
                quartic.third quartic.fourth)))
      exact Q'.eqv_trans _ _ _ expandQuartics reduceQuartics)
  exact Q'.eqv_trans _ _ _ expandQuadratics reduceQuadratics

/-- Exact finite Wick value of the two even source-source order-six
covariances for two selected history times. -/
def openCubeBulkCayleyTraceEvenOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  finiteGaussianWeightedTwoFourCovarianceWickSum N
      (openCubeBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage rightTime)
      (openCubeBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage leftTime) +
    finiteGaussianWeightedTwoFourCovarianceWickSum N
      (openCubeBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage leftTime)
      (openCubeBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage rightTime)

/-- The literal even source-source contribution
`Cov(A4(left),A2(right))+Cov(A2(left),A4(right))` is exactly the displayed
finite weighted six-row Wick sum. -/
theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_even_orderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA4
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA4
          timeBonds side sidePositive stage rightTime) ≈
      openCubeBulkCayleyTraceEvenOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let leftQuadratics := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightQuadratics := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let leftQuartics := openCubeBulkCayleyTraceA4RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightQuartics := openCubeBulkCayleyTraceA4RowBlocks
    timeBonds side sidePositive stage rightTime
  have leftQuadraticCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightQuadraticCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have leftQuarticCertificate := openCubeBulkCayleyTraceA4_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightQuarticCertificate := openCubeBulkCayleyTraceA4_coeffEqv
    timeBonds side sidePositive stage rightTime
  have firstCovariance :
      finiteGaussianCovariance N
          (openCubeBulkCayleyTraceA4
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage rightTime) ≈
        finiteGaussianWeightedTwoFourCovarianceWickSum
          N rightQuadratics leftQuartics := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N
        leftQuarticCertificate rightQuadraticCertificate)
      (Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_comm N
          (weightedTermPolynomial
            (leftQuartics.map (weightedQuarticRowBlockTerm N)))
          (weightedTermPolynomial
            (rightQuadratics.map (weightedQuadraticRowBlockTerm N))))
        (finiteGaussianCovariance_weighted_two_four_row_blocks_wick
          N rightQuadratics leftQuartics))
  have secondCovariance :
      finiteGaussianCovariance N
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA4
            timeBonds side sidePositive stage rightTime) ≈
        finiteGaussianWeightedTwoFourCovarianceWickSum
          N leftQuadratics rightQuartics := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N
        leftQuadraticCertificate rightQuarticCertificate)
      (finiteGaussianCovariance_weighted_two_four_row_blocks_wick
        N leftQuadratics rightQuartics)
  unfold openCubeBulkCayleyTraceEvenOrderSixCovarianceWickSum
  exact Q'.add_eqv_congr' firstCovariance secondCovariance

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance.finiteGaussianCovariance_two_four_row_words_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance.finiteGaussianCovariance_weighted_two_four_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance.finiteGaussianCovariance_openCube_bulk_cayley_trace_even_orderSix_wick
