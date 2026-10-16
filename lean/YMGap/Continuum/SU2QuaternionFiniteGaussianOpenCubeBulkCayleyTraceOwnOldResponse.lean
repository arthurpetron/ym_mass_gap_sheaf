/-
# Finite Cayley trace-source OWN/OLD response assembly

The connected coefficients do not by themselves equal the PRIMARY response
formed with a separately supplied OLD center.  This leaf records the exact
finite OWN means

  a2 = E A2,
  a3 = E A3 - Cov(A2,V3),
  a4 = E A4 - Cov(A3,V3) + Cov(A2,J2-V4)
         + (1/2) kappa(A2,V3,V3),

and assembles the literal OLD-centered coefficients `P4`, `P5`, `P6` for two
selected history times.  It also proves constructively that every actual
finite `a3` vanishes.  The supplied OLD coefficient `c3` is not assumed zero,
so its residual terms remain visible in both `P5` and `P6`.

This is finite FREE reference algebra.  It does not supply an ORIGINAL-law
center identification, higher-remainder control, a uniform signed estimate,
or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
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
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6

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

/-- Every finite weighted sum of ordered cubic row words has zero finite
product-Gaussian expectation. -/
theorem finiteProductGaussian_weighted_cubic_row_blocks_zero
    (N : Nat) : ∀ blocks : List WeightedCubicRowBlock,
    finiteProductGaussian N
        (weightedTermPolynomial
          (blocks.map (weightedCubicRowBlockTerm N))) ≈ 0
  | [] => gaussian_zero N
  | block :: blocks => by
      change finiteProductGaussian N
          (polyAdd
            (polySmul block.weight
              (finiteGaussianRowWord N
                [block.first, block.second, block.third]))
            (weightedTermPolynomial
              (blocks.map (weightedCubicRowBlockTerm N)))) ≈ 0
      exact Q'.eqv_trans _ _ _
        (gaussian_add N _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (gaussian_smul N block.weight _)
              (Q'.eqv_trans _ _ _
                (Q'.mul_eqv_congr_left block.weight _ _
                  (finiteProductGaussian_three_row_word_zero N
                    block.first block.second block.third))
                (Q'.mul_zero_eqv block.weight)))
            (finiteProductGaussian_weighted_cubic_row_blocks_zero N blocks))
          (QPoly.q_zero_add_eqv 0))

/-- A quadratic row word has zero covariance with a cubic row word. -/
theorem finiteGaussianCovariance_two_three_row_words_zero
    (N : Nat) (a b c d e : Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d, e]) ≈ 0 := by
  have productPolynomial : RatPolyCoeffEqv
      (polyMul
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d, e]))
      (finiteGaussianRowWord N [a, b, c, d, e]) :=
    finiteGaussianRowWord_append_nonempty N a c [b] [d, e]
  have productZero := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N productPolynomial)
    (finiteProductGaussian_five_row_word_zero N a b c d e)
  have quadraticValue := finiteProductGaussian_two_row_word N a b
  have cubicZero := finiteProductGaussian_three_row_word_zero N c d e
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' productZero
      (Q'.neg_eqv_congr _ _
        (mul_congr quadraticValue cubicZero)))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.var 0) (.const 0))))
      (.const 0) (by decide)
      (fun _ => finiteRowGram N a b))

private theorem qListSum_zero {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → value item ≈ 0) →
    qListSum (items.map value) ≈ 0
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hypothesis item List.mem_cons_self)
          (qListSum_zero value items
            (fun other membership =>
              hypothesis other (List.mem_cons_of_mem item membership))))
        (QPoly.q_zero_add_eqv 0)

/-- Finite weighted quadratic row blocks have zero covariance with finite
weighted cubic row blocks. -/
theorem finiteGaussianCovariance_weighted_two_three_row_blocks_zero
    (N : Nat)
    (quadratics : List WeightedQuadraticRowBlock)
    (cubics : List WeightedCubicRowBlock) :
    finiteGaussianCovariance N
        (weightedTermPolynomial
          (quadratics.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (cubics.map (weightedCubicRowBlockTerm N))) ≈ 0 := by
  let quadraticPolynomial := fun quadratic : WeightedQuadraticRowBlock =>
    polySmul quadratic.weight
      (finiteGaussianRowWord N [quadratic.first, quadratic.second])
  let cubicPolynomial := fun cubic : WeightedCubicRowBlock =>
    polySmul cubic.weight
      (finiteGaussianRowWord N [cubic.first, cubic.second, cubic.third])
  unfold weightedTermPolynomial
    weightedQuadraticRowBlockTerm weightedCubicRowBlockTerm
  simp only [List.map_map]
  change finiteGaussianCovariance N
      (polySum (quadratics.map quadraticPolynomial))
      (polySum (cubics.map cubicPolynomial)) ≈ 0
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_polySum_left N _
      (quadratics.map quadraticPolynomial))
    (qListSum_zero _ (quadratics.map quadraticPolynomial) (by
      intro quadraticPolynomialTerm membership
      obtain ⟨quadratic, quadraticMembership, rfl⟩ :=
        List.mem_map.mp membership
      exact Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_polySum_right N _
          (cubics.map cubicPolynomial))
        (qListSum_zero _ (cubics.map cubicPolynomial) (by
          intro cubicPolynomialTerm cubicMembership
          obtain ⟨cubic, _, rfl⟩ := List.mem_map.mp cubicMembership
          exact Q'.eqv_trans _ _ _
            (finiteGaussianCovariance_smul N
              quadratic.weight cubic.weight _ _)
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left _ _ _
                (finiteGaussianCovariance_two_three_row_words_zero N
                  quadratic.first quadratic.second
                  cubic.first cubic.second cubic.third))
              (Q'.mul_zero_eqv _))))))

private theorem completeActionCubicCertificate
    (timeBonds side stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage)
      (weightedTermPolynomial
        ((completeOpenCubeSpatialCubicRowBlocks
          timeBonds (bulkSourceWidth side) stage).map
            (weightedCubicRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) =
        bulkSourceNoiseCount timeBonds side := by
    unfold combGaugePlaquetteNoiseCount bulkSourceNoiseCount
    rfl
  rw [← noiseEquality]
  exact completeOpenCubeSpatialCubicPolynomial_coeffEqv
    timeBonds (bulkSourceWidth side) stage

/-- The actual finite trace-source cubic has zero Gaussian mean. -/
theorem finiteProductGaussian_openCube_bulk_cayley_trace_A3_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage time) ≈ 0 := by
  have coefficientCertificate := openCubeBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage time
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side) coefficientCertificate)
    (finiteProductGaussian_weighted_cubic_row_blocks_zero
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA3RowBlocks
        timeBonds side sidePositive stage time))

/-- The trace-source quadratic has zero covariance with the TOTAL spatial
action cubic. -/
theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_actionV3_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈ 0 := by
  have sourceCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage time
  have actionCertificate := completeActionCubicCertificate
    timeBonds side stage
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      sourceCertificate actionCertificate)
    (finiteGaussianCovariance_weighted_two_three_row_blocks_zero
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage time)
      (completeOpenCubeSpatialCubicRowBlocks
        timeBonds (bulkSourceWidth side) stage))

/-- Complete even second-density part entering the OWN fourth source mean:
`J2-V4_spatial-V4_kinetic`. -/
def completeOpenCubeJ2MinusV4Polynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeCayleyHaarJ2Polynomial timeBonds width stage)
    (polyAdd
      (polySmul (-1)
        (completeOpenCubeSpatialHeatActionFourthPolynomial
          timeBonds width stage))
      (polySmul (-1)
        (completeOpenCubeKineticFourthActionPolynomial
          timeBonds width stage)))

/-- OWN second source coefficient at one selected history time. -/
def openCubeBulkCayleyTraceOwnA2Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA2
      timeBonds side sidePositive stage time)

/-- OWN third source coefficient at one selected history time. -/
def openCubeBulkCayleyTraceOwnA3Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA3
        timeBonds side sidePositive stage time) -
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (completeOpenCubeSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage)

/-- OWN fourth source coefficient at one selected history time, with every
density and repeated-cubic term retained literally. -/
def openCubeBulkCayleyTraceOwnA4Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let A3 := openCubeBulkCayleyTraceA3
    timeBonds side sidePositive stage time
  let A4 := openCubeBulkCayleyTraceA4
    timeBonds side sidePositive stage time
  let V3 := completeOpenCubeSpatialCubicPolynomial
    timeBonds (bulkSourceWidth side) stage
  let evenDensity := completeOpenCubeJ2MinusV4Polynomial
    timeBonds (bulkSourceWidth side) stage
  (((finiteProductGaussian N A4 - finiteGaussianCovariance N A3 V3) +
      finiteGaussianCovariance N A2 evenDensity) +
    cubicPairHalf * finiteGaussianThirdCumulant N A2 V3 V3)

/-- The actual finite OWN third source coefficient vanishes by Gaussian
parity. -/
theorem openCubeBulkCayleyTraceOwnA3Mean_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeBulkCayleyTraceOwnA3Mean
      timeBonds side sidePositive stage time ≈ 0 := by
  unfold openCubeBulkCayleyTraceOwnA3Mean
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteProductGaussian_openCube_bulk_cayley_trace_A3_zero
        timeBonds side sidePositive stage time)
      (Q'.neg_eqv_congr _ _
        (finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_actionV3_zero
          timeBonds side sidePositive stage time)))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.const 0)))
      (.const 0) (by decide) (fun _ => 0))

/-- Supplied OLD center coefficients.  No relation to the finite Gaussian
OWN means is assumed. -/
structure CayleyTraceOldCenter where
  c2 : Q'
  c3 : Q'
  c4 : Q'

/-- Complete connected fourth coefficient. -/
def openCubeBulkCayleyTraceConnectedR4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA2
      timeBonds side sidePositive stage leftTime)
    (openCubeBulkCayleyTraceA2
      timeBonds side sidePositive stage rightTime)

/-- OLD-centered fourth response coefficient. -/
def openCubeBulkCayleyTraceP4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeBulkCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime +
    (openCubeBulkCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage leftTime - oldCenter.c2) *
      (openCubeBulkCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- OLD-centered fifth response coefficient.  The supplied `c3` remains
literal even though both OWN third means vanish. -/
def openCubeBulkCayleyTraceP5
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  (openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c2) *
    (openCubeBulkCayleyTraceOwnA3Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c3) +
  (openCubeBulkCayleyTraceOwnA3Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c3) *
    (openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- OLD-centered sixth response coefficient.  Every OWN/OLD residual product
is retained in addition to the checked connected `R6`. -/
def openCubeBulkCayleyTraceP6
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  ((openCubeBulkCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime +
      (openCubeBulkCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
        (openCubeBulkCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
    (openCubeBulkCayleyTraceOwnA3Mean
        timeBonds side sidePositive stage leftTime - oldCenter.c3) *
      (openCubeBulkCayleyTraceOwnA3Mean
        timeBonds side sidePositive stage rightTime - oldCenter.c3)) +
  (openCubeBulkCayleyTraceOwnA4Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c4) *
    (openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- Parity-normalized form of `P5`.  It does not set the supplied OLD `c3`
to zero. -/
theorem openCubeBulkCayleyTraceP5_parity
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceP5
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      (openCubeBulkCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
          (-oldCenter.c3) +
        (-oldCenter.c3) *
          (openCubeBulkCayleyTraceOwnA2Mean
            timeBonds side sidePositive stage rightTime - oldCenter.c2) := by
  unfold openCubeBulkCayleyTraceP5
  have leftCubicResidual :
      openCubeBulkCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeBulkCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage leftTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  have rightCubicResidual :
      openCubeBulkCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeBulkCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      rightCubicResidual)
    (Q'.mul_eqv_congr_right _ _ _
      leftCubicResidual)

/-- Parity-normalized form of `P6`.  The surviving OLD cubic-center square
`(-c3)*(-c3)` remains explicit. -/
theorem openCubeBulkCayleyTraceP6_parity
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceP6
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      ((openCubeBulkCayleyTraceConnectedR6WickSum
            timeBonds side sidePositive stage leftTime rightTime +
          (openCubeBulkCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage leftTime - oldCenter.c2) *
            (openCubeBulkCayleyTraceOwnA4Mean
              timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
        (-oldCenter.c3) * (-oldCenter.c3)) +
      (openCubeBulkCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c4) *
        (openCubeBulkCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2) := by
  unfold openCubeBulkCayleyTraceP6
  have leftCubicResidual :
      openCubeBulkCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeBulkCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage leftTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  have rightCubicResidual :
      openCubeBulkCayleyTraceOwnA3Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c3 ≈
        -oldCenter.c3 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (openCubeBulkCayleyTraceOwnA3Mean_zero
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _)
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (mul_congr leftCubicResidual rightCubicResidual))
    (Q'.eqv_refl _)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse.finiteProductGaussian_weighted_cubic_row_blocks_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse.finiteGaussianCovariance_weighted_two_three_row_blocks_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse.openCubeBulkCayleyTraceOwnA3Mean_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse.openCubeBulkCayleyTraceP5_parity
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse.openCubeBulkCayleyTraceP6_parity
