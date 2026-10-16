/-
# Identity value of the global Cayley clearing denominator

The exact outer denominator in the cleared vector-jet quadratic carrier is
evaluated on the all-identity ORIGINAL link assignment.  Its value is the
explicit rational scale `2^32 = 4294967296`.  This selects the canonical
reference in the preceding parametric outer-denominator split.

Only a point evaluation and exact algebraic specialization are asserted.  The
inner denominator powers in the degree-two polynomial remain unchanged.  No
deformation estimate, FREE Gaussian identification, cutoff removal, continuum
theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarFiniteProductOrder
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a + c ≈ b + d :=
  Q'.add_eqv_congr' h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_eval (rho : Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum (evalMono rho) polynomial = evalRatPoly rho polynomial
  | [] => rfl
  | term :: rest =>
      congrArg (fun value => term.2 * evalMono rho term.1 + value)
        (weighted_eval rho rest)

private theorem eval_coeffEqv
    (rho : Nat → Q') {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    evalRatPoly rho left ≈ evalRatPoly rho right := by
  simpa only [weighted_eval] using h (evalMono rho)

/-- The ORIGINAL assignment sending every link variable to the identity. -/
def identityLinkAssignment : Nat → UnitNorm := fun _ => unitOne

/-- The exact identity-chart value of the four-factor global clearing
denominator. -/
def identityCayleyDenominatorReference : Q' := Q'.ofNat 4294967296

private theorem identity_linkValue
    (extent : Nat) (link : Z4Link) :
    (linkValue extent identityLinkAssignment link).Equivalent unitOne := by
  unfold linkValue identityLinkAssignment
  split <;> exact UnitNorm.semanticSetoid.iseqv.refl unitOne

private theorem identity_orientedLinkValue
    (extent : Nat) (entry : OrientedBF4Link) :
    (orientedLinkValue extent identityLinkAssignment entry).Equivalent
      unitOne := by
  unfold orientedLinkValue
  split
  · have hinvOne : (UnitNorm.inv unitOne).Equivalent unitOne := by
      change (RationalQuaternion.conj RationalQuaternion.one).Equivalent
        RationalQuaternion.one
      exact RationalQuaternion.conj_one
    exact UnitNorm.semanticSetoid.iseqv.trans
      (UnitNorm.inv_congr (identity_linkValue extent entry.link)) hinvOne
  · exact identity_linkValue extent entry.link

private theorem unitValue_congr {left right : UnitNorm}
    (h : left.Equivalent right) :
    QuaternionValue.Eqv (unitValue left) (unitValue right) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem identity_oriented_link_eval
    (extent : Nat) (entry : OrientedBF4Link) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment identityLinkAssignment)
        (orientedCorrectedSlabLinkPolynomial extent entry))
      (unitValue unitOne) := by
  have hlink := oriented_link_eval extent identityLinkAssignment entry
  have hone := unitValue_congr (identity_orientedLinkValue extent entry)
  exact ⟨Q'.eqv_trans _ _ _ hlink.scalar hone.scalar,
    Q'.eqv_trans _ _ _ hlink.iPart hone.iPart,
    Q'.eqv_trans _ _ _ hlink.jPart hone.jPart,
    Q'.eqv_trans _ _ _ hlink.kPart hone.kPart⟩

private def clearedFactorExpansion
    (quaternion : PolyQuaternion) (complement : RatPoly) : RatPoly :=
  let denominator := polyMul
    (polyAdd (polySmul (Q'.ofInt 1) polyOne) quaternion.scalar)
    complement
  let iNumerator := polyMul complement quaternion.iPart
  let jNumerator := polyMul complement quaternion.jPart
  let kNumerator := polyMul complement quaternion.kPart
  polyAdd (polyMul denominator denominator)
    (polyAdd
      (polyAdd
        (polyMul iNumerator iNumerator)
        (polyMul jNumerator jNumerator))
      (polyMul kNumerator kNumerator))

private theorem clearedCayleyFactorPolynomial_coeff_expansion
    (quaternion : PolyQuaternion) (complement : RatPoly) :
    RatPolyCoeffEqv
      (clearedCayleyFactorPolynomial quaternion complement)
      (clearedFactorExpansion quaternion complement) := by
  exact RatPolyCoeffEqv.refl _

private theorem eval_onePolynomial (rho : Nat → Q') :
    evalRatPoly rho (polySmul (Q'.ofInt 1) polyOne) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_smul rho (Q'.ofInt 1) polyOne)
    (mc (Q'.eqv_refl _) (evalRatPoly_one rho))

private theorem eval_chart_denominator_identity
    (rho : Nat → Q') (quaternion : PolyQuaternion)
    (hquaternion : QuaternionValue.Eqv
      (evalPolyQuaternion rho quaternion) (unitValue unitOne)) :
    evalRatPoly rho (cayleyChartDenominatorPolynomial quaternion) ≈ 2 := by
  have hscalar : evalRatPoly rho quaternion.scalar ≈ 1 := by
    simpa [evalPolyQuaternion, unitValue, unitOne,
      RationalQuaternion.one] using hquaternion.scalar
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_add rho (polySmul (Q'.ofInt 1) polyOne) quaternion.scalar)
    (ac (eval_onePolynomial rho) hscalar)

private theorem eval_complement_identity
    (rho : Nat → Q') (left middle right : PolyQuaternion)
    (hleft : QuaternionValue.Eqv
      (evalPolyQuaternion rho left) (unitValue unitOne))
    (hmiddle : QuaternionValue.Eqv
      (evalPolyQuaternion rho middle) (unitValue unitOne))
    (hright : QuaternionValue.Eqv
      (evalPolyQuaternion rho right) (unitValue unitOne)) :
    evalRatPoly rho
      (polyMul
        (polyMul
          (cayleyChartDenominatorPolynomial left)
          (cayleyChartDenominatorPolynomial middle))
        (cayleyChartDenominatorPolynomial right)) ≈ 8 := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_mul rho _ _)
    (mc
      (Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho _ _)
        (mc
          (eval_chart_denominator_identity rho left hleft)
          (eval_chart_denominator_identity rho middle hmiddle)))
      (eval_chart_denominator_identity rho right hright))

private theorem eval_clearedFactor_identity
    (rho : Nat → Q') (quaternion : PolyQuaternion) (complement : RatPoly)
    (hquaternion : QuaternionValue.Eqv
      (evalPolyQuaternion rho quaternion) (unitValue unitOne))
    (hcomplement : evalRatPoly rho complement ≈ 8) :
    evalRatPoly rho
      (clearedCayleyFactorPolynomial quaternion complement) ≈ 256 := by
  have hscalar : evalRatPoly rho quaternion.scalar ≈ 1 := by
    simpa [evalPolyQuaternion, unitValue, unitOne,
      RationalQuaternion.one] using hquaternion.scalar
  have hi : evalRatPoly rho quaternion.iPart ≈ 0 := by
    simpa [evalPolyQuaternion, unitValue, unitOne,
      RationalQuaternion.one] using hquaternion.iPart
  have hj : evalRatPoly rho quaternion.jPart ≈ 0 := by
    simpa [evalPolyQuaternion, unitValue, unitOne,
      RationalQuaternion.one] using hquaternion.jPart
  have hk : evalRatPoly rho quaternion.kPart ≈ 0 := by
    simpa [evalPolyQuaternion, unitValue, unitOne,
      RationalQuaternion.one] using hquaternion.kPart
  have hdenominator : evalRatPoly rho
      (polyMul
        (polyAdd (polySmul (Q'.ofInt 1) polyOne) quaternion.scalar)
        complement) ≈ 16 := by
    exact Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc
        (Q'.eqv_trans _ _ _
          (evalRatPoly_add rho _ _)
          (ac (eval_onePolynomial rho) hscalar))
        hcomplement)
  have himaginary : evalRatPoly rho
      (polyMul complement quaternion.iPart) ≈ 0 :=
    Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc hcomplement hi)
  have hjmaginary : evalRatPoly rho
      (polyMul complement quaternion.jPart) ≈ 0 :=
    Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc hcomplement hj)
  have hkmaginary : evalRatPoly rho
      (polyMul complement quaternion.kPart) ≈ 0 :=
    Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc hcomplement hk)
  refine Q'.eqv_trans _ _ _
    (eval_coeffEqv rho
      (clearedCayleyFactorPolynomial_coeff_expansion
        quaternion complement)) ?_
  simp only [clearedFactorExpansion]
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_add rho _ _)
    (ac
      (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
        (mc hdenominator hdenominator))
      (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (ac
          (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
            (ac
              (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
                (mc himaginary himaginary))
              (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
                (mc hjmaginary hjmaginary))))
          (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
            (mc hkmaginary hkmaginary)))))

set_option maxHeartbeats 2000000 in
private theorem compiled_denominator_identity
    (rho : Nat → Q') (q0 q1 q2 q3 : PolyQuaternion)
    (h0 : QuaternionValue.Eqv
      (evalPolyQuaternion rho q0) (unitValue unitOne))
    (h1 : QuaternionValue.Eqv
      (evalPolyQuaternion rho q1) (unitValue unitOne))
    (h2 : QuaternionValue.Eqv
      (evalPolyQuaternion rho q2) (unitValue unitOne))
    (h3 : QuaternionValue.Eqv
      (evalPolyQuaternion rho q3) (unitValue unitOne)) :
    evalRatPoly rho
      (compiledCayleyDenominatorPolynomial q0 q1 q2 q3) ≈
        identityCayleyDenominatorReference := by
  have hc0 := eval_complement_identity rho q1 q2 q3 h1 h2 h3
  have hc1 := eval_complement_identity rho q0 q2 q3 h0 h2 h3
  have hc2 := eval_complement_identity rho q0 q1 q3 h0 h1 h3
  have hc3 := eval_complement_identity rho q0 q1 q2 h0 h1 h2
  have hf0 := eval_clearedFactor_identity rho q0
    (cayleyComplement0Polynomial q0 q1 q2 q3) h0 hc0
  have hf1 := eval_clearedFactor_identity rho q1
    (cayleyComplement1Polynomial q0 q1 q2 q3) h1 hc1
  have hf2 := eval_clearedFactor_identity rho q2
    (cayleyComplement2Polynomial q0 q1 q2 q3) h2 hc2
  have hf3 := eval_clearedFactor_identity rho q3
    (cayleyComplement3Polynomial q0 q1 q2 q3) h3 hc3
  refine Q'.eqv_trans _ _ _
    (eval_coeffEqv rho
      (clearedCayleyScaleProduct_coeff_compiled q0 q1 q2 q3).symm) ?_
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_mul rho _ _)
    (mc
      (Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho _ _)
        (mc
          (Q'.eqv_trans _ _ _
            (evalRatPoly_mul rho _ _)
            (mc hf0 hf1))
          hf2))
      hf3)

/-- The actual ORIGINAL global Cayley denominator evaluates at the all-identity
link assignment to the exact rational scale `2^32 = 4294967296`. -/
theorem globalCayleyDenominatorPolynomial_identity_eval
    (extent : Nat) (face : Z4Plaq) :
    evalRatPoly (environment identityLinkAssignment)
      (globalCayleyDenominatorPolynomial extent face) ≈
        identityCayleyDenominatorReference := by
  refine Q'.eqv_trans _ _ _
    (eval_coeffEqv (environment identityLinkAssignment)
      (globalCayleyDenominatorPolynomial_coeff_compiled extent face)) ?_
  apply compiled_denominator_identity
  all_goals exact identity_oriented_link_eval extent _

/-- Canonical one-face outer-denominator split using the proved identity-chart
reference `2^32`, while retaining the complete inner degree-two polynomial. -/
theorem globalCayleyVectorJetQuadratic_identityDenominator_split
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetQuadraticPolynomial extent face)
      (polyAdd
        (globalCayleyVectorJetReferenceQuadraticPolynomial
          identityCayleyDenominatorReference extent face)
        (globalCayleyVectorJetOuterDenominatorRemainderPolynomial
          identityCayleyDenominatorReference extent face)) :=
  globalCayleyVectorJetQuadratic_outerDenominator_split
    identityCayleyDenominatorReference extent face

/-- The centered cleared ORIGINAL response with the now-canonical identity
reference.  Both the outer-denominator deformation and the Cayley residual
remain explicit in the unchanged total remainder. -/
theorem globalCayleyVectorJetBulkCentered_identityDenominator_total_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredClearedResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
          identityCayleyDenominatorReference
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredReferenceTotalRemainder
          identityCayleyDenominatorReference
          w hw0 hw1 half s hs leftTime rightTime)) :=
  globalCayleyVectorJetBulkCentered_reference_total_split
    identityCayleyDenominatorReference
    w hw0 hw1 half s hs leftTime rightTime
    hwidth hleftTime hrightTime

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator.globalCayleyDenominatorPolynomial_identity_eval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator.globalCayleyVectorJetQuadratic_identityDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator.globalCayleyVectorJetBulkCentered_identityDenominator_total_split
