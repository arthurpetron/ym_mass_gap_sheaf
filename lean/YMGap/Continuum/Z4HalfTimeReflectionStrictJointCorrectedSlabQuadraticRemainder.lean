/-
# Exact corrected-slab quadratic remainder for strict time translation

The entrywise corrected-slab covariance remainder has no fixed sign: the
coefficients of a strict cylinder may themselves be signed.  The contraction
question is therefore a quadratic aggregate question.  This file sums the
literal corrected-slab event numerators against the actual finite cylinder
coefficients, keeps the source and target fingerprint spaces distinct, and
cross-multiplies their two positive slab normalizations.

The resulting signed cross remainder is exactly the translated reflection
quadratic minus the source reflection quadratic, up to division by the
positive product denominator.  Consequently finite-radius contraction is
equivalent to one explicit aggregate compression sign.  No entrywise sign,
whole-event covariance, conditional-expectation identity, limiting state
invariance, or contraction hypothesis is assumed.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabCovarianceRemainder

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabQuadraticRemainder

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabCovarianceRemainder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointFiniteCovarianceFence
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4TimeShiftedFiniteNormalizedCovarianceRemainder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite-quadratic normalization algebra -/

/-- Pointwise equivalence of a joint kernel passes through its complete
finite quadratic form. -/
theorem finiteJointQuadratic_joint_eqv
    {State : Type} (states : List State) (coefficient : State → Q')
    (leftJoint rightJoint : State → State → Q')
    (hjoint : ∀ left right, leftJoint left right ≈ rightJoint left right) :
    finiteJointQuadratic states coefficient leftJoint ≈
      finiteJointQuadratic states coefficient rightJoint := by
  unfold finiteJointQuadratic
  apply listQSum_congr
  intro left
  apply listQSum_congr
  intro right
  exact Q'.mul_eqv_congr_left
    (coefficient left * coefficient right) _ _ (hjoint left right)

/-- A common positive denominator can be factored through a complete finite
quadratic. -/
theorem finiteJointQuadratic_divPos_kernel_eqv
    {State : Type} (states : List State) (coefficient : State → Q')
    (numerator : State → State → Q')
    (denominator : Q') (hdenominator : (0 : Q') < denominator) :
    finiteJointQuadratic states coefficient
        (fun left right =>
          Q'.divPos (numerator left right)
            denominator hdenominator) ≈
      Q'.divPos
        (finiteJointQuadratic states coefficient numerator)
        denominator hdenominator := by
  unfold finiteJointQuadratic Q'.divPos
  have hrow : ∀ left,
      listQSum
          (fun right =>
            (coefficient left * coefficient right) *
              (numerator left right *
                Q'.recipPos denominator hdenominator))
          states ≈
        listQSum
            (fun right =>
              (coefficient left * coefficient right) *
                numerator left right)
            states * Q'.recipPos denominator hdenominator := by
    intro left
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun right =>
        Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (coefficient left * coefficient right)
            (numerator left right)
            (Q'.recipPos denominator hdenominator))) states) ?_
    exact listQSum_mul_right
      (fun right =>
        (coefficient left * coefficient right) * numerator left right)
      (Q'.recipPos denominator hdenominator) states
  refine Q'.eqv_trans _ _ _ (listQSum_congr hrow states) ?_
  exact listQSum_mul_right
      (fun left => listQSum
        (fun right =>
          (coefficient left * coefficient right) * numerator left right)
        states)
      (Q'.recipPos denominator hdenominator) states

/-- Positive-denominator quotient comparison is equivalent to its exact
cross-multiplied inequality. -/
theorem divPos_le_divPos_iff_cross
    (targetNumerator targetDenominator
      sourceNumerator sourceDenominator : Q')
    (htarget : (0 : Q') < targetDenominator)
    (hsource : (0 : Q') < sourceDenominator) :
    Q'.divPos targetNumerator targetDenominator htarget ≤
        Q'.divPos sourceNumerator sourceDenominator hsource ↔
      targetNumerator * sourceDenominator ≤
        sourceNumerator * targetDenominator := by
  constructor
  · intro hquotient
    have hproduct := Q'.mul_le_mul_of_nonneg_right
      (Q'.divPos targetNumerator targetDenominator htarget)
      (Q'.divPos sourceNumerator sourceDenominator hsource)
      (targetDenominator * sourceDenominator)
      hquotient
      (Q'.le_of_lt (Q'.mul_pos htarget hsource))
    have hleft :
        Q'.divPos targetNumerator targetDenominator htarget *
            (targetDenominator * sourceDenominator) ≈
          targetNumerator * sourceDenominator := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.divPos targetNumerator targetDenominator htarget)
            targetDenominator sourceDenominator)) ?_
      exact Q'.mul_eqv_congr_right _ _ sourceDenominator
        (Q'.divPos_mul_eqv
          targetNumerator targetDenominator htarget)
    have hright :
        Q'.divPos sourceNumerator sourceDenominator hsource *
            (targetDenominator * sourceDenominator) ≈
          sourceNumerator * targetDenominator := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos sourceNumerator sourceDenominator hsource)
          _ _ (Q'.mul_comm_eqv targetDenominator sourceDenominator)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.divPos sourceNumerator sourceDenominator hsource)
            sourceDenominator targetDenominator)) ?_
      exact Q'.mul_eqv_congr_right _ _ targetDenominator
        (Q'.divPos_mul_eqv
          sourceNumerator sourceDenominator hsource)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hright))
  · intro hcross
    exact
      YMGap.Continuum.Z4CanonicalOccurrenceStability.divPos_le_divPos_of_cross_local
        targetNumerator targetDenominator
        sourceNumerator sourceDenominator
        htarget hsource hcross

/-! ## 2. Literal source and translated quadratic numerators -/

/-- The unnormalized corrected-slab quadratic numerator at one radius.  The
kernel entry is the physical marked-cylinder numerator before conditioning
on slab support. -/
def strictJointCorrectedSlabQuadraticNumerator
    (coupling : Q') (cutoff radius : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) : Q' :=
  finiteJointQuadratic
    (centralLocalSupportFingerprintSpace radius
      (centralStrictLocalQueryCode radius base vector.roots))
    vector.coefficient
    (fun left right =>
      couplingParametricKPhysicalSlabRestrictedNumerator
        coupling cutoff (centralExtent radius)
        (strictJointCorrectedSlabCylinderEvent
          radius hbase vector left right))

/-- The target quadratic numerator after synchronously increasing radius and
translating the strict cylinder. -/
def timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
    (coupling : Q') (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) : Q' :=
  strictJointCorrectedSlabQuadraticNumerator
    coupling cutoff (radius + shift)
    (strictQueryBase_le_after_timeTranslate hbase shift)
    (timeTranslateStrictJointCylinderVector shift vector)

/-- The complete local joint quadratic is its literal corrected-slab
quadratic numerator divided by the common positive slab denominator. -/
theorem strictJointLocalQuadratic_eqv_correctedSlabNumerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    finiteJointQuadratic
        (centralLocalSupportFingerprintSpace radius
          (centralStrictLocalQueryCode radius base vector.roots))
        vector.coefficient
        (centralNormalizedLocalSupportPairLaw
          coupling hcoupling cutoff radius
          (centralStrictLocalQueryCode radius base vector.roots)) ≈
      Q'.divPos
        (strictJointCorrectedSlabQuadraticNumerator
          coupling cutoff radius hbase vector)
        (couplingParametricKPhysicalSlabSupportDenominator
          coupling cutoff (centralExtent radius))
        (couplingParametricKPhysicalSlabSupportNumerator_pos
          hcoupling cutoff (centralExtent radius)) := by
  have hentry : ∀ left right,
      centralNormalizedLocalSupportPairLaw
          coupling hcoupling cutoff radius
          (centralStrictLocalQueryCode radius base vector.roots)
          left right ≈
        Q'.divPos
          (couplingParametricKPhysicalSlabRestrictedNumerator
            coupling cutoff (centralExtent radius)
            (strictJointCorrectedSlabCylinderEvent
              radius hbase vector left right))
          (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent radius))
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent radius)) := by
    intro left right
    simpa only [strictJointCorrectedSlabCylinderEvent,
      couplingParametricKPhysicalGivenSlabProbability,
      couplingParametricKPhysicalSlabRestrictedNumerator,
      couplingParametricKPhysicalSlabSupportDenominator] using
      (centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
        coupling hcoupling cutoff hbase vector.rootsCanonical left right)
  refine Q'.eqv_trans _ _ _
    (finiteJointQuadratic_joint_eqv
      (centralLocalSupportFingerprintSpace radius
        (centralStrictLocalQueryCode radius base vector.roots))
      vector.coefficient
      (centralNormalizedLocalSupportPairLaw
        coupling hcoupling cutoff radius
        (centralStrictLocalQueryCode radius base vector.roots))
      (fun left right =>
        Q'.divPos
          (couplingParametricKPhysicalSlabRestrictedNumerator
            coupling cutoff (centralExtent radius)
            (strictJointCorrectedSlabCylinderEvent
              radius hbase vector left right))
          (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent radius))
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent radius)))
      hentry) ?_
  simpa only [strictJointCorrectedSlabQuadraticNumerator] using
    (finiteJointQuadratic_divPos_kernel_eqv
      (centralLocalSupportFingerprintSpace radius
        (centralStrictLocalQueryCode radius base vector.roots))
      vector.coefficient
      (fun left right =>
        couplingParametricKPhysicalSlabRestrictedNumerator
          coupling cutoff (centralExtent radius)
          (strictJointCorrectedSlabCylinderEvent
            radius hbase vector left right))
      (couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent radius))
      (couplingParametricKPhysicalSlabSupportNumerator_pos
        hcoupling cutoff (centralExtent radius)))

/-! ## 3. Source and target reflection quadratics as two quotients -/

theorem strictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionQuadratic
        coupling hcoupling cutoff radius vector ≈
      Q'.divPos
        (strictJointCorrectedSlabQuadraticNumerator
          coupling cutoff radius hbase vector)
        (couplingParametricKPhysicalSlabSupportDenominator
          coupling cutoff (centralExtent radius))
        (couplingParametricKPhysicalSlabSupportNumerator_pos
          hcoupling cutoff (centralExtent radius)) := by
  unfold strictJointCylinderRadiusReflectionQuadratic
    strictJointCylinderRadiusCoefficient
  exact Q'.eqv_trans _ _ _
    (centralNormalizedSupportReflectionQuadratic_eq_localJointLaw
      coupling hcoupling cutoff radius
      (centralStrictLocalQueryCode radius base vector.roots)
      vector.coefficient)
    (strictJointLocalQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff radius hbase vector)

theorem timeTranslatedStrictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift vector ≈
      Q'.divPos
        (timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
          coupling cutoff radius shift hbase vector)
        (couplingParametricKPhysicalSlabSupportDenominator
          coupling cutoff (centralExtent (radius + shift)))
        (couplingParametricKPhysicalSlabSupportNumerator_pos
          hcoupling cutoff (centralExtent (radius + shift))) := by
  unfold strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
    timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
  exact
    strictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff (radius + shift)
      (strictQueryBase_le_after_timeTranslate hbase shift)
      (timeTranslateStrictJointCylinderVector shift vector)

/-! ## 4. Exact aggregate cross remainder and compression sign -/

/-- The signed aggregate obstruction with the correct target-minus-source
orientation.  Source and target retain their own attained fingerprint spaces. -/
def timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder
    (coupling : Q') (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) : Q' :=
  timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius shift hbase vector *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent radius) -
    strictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius hbase vector *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent (radius + shift))

/-- Exact translated-minus-source reflection-quadratic remainder. -/
theorem timeTranslatedStrictJointReflectionQuadratic_sub_source_eqv_remainder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
          coupling hcoupling cutoff radius shift vector -
        strictJointCylinderRadiusReflectionQuadratic
          coupling hcoupling cutoff radius vector ≈
      Q'.divPos
        (timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder
          coupling cutoff radius shift hbase vector)
        (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent (radius + shift)) *
          couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent radius))
        (Q'.mul_pos
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent (radius + shift)))
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent radius))) := by
  have htarget :=
    timeTranslatedStrictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff radius shift hbase vector
  have hsource :=
    strictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff radius hbase vector
  have hreplace := Q'.add_eqv_congr' htarget
    (Q'.neg_eqv_congr _ _ hsource)
  refine Q'.eqv_trans _ _ _ hreplace ?_
  simpa only [timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder] using
    (divPos_sub_eqv_crossDifference
      (timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius shift hbase vector)
      (couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent (radius + shift)))
      (strictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius hbase vector)
      (couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent radius))
      (couplingParametricKPhysicalSlabSupportNumerator_pos
        hcoupling cutoff (centralExtent (radius + shift)))
      (couplingParametricKPhysicalSlabSupportNumerator_pos
        hcoupling cutoff (centralExtent radius)))

/-- The exact aggregate compression sign, written without subtraction. -/
def StrictJointFiniteCompressionCross
    (coupling : Q') (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) : Prop :=
  timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius shift hbase vector *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent radius) ≤
    strictJointCorrectedSlabQuadraticNumerator
        coupling cutoff radius hbase vector *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff (centralExtent (radius + shift))

/-- The signed remainder is nonpositive exactly when the subtraction-free
aggregate compression cross inequality holds. -/
theorem timeTranslatedStrictJointQuadraticCrossRemainder_nonpositive_iff
    (coupling : Q') (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder
          coupling cutoff radius shift hbase vector ≤ 0 ↔
      StrictJointFiniteCompressionCross
        coupling cutoff radius shift hbase vector := by
  unfold timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder
    StrictJointFiniteCompressionCross
  constructor
  · intro hremainder
    have hadd :=
      YMGap.Continuum.Z4CanonicalOccurrenceStability.le_add_of_sub_le_local
        hremainder
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.eqv_of_eq
          (Q'.add_zero'
            (strictJointCorrectedSlabQuadraticNumerator
                coupling cutoff radius hbase vector *
              couplingParametricKPhysicalSlabSupportDenominator
                coupling cutoff (centralExtent (radius + shift))))))
  · intro hcross
    apply Q'.sub_le_of_le_add
    exact Q'.le_trans' _ _ _ hcross
      (Q'.ge_of_eqv
        (Q'.eqv_of_eq
          (Q'.add_zero'
            (strictJointCorrectedSlabQuadraticNumerator
                coupling cutoff radius hbase vector *
              couplingParametricKPhysicalSlabSupportDenominator
                coupling cutoff (centralExtent (radius + shift))))))

/-- Finite-radius reflection contraction is equivalent to the one explicit
aggregate corrected-slab compression cross inequality.  This is the exact
remaining sign theorem; entrywise positivity does not discharge it. -/
theorem timeTranslatedStrictJointReflectionQuadratic_le_source_iff_compressionCross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
          coupling hcoupling cutoff radius shift vector ≤
        strictJointCylinderRadiusReflectionQuadratic
          coupling hcoupling cutoff radius vector ↔
      StrictJointFiniteCompressionCross
        coupling cutoff radius shift hbase vector := by
  have htarget :=
    timeTranslatedStrictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff radius shift hbase vector
  have hsource :=
    strictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
      hcoupling cutoff radius hbase vector
  have hquotient := divPos_le_divPos_iff_cross
    (timeTranslatedStrictJointCorrectedSlabQuadraticNumerator
      coupling cutoff radius shift hbase vector)
    (couplingParametricKPhysicalSlabSupportDenominator
      coupling cutoff (centralExtent (radius + shift)))
    (strictJointCorrectedSlabQuadraticNumerator
      coupling cutoff radius hbase vector)
    (couplingParametricKPhysicalSlabSupportDenominator
      coupling cutoff (centralExtent radius))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff (centralExtent (radius + shift)))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff (centralExtent radius))
  unfold StrictJointFiniteCompressionCross
  constructor
  · intro hcontract
    apply hquotient.mp
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htarget)
      (Q'.le_trans' _ _ _ hcontract (Q'.le_of_eqv hsource))
  · intro hcross
    have hquot := hquotient.mpr hcross
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htarget)
      (Q'.le_trans' _ _ _ hquot (Q'.ge_of_eqv hsource))

/-- Equivalent signed-residual form of the finite-radius contraction
obligation. -/
theorem timeTranslatedStrictJointReflectionQuadratic_le_source_iff_remainder_nonpositive
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
          coupling hcoupling cutoff radius shift vector ≤
        strictJointCylinderRadiusReflectionQuadratic
          coupling hcoupling cutoff radius vector ↔
      timeTranslatedStrictJointCorrectedSlabQuadraticCrossRemainder
        coupling cutoff radius shift hbase vector ≤ 0 := by
  exact Iff.trans
    (timeTranslatedStrictJointReflectionQuadratic_le_source_iff_compressionCross
      hcoupling cutoff radius shift hbase vector)
    (Iff.symm
      (timeTranslatedStrictJointQuadraticCrossRemainder_nonpositive_iff
        coupling cutoff radius shift hbase vector))

#print axioms finiteJointQuadratic_joint_eqv
#print axioms finiteJointQuadratic_divPos_kernel_eqv
#print axioms divPos_le_divPos_iff_cross
#print axioms strictJointLocalQuadratic_eqv_correctedSlabNumerator
#print axioms strictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
#print axioms timeTranslatedStrictJointCylinderRadiusReflectionQuadratic_eqv_correctedSlabNumerator
#print axioms timeTranslatedStrictJointReflectionQuadratic_sub_source_eqv_remainder
#print axioms timeTranslatedStrictJointQuadraticCrossRemainder_nonpositive_iff
#print axioms timeTranslatedStrictJointReflectionQuadratic_le_source_iff_compressionCross
#print axioms timeTranslatedStrictJointReflectionQuadratic_le_source_iff_remainder_nonpositive

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabQuadraticRemainder
