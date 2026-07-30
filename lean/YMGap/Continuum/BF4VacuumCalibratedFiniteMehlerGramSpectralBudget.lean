/-
# Stationary-vacuum calibration of the finite BF4 Mehler Gram

The canonical positive Mehler Gram is normalized by its own vacuum
coefficient, so its vacuum--vacuum entry is one.  The physical reflected
kernel is instead a probability joint with stationary marginal `pi`.
`BF4CanonicalFiniteMehlerGramSpectralBudget` proves that the uncalibrated
quarter cost therefore forces the nonphysical condition `pi(0) > 1/2`.

This module removes that scalar obstruction constructively.  It multiplies
the Gram by the literal square `pi(0)^2`, so the vacuum entry agrees exactly
with the stationary rank-one joint `pi ⊗ pi`.  Square scaling preserves
symmetry, positive semidefiniteness, and the physical-mean-zero Rayleigh
bound.  The remaining quarter estimate is consequently a genuine
Yang--Mills entry/tail estimate, rather than a normalization mismatch.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive square scaling -/

/-- Scaling every entry of a finite joint pulls through its quadratic form. -/
theorem finiteJointQuadratic_scale_joint
    {State : Type}
    (states : List State)
    (observable : State → Q')
    (scale : Q')
    (joint : State → State → Q') :
    finiteJointQuadratic states observable
        (fun left right => scale * joint left right) ≈
      scale *
        finiteJointQuadratic states observable joint := by
  unfold finiteJointQuadratic
  have hinner :
      ∀ left,
        listQSum
            (fun right =>
              (observable left * observable right) *
                (scale * joint left right))
            states ≈
          scale *
            listQSum
              (fun right =>
                (observable left * observable right) *
                  joint left right)
              states := by
    intro left
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun right => ?_) states)
      (listQSum_mul_left
        scale
        (fun right =>
          (observable left * observable right) *
            joint left right)
        states)
    exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (observable left * observable right)
            scale (joint left right)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            ((observable left * observable right) * scale)
            (scale * (observable left * observable right))
            (joint left right)
            (Q'.mul_comm_eqv
              (observable left * observable right)
              scale))
          (Q'.mul_assoc_eqv
            scale
            (observable left * observable right)
            (joint left right)))
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hinner states) ?_
  exact listQSum_mul_left
      scale
      (fun left =>
        listQSum
          (fun right =>
            (observable left * observable right) *
              joint left right)
          states)
      states

/-- Multiplying a raw endpoint numerator and its Rayleigh rate by a rational
square preserves every algebraic endpoint field. -/
def squareScaledRawMehlerEndpoint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (scale : Q') (_hscale : (0 : Q') ≤ scale)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator :=
    fun left right =>
      (scale * scale) * endpoint.numerator left right
  partition := endpoint.partition
  partition_pos := endpoint.partition_pos
  numerator_symmetric := by
    intro left right hleft hright
    exact Q'.mul_eqv_congr_left
      (scale * scale)
      (endpoint.numerator left right)
      (endpoint.numerator right left)
      (endpoint.numerator_symmetric
        left right hleft hright)
  normalized_quadratic_nonnegative := by
    intro observable
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let oldJoint := endpoint.joint
    let scaledJoint :=
      fun left right =>
        Q'.divPos
          ((scale * scale) *
            endpoint.numerator left right)
          endpoint.partition endpoint.partition_pos
    have hentry :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            scaledJoint left right ≈
              (scale * scale) * oldJoint left right := by
      intro left _ right _
      unfold scaledJoint oldJoint
        CentralPhysicalRawMehlerEndpoint.joint
        Q'.divPos
      exact Q'.mul_assoc_eqv
        (scale * scale)
        (endpoint.numerator left right)
        (Q'.recipPos
          endpoint.partition endpoint.partition_pos)
    have hquadratic :
        finiteJointQuadratic states observable scaledJoint ≈
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint := by
      exact Q'.eqv_trans _ _ _
        (finiteJointQuadratic_joint_eqv
          states observable scaledJoint
          (fun left right =>
            (scale * scale) * oldJoint left right)
          hentry)
        (finiteJointQuadratic_scale_joint
          states observable (scale * scale) oldJoint)
    have hproduct :
        (0 : Q') ≤
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint :=
      Q'.mul_nonneg _ _
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
          scale)
        (endpoint.normalized_quadratic_nonnegative
          observable)
    exact Q'.le_trans' _ _ _
      hproduct (Q'.ge_of_eqv hquadratic)
  rate := (scale * scale) * endpoint.rate
  rate_nonnegative :=
    Q'.mul_nonneg _ _
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        scale)
      endpoint.rate_nonnegative
  normalized_meanZero_quadratic := by
    intro observable hmean
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let oldJoint := endpoint.joint
    let scaledJoint :=
      fun left right =>
        Q'.divPos
          ((scale * scale) *
            endpoint.numerator left right)
          endpoint.partition endpoint.partition_pos
    have hsquare :
        (0 : Q') ≤ scale * scale :=
      YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        scale
    have hentry :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            scaledJoint left right ≈
              (scale * scale) * oldJoint left right := by
      intro left _ right _
      unfold scaledJoint oldJoint
        CentralPhysicalRawMehlerEndpoint.joint
        Q'.divPos
      exact Q'.mul_assoc_eqv
        (scale * scale)
        (endpoint.numerator left right)
        (Q'.recipPos
          endpoint.partition endpoint.partition_pos)
    have hquadratic :
        finiteJointQuadratic states observable scaledJoint ≈
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint := by
      exact Q'.eqv_trans _ _ _
        (finiteJointQuadratic_joint_eqv
          states observable scaledJoint
          (fun left right =>
            (scale * scale) * oldJoint left right)
          hentry)
        (finiteJointQuadratic_scale_joint
          states observable (scale * scale) oldJoint)
    have habsFactor :
        Q'.abs
            ((scale * scale) *
              finiteJointQuadratic
                states observable oldJoint) ≤
          (scale * scale) *
            Q'.abs
              (finiteJointQuadratic
                states observable oldJoint) := by
      have hmul :=
        YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
          (scale * scale)
          (finiteJointQuadratic
            states observable oldJoint)
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
        hsquare] at hmul
      exact hmul
    have hold :=
      endpoint.normalized_meanZero_quadratic
        observable hmean
    have hscaled :
        (scale * scale) *
            Q'.abs
              (finiteJointQuadratic
                states observable oldJoint) ≤
          (scale * scale) *
            (endpoint.rate *
              centralPhysicalWeightedInner
                w hw K halfExtent
                observable observable) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hold hsquare
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr hquadratic))
        habsFactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (scale * scale)
              endpoint.rate
              (centralPhysicalWeightedInner
                w hw K halfExtent
                observable observable)))))

/-- The normalized joint of a square-scaled endpoint is the corresponding
square multiple of the original joint. -/
theorem squareScaledRawMehlerEndpoint_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (scale : Q') (hscale : (0 : Q') ≤ scale)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (left right : EdgeLabelling) :
    (squareScaledRawMehlerEndpoint
        scale hscale endpoint).joint left right ≈
      (scale * scale) * endpoint.joint left right := by
  unfold squareScaledRawMehlerEndpoint
    CentralPhysicalRawMehlerEndpoint.joint
    Q'.divPos
  exact Q'.mul_assoc_eqv
    (scale * scale)
    (endpoint.numerator left right)
    (Q'.recipPos
      endpoint.partition endpoint.partition_pos)

/-! ## 2. Physical stationary-vacuum calibration -/

/-- Calibrate the exact positive Gram by the physical stationary-vacuum
amplitude `pi0²`. -/
def vacuumCalibratedExactCenteredMehlerGramRawEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  squareScaledRawMehlerEndpoint
    pi0
    (centralPhysicalRowMarginal_nonnegative
      hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
    (exactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)

/-- Vacuum calibration exactly matches the stationary rank-one vacuum
coefficient and hence removes the normalization fence. -/
theorem vacuumCalibratedExactCenteredMehlerGramRawEndpoint_vacuum
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≈
      pi0 * pi0 := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hscale :=
    squareScaledRawMehlerEndpoint_joint
      pi0
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
      (exactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  refine Q'.eqv_trans _ _ _ hscale ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (pi0 * pi0)
      ((exactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder).joint
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
      1
      (normalizedBF4MehlerGramJoint_vacuum
        diagonalOrder crossOrder))
    (Q'.mul_one_eqv (pi0 * pi0))

/-- Stationary-vacuum calibration cannot increase the certified centered
Rayleigh rate, since every physical row marginal is at most one. -/
theorem vacuumCalibratedExactCenteredMehlerGramRawEndpoint_rate_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).rate ≤
      exactCenteredMehlerGramRate
        w hw K halfExtent diagonalOrder crossOrder := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  let rate :=
    exactCenteredMehlerGramRate
      w hw K halfExtent diagonalOrder crossOrder
  have hvacuumMember :
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ∈
        centralPositiveHalfStates
          w hw K halfExtent :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent
  have hpi0nonnegative :
      (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hpi0le : pi0 ≤ (1 : Q') :=
    centralPhysicalRowMarginal_le_one_on_carrier
      hvacuumMember
  have hsquare :
      pi0 * pi0 ≤ (1 : Q') * 1 :=
    Q'.mul_le_mul_of_nonneg
      hpi0le hpi0le (by decide) hpi0nonnegative
  have hscaled :
      (pi0 * pi0) * rate ≤
        ((1 : Q') * 1) * rate :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hsquare
      (exactCenteredMehlerGramRate_nonnegative
        w hw K halfExtent diagonalOrder crossOrder)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          ((1 : Q') * 1) 1 rate
          (Q'.mul_one_eqv 1))
        (Q'.one_mul_eqv rate)))

/-! ## 3. Matched physical AF coordinates -/

/-- The calibrated endpoint on the exact matched BF4 carrier at one scale. -/
def matchedVacuumCalibratedMehlerGramRawEndpointAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalRawMehlerEndpoint
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  vacuumCalibratedExactCenteredMehlerGramRawEndpoint
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (diagonalOrder scale)
    (crossOrder scale)

/-- The exact finite comparison cost after removing the scalar vacuum
normalization obstruction. -/
def matchedVacuumCalibratedMehlerGramQuarterCostAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  let endpoint :=
    matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale
  endpoint.rate + exactFiniteEpsilon endpoint

theorem matchedVacuumCalibratedMehlerGramQuarterCostAt_nonnegative
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    (0 : Q') ≤
      matchedVacuumCalibratedMehlerGramQuarterCostAt
        family coupling halfExtent
        diagonalOrder crossOrder scale := by
  unfold matchedVacuumCalibratedMehlerGramQuarterCostAt
  exact Q'.zero_le_add _ _
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale).rate_nonnegative
    (exactFiniteEpsilon_nonnegative
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale))

/-- The calibrated endpoint rate is the old exact centered rate multiplied
by the physical vacuum marginal square. -/
theorem matchedVacuumCalibratedMehlerGramRate_eqv
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).rate ≈
      (pi0 * pi0) *
        exactCenteredMehlerGramRate
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          (diagonalOrder scale)
          (crossOrder scale) := by
  exact Q'.eqv_refl _

/-- A quarter estimate for the calibrated exact cost gives the desired
physical mean-zero Markov contraction at that matched scale. -/
theorem matchedVacuumCalibratedMehlerGram_physical_quarter_at
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat)
    (hquarter :
      matchedVacuumCalibratedMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact
    exactFinite_physical_markov_quadratic_abs_le_quarter
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale)
      hquarter observable hmean

/-! ## 4. The corrected spacing-uniform analytic interface -/

/-- The two genuinely analytic estimates remaining after stationary-vacuum
calibration.  The coupling window is tied to the same physical
`CubicMarginLaw` and `PhysicalSpacingEnvelope`; the two eighth-budgets are
stated on the literal matched carrier and exact finite tolerance. -/
structure MatchedVacuumCalibratedQuarterBudget
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_eighth :
    ∀ scale,
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale).rate ≤
        Q'.mkPos 1 8 (by decide)
  comparison_eighth :
    ∀ scale,
      exactFiniteEpsilon
          (matchedVacuumCalibratedMehlerGramRawEndpointAt
            family coupling halfExtent
            diagonalOrder crossOrder scale) ≤
        Q'.mkPos 1 8 (by decide)

namespace MatchedVacuumCalibratedQuarterBudget

/-- The two spacing-uniform eighth estimates add to the exact quarter
estimate at every scale. -/
theorem quarterCostAt_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (budget :
      MatchedVacuumCalibratedQuarterBudget
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    ∀ scale,
      matchedVacuumCalibratedMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide) := by
  intro scale
  unfold matchedVacuumCalibratedMehlerGramQuarterCostAt
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add
      (budget.spectral_eighth scale)
      (budget.comparison_eighth scale))
    (Q'.le_of_eqv (by decide))

/-- The calibrated budget supplies physical quarter contraction uniformly
on the complete matched AF trajectory. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (budget :
      MatchedVacuumCalibratedQuarterBudget
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact matchedVacuumCalibratedMehlerGram_physical_quarter_at
    family coupling halfExtent diagonalOrder crossOrder
    scale (budget.quarterCostAt_le scale)
    observable hmean

end MatchedVacuumCalibratedQuarterBudget

end YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.finiteJointQuadratic_scale_joint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.squareScaledRawMehlerEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.squareScaledRawMehlerEndpoint_joint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint_vacuum
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint_rate_le
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramRawEndpointAt
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramQuarterCostAt_nonnegative
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramRate_eqv
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGram_physical_quarter_at
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedQuarterBudget.quarterCostAt_le
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedQuarterBudget.physical_quarter_uniform
