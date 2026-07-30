/-
# Physical recentering of a finite BF4 endpoint rate

A stationary-vacuum calibration changes the endpoint joint but need not
change the physical Perron rank-one term.  Merely scaling a previously
centered rate therefore leaves a removable rank-one contribution in the
row majorant.

This module retightens any symmetric positive BF4 endpoint around the
literal physical vacuum joint

    V(x,y) = pi(x) pi(y).

It computes the exact finite maximum of the row-relative masses of
`endpoint.joint - V`.  The quadratic form of `V` vanishes on the physical
mean-zero carrier, so this exact Schur maximum certifies the unchanged
endpoint joint.  Numerator, partition, normalized joint, symmetry, and
positive semidefiniteness are all preserved.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4PhysicalRecenteredEndpointRate

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact physical-centered row maximum -/

/-- Absolute row mass of an arbitrary endpoint after subtraction of the
literal physical Perron rank-one joint. -/
def physicalCenteredEndpointRowMass
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPositiveHalfStates w hw K halfExtent)
    endpoint.joint
    (centralPhysicalVacuumJoint
      w hw K halfExtent)
    source

theorem physicalCenteredEndpointRowMass_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      physicalCenteredEndpointRowMass
        endpoint source := by
  unfold physicalCenteredEndpointRowMass
    finiteJointDifferenceAbsRowMass
  exact listQSum_nonnegative_on _ _
    (fun target _ => Q'.abs_nonneg _)

/-- Physical-centered row mass divided by the exact positive physical
marginal.  The zero branch occurs only outside the retained carrier. -/
def physicalCenteredEndpointRowRatio
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  if hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source
  then
    Q'.divPos
      (physicalCenteredEndpointRowMass
        endpoint source)
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      hpositive
  else 0

theorem physicalCenteredEndpointRowRatio_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      physicalCenteredEndpointRowRatio
        endpoint source := by
  unfold physicalCenteredEndpointRowRatio
  split
  next hpositive =>
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (physicalCenteredEndpointRowMass_nonnegative
        endpoint source)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ hpositive))
  next _ =>
    exact Q'.le_refl' 0

/-- Exact finite Schur rate of `endpoint.joint - pi tensor pi`. -/
def physicalCenteredEndpointRate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  listQMaxZero
    (physicalCenteredEndpointRowRatio endpoint)
    (centralPositiveHalfStates w hw K halfExtent)

theorem physicalCenteredEndpointRate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') ≤
      physicalCenteredEndpointRate endpoint := by
  unfold physicalCenteredEndpointRate
  exact listQMaxZero_nonnegative _
    (physicalCenteredEndpointRowRatio_nonnegative endpoint)
    (centralPositiveHalfStates w hw K halfExtent)

/-- The exact finite maximum controls every retained centered row with no
carrier-cardinality or minimum-marginal loss. -/
theorem physicalCenteredEndpointRowMass_le_rate_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent}
    {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates
          w hw K halfExtent) :
    physicalCenteredEndpointRowMass
        endpoint source ≤
      physicalCenteredEndpointRate endpoint *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  have hratio :
      physicalCenteredEndpointRowRatio endpoint source ≤
        physicalCenteredEndpointRate endpoint := by
    exact le_listQMaxZero_of_mem
      (physicalCenteredEndpointRowRatio endpoint)
      (centralPositiveHalfStates
        w hw K halfExtent)
      hsource
  unfold physicalCenteredEndpointRowRatio at hratio
  rw [dif_pos hpositive] at hratio
  have hscaled :
      Q'.divPos
          (physicalCenteredEndpointRowMass
            endpoint source)
          (centralPhysicalRowMarginal
            w hw K halfExtent source)
          hpositive *
          centralPhysicalRowMarginal
            w hw K halfExtent source ≤
        physicalCenteredEndpointRate endpoint *
          centralPhysicalRowMarginal
            w hw K halfExtent source :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hratio (Q'.le_of_lt hpositive)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (physicalCenteredEndpointRowMass
          endpoint source)
        (centralPhysicalRowMarginal
          w hw K halfExtent source)
        hpositive))
    hscaled

/-- A uniform relative bound on every retained row bounds the exact
physical-centered maximum. -/
theorem physicalCenteredEndpointRate_le_of_rows
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (hrow :
      ∀ source,
        source ∈
            centralPositiveHalfStates
              w hw K halfExtent →
          physicalCenteredEndpointRowMass
              endpoint source ≤
            epsilon *
              centralPhysicalRowMarginal
                w hw K halfExtent source) :
    physicalCenteredEndpointRate endpoint ≤
      epsilon := by
  unfold physicalCenteredEndpointRate
  apply listQMaxZero_le_of_on_mem
    (physicalCenteredEndpointRowRatio endpoint)
    (centralPositiveHalfStates w hw K halfExtent)
    epsilon hepsilon
  intro source hsource
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  unfold physicalCenteredEndpointRowRatio
  rw [dif_pos hpositive]
  exact Q'.divPos_le_of_le_mul _ _ _
    (hrow source hsource)

/-- The exact finite rate bound is equivalent to its literal all-row
relative estimate. -/
theorem physicalCenteredEndpointRate_le_iff_rows
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon) :
    physicalCenteredEndpointRate endpoint ≤ epsilon ↔
      ∀ source,
        source ∈
            centralPositiveHalfStates
              w hw K halfExtent →
          physicalCenteredEndpointRowMass
              endpoint source ≤
            epsilon *
              centralPhysicalRowMarginal
                w hw K halfExtent source := by
  constructor
  · intro hrate source hsource
    have hrow :=
      physicalCenteredEndpointRowMass_le_rate_mul_marginal
        (endpoint := endpoint) hsource
    have hmarginal :
        (0 : Q') ≤
          centralPhysicalRowMarginal
            w hw K halfExtent source :=
      centralPhysicalRowMarginal_nonnegative
        hw K halfExtent source
    exact Q'.le_trans' _ _ _ hrow
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hrate hmarginal)
  · exact physicalCenteredEndpointRate_le_of_rows
      endpoint epsilon hepsilon

/-! ## 2. Mean-zero cancellation and endpoint-preserving adapter -/

/-- The physical-centered row maximum is a valid Rayleigh rate for the
unchanged endpoint joint. -/
theorem physicalCenteredEndpoint_meanZero_quadratic
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (finiteJointQuadratic
          (centralPositiveHalfStates
            w hw K halfExtent)
          observable endpoint.joint) ≤
      physicalCenteredEndpointRate endpoint *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  let states :=
    centralPositiveHalfStates
      w hw K halfExtent
  let vacuum :=
    centralPhysicalVacuumJoint
      w hw K halfExtent
  let endpointQuadratic :=
    finiteJointQuadratic states observable endpoint.joint
  let vacuumQuadratic :=
    finiteJointQuadratic states observable vacuum
  have hvacuum :
      vacuumQuadratic ≈ 0 :=
    centralPhysicalVacuumJoint_quadratic_meanZero
      observable hmean
  have hdifference :
      endpointQuadratic + (-vacuumQuadratic) ≈
        endpointQuadratic := by
    exact Q'.eqv_trans _
      (endpointQuadratic + 0) _
      (Q'.add_eqv_congr_left
        endpointQuadratic (-vacuumQuadratic) 0
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hvacuum)
          (Q'.eqv_refl 0)))
      (Q'.eqv_of_eq
        (Q'.add_zero' endpointQuadratic))
  have hperturbation :
      Q'.abs
          (endpointQuadratic + (-vacuumQuadratic)) ≤
        physicalCenteredEndpointRate endpoint *
          finiteWeightedSquare
            states
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            observable :=
    finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      endpoint.joint vacuum
      (physicalCenteredEndpointRate endpoint)
      (fun left right hleft hright =>
        endpoint.joint_symmetric hleft hright)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K halfExtent left right)
      (fun state hstate =>
        physicalCenteredEndpointRowMass_le_rate_mul_marginal
          hstate)
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hperturbation ?_)
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left
      (physicalCenteredEndpointRate endpoint)
      (finiteWeightedSquare
        states
        (centralPhysicalRowMarginal
          w hw K halfExtent)
        observable)
      (centralPhysicalWeightedInner
        w hw K halfExtent observable observable)
      (finiteWeightedSquare_physical_eqv_inner
        w hw K halfExtent observable))

/-- Replace only the rate certificate of a raw endpoint by its exact
physical-centered finite-row rate. -/
def physicalRecenterRawMehlerEndpointRate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator := endpoint.numerator
  partition := endpoint.partition
  partition_pos := endpoint.partition_pos
  numerator_symmetric := endpoint.numerator_symmetric
  normalized_quadratic_nonnegative :=
    endpoint.normalized_quadratic_nonnegative
  rate := physicalCenteredEndpointRate endpoint
  rate_nonnegative :=
    physicalCenteredEndpointRate_nonnegative endpoint
  normalized_meanZero_quadratic :=
    physicalCenteredEndpoint_meanZero_quadratic endpoint

/-- Physical recentering preserves every normalized endpoint entry. -/
theorem physicalRecenterRawMehlerEndpointRate_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (left right : EdgeLabelling) :
    (physicalRecenterRawMehlerEndpointRate endpoint).joint
        left right ≈
      endpoint.joint left right := by
  exact Q'.eqv_refl _

/-- Because physical recentering changes no joint entry, it leaves the
literal physical-minus-endpoint row error unchanged. -/
theorem physicalNormalizedJointRowError_recenter_eqv
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    physicalNormalizedJointRowError
        (physicalRecenterRawMehlerEndpointRate endpoint)
        source ≈
      physicalNormalizedJointRowError endpoint source := by
  unfold physicalNormalizedJointRowError
    finiteJointDifferenceAbsRowMass
  apply listQSum_congr
  intro target
  apply Q'.abs_eqv_congr
  apply Q'.add_eqv_congr_left
  exact Q'.neg_eqv_congr _ _
    (physicalRecenterRawMehlerEndpointRate_joint
      endpoint source target)

/-! ## 3. Correctly recentered vacuum-calibrated endpoint -/

/-- The vacuum-calibrated BF4 positive Gram equipped with the exact
post-calibration physical-centered rate. -/
def physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent :=
  physicalRecenterRawMehlerEndpointRate
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)

/-- Recentring changes no entry of the calibrated normalized joint. -/
theorem physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        left right ≈
      (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        left right := by
  exact physicalRecenterRawMehlerEndpointRate_joint
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)
    left right

/-- Explicit normalized joint of the calibrated endpoint:
`pi0^2` times the vacuum-normalized five-holonomy Gram. -/
theorem physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint_eqv_scaled
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        left right ≈
      (pi0 * pi0) *
        normalizedBF4MehlerGramJoint
          diagonalOrder crossOrder left right := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  refine Q'.eqv_trans _ _ _
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint
      w hw K halfExtent diagonalOrder crossOrder
      left right) ?_
  refine Q'.eqv_trans _ _ _
    (physicalRepartitionRawMehlerEndpoint_joint
      (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      left right) ?_
  exact Q'.eqv_trans _ _ _
    (squareScaledRawMehlerEndpoint_joint
      pi0
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
      (exactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      left right)
    (Q'.eqv_refl _)

/-- The corrected calibrated `1/8` problem is exactly the all-retained-row
estimate for `pi0^2 M - pi tensor pi`.  No inherited pre-calibration rate
appears. -/
theorem physicallyRecenteredVacuumCalibrated_rate_le_eighth_iff_rows
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).rate ≤
      Q'.mkPos 1 8 (by decide) ↔
    ∀ source,
      source ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        physicalCenteredEndpointRowMass
            (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
              w hw K halfExtent diagonalOrder crossOrder)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            centralPhysicalRowMarginal
              w hw K halfExtent source := by
  exact physicalCenteredEndpointRate_le_iff_rows
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)
    (Q'.mkPos 1 8 (by decide)) (by decide)

/-- The correctly recentered calibrated endpoint still exactly matches the
physical stationary-vacuum coefficient. -/
theorem physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_vacuum
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≈
      pi0 * pi0 := by
  exact Q'.eqv_trans _ _ _
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint
      w hw K halfExtent diagonalOrder crossOrder
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint_vacuum
      w hw K halfExtent diagonalOrder crossOrder)

end YMGap.Continuum.BF4PhysicalRecenteredEndpointRate

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicalCenteredEndpointRowMass_le_rate_mul_marginal
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicalCenteredEndpointRate_le_iff_rows
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicalCenteredEndpoint_meanZero_quadratic
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicalRecenterRawMehlerEndpointRate_joint
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicalNormalizedJointRowError_recenter_eqv
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint_eqv_scaled
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicallyRecenteredVacuumCalibrated_rate_le_eighth_iff_rows
#print axioms YMGap.Continuum.BF4PhysicalRecenteredEndpointRate.physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_vacuum
