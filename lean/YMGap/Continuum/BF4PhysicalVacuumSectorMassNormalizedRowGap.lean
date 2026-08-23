/-
# Mass-normalized row distance on the canonical BF4 vacuum sector

The canonical vacuum component generally has stationary mass strictly between
zero and one.  Its equilibrium joint is therefore not the unnormalized
product `pi(x) * pi(y)`, but the component-conditioned product

    pi(x) * pi(y) / mass(component).

This file makes that normalization exact.  A symmetric joint that is
rowwise close to the mass-normalized product has the same centered quadratic
contraction as in the probability-normalized case, because the rank-one
reference still vanishes on exactly sector-centered coefficients.  A
constructively cofinal family of these corrected row estimates then compiles
to the existing same-object cutoff-limit gap.

No inhabitant of the cofinal certificate is asserted.  No thermodynamic or
continuum limit is constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic mass-normalized stationary product -/

/-- The rank-one stationary joint conditioned on a component of positive
stationary mass. -/
def finiteCarrierMassNormalizedStationaryProductJoint
    {State : Type} (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (left right : State) : Q' :=
  finiteStationaryProductJoint weight left right *
    Q'.recipPos mass mass_pos

/-- The mass-normalized rank-one quadratic is the unnormalized rank-one
quadratic multiplied by the reciprocal component mass. -/
theorem finiteCarrierMassNormalizedStationaryProductJoint_quadratic_eqv
    {State : Type} (states : List State) (mass : Q')
    (mass_pos : (0 : Q') < mass)
    (weight coefficient : State → Q') :
    finiteJointQuadratic states coefficient
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) ≈
      finiteJointQuadratic states coefficient
          (finiteStationaryProductJoint weight) *
        Q'.recipPos mass mass_pos := by
  let reciprocal := Q'.recipPos mass mass_pos
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            ((coefficient left * coefficient right) *
                finiteStationaryProductJoint weight left right) *
              reciprocal)
          states)
      states) _ ?_ ?_
  · unfold finiteJointQuadratic
      finiteCarrierMassNormalizedStationaryProductJoint reciprocal
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficient left * coefficient right)
        (finiteStationaryProductJoint weight left right)
        (Q'.recipPos mass mass_pos))
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum
              (fun right =>
                (coefficient left * coefficient right) *
                  finiteStationaryProductJoint weight left right)
              states * reciprocal)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      exact listQSum_mul_right _ reciprocal states
    · unfold finiteJointQuadratic reciprocal
      exact listQSum_mul_right _ (Q'.recipPos mass mass_pos) states

/-- Exact sector centering also kills the correctly mass-normalized
stationary-product quadratic. -/
theorem finiteCarrierMassNormalizedStationaryProductJoint_quadratic_centered_eqv_zero
    {State : Type} {states : List State} {mass : Q'}
    {mass_pos : (0 : Q') < mass}
    {weight coefficient : State → Q'}
    (hcenter :
      listQSum (fun state => coefficient state * weight state) states ≈ 0) :
    finiteJointQuadratic states coefficient
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) ≈ 0 := by
  refine Q'.eqv_trans _
    (finiteJointQuadratic states coefficient
        (finiteStationaryProductJoint weight) *
      Q'.recipPos mass mass_pos) _
    (finiteCarrierMassNormalizedStationaryProductJoint_quadratic_eqv
      states mass mass_pos weight coefficient) ?_
  refine Q'.eqv_trans _
    (0 * Q'.recipPos mass mass_pos) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _
        (finiteListWeightedMean states weight coefficient *
          finiteListWeightedMean states weight coefficient) _
        (finiteStationaryProductJoint_quadratic_eqv_mean_square
          states weight coefficient)
        (Q'.eqv_trans _
          (0 * finiteListWeightedMean states weight coefficient) _
          (Q'.mul_eqv_congr_right _ _ _ hcenter)
          (Q'.zero_mul_eqv _)))
  · exact Q'.zero_mul_eqv _

/-- A symmetric joint is rowwise close to the equilibrium joint conditioned
on one finite positive-mass component. -/
structure FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
    {State : Type} (states : List State) (mass rate : Q')
    (mass_pos : (0 : Q') < mass) (weight : State → Q')
    (kernel : State → State → Q') : Type 1 where
  kernelSymmetric : ∀ left right,
    left ∈ states → right ∈ states →
      kernel left right ≈ kernel right left
  rowDistance : ∀ source, source ∈ states →
    finiteJointDifferenceAbsRowMass states kernel
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) source ≤
      rate * weight source

namespace FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate

/-- The corrected component-conditioned row distance proves the absolute
centered quadratic contraction on exactly that component. -/
theorem absContraction
    {State : Type} {states : List State} {mass rate : Q'}
    {mass_pos : (0 : Q') < mass} {weight : State → Q'}
    {kernel : State → State → Q'}
    (certificate :
      FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
        states mass rate mass_pos weight kernel)
    (coefficient : State → Q')
    (hcenter :
      listQSum (fun state => coefficient state * weight state) states ≈ 0) :
    Q'.abs (finiteJointQuadratic states coefficient kernel) ≤
      rate * finiteWeightedSquare states weight coefficient := by
  have hproductSymmetric : ∀ left right,
      left ∈ states → right ∈ states →
        finiteCarrierMassNormalizedStationaryProductJoint
            mass mass_pos weight left right ≈
          finiteCarrierMassNormalizedStationaryProductJoint
            mass mass_pos weight right left := by
    intro left right _ _
    unfold finiteCarrierMassNormalizedStationaryProductJoint
      finiteStationaryProductJoint
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
  have hperturb := finiteJointQuadratic_abs_sub_le_weightedSquare
    states coefficient weight kernel
    (finiteCarrierMassNormalizedStationaryProductJoint
      mass mass_pos weight) rate
    certificate.kernelSymmetric hproductSymmetric certificate.rowDistance
  have hproduct :=
    finiteCarrierMassNormalizedStationaryProductJoint_quadratic_centered_eqv_zero
      (mass := mass) (mass_pos := mass_pos) hcenter
  have hdiff :
      finiteJointQuadratic states coefficient kernel +
          (-finiteJointQuadratic states coefficient
            (finiteCarrierMassNormalizedStationaryProductJoint
              mass mass_pos weight)) ≈
        finiteJointQuadratic states coefficient kernel := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic states coefficient kernel + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hproduct) (by decide))
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hdiff))) hperturb

end FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate

/-! ## 2. Physical cofinal vacuum-sector specialization -/

/-- One strict rate and one constructively cofinal corrected row-distance
certificate.  The comparison joint is normalized by the actual stationary
mass of the selected canonical component. -/
structure FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  rowDistance : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      finiteJointDifferenceAbsRowMass
          (centralPhysicalFiniteVacuumSectorIndices
            w hw (anchor base threshold) half)
          (centralPhysicalFiniteKernel
            w hw (anchor base threshold) half)
          (finiteCarrierMassNormalizedStationaryProductJoint
            (centralPhysicalFiniteVacuumSectorMass
              w hw (anchor base threshold) half)
            (centralPhysicalFiniteVacuumSectorWeightSum_pos
              w hw (anchor base threshold) half)
            (centralPhysicalFiniteWeight
              w hw (anchor base threshold) half))
          source ≤
        rate * centralPhysicalFiniteWeight
          w hw (anchor base threshold) half source

namespace FixedNomeCofinalVacuumSectorMassNormalizedRowDistance

/-- Package one selected physical cutoff as the generic corrected finite
carrier certificate. -/
def finiteCertificate
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
        w hw half rate)
    (base threshold : Nat) :
    FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteVacuumSectorIndices
        w hw (family.anchor base threshold) half)
      (centralPhysicalFiniteVacuumSectorMass
        w hw (family.anchor base threshold) half)
      rate
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw (family.anchor base threshold) half)
      (centralPhysicalFiniteWeight
        w hw (family.anchor base threshold) half)
      (centralPhysicalFiniteKernel
        w hw (family.anchor base threshold) half) where
  kernelSymmetric := by
    intro left right hleft hright
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base threshold) half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw (family.anchor base threshold) half hleft))).1
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base threshold) half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw (family.anchor base threshold) half hright))).1
  rowDistance := family.rowDistance base threshold

/-- Corrected mass-normalized row distance supplies the exact cofinal
same-object centered gap consumed by the cutoff limits. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  centeredGap := by
    intro base threshold coefficient
    let later := family.anchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold)
        (family.anchor_ge base threshold)
    have hcenter :
        centralPhysicalFiniteVacuumSectorWeightedMean
            w hw later half extended ≈ 0 :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hfinite :=
      (family.finiteCertificate base threshold).absContraction
        extended hcenter
    have hmatrix :
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
        hbaseLater coefficient
    have hdiagonal :
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw later half extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
        hbaseLater coefficient
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hfinite
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate _ _
            (Q'.eqv_trans _ _ _
              (finiteWeightedSquare_vacuumSector_eqv_diagonal
                w hw later half extended)
              hdiagonal))))

/-- The corrected sector-local row frontier contracts to the strict
comparison of the two moving centered Bishop-real limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
        w (Q'.le_of_lt hw0) half rate)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' rate)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap base coefficient

end FixedNomeCofinalVacuumSectorMassNormalizedRowDistance

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.finiteCarrierMassNormalizedStationaryProductJoint_quadratic_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.finiteCarrierMassNormalizedStationaryProductJoint_quadratic_centered_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate.absContraction
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.FixedNomeCofinalVacuumSectorMassNormalizedRowDistance.finiteCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.FixedNomeCofinalVacuumSectorMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap.FixedNomeCofinalVacuumSectorMassNormalizedRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
