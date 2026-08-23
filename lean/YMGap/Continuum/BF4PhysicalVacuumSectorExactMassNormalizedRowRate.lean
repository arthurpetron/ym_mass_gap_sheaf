/-
# The sharp exact mass-normalized row rate

The centered boundary-Gram row majorant applies Tonelli before summing the
actual centered kernel row, so its exact finite maximum can still contain
triangle-inequality slack.  The literal mass-normalized row distance supplies
the next sharper scalar: divide each canonical source row by its strictly
positive stationary weight and take the located finite maximum.

This module constructs that scalar, proves it is the least displayed common
coefficient for the actual row-distance inequalities, compares it to the
exact centered-Gram row rate, and evaluates it to zero at cutoff one.

A constructively cofinal upper bound below one for this exact row scalar
compiles directly to the completed same-object vacuum-sector gap.  No such
bound is inhabited here, and no finite calculation is promoted to a
thermodynamic or continuum statement.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate
open YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal row distance and its exact normalized maximum -/

/-- Actual row distance between the physical joint and the stationary product
conditioned on the canonical vacuum component. -/
def centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    (finiteCarrierMassNormalizedStationaryProductJoint
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half))
    source

theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
    finiteJointDifferenceAbsRowMass
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.abs_nonneg _

/-- The normalized actual row distance on a canonical source, and zero
outside the canonical component. -/
def centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    Q'.divPos
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        w hw cutoff half source)
      (centralPhysicalFiniteWeight w hw cutoff half source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  else 0

/-- Located maximum of the normalized actual mass-conditioned rows. -/
def centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteMaxZero
    (centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorNormalizedMassRowRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
        w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
  by_cases hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · rw [dif_pos hsource]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_nonnegative
        w hw cutoff half source)
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  · rw [dif_neg hsource]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
  exact finiteMaxZero_nonnegative _ _
    (fun source _ =>
      centralPhysicalFiniteVacuumSectorNormalizedMassRowRate_nonnegative
        w hw cutoff half source)

/-! ## 2. Exact row bound and minimality -/

theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        w hw cutoff half source ≤
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
          w hw cutoff half *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  let row := centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
    w hw cutoff half source
  let weight := centralPhysicalFiniteWeight w hw cutoff half source
  let weight_pos :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hnormalized : Q'.divPos row weight weight_pos ≤
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half := by
    have hmax := le_finiteMaxZero_of_mem
      (centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
        w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) hsource
    simpa [centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate,
      centralPhysicalFiniteVacuumSectorNormalizedMassRowRate,
      hsource, row, weight, weight_pos] using hmax
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    hnormalized (Q'.le_of_lt weight_pos)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.divPos_mul_eqv row weight weight_pos)))
    hscaled

/-- Any nonnegative scalar that bounds every actual mass-normalized row also
bounds their exact normalized maximum. -/
theorem centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_of_rowBound
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {rate : Q'}
    (rate_nonnegative : (0 : Q') ≤ rate)
    (hrow : ∀ source,
      (hsource : source ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) →
      centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
          w hw cutoff half source ≤
        rate * centralPhysicalFiniteWeight w hw cutoff half source) :
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half ≤ rate := by
  unfold centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
  apply finiteMaxZero_le _ rate _ rate_nonnegative
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorNormalizedMassRowRate
  rw [dif_pos hsource]
  exact Q'.divPos_le_of_le_mul _ _
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
    (hrow source hsource)

/-! ## 3. Cofinal exact-rate compiler -/

structure FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  exactRateBound : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw (anchor base threshold) half ≤ rate

namespace FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound

def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    refine Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight
        hsource) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (family.exactRateBound base threshold)
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound

/-! ## 4. Comparison to the exact centered-Gram row rate -/

theorem centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactCenteredGramRowRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half := by
  exact centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_of_rowBound
    (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_nonnegative
      w hw cutoff half)
    (fun source hsource =>
      Q'.le_trans' _ _ _
        (centralPhysicalFiniteVacuumSector_rowDistance_le_centeredGramMajorant
          hsource)
        (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactCenteredGramRowRate_mul_weight
          hsource))

theorem centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactPosteriorL1MaximumRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w hw cutoff half :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactCenteredGramRowRate
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate
      w hw cutoff half)

/-! ## 5. Exact cutoff-one value -/

theorem centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  have hle :
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
          w (Q'.le_of_lt hw) 1 0 ≤ 0 :=
    Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactCenteredGramRowRate
        w (Q'.le_of_lt hw) 1 0)
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_cutoffOne_eqv_zero
          hw))
  exact Q'.eqv_of_le_le hle
    (centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_nonnegative
      w (Q'.le_of_lt hw) 1 0)

end YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_of_rowBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactCenteredGramRowRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate.centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_cutoffOne_eqv_zero
