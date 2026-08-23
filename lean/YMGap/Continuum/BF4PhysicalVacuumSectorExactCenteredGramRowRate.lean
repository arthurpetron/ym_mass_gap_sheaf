/-
# The sharp exact centered-Gram row rate

The exact posterior-maximum product still separates the two Bayes directions
before multiplying their worst cases.  The literal physical centered-Gram
majorant already supplies a sharper scalar: divide each canonical source row
by its strictly positive stationary weight and take the located finite
maximum.  This module constructs that rate, proves it is the least displayed
common row coefficient, compares it to the posterior-maximum product, and
evaluates it to zero at cutoff one.

A constructively cofinal upper bound below one for this exact row scalar
compiles directly to the completed same-object vacuum-sector gap.  No such
bound is inhabited here, and no finite calculation is promoted to a
thermodynamic or continuum statement.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact normalized row scalar -/

theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
    YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.finiteWeightedGramCenteredRowMajorant
  apply listQSum_nonnegative_on
  intro boundary _
  apply Q'.mul_nonneg
  · exact Q'.abs_nonneg _
  · apply listQSum_nonnegative_on
    intro target _
    exact Q'.abs_nonneg _

/-- The normalized physical row majorant on a canonical source, and zero
outside the canonical component. -/
def centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    Q'.divPos
      (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source)
      (centralPhysicalFiniteWeight w hw cutoff half source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  else 0

/-- Located maximum of the exact normalized centered-Gram rows. -/
def centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteMaxZero
    (centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
        w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
  by_cases hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · rw [dif_pos hsource]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_nonnegative
        w hw cutoff half source)
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  · rw [dif_neg hsource]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
  exact finiteMaxZero_nonnegative _ _
    (fun source _ =>
      centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate_nonnegative
        w hw cutoff half source)

/-! ## 2. Exact row bound and minimality -/

theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactCenteredGramRowRate_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source ≤
      centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
          w hw cutoff half *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  let row := centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
    w hw cutoff half source
  let weight := centralPhysicalFiniteWeight w hw cutoff half source
  let weight_pos :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hnormalized : Q'.divPos row weight weight_pos ≤
      centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half := by
    have hmax := le_finiteMaxZero_of_mem
      (centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
        w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) hsource
    simpa [centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate,
      centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate,
      hsource, row, weight, weight_pos] using hmax
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    hnormalized (Q'.le_of_lt weight_pos)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.divPos_mul_eqv row weight weight_pos)))
    hscaled

/-- Any nonnegative scalar that bounds every canonical centered-Gram row
also bounds the exact normalized row maximum. -/
theorem centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_of_rowBound
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {rate : Q'}
    (rate_nonnegative : (0 : Q') ≤ rate)
    (hrow : ∀ source,
      (hsource : source ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) →
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
          w hw cutoff half source ≤
        rate * centralPhysicalFiniteWeight w hw cutoff half source) :
    centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half ≤ rate := by
  unfold centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
  apply finiteMaxZero_le _ rate _ rate_nonnegative
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorNormalizedCenteredGramRowRate
  rw [dif_pos hsource]
  exact Q'.divPos_le_of_le_mul _ _
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
    (hrow source hsource)

/-! ## 3. Cofinal exact-rate compiler -/

structure FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  exactRateBound : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw (anchor base threshold) half ≤ rate

namespace FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound

def toCenteredGramMajorant
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  majorantBound := by
    intro base threshold source hsource
    refine Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactCenteredGramRowRate_mul_weight
        hsource) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (family.exactRateBound base threshold)
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toCenteredGramMajorant.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound

/-! ## 4. Comparison to the posterior-maximum product -/

theorem centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w hw cutoff half := by
  exact centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_of_rowBound
    (centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_nonnegative
      w hw cutoff half)
    (fun source hsource =>
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactPosteriorL1MaximumRate_mul_weight
        hsource)

theorem centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_overlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w hw cutoff half ≤
      YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w hw cutoff half := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_le_overlapResidualRate
      w hw cutoff half)

/-! ## 5. Exact cutoff-one value -/

theorem centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  have hle :
      centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate
          w (Q'.le_of_lt hw) 1 0 ≤ 0 :=
    Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate
        w (Q'.le_of_lt hw) 1 0)
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_cutoffOne_eqv_zero
          hw))
  exact Q'.eqv_of_le_le hle
    (centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_nonnegative
      w (Q'.le_of_lt hw) 1 0)

end YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactCenteredGramRowRate_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_of_rowBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactCenteredGramRowRate.centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_cutoffOne_eqv_zero
