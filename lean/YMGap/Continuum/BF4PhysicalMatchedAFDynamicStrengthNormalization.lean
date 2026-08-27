/-
# Automatic normalization of the matched adaptive BF4 strength

The exact matched dynamic-family compiler currently presents its physical-rate
frontier as a `DynamicVacuumSectorStrengthBand`.  That record asks for a
separate finite cap on the normalized local strength

  strength_j = ((1/2) * rayDelta_j) * sectorMassFloor_j.

For the actual adaptive BF4 producer this cap is not analytic input.  The
cofinal ray-capacity law gives `2 * rayDelta_j` below a genuine conditional
return probability.  One Markov row has mass one, hence that return
probability is at most one and `rayDelta_j <= 1/2`.  The constructed uniform
sector-mass floor is also at most one.  Therefore

  strength_j <= (1/2) * (1/2) = 1/4

at every scale, independently of the representation cutoff and without an
extra hypothesis.

This module removes that redundant field from the exact matched-AF path.  The
remaining `MatchedPhysicalDynamicStrengthScaling` contains precisely the two
genuine estimates: positive lower and finite upper comparison of the actual
strength with the actual transfer spacing.  It does not inhabit either
comparison, the local producer, the matched cubic law, the physical spacing
envelope, a continuum carrier, or the Clay target.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A genuine conditional return probability is at most one -/

/-- One spin-cube-to-vacuum return probability is at most one.  The proof
uses its literal normalized joint-kernel row, rather than adding a bound to
the cofinal capacity interface. -/
theorem centralLowerExcitedSpinCubeVacuumReturnProbability_le_one
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset <= 1 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let sector := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let row := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 index
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 index
  have hindex : index ∈ sector :=
    centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)
  have hzero : 0 ∈ sector :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0
  have hentry_le_sum : row 0 <= listQSum row sector :=
    listQSum_member_le_nonnegative row
      (fun target => by
        unfold row centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K 0 _ _)
      sector hzero
  have hsum : listQSum row sector ≈ weight :=
    centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hindex
  have hentry_le_weight : row 0 <= weight :=
    Q'.le_trans' _ _ _ hentry_le_sum (Q'.le_of_eqv hsum)
  unfold centralLowerExcitedSpinCubeVacuumReturnProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ weight _ hentry_le_weight
    (Q'.ge_of_eqv (Q'.one_mul_eqv weight))

/-! ## 2. The cofinal ray capacity and local strength are normalized -/

/-- Every admissible cofinal ray capacity has `delta <= 1/2`.  Choosing the
first nonempty cutoff above its start makes the defining return comparison
non-vacuous. -/
theorem FixedNomeCofinalSpinCubeRayCapacity.delta_le_half
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw) :
    capacity.delta <= HalfPow.half := by
  let K := capacity.start + 1
  have hoffset : 0 < K := by
    unfold K
    omega
  have htwice_return :
      2 * capacity.delta <=
        centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset :=
    capacity.twice_le_return K (by unfold K; omega) 0 hoffset
  have htwice_one : 2 * capacity.delta <= 1 :=
    Q'.le_trans' _ _ _ htwice_return
      (centralLowerExcitedSpinCubeVacuumReturnProbability_le_one
        hw hoffset)
  have htwice_half : 2 * capacity.delta <= 2 * HalfPow.half :=
    Q'.le_trans' _ 1 _ htwice_one
      (Q'.ge_of_eqv (by decide : (2 : Q') * HalfPow.half ≈ 1))
  exact Q'.le_of_mul_le_mul_left htwice_half (by decide)

/-- The exact residual-family strength has the canonical cap `1/4`, written
constructively as `half * half`. -/
theorem DynamicSpinCubeOffRayResidualCoercivityFamily.strength_le_half_sq
    (family : DynamicSpinCubeOffRayResidualCoercivityFamily)
    (scale : Nat) :
    family.strength scale <= HalfPow.half * HalfPow.half := by
  let delta := (family.rayCapacity scale).delta
  let factor := HalfPow.half * delta
  let massFloor := centralPhysicalFiniteVacuumSectorUniformMassFloor
    (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) 0
  have hdelta0 : (0 : Q') <= delta :=
    Q'.le_of_lt (family.rayCapacity scale).delta_pos
  have hdelta : delta <= HalfPow.half :=
    FixedNomeCofinalSpinCubeRayCapacity.delta_le_half
      (family.rayCapacity scale)
  have hfactor0 : (0 : Q') <= factor :=
    Q'.mul_nonneg _ _ (by decide) hdelta0
  have hfactor : factor <= HalfPow.half * HalfPow.half :=
    Q'.mul_le_mul_of_nonneg_left
      delta HalfPow.half HalfPow.half hdelta (by decide)
  have hmass : massFloor <= 1 :=
    centralPhysicalFiniteVacuumSectorUniformMassFloor_le_one
      (family.nome_pos scale) (family.nome_lt_one scale) 0
  have hfirst : factor * massFloor <= factor * 1 :=
    Q'.mul_le_mul_of_nonneg_left massFloor 1 factor hmass hfactor0
  have hsecond : factor * 1 <=
      (HalfPow.half * HalfPow.half) * 1 :=
    Q'.mul_le_mul_of_nonneg_right factor
      (HalfPow.half * HalfPow.half) 1 hfactor (by decide)
  unfold DynamicSpinCubeOffRayResidualCoercivityFamily.strength
    cutoffTwoDirichletGluingStrength
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv (Q'.mul_one_eqv
        (HalfPow.half * HalfPow.half))))

/-! ## 3. Only the two-sided strength/spacing comparison remains -/

/-- The reduced physical-scaling frontier on an actual adaptive completed
family.  The `1/4` cap and positivity of `upper` are consequences. -/
structure DynamicSpinCubeOffRayAdaptiveStrengthScaling
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  lowerScale : ∀ scale,
    lower * family.transferSpacing.spacing scale <=
      family.toResidualCoercivityFamily.strength scale
  upperScale : ∀ scale,
    family.toResidualCoercivityFamily.strength scale <=
      upper * family.transferSpacing.spacing scale

namespace DynamicSpinCubeOffRayAdaptiveStrengthScaling

/-- The upper spacing multiplier is forced positive already at scale zero. -/
theorem upper_pos
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (scaling : DynamicSpinCubeOffRayAdaptiveStrengthScaling family) :
    (0 : Q') < scaling.upper := by
  have hquotientPos :
      (0 : Q') < Q'.divPos
        (family.toResidualCoercivityFamily.strength 0)
        (family.transferSpacing.spacing 0)
        (family.transferSpacing.spacing_pos 0) :=
    Q'.divPos_pos _ _ (family.transferSpacing.spacing_pos 0)
      (family.toResidualCoercivityFamily.strength_pos 0)
  have hquotientLe :
      Q'.divPos
          (family.toResidualCoercivityFamily.strength 0)
          (family.transferSpacing.spacing 0)
          (family.transferSpacing.spacing_pos 0) <=
        scaling.upper :=
    Q'.divPos_le_of_le_mul _ _
      (family.transferSpacing.spacing_pos 0)
      (scaling.upperScale 0)
  exact Q'.pos_of_lt_of_le hquotientPos hquotientLe

/-- Supply the formerly explicit cap with its proved canonical value `1/4`. -/
def toStrengthBand
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (scaling : DynamicSpinCubeOffRayAdaptiveStrengthScaling family) :
    family.StrengthBand where
  lower := scaling.lower
  lower_pos := scaling.lower_pos
  upper := scaling.upper
  upper_pos := scaling.upper_pos
  cap := HalfPow.half * HalfPow.half
  cap_nonnegative := Q'.mul_nonneg _ _ (by decide) (by decide)
  lowerScale := scaling.lowerScale
  upperScale := scaling.upperScale
  strengthCap :=
    DynamicSpinCubeOffRayResidualCoercivityFamily.strength_le_half_sq
      family.toResidualCoercivityFamily

/-- The reduced two-sided scaling input reaches the same-object physical-rate
band on the exact adaptive completed transfer family. -/
def toPhysicalRateBand
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (scaling : DynamicSpinCubeOffRayAdaptiveStrengthScaling family) :
    DynamicVacuumSectorPhysicalRateBand family.toCompletedFamily :=
  scaling.toStrengthBand.toPhysicalRateBand

/-- Scalar physical-gap export from the same exact completed transfer. -/
def toContinuumGapTheorem
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (scaling : DynamicSpinCubeOffRayAdaptiveStrengthScaling family) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toStrengthBand.toContinuumGapTheorem

end DynamicSpinCubeOffRayAdaptiveStrengthScaling

/-! ## 4. Exact matched-AF specialization -/

/-- On the exact matched action, only the two scale comparisons remain after
the local producer has been supplied. -/
abbrev MatchedPhysicalDynamicStrengthScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  DynamicSpinCubeOffRayAdaptiveStrengthScaling
    (trajectory.toDynamicFamily producer)

/-- The reduced matched scaling certificate constructs the physical-rate band
on the literal matched completed carrier and transfer. -/
def MatchedPhysicalDynamicStrengthScaling.toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer) :
    DynamicVacuumSectorPhysicalRateBand
      (trajectory.toCompletedFamily producer) :=
  DynamicSpinCubeOffRayAdaptiveStrengthScaling.toPhysicalRateBand scaling

/-- The same reduced matched certificate reaches the sharp scalar continuum-
gap interface, without claiming a continuum carrier. -/
def MatchedPhysicalDynamicStrengthScaling.toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  DynamicSpinCubeOffRayAdaptiveStrengthScaling.toContinuumGapTheorem scaling

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.centralLowerExcitedSpinCubeVacuumReturnProbability_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.FixedNomeCofinalSpinCubeRayCapacity.delta_le_half
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.DynamicSpinCubeOffRayResidualCoercivityFamily.strength_le_half_sq
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.DynamicSpinCubeOffRayAdaptiveStrengthScaling.upper_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.DynamicSpinCubeOffRayAdaptiveStrengthScaling.toStrengthBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.DynamicSpinCubeOffRayAdaptiveStrengthScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.MatchedPhysicalDynamicStrengthScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization.MatchedPhysicalDynamicStrengthScaling.toContinuumGapTheorem
