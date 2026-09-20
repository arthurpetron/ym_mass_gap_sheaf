/-
# Compile an exact fixed-ratio producer into the normalized moving-cube route

The normalized moving-cube clustering bridge requires an explicit
`NormalizedMovingCubeRatePowerGeometricIdentification`.  This module factors
that obligation to its smallest same-stream input: a rational `ratio` and a
pointwise `Q'` equality between the *actual* scheduled rate-power stream and
`ratio ^ time` at every cutoff and physical time.

The pointwise equality is not proved here and is not replaced by a proxy.  Once
it is supplied, the exact stream has a constant CReal limit with an explicit
zero-stage convergence modulus, and the existing same-object continuum
certificate can be assembled without changing its raw representative or
normalization-debt limit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeFixedRatioCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Minimal fixed-ratio input -/

/-- Pointwise data for the exact scheduled squared-rate stream.  This is the
minimal finite-to-geometric input: it names the same family, the same cutoff
index, and the same physical-time schedule used by the normalized decay
theorem. -/
structure NormalizedMovingCubeFixedRatioData
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  ratio : Q'
  ratio_nonneg : (0 : Q') <= ratio
  ratio_lt_one : ratio < (1 : Q')
  pointwise : forall scale time : Nat,
    normalizedMovingCubeSampledRatePower family scale time ≈ ratio ^ time

/-! ## 2. Constant-limit construction -/

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

/-- The exact scheduled stream has the fixed-ratio CReal limit when the
pointwise producer data are supplied.  Its convergence stage is zero because
the finite stream is pointwise equivalent to a constant sequence. -/
def NormalizedMovingCubeFixedRatioData.toRatePowerLimit
    {family : DynamicVacuumSectorCompletedFamily 0}
    (data : NormalizedMovingCubeFixedRatioData family) :
    NormalizedMovingCubeSampledRatePowerLimit family where
  limitRepresentative := fun time => CReal.ofQ' (data.ratio ^ time)
  converges := fun time =>
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (fun scale =>
        YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
          (Q'.eqv_symm (data.pointwise scale time)))
      (convergesTo_const (CReal.ofQ' (data.ratio ^ time)))

/-! ## 3. Fixed-ratio identification and same-object certificate -/

/-- The constructed rate-power limit carries the exact geometric
identification required by the canonical clustering interface. -/
def NormalizedMovingCubeFixedRatioData.toGeometricIdentification
    {family : DynamicVacuumSectorCompletedFamily 0}
    (data : NormalizedMovingCubeFixedRatioData family) :
    NormalizedMovingCubeRatePowerGeometricIdentification family
      data.toRatePowerLimit where
  ratio := data.ratio
  ratio_nonneg := data.ratio_nonneg
  ratio_lt_one := data.ratio_lt_one
  ratePower_eq_ratio_pow := fun _ => rfl

/-- Assemble the same-observable continuum certificate from raw and
normalization-debt variation streams plus the minimal exact fixed-ratio data.
The rate-power stream in the result is definitionally the actual scheduled
stream's constant limit, not a surrogate sequence. -/
def NormalizedMovingCubeContinuumCertificate.ofFixedRatioData
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtVariation family)
    (data : NormalizedMovingCubeFixedRatioData family) :
    NormalizedMovingCubeContinuumCertificate family where
  limit := normalizedMovingCubeLimitOfVariations family raw normDebt
  ratePower := data.toRatePowerLimit
  geometricRate := data.toGeometricIdentification

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeFixedRatioCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeFixedRatioCompiler.NormalizedMovingCubeFixedRatioData.toRatePowerLimit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeFixedRatioCompiler.NormalizedMovingCubeFixedRatioData.toGeometricIdentification
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeFixedRatioCompiler.NormalizedMovingCubeContinuumCertificate.ofFixedRatioData
