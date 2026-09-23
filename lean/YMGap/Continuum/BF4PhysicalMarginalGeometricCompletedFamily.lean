/-
# Inhabited marginal completed-family staging certificate

The fixed-nome marginal SU(2) contraction is already inhabited at
`w = 1/2`, and the repository has an explicit geometric spacing with a
constructive modulus tending to zero.  This module joins those two pieces into
one scale-indexed `DynamicVacuumSectorCompletedFamily`.

The result is deliberately a staging object, not a continuum mass-gap
certificate: its lattice margin is fixed while its spacing vanishes, so no
two-sided physical-rate band or same-family physical-gap variation is claimed.
The completed carrier, transfer, and norm-decay law remain the actual same
objects at every scale.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate
import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap

namespace YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement
open YMGap.Continuum.PhysicalSeparatorLinearTail

/-! ## 1. The inhabited scale-indexed family -/

/-- A concrete scale-indexed family of the actual completed SU(2) marginal
sector.  The nome is held at `1/2`, while the attached physical spacing is the
explicit geometric sequence `(1/2)^scale`.  This family is useful for testing
same-object dynamic consumers, but its physical gap is intentionally not
claimed to stay in a finite positive band. -/
def marginalHalfGeometricCompletedFamily :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := fun _ => HalfPow.half
  nome_pos := fun _ => by decide
  nome_lt_one := fun _ => by decide
  transferSpacing := canonicalAFGeometricPhysicalSpacing
  transferSpacingToZero := canonicalAFGeometricSpacingToZero
  completedGap := fun _ =>
    completedSectorContraction
      (w := HalfPow.half) (by decide) (by decide) (by decide)

@[simp] theorem marginalHalfGeometricCompletedFamily_nome (scale : Nat) :
    marginalHalfGeometricCompletedFamily.nome scale = HalfPow.half := rfl

@[simp] theorem marginalHalfGeometricCompletedFamily_spacing (scale : Nat) :
    marginalHalfGeometricCompletedFamily.transferSpacing.spacing scale =
      canonicalAFGeometricSpacing scale := rfl

def marginalHalfGeometricCompletedFamily_spacing_to_zero :
    SpacingToZero marginalHalfGeometricCompletedFamily.transferSpacing :=
  marginalHalfGeometricCompletedFamily.transferSpacingToZero

/-! ## 2. Exact rate and decay pins -/

/-- The completed-sector rate in this staging family is exactly the inhabited
fixed-nome marginal rate; no abstract rate is substituted. -/
theorem marginalHalfGeometricCompletedFamily_rate (scale : Nat) :
    (marginalHalfGeometricCompletedFamily.completedGap scale).rate =
      cutoffUniformRate HalfPow.half (by decide) := by
  exact completedSectorContraction_rate
    (w := HalfPow.half) (by decide) (by decide) (by decide)

theorem marginalHalfGeometricCompletedFamily_rate_pos (scale : Nat) :
    (0 : Q') <
      (marginalHalfGeometricCompletedFamily.completedGap scale).rate := by
  rw [marginalHalfGeometricCompletedFamily_rate]
  exact cutoffUniformRate_pos HalfPow.half (by decide)

theorem marginalHalfGeometricCompletedFamily_rate_lt_one (scale : Nat) :
    (marginalHalfGeometricCompletedFamily.completedGap scale).rate <
      (1 : Q') := by
  exact (marginalHalfGeometricCompletedFamily.completedGap scale).rate_lt_one

/-- Every scale in the staging family has the existing same-object completed
autocorrelation squared bound, with the family-selected carrier and rate. -/
theorem marginalHalfGeometricCompletedFamily_autocorrelation_sq_decay
    (scale n : Nat)
    (vector :
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        (marginalHalfGeometricCompletedFamily.nome_pos scale)
        (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale)
          0 n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale)
          0 n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          (((marginalHalfGeometricCompletedFamily.completedGap scale).rate *
              (marginalHalfGeometricCompletedFamily.completedGap scale).rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (marginalHalfGeometricCompletedFamily.nome_pos scale)
            (marginalHalfGeometricCompletedFamily.nome_lt_one scale)
            0 vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale)
          0 vector.1 vector.1)) := by
  exact DynamicVacuumSectorCompletedFamily.completedAutocorrelation_sq_decay
    marginalHalfGeometricCompletedFamily scale n vector

/-! ## 3. The literal moving-centered cube instance -/

/-- The staging-family decay law specializes to the literal moving-centered
cube observable already packaged by the concrete SU(2) carrier certificate.
No carrier, transfer, or observable is changed by this specialization. -/
theorem marginalHalfGeometricCompletedFamily_concrete_cube_autocorrelation_sq_decay
    (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation
          (w := HalfPow.half) (by decide) (by decide) n)
        (concreteSameObjectAutocorrelation
          (w := HalfPow.half) (by decide) (by decide) n))
      (CReal.RCmul
        (CReal.RCscale
          (((marginalHalfGeometricCompletedFamily.completedGap 0).rate *
              (marginalHalfGeometricCompletedFamily.completedGap 0).rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (by decide) (by decide) 0
            (concreteVacuumComplementVector
              (w := HalfPow.half) (by decide) (by decide)).1
            (concreteVacuumComplementVector
              (w := HalfPow.half) (by decide) (by decide)).1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (by decide) (by decide) 0
          (concreteVacuumComplementVector
            (w := HalfPow.half) (by decide) (by decide)).1
          (concreteVacuumComplementVector
            (w := HalfPow.half) (by decide) (by decide)).1)) := by
  simpa only [concreteSameObjectAutocorrelation, concreteVacuumComplementVector] using
    (marginalHalfGeometricCompletedFamily_autocorrelation_sq_decay
      0 n
      (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
        (by decide) (by decide)))

/-! ## Dependency gates -/

end YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_spacing_to_zero
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_rate
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_rate_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_rate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_autocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_concrete_cube_autocorrelation_sq_decay
