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
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

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

/-! ## 4. The staging family cannot supply the physical-rate band -/

/-- The fixed completed lattice margin in the staging family is incompatible
with the upper half of the physical-rate-band contract when the attached
spacing tends to zero.  This prunes a false continuum shortcut; it does not
refute a genuinely scale-dependent completed transfer family. -/
theorem noPhysicalRateBand_of_marginalHalfGeometricCompletedFamily
    (band :
      DynamicVacuumSectorPhysicalRateBand
        marginalHalfGeometricCompletedFamily) :
    False := by
  let family := marginalHalfGeometricCompletedFamily
  have hmarginPos : (0 : Q') < family.latticeMargin 0 :=
    family.latticeMargin_pos 0
  let epsilon : Q' := HalfPow.half * family.latticeMargin 0
  have hepsilon : (0 : Q') < epsilon := by
    unfold epsilon
    exact ExpNeg.half_mul_pos _ hmarginPos
  let hscale := band.marginModulus epsilon
  have hsmall := band.latticeMargin_le_epsilon
    epsilon hepsilon hscale (Nat.le_refl _)
  have hfixed : family.latticeMargin hscale ≈
      family.latticeMargin 0 := by
    unfold family marginalHalfGeometricCompletedFamily
      DynamicVacuumSectorCompletedFamily.latticeMargin
    exact Q'.eqv_refl _
  have hle : family.latticeMargin 0 ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hfixed)) hsmall
  have hmul := Q'.mul_lt_mul_of_pos_left
    hmarginPos (by decide : HalfPow.half < (1 : Q'))
  have hstrict : epsilon < family.latticeMargin 0 * (1 : Q') := by
    unfold epsilon
    exact Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (Q'.mul_comm_eqv
        HalfPow.half (family.latticeMargin 0))) hmul
  have hreverse : family.latticeMargin 0 * (1 : Q') ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (family.latticeMargin 0))) hle
  exact (Int.not_lt_of_ge hreverse) hstrict

/-! ## 5. Explicit rate padding, kept separate from physical calibration -/

/-- Weaker finite cofinal rates preserve the same centered carrier bound.
This is a bookkeeping lemma only: because it deliberately replaces a rate by
a larger upper bound, it must not be used as a physical mass calibration. -/
def FixedNomeCofinalVacuumSectorCenteredStrictGap.weakenRate
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {q₀ q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half q₀)
    (h_rate : q₀ ≤ q)
    (hq_lt_one : q < (1 : Q')) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q where
  rate_nonnegative :=
    Q'.le_trans' _ _ _ certificate.rate_nonnegative h_rate
  rate_lt_one := hq_lt_one
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  centeredGap := by
    intro base threshold coefficient
    let later := certificate.anchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    have hbase : base ≤ later := by
      exact Nat.le_trans (Nat.le_max_left _ _)
        (certificate.anchor_ge base threshold)
    have h_old := certificate.centeredGap base threshold coefficient
    have h_matrix_nonnegative := fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := hw) base later half hbase coefficient
    have h_matrix_le_diagonal := fixedBasePulledMovingMatrix_le_diagonal
      (w := w) (hw := hw) base later half hbase coefficient
    have h_diagonal_nonnegative :
        (0 : Q') ≤
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      Q'.le_trans' _ _ _ h_matrix_nonnegative h_matrix_le_diagonal
    exact Q'.le_trans' _ _ _ h_old
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h_rate h_diagonal_nonnegative)

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
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.noPhysicalRateBand_of_marginalHalfGeometricCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily.FixedNomeCofinalVacuumSectorCenteredStrictGap.weakenRate
