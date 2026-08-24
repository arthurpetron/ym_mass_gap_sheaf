/-
# Physical-time sampling of the dynamic BF4 same-object RC channel

The dynamic same-object channel already retains one actual completed
vacuum-complement vector, transfer, norm, and connected autocorrelation at
every cutoff scale.  This file applies the canonical floor sampling
`n_j(t) = floor(t/a_j)` supplied by spacing-to-zero and proves that the sampled
moment remains the same global adaptive-transfer matrix coefficient with the
same completed decay rate.

The remaining cutoff-removal input is stated in the correct completed-real
currency.  `ScheduledRCContinuumLimit` carries explicit `CReal`
representatives of the sampled `RC` classes, their continuum representatives,
and convergence moduli.  This is data, not a hidden choice of quotient
representatives.  A separate `DynamicVacuumSectorUniformRCNormFloor` records
the genuinely additional scale-uniform nontriviality estimate.  Together they
prove strict positivity of the continuum zero-time channel.

No scheduled RC continuum limit, uniform norm floor, dynamic completed
family, physical rate band, projective measure, OS reconstruction, continuum
Yang--Mills theory, or Clay conclusion is inhabited here.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. Canonical physical-time sampling -/

/-- The spacing-to-zero data already carried by the dynamic family constructs
the canonical floor sampling; it is not an additional analytic input. -/
def centralPhysicalDynamicRCSampling
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) :
    PhysicalSeparationSampling family.transferSpacing :=
  physicalSeparationSamplingOfSpacingToZero
    family.transferSpacing family.transferSpacingToZero

/-- The exact lattice power used at one cutoff scale and integer physical
time. -/
def centralPhysicalDynamicRCLatticeSteps
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale time : Nat) : Nat :=
  (centralPhysicalDynamicRCSampling family).latticeSteps scale time

/-- The sampled physical distance converges constructively to the requested
integer time. -/
theorem centralPhysicalDynamicRCSampledDistance_converges
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (family.transferSpacing.spacing scale *
          Q'.ofNat
            (centralPhysicalDynamicRCLatticeSteps family scale time)))
      (CReal.ofQ' (Q'.ofNat time)) :=
  (centralPhysicalDynamicRCSampling family).distanceConverges time

/-! ## 2. The same moment under scheduled powers -/

/-- The literal connected autocorrelation sampled at fixed physical time. -/
def sampledConnectedAutocorrelation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) : CReal.RC :=
  channel.connectedAutocorrelation scale
    (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- The squared sampled connected autocorrelation. -/
def sampledConnectedAutocorrelationSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) : CReal.RC :=
  channel.connectedAutocorrelationSq scale
    (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- Scheduled sampling preserves the completed decay theorem with the exact
lattice power selected for the requested physical time. -/
theorem sampledConnectedAutocorrelationSq_decay
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) :
    CReal.RCle
      (sampledConnectedAutocorrelationSq channel scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^
            (centralPhysicalDynamicRCLatticeSteps family scale time))
          (channel.normSq scale))
        (channel.normSq scale)) :=
  channel.connectedAutocorrelationSq_decay scale
    (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- Scheduled sampling preserves the exact identification with the global
adaptive-transfer matrix coefficient of the same embedded vector. -/
theorem sampledConnectedAutocorrelation_eq_global
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) :
    sampledConnectedAutocorrelation channel scale time =
      centralPhysicalCutoffCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (family.nome_pos scale) (family.nome_lt_one scale) half
          (centralPhysicalDynamicRCLatticeSteps family scale time)
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (channel.vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (channel.vectorAt scale).1) :=
  channel.connectedAutocorrelation_eq_global scale
    (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- Floor sampling at physical time zero uses zero transfer steps, so the
sampled channel is exactly the same completed norm square. -/
theorem sampledConnectedAutocorrelation_zero_eq_normSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    sampledConnectedAutocorrelation channel scale 0 =
      channel.normSq scale := by
  simpa [sampledConnectedAutocorrelation,
    centralPhysicalDynamicRCLatticeSteps,
    centralPhysicalDynamicRCSampling,
    physicalSeparationSamplingOfSpacingToZero, floorLatticeSteps] using
      (channel.connectedAutocorrelation_zero_eq_normSq scale)

/-- At every finite cutoff, the scheduled zero-time channel retains the
channel's explicit positive rational witness. -/
theorem sampledConnectedAutocorrelation_zero_isPositive
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    RCIsPositive (sampledConnectedAutocorrelation channel scale 0) := by
  rw [sampledConnectedAutocorrelation_zero_eq_normSq]
  exact channel.connectedAutocorrelation_zero_isPositive scale

/-! ## 3. Honest cutoff-removal data and continuum nontriviality -/

/-- A scale-uniform positive lower floor for the norm of the definitionally
same dynamic channel.  Per-scale positivity alone does not inhabit this
structure: the floor may otherwise vanish along the cutoff trajectory. -/
structure DynamicVacuumSectorUniformRCNormFloor
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_le : forall scale,
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' floor))
      (channel.normSq scale)

/-- Explicit representative-level cutoff removal for the scheduled `RC`
channel.  `represents` prevents an unrelated CReal sequence from serving as
the limit source; `converges` carries the constructive modulus. -/
structure ScheduledRCContinuumLimit
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family) : Type 1 where
  representative : Nat -> Nat -> CReal
  represents : forall time scale,
    Quotient.mk CReal.crealSetoid (representative time scale) =
      sampledConnectedAutocorrelation channel scale time
  limitRepresentative : Nat -> CReal
  converges : forall time,
    CReal.ConvergesTo (fun scale => representative time scale)
      (limitRepresentative time)

namespace ScheduledRCContinuumLimit

/-- The continuum same-object correlation selected by the explicit
representative limit. -/
def continuumConnectedAutocorrelation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {channel : DynamicVacuumSectorSameObjectRCChannel family}
    (limit : ScheduledRCContinuumLimit channel)
    (time : Nat) : CReal.RC :=
  Quotient.mk CReal.crealSetoid (limit.limitRepresentative time)

/-- A uniform norm floor passes through the explicit same-channel cutoff
limit and makes the continuum zero-time autocorrelation strictly positive. -/
theorem continuumConnectedAutocorrelation_zero_isPositive
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {channel : DynamicVacuumSectorSameObjectRCChannel family}
    (limit : ScheduledRCContinuumLimit channel)
    (uniform : DynamicVacuumSectorUniformRCNormFloor channel) :
    RCIsPositive (limit.continuumConnectedAutocorrelation 0) := by
  have hterm : forall scale,
      CReal.leEv (CReal.ofQ' uniform.floor)
        (limit.representative 0 scale) := by
    intro scale
    have hrc : CReal.RCle
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' uniform.floor))
        (Quotient.mk CReal.crealSetoid
          (limit.representative 0 scale)) := by
      rw [limit.represents 0 scale,
        sampledConnectedAutocorrelation_zero_eq_normSq]
      exact uniform.floor_le scale
    exact hrc
  have hlimit : CReal.leEv
      (CReal.ofQ' uniform.floor) (limit.limitRepresentative 0) := by
    apply CReal.leEv_of_convergesTo_le
      (CReal.convergesTo_const (CReal.ofQ' uniform.floor))
      (limit.converges 0)
    exact hterm
  exact ⟨uniform.floor, uniform.floor_pos, hlimit⟩

end ScheduledRCContinuumLimit

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel.centralPhysicalDynamicRCSampledDistance_converges
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel.sampledConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel.sampledConnectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel.sampledConnectedAutocorrelation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel.ScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
