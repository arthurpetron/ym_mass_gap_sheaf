/-
# Canonical full-density certificate and explicit power debt

The finite physical construction already provides a canonical one-step
density on the positive carrier.  This file packages its exact state-level
row and column laws, and records the remaining multi-slab identity as a
separate Type-level debt.  The latter is the statement needed by the
full-factorization adapter; it is not inferred from one-slab normalization.

No factorization, cofinal family, thermodynamic limit, or continuum claim is
constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
import YMGap.Continuum.BF4StationaryDensityBufferSplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical one-step state kernel -/

/-- The canonical state-level one-step density is the exact conditional
density already defined from the reflected physical joint. -/
def canonicalFullDensityOneStepState
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    EdgeLabelling → EdgeLabelling → Q' :=
  centralPhysicalConditionalDensity w hw cutoff half

/-- Exact weighted row normalization on the complete positive physical
carrier. -/
theorem canonicalFullDensityOneStepState_row
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half) :
    listQSum
        (fun target =>
          centralPhysicalRowMarginal w hw cutoff half target *
            canonicalFullDensityOneStepState w hw cutoff half source target)
        (centralPositiveHalfStates w hw cutoff half) ≈ 1 :=
  centralPhysicalConditionalDensity_row_normalized hsource

/-- Exact weighted column normalization on the complete positive physical
carrier. -/
theorem canonicalFullDensityOneStepState_column
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {target : EdgeLabelling}
    (htarget : target ∈ centralPositiveHalfStates w hw cutoff half) :
    listQSum
        (fun source =>
          centralPhysicalRowMarginal w hw cutoff half source *
            canonicalFullDensityOneStepState w hw cutoff half source target)
        (centralPositiveHalfStates w hw cutoff half) ≈ 1 :=
  centralPhysicalConditionalDensity_column_normalized htarget

/-- The canonical density reconstructs the normalized reflected joint on
positive endpoints. -/
theorem canonicalFullDensityOneStepState_reconstructs_joint
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source target : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half)
    (htarget : target ∈ centralPositiveHalfStates w hw cutoff half) :
    centralNormalizedPhysicalReflectedKernel
        w hw cutoff half source target ≈
      (centralPhysicalRowMarginal w hw cutoff half source *
        centralPhysicalRowMarginal w hw cutoff half target) *
          canonicalFullDensityOneStepState
            w hw cutoff half source target :=
  normalizedJoint_eq_marginals_mul_density hsource htarget

/-! ## 2. The remaining constructive debt -/

/-- The exact multi-slab power identity still required to turn the canonical
one-step density into the adapter's full factorization.  This is a
Type-level certificate: an inhabitant must supply the actual identity for the
same physical carrier, not merely a normalization law. -/
structure CanonicalFullDensityPowerDebt
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half depth : Nat) : Type 1 where
  depth_at_least_three : 3 ≤ depth
  full_density_power : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    centralPhysicalFiniteFullDensity w hw cutoff half source target ≈
      finiteWeightedDensityPower
        (centralPhysicalFiniteIndexCarrier w hw cutoff half)
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteFullDensity w hw cutoff half)
        (depth - 1) source target

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_row
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_column
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_reconstructs_joint
