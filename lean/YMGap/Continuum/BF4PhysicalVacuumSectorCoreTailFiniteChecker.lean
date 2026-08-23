/-
# Executable core/tail checker on the conditioned BF4 vacuum sector

The full-carrier physical core/tail checker cannot provide a uniform gap:
the full positive carrier is already reducible at cutoff two.  This file
specializes the same exact rational checker to the canonical communicating
component and its conditioned probability weight and density.

A true row check gives

    sum_y |J(x,y) - pi(x)pi(y)/pi(S)| <= (1/16) pi(x).

A true all-row check packages the corrected finite row certificate.  A
constructively cofinal family of such checks compiles to the existing
same-object centered cutoff-limit gap at rate `1/16`.

No nontrivial cofinal checked family is asserted.  No thermodynamic or
continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
import YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One exact sector-conditioned core/tail check -/

/-- Run the generic exact core/tail checker on one canonical vacuum-sector
row with the component-conditioned probability weight and density. -/
def centralPhysicalFiniteVacuumSectorCoreTailRowCheck
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat)
    (inCore : Nat → Bool) : Bool :=
  finiteWeightedDensityCoreTailCheck
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
      w hw cutoff half)
    source inCore
    (Q'.mkPos 1 32 (by decide))
    (Q'.mkPos 1 64 (by decide))

/-- Soundness of one exact sector-conditioned core/tail row check. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_rowCheck
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    {inCore : Nat → Bool}
    (source_mem : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (checked :
      centralPhysicalFiniteVacuumSectorCoreTailRowCheck
        w hw cutoff half source inCore = true) :
    finiteJointDifferenceAbsRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half)
        (finiteCarrierMassNormalizedStationaryProductJoint
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half))
        source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorCoreTailRowCheck at checked
  have window := finiteWeightedDensityCoreTailWindow_of_check checked
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedWeight
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity at window
  exact finiteCarrierMassNormalizedRowDistance_le_sixteenth_of_coreTail
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex source_mem)
    (fun target htarget =>
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
    window

/-! ## 2. All-row exact scan and finite certificate -/

/-- Scan only the canonical vacuum component, with a source-dependent core. -/
def centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (inCore : Nat → Nat → Bool) : Bool :=
  (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).all
    (fun source =>
      centralPhysicalFiniteVacuumSectorCoreTailRowCheck
        w hw cutoff half source (inCore source))

/-- A true sector-only all-row core/tail scan proves every corrected row
estimate at rate `1/16`. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {inCore : Nat → Nat → Bool}
    (checked :
      centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck
        w hw cutoff half inCore = true)
    (source : Nat)
    (source_mem : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteJointDifferenceAbsRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half)
        (finiteCarrierMassNormalizedStationaryProductJoint
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half))
        source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck at checked
  have hrow := List.all_eq_true.mp checked source source_mem
  exact
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_rowCheck
      source_mem hrow

/-- One true sector-conditioned core/tail scan packages the corrected finite
row-distance certificate at rate `1/16`. -/
def centralPhysicalFiniteVacuumSectorCoreTailCertificate_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {inCore : Nat → Nat → Bool}
    (checked :
      centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck
        w hw cutoff half inCore = true) :
    FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (Q'.mkPos 1 16 (by decide))
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half)
      (centralPhysicalFiniteKernel w hw cutoff half) where
  kernelSymmetric := by
    intro left right hleft hright
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw cutoff half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw cutoff half hleft))).1
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw cutoff half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw cutoff half hright))).1
  rowDistance :=
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_allRowsCheck
      checked

/-! ## 3. Cofinal core/tail compiler -/

/-- The corrected local analytic frontier: one exact sector-conditioned
core/tail scan succeeds at every constructively selected cofinal cutoff. -/
structure FixedNomeCofinalVacuumSectorCoreTailCheckedRows
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type where
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  inCore : Nat → Nat → Nat → Nat → Bool
  allRows_checked : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck
      w hw (anchor base threshold) half (inCore base threshold) = true

namespace FixedNomeCofinalVacuumSectorCoreTailCheckedRows

/-- Compile the cofinal sector-conditioned core/tail checks to the corrected
mass-normalized row-distance frontier at the fixed strict rate `1/16`. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (checked :
      FixedNomeCofinalVacuumSectorCoreTailCheckedRows w hw half) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half (Q'.mkPos 1 16 (by decide)) where
  rate_nonnegative := by decide
  rate_lt_one := by decide
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  rowDistance := by
    intro base threshold source source_mem
    exact
      centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_allRowsCheck
        (checked.allRows_checked base threshold) source source_mem

/-- Compile the local exact checks all the way to the existing same-object
centered cutoff-limit gap at rate `1/16`. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (checked :
      FixedNomeCofinalVacuumSectorCoreTailCheckedRows w hw half) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (Q'.mkPos 1 16 (by decide)) :=
  checked.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorCoreTailCheckedRows

end YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker.centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_rowCheck
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker.centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_sixteenth_of_allRowsCheck
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker.centralPhysicalFiniteVacuumSectorCoreTailCertificate_of_allRowsCheck
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker.FixedNomeCofinalVacuumSectorCoreTailCheckedRows.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCoreTailFiniteChecker.FixedNomeCofinalVacuumSectorCoreTailCheckedRows.toVacuumSectorCenteredStrictGap
