/-
# Executable mass-normalized row checker on the BF4 vacuum sector

The full positive physical carrier is reducible, and the canonical vacuum
component generally has stationary mass below one.  This file therefore
checks the exact component-conditioned row estimate

    sum_y |J(x,y) - pi(x) pi(y) / pi(S)| <= q pi(x)

only on the canonical vacuum sector `S`.  The Boolean checker uses exact
`Q'` arithmetic.  Its soundness theorem feeds the corrected cofinal
mass-normalized row interface and hence the existing same-object cutoff-limit
gap.

No cofinal all-cutoff check is claimed here.  The previously checked
cutoff-zero full-carrier base case remains available separately; this module
does not force the graph-defined sector enumeration to reduce during every
focused audit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic exact row check -/

/-- Executably check one component-conditioned stationary-product row. -/
def finiteCarrierMassNormalizedStationaryProductRowDistanceCheck
    {State : Type} (states : List State)
    (mass rate : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (joint : State → State → Q')
    (source : State) : Bool :=
  decide
    (finiteJointDifferenceAbsRowMass states joint
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) source ≤
      rate * weight source)

/-- Soundness of the generic exact row check. -/
theorem finiteCarrierMassNormalizedStationaryProductRowDistance_of_check
    {State : Type} {states : List State}
    {mass rate : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source : State}
    (checked :
      finiteCarrierMassNormalizedStationaryProductRowDistanceCheck
        states mass rate mass_pos weight joint source = true) :
    finiteJointDifferenceAbsRowMass states joint
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) source ≤
      rate * weight source := by
  unfold finiteCarrierMassNormalizedStationaryProductRowDistanceCheck
    at checked
  simpa only [decide_eq_true_eq] using checked

/-! ## 2. Canonical vacuum-sector specialization -/

/-- Check one finite BF4 vacuum-sector row against its correctly normalized
component equilibrium joint. -/
def centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (rate : Q') (source : Nat) : Bool :=
  finiteCarrierMassNormalizedStationaryProductRowDistanceCheck
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    rate
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    source

/-- Scan exactly the canonical vacuum component at one cutoff.  Neither
sources nor targets outside that communicating component are inspected. -/
def centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (rate : Q') : Bool :=
  (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).all
    (centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck
      w hw cutoff half rate)

/-- A true sector-only scan proves every corrected row estimate at that
cutoff. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {rate : Q'}
    (checked :
      centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
        w hw cutoff half rate = true)
    (source : Nat)
    (source_mem :
      source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw cutoff half) :
    finiteJointDifferenceAbsRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half)
        (finiteCarrierMassNormalizedStationaryProductJoint
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half))
        source ≤
      rate * centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
    at checked
  have hrow := List.all_eq_true.mp checked source source_mem
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck at hrow
  exact
    finiteCarrierMassNormalizedStationaryProductRowDistance_of_check hrow

/-- One true sector scan packages the generic finite corrected row
certificate, including the production-kernel symmetry proof. -/
def centralPhysicalFiniteVacuumSectorMassNormalizedCertificate_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {rate : Q'}
    (checked :
      centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
        w hw cutoff half rate = true) :
    FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      rate
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
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_of_allRowsCheck
      checked

/-! ## 3. Cofinal checked family and compiler -/

/-- The remaining uniform finite-computation target in its corrected
sector-only form: one constructively cofinal exact scan succeeds at a single
strict rate independent of the base and threshold. -/
structure FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  allRows_checked : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
      w hw (anchor base threshold) half rate = true

namespace FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows

/-- Compile cofinal exact sector scans to the corrected analytic row
certificate. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (checked :
      FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows
        w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate where
  rate_nonnegative := checked.rate_nonnegative
  rate_lt_one := checked.rate_lt_one
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  rowDistance := by
    intro base threshold source source_mem
    exact
      centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_of_allRowsCheck
        (checked.allRows_checked base threshold) source source_mem

/-- Compile the exact cofinal scans all the way to the existing centered
same-object gap certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (checked :
      FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  checked.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.finiteCarrierMassNormalizedStationaryProductRowDistance_of_check
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_of_allRowsCheck
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.centralPhysicalFiniteVacuumSectorMassNormalizedCertificate_of_allRowsCheck
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toVacuumSectorCenteredStrictGap
