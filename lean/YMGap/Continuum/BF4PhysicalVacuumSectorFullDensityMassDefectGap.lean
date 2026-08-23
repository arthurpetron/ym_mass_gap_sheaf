/-
# Full-density mixing plus vacuum-mass concentration implies the BF4 gap

The exact component-density identity gives a causal two-budget route to the
correct vacuum-sector row estimate.  At each selected cutoff it is enough to
prove, for every canonical vacuum-sector source,

    restricted full-density row error <= 1/32

and, independently,

    |mass(vacuum sector) - 1| <= 1/32.

Their sum bounds the component-conditioned density row by `1/16`, which this
file compiles through the corrected mass-normalized row comparison and the
existing same-object cutoff limit to the completed vacuum-sector strict gap.

Neither budget is inhabited here.  In particular, this file does not assert
that the canonical vacuum component asymptotically carries all stationary
mass.  Sector-local normalized mixing remains the alternative route that
does not require that concentration statement.

No thermodynamic or continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect

namespace YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two explicit finite-cutoff budgets -/

/-- The full physical density error, but integrated only over targets in the
canonical vacuum component and with the original unconditioned stationary
weights. -/
def centralPhysicalFiniteVacuumSectorRestrictedFullDensityCenteredRowMass
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  listQSum
    (fun target =>
      centralPhysicalFiniteWeight w hw cutoff half target *
        Q'.abs
          (finiteCenteredDensity
            (fun left right =>
              centralPhysicalConditionalDensity w hw cutoff half
                (centralPhysicalFiniteStateAt w hw cutoff half left)
                (centralPhysicalFiniteStateAt w hw cutoff half right))
            source target))
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

/-- The weighted-row mass-defect theorem in compact physical notation. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect'
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half)
        source ≤
      centralPhysicalFiniteVacuumSectorRestrictedFullDensityCenteredRowMass
          w hw cutoff half source +
        Q'.abs
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half + (-1)) := by
  unfold centralPhysicalFiniteVacuumSectorRestrictedFullDensityCenteredRowMass
  exact
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
      hsource

/-- A constructively cofinal family of the two sufficient `1/32` budgets.
The source-row budget is sector-restricted; the mass budget is one scalar per
selected cutoff. -/
structure FixedNomeCofinalVacuumSectorFullDensityMassDefect
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  restrictedFullDensity_le_thirtySecond : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      centralPhysicalFiniteVacuumSectorRestrictedFullDensityCenteredRowMass
          w hw (anchor base threshold) half source ≤
        Q'.mkPos 1 32 (by decide)
  massDefect_le_thirtySecond : ∀ base threshold,
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMass
          w hw (anchor base threshold) half + (-1)) ≤
      Q'.mkPos 1 32 (by decide)

namespace FixedNomeCofinalVacuumSectorFullDensityMassDefect

/-! ## 2. Contraction into the corrected row and completed-gap interfaces -/

/-- The two explicit `1/32` budgets give the conditioned weighted density row
bound `1/16`. -/
theorem conditionedDensityCenteredRow_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (data : FixedNomeCofinalVacuumSectorFullDensityMassDefect w hw half)
    (base threshold source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w hw (data.anchor base threshold) half) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices
          w hw (data.anchor base threshold) half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw (data.anchor base threshold) half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw (data.anchor base threshold) half)
        source ≤
      Q'.mkPos 1 16 (by decide) := by
  have hsplit :=
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect'
      hsource
  have hbudgets := Q'.add_le_add
    (data.restrictedFullDensity_le_thirtySecond
      base threshold source hsource)
    (data.massDefect_le_thirtySecond base threshold)
  exact Q'.le_trans' _ _ _ hsplit
    (Q'.le_trans' _ _ _ hbudgets (Q'.le_of_eqv (by decide)))

/-- Compile the two-budget density estimate to the correctly normalized
finite joint-row comparison at rate `1/16`. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (data : FixedNomeCofinalVacuumSectorFullDensityMassDefect w hw half) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half (Q'.mkPos 1 16 (by decide)) where
  rate_nonnegative := by decide
  rate_lt_one := by decide
  anchor := data.anchor
  anchor_ge := data.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    let cutoff := data.anchor base threshold
    have hsourcePos : (0 : Q') <
        centralPhysicalFiniteWeight w hw cutoff half source :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hdensity :=
      data.conditionedDensityCenteredRow_le_sixteenth
        base threshold source hsource
    have hidentity :=
      finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        (states := centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half)
        (mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
        (mass_pos := centralPhysicalFiniteVacuumSectorWeightSum_pos
          w hw cutoff half)
        (weight := centralPhysicalFiniteWeight w hw cutoff half)
        (joint := centralPhysicalFiniteKernel w hw cutoff half)
        hsourcePos
        (fun target htarget =>
          centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdensity
      (Q'.le_of_lt hsourcePos)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity) ?_
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralPhysicalFiniteWeight w hw cutoff half source)
        (Q'.mkPos 1 16 (by decide)))

/-- Compile the two-budget route all the way to the existing moving
same-object completed vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (data : FixedNomeCofinalVacuumSectorFullDensityMassDefect w hw half) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (Q'.mkPos 1 16 (by decide)) :=
  data.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorFullDensityMassDefect

end YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap.centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect'
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap.FixedNomeCofinalVacuumSectorFullDensityMassDefect.conditionedDensityCenteredRow_le_sixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap.FixedNomeCofinalVacuumSectorFullDensityMassDefect.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorFullDensityMassDefectGap.FixedNomeCofinalVacuumSectorFullDensityMassDefect.toVacuumSectorCenteredStrictGap
