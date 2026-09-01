/-
# The exact full-row enhancement for the growing closed-surface grid

The selected-term grid estimate retains only one positive summand and hence
inherits the sixth power of the replica coefficient.  This module divides the
literal grid raw row by that selected face activity and names the quotient the
`full-row enhancement`.  The quotient is positive, at least one, and cancels
back to the literal raw row exactly.

Combining this identity with the existing spin-cube raw-row ceiling gives a
strictly sharper pointwise floor: the old replica coefficient is multiplied by
the full-row enhancement.  Thus the remaining finite-cutoff asymptotic burden
is stated without discarded row mass: one must show that the enhancement
compensates the coefficient decay uniformly over the growing grid.  No such
compensation estimate, effective-multiplicity divergence, continuum limit, or
Clay conclusion is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor

namespace YMGap.Continuum.BF4GrowingGridFullRowEnhancement

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
open YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qpow_pos_local {value : Q'} (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

/-! ## 1. The literal activity and its full-row quotient -/

/-- Exact two-surface face activity used as the positive denominator of the
full-row enhancement. -/
def gridReplicaActivity (firstSpin replica : Nat) : Q' :=
  (coeffW anchorCoupling firstSpin) ^ 6 *
    (coeffW anchorCoupling replica) ^ 6

theorem gridReplicaActivity_pos (firstSpin replica : Nat) :
    (0 : Q') < gridReplicaActivity firstSpin replica := by
  unfold gridReplicaActivity
  exact Q'.mul_pos
    (qpow_pos_local (coeffW_pos (by decide) firstSpin) 6)
    (qpow_pos_local (coeffW_pos (by decide) replica) 6)

/-- The entire literal positive-carrier grid row, measured in units of the
selected two-surface face activity. -/
def gridReplicaFullRowEnhancement
    (cutoff firstSpin replica : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalPositiveRawRowMass
      anchorCoupling (by decide) cutoff 0
      (centralGridRowState firstSpin replica))
    (gridReplicaActivity firstSpin replica)
    (gridReplicaActivity_pos firstSpin replica)

theorem gridReplicaFullRowEnhancement_pos
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    (0 : Q') <
      gridReplicaFullRowEnhancement cutoff firstSpin replica := by
  unfold gridReplicaFullRowEnhancement
  apply Q'.divPos_pos
  exact centralPhysicalPositiveRawRowMass_pos
    (centralGridRowState_mem_centralPositiveHalfStates
      (by decide) hfirstSpin hreplica)

/-- The enhancement is at least one because the selected activity is a
literal positive summand of the full row. -/
theorem one_le_gridReplicaFullRowEnhancement
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    (1 : Q') ≤
      gridReplicaFullRowEnhancement cutoff firstSpin replica := by
  unfold gridReplicaFullRowEnhancement
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.one_mul_eqv
      (gridReplicaActivity firstSpin replica)))
    (by
      unfold gridReplicaActivity
      exact centralGridActivity_le_rawRowMass
        (by decide) hfirstSpin hreplica)

/-- Exact cancellation: activity times enhancement recovers the entire raw
grid row, rather than merely its selected summand. -/
theorem gridReplicaActivity_mul_fullRowEnhancement_eqv_rawRow
    (cutoff firstSpin replica : Nat) :
    gridReplicaActivity firstSpin replica *
        gridReplicaFullRowEnhancement cutoff firstSpin replica ≈
      centralPhysicalPositiveRawRowMass
        anchorCoupling (by decide) cutoff 0
        (centralGridRowState firstSpin replica) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (gridReplicaActivity firstSpin replica)
      (gridReplicaFullRowEnhancement cutoff firstSpin replica)) ?_
  unfold gridReplicaFullRowEnhancement
  exact Q'.divPos_mul_eqv _ _ _

/-! ## 2. The compensated pointwise row floor -/

/-- The replica activity after restoring all raw-row mass discarded by the
selected-summand estimate. -/
def gridReplicaCompensatedActivity
    (cutoff firstSpin replica : Nat) : Q' :=
  (coeffW anchorCoupling replica) ^ 6 *
    gridReplicaFullRowEnhancement cutoff firstSpin replica

theorem gridReplicaCompensatedActivity_pos
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    (0 : Q') <
      gridReplicaCompensatedActivity cutoff firstSpin replica := by
  unfold gridReplicaCompensatedActivity
  exact Q'.mul_pos
    (qpow_pos_local (coeffW_pos (by decide) replica) 6)
    (gridReplicaFullRowEnhancement_pos hfirstSpin hreplica)

/-- The full-row pointwise floor obtained by dividing the compensated
replica activity by the existing uniform residual-carrier ceiling. -/
def gridReplicaFullRowFloor
    (cutoff firstSpin replica : Nat) : Q' :=
  Q'.divPos
    (gridReplicaCompensatedActivity cutoff firstSpin replica)
    centralSpinCubeResidualCarrierCeiling
    centralSpinCubeResidualCarrierCeiling_pos

theorem gridReplicaFullRowFloor_pos
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    (0 : Q') < gridReplicaFullRowFloor cutoff firstSpin replica := by
  unfold gridReplicaFullRowFloor
  exact Q'.divPos_pos _ _ centralSpinCubeResidualCarrierCeiling_pos
    (gridReplicaCompensatedActivity_pos hfirstSpin hreplica)

/-- Restoring the discarded full-row mass can only improve the old selected
pointwise floor. -/
theorem gridReplicaSelectedFloor_le_fullRowFloor
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    gridReplicaSelectedFloor replica ≤
      gridReplicaFullRowFloor cutoff firstSpin replica := by
  unfold gridReplicaSelectedFloor gridReplicaFullRowFloor
  apply Q'.le_divPos_of_mul_le
  let replicaActivity := (coeffW anchorCoupling replica) ^ 6
  let enhancement :=
    gridReplicaFullRowEnhancement cutoff firstSpin replica
  have hactivity0 : (0 : Q') ≤ replicaActivity :=
    Q'.pow_nonneg _ (coeffW_nonneg (by decide) replica) 6
  have hone := one_le_gridReplicaFullRowEnhancement hfirstSpin hreplica
  have hscaled : replicaActivity * 1 ≤ replicaActivity * enhancement :=
    Q'.mul_le_mul_of_nonneg_left 1 enhancement replicaActivity
      hone hactivity0
  have hbase : replicaActivity ≤ replicaActivity * enhancement :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv replicaActivity)) hscaled
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.divPos_mul_eqv replicaActivity
        centralSpinCubeResidualCarrierCeiling
        centralSpinCubeResidualCarrierCeiling_pos))
    hbase

/-- **Full-row comparison.**  The source spin-cube row times the compensated
floor is bounded by the complete grid row.  This is the selected-term proof
with the enhancement retained all the way to its exact cancellation. -/
theorem centralSpinCubeRawRow_mul_gridReplicaFullRowFloor_le_gridRawRow
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    centralPhysicalPositiveRawRowMass
          anchorCoupling (by decide) cutoff 0
          (centralLowerSpinCubeState firstSpin) *
        gridReplicaFullRowFloor cutoff firstSpin replica ≤
      centralPhysicalPositiveRawRowMass
          anchorCoupling (by decide) cutoff 0
          (centralGridRowState firstSpin replica) := by
  let firstActivity := (coeffW anchorCoupling firstSpin) ^ 6
  let replicaActivity := (coeffW anchorCoupling replica) ^ 6
  let enhancement :=
    gridReplicaFullRowEnhancement cutoff firstSpin replica
  let ceiling := centralSpinCubeResidualCarrierCeiling
  have hsource :=
    centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling hfirstSpin
  have hfloor0 :
      (0 : Q') ≤ gridReplicaFullRowFloor cutoff firstSpin replica :=
    Q'.le_of_lt (gridReplicaFullRowFloor_pos hfirstSpin hreplica)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hsource hfloor0
  have hcancelCeiling :
      (firstActivity * ceiling) *
          gridReplicaFullRowFloor cutoff firstSpin replica ≈
        firstActivity * (replicaActivity * enhancement) := by
    unfold gridReplicaFullRowFloor gridReplicaCompensatedActivity
    refine Q'.eqv_trans _
      (firstActivity *
        (centralSpinCubeResidualCarrierCeiling *
          Q'.divPos
            ((coeffW anchorCoupling replica) ^ 6 *
              gridReplicaFullRowEnhancement cutoff firstSpin replica)
            centralSpinCubeResidualCarrierCeiling
            centralSpinCubeResidualCarrierCeiling_pos)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (firstActivity *
        (Q'.divPos
            ((coeffW anchorCoupling replica) ^ 6 *
              gridReplicaFullRowEnhancement cutoff firstSpin replica)
            centralSpinCubeResidualCarrierCeiling
            centralSpinCubeResidualCarrierCeiling_pos *
          centralSpinCubeResidualCarrierCeiling)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.divPos_mul_eqv _ _ centralSpinCubeResidualCarrierCeiling_pos)
  have hrestore :
      firstActivity * (replicaActivity * enhancement) ≈
        centralPhysicalPositiveRawRowMass
          anchorCoupling (by decide) cutoff 0
          (centralGridRowState firstSpin replica) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv firstActivity replicaActivity enhancement)) ?_
    unfold firstActivity replicaActivity enhancement
    simpa only [gridReplicaActivity] using
      (gridReplicaActivity_mul_fullRowEnhancement_eqv_rawRow
        cutoff firstSpin replica)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hcancelCeiling hrestore))

/-! ## 3. A concrete finite common floor retaining the full rows -/

/-- The admitted source-offset/replica pairs at cutoff `K`. -/
def growingGridFullRowPairs (cutoff : Nat) : List (Nat × Nat) :=
  cartesian (List.range cutoff) (List.range (cutoff + 1))

/-- The positive minimum of the compensated pointwise floors over the entire
growing grid.  The unit fallback also caps the result by one. -/
def growingGridFullRowCommonFloor (cutoff : Nat) : Q' :=
  listPositiveMinOne
    (fun pair =>
      gridReplicaFullRowFloor cutoff (pair.1 + 1) pair.2)
    (growingGridFullRowPairs cutoff)

private theorem listPositiveMinOne_le_one_local
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listPositiveMinOne value states ≤ 1
  | [] => Q'.le_refl' 1
  | _first :: rest =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

private theorem le_listPositiveMinOne_of_forall_local
    {State : Type} (value : State → Q') (candidate : Q') :
    ∀ states : List State,
      candidate ≤ 1 →
      (∀ state, state ∈ states → candidate ≤ value state) →
      candidate ≤ listPositiveMinOne value states
  | [], hunit, _hall => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact le_listPositiveMinOne_of_forall_local
          value candidate rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

theorem growingGridFullRowCommonFloor_pos (cutoff : Nat) :
    (0 : Q') < growingGridFullRowCommonFloor cutoff := by
  unfold growingGridFullRowCommonFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  have hparts := (mem_cartesian_iff
    (List.range cutoff) (List.range (cutoff + 1)) pair).mp hpair
  exact gridReplicaFullRowFloor_pos
    (by have := List.mem_range.mp hparts.1; omega)
    (by have := List.mem_range.mp hparts.2; omega)

theorem growingGridFullRowCommonFloor_le_one (cutoff : Nat) :
    growingGridFullRowCommonFloor cutoff ≤ 1 := by
  unfold growingGridFullRowCommonFloor
  exact listPositiveMinOne_le_one_local _ _

/-- Every admitted pointwise compensated floor lies above the concrete common
minimum. -/
theorem growingGridFullRowCommonFloor_le_pointwise
    {cutoff offset replica : Nat}
    (hoffset : offset < cutoff) (hreplica : replica < cutoff + 1) :
    growingGridFullRowCommonFloor cutoff ≤
      gridReplicaFullRowFloor cutoff (offset + 1) replica := by
  have hmem : (offset, replica) ∈ growingGridFullRowPairs cutoff := by
    unfold growingGridFullRowPairs
    exact (mem_cartesian_iff
      (List.range cutoff) (List.range (cutoff + 1))
      (offset, replica)).mpr
        ⟨List.mem_range.mpr hoffset, List.mem_range.mpr hreplica⟩
  unfold growingGridFullRowCommonFloor
  exact listPositiveMinOne_le_of_mem
    (fun pair : Nat × Nat =>
      gridReplicaFullRowFloor cutoff (pair.1 + 1) pair.2)
    (growingGridFullRowPairs cutoff) (offset, replica) hmem

/-- The full-row common floor dominates the selected-summand common floor.
Thus it is a genuinely sharper analytic witness, even though divergence still
requires a new compensation estimate. -/
theorem growingGridSelectedCommonFloor_le_fullRowCommonFloor
    (cutoff : Nat) :
    growingGridSelectedCommonFloor cutoff ≤
      growingGridFullRowCommonFloor cutoff := by
  unfold growingGridFullRowCommonFloor
  apply le_listPositiveMinOne_of_forall_local
  · exact growingGridSelectedCommonFloor_le_one cutoff
  · intro pair hpair
    have hparts := (mem_cartesian_iff
      (List.range cutoff) (List.range (cutoff + 1)) pair).mp hpair
    have hoffset : pair.1 < cutoff := List.mem_range.mp hparts.1
    have hreplica : pair.2 < cutoff + 1 := List.mem_range.mp hparts.2
    have hselectedReplica :
        growingGridSelectedCommonFloor cutoff ≤
          gridReplicaSelectedFloor pair.2 :=
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (gridReplicaSelectedFloor_antitone (by omega))
    exact Q'.le_trans' _ _ _ hselectedReplica
      (gridReplicaSelectedFloor_le_fullRowFloor
        (by omega) (by omega))

/-- The full-row finite minimum compiles directly into the already computed
raw-row ratio floor. -/
theorem growingGridFullRowCommonFloor_le_computedFloor (cutoff : Nat) :
    growingGridFullRowCommonFloor cutoff ≤
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) cutoff).rawRowRatioFloor := by
  apply growingGrid_lower_le_rawRowRatioFloor_of_scaledRawRow_le
  · exact growingGridFullRowCommonFloor_le_one cutoff
  · intro offset replica hoffset hreplica
    have hsource0 := centralPhysicalPositiveRawRowMass_nonnegative
      (by decide : (0 : Q') ≤ anchorCoupling) cutoff 0
      (centralLowerSpinCubeState (offset + 1))
    have hcommon := growingGridFullRowCommonFloor_le_pointwise
      hoffset hreplica
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hcommon hsource0
    exact Q'.le_trans' _ _ _ hscaled
      (centralSpinCubeRawRow_mul_gridReplicaFullRowFloor_le_gridRawRow
        (by omega) (by omega))

/-- The exact growing factor therefore multiplies the sharper full-row common
floor below the computed effective multiplicity. -/
theorem growingGrid_fullRowEffectiveMultiplicityLowerBound (cutoff : Nat) :
    Q'.ofNat (cutoff + 1) * growingGridFullRowCommonFloor cutoff ≤
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) cutoff).toWeighted.effectiveMultiplicity := by
  change Q'.ofNat (cutoff + 1) * growingGridFullRowCommonFloor cutoff ≤
    Q'.ofNat (cutoff + 1) *
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) cutoff).rawRowRatioFloor
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (growingGridFullRowCommonFloor_le_computedFloor cutoff)
    (zero_le_ofNat (cutoff + 1))

end YMGap.Continuum.BF4GrowingGridFullRowEnhancement

#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.gridReplicaActivity_pos
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.gridReplicaFullRowEnhancement_pos
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.one_le_gridReplicaFullRowEnhancement
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.gridReplicaActivity_mul_fullRowEnhancement_eqv_rawRow
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.gridReplicaSelectedFloor_le_fullRowFloor
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.centralSpinCubeRawRow_mul_gridReplicaFullRowFloor_le_gridRawRow
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.growingGridFullRowCommonFloor_pos
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.growingGridSelectedCommonFloor_le_fullRowCommonFloor
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.growingGridFullRowCommonFloor_le_computedFloor
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowEnhancement.growingGrid_fullRowEffectiveMultiplicityLowerBound
