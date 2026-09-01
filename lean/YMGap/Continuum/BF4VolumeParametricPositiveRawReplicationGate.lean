/-
# Volume-parametric positive raw-row replication gate

The earlier positive-replication compiler fixes the central reflection half
at zero and uses cutoff-labelled spin-cube sources.  Growing-volume replica
families need the same finite comparison at arbitrary cutoff and arbitrary
reflection half-volume.

This file provides that generic finite interface.  A certificate consists of
one positive reference state and a nonempty duplicate-free list of positive
replica states.  The compiler takes the finite minimum of the clipped exact
replica/reference raw-row ratios.  It then proves constructively that

  referenceRawRow * (replicaCount * ratioFloor) <= physicalPartition.

All quantitative fields are computed from literal finite data.  No claim is
made that the resulting effective multiplicity diverges with volume; that is
the remaining analytic input for a cofinal gap, continuum limit, or Clay
conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate

namespace YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

private def listQMinOne {A : Type} (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => Q'.min' (value head) (listQMinOne value tail)

private theorem listQMinOne_pos_local {A : Type}
    (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') < value item) →
        (0 : Q') < listQMinOne value items
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hpos =>
      CReal.min_pos
        (hpos head List.mem_cons_self)
        (listQMinOne_pos_local value tail
          (fun item hitem =>
            hpos item (List.mem_cons_of_mem head hitem)))

private theorem listQMinOne_le_selected_local {A : Type}
    (value : A → Q') :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      listQMinOne value items ≤ value selected
  | [], _, hmem => by cases hmem
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selected
        exact Q'.min_le_left' _ _
      · exact Q'.le_trans' _ _ _
          (Q'.min_le_right' _ _)
          (listQMinOne_le_selected_local value tail htail)

private theorem lower_le_listQMinOne_local {A : Type}
    (value : A → Q') (lower : Q') :
    ∀ items : List A,
      lower ≤ 1 →
      (∀ item, item ∈ items → lower ≤ value item) →
        lower ≤ listQMinOne value items
  | [], hlowerOne, _ => hlowerOne
  | head :: tail, hlowerOne, hlower => by
      apply (Q'.le_min'_iff lower _ _).mpr
      exact
        ⟨hlower head List.mem_cons_self,
          lower_le_listQMinOne_local value lower tail hlowerOne
            (fun item hitem =>
              hlower item (List.mem_cons_of_mem head hitem))⟩

private theorem listQMinOne_eq_one_local {A : Type}
    (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item = 1) →
        listQMinOne value items = 1
  | [], _ => rfl
  | head :: tail, hone => by
      unfold listQMinOne
      rw [hone head List.mem_cons_self]
      rw [listQMinOne_eq_one_local value tail
        (fun item hitem =>
          hone item (List.mem_cons_of_mem head hitem))]
      unfold Q'.min'
      split <;> rfl

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

private theorem ofNat_pos_of_pos_local {value : Nat}
    (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  cases value with
  | zero => contradiction
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

private theorem reference_mul_count_mul_floor_eqv
    (reference floor : Q') (count : Nat) :
    reference * (Q'.ofNat count * floor) ≈
      Q'.ofNat count * (reference * floor) := by
  refine Q'.eqv_trans _
    (reference * (floor * Q'.ofNat count)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat count) floor)
  refine Q'.eqv_trans _
    ((reference * floor) * Q'.ofNat count) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_comm_eqv _ _

/-! ## 1. Arbitrary-volume finite replication data -/

/-- One positive reference row and a nonempty duplicate-free list of positive
replica rows at arbitrary cutoff and central reflection half-volume. -/
structure CentralPositiveRawReplicationListAt
    (w : Q') (hw0 : (0 : Q') < w) (K half : Nat) : Type where
  reference : EdgeLabelling
  reference_mem : reference ∈
    centralPositiveHalfStates w (Q'.le_of_lt hw0) K half
  replicas : List EdgeLabelling
  replicas_nodup : replicas.Nodup
  replicas_nonempty : replicas ≠ []
  replicas_mem : ∀ state, state ∈ replicas →
    state ∈ centralPositiveHalfStates w (Q'.le_of_lt hw0) K half

namespace CentralPositiveRawReplicationListAt

theorem replicaCount_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    0 < replication.replicas.length := by
  cases hreplicas : replication.replicas with
  | nil => exact False.elim (replication.replicas_nonempty hreplicas)
  | cons _head _tail =>
      simp only [List.length_cons]
      omega

theorem referenceRawRow_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    (0 : Q') < centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K half replication.reference := by
  exact centralPhysicalPositiveRawRowMass_pos replication.reference_mem

/-! ## 2. Computed finite row-ratio floor -/

def rawRowRatio
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    (state : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K half state)
    (centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K half replication.reference)
    replication.referenceRawRow_pos

def clippedRawRowRatio
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    (state : EdgeLabelling) : Q' :=
  Q'.min' 1 (replication.rawRowRatio state)

theorem clippedRawRowRatio_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    {state : EdgeLabelling} (hstate : state ∈ replication.replicas) :
    (0 : Q') < replication.clippedRawRowRatio state := by
  unfold clippedRawRowRatio rawRowRatio
  exact CReal.min_pos (by decide)
    (Q'.divPos_pos _ _ replication.referenceRawRow_pos
      (centralPhysicalPositiveRawRowMass_pos
        (replication.replicas_mem state hstate)))

def rawRowRatioFloor
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) : Q' :=
  listQMinOne replication.clippedRawRowRatio replication.replicas

theorem rawRowRatioFloor_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    (0 : Q') < replication.rawRowRatioFloor := by
  unfold rawRowRatioFloor
  apply listQMinOne_pos_local
  intro state hstate
  exact replication.clippedRawRowRatio_pos hstate

theorem rawRowRatioFloor_le_clipped
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    {state : EdgeLabelling} (hstate : state ∈ replication.replicas) :
    replication.rawRowRatioFloor ≤
      replication.clippedRawRowRatio state := by
  unfold rawRowRatioFloor
  exact listQMinOne_le_selected_local
    replication.clippedRawRowRatio replication.replicas hstate

/-- Any capped pointwise comparison between the common reference row and all
selected replica rows transfers to the computed arbitrary-volume minimum. -/
theorem lower_le_rawRowRatioFloor_of_scaledReferenceRawRow_le
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    (lower : Q') (hlowerOne : lower ≤ 1)
    (hscaled : ∀ state, state ∈ replication.replicas →
      centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K half replication.reference * lower ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half state) :
    lower ≤ replication.rawRowRatioFloor := by
  unfold rawRowRatioFloor
  apply lower_le_listQMinOne_local
  · exact hlowerOne
  · intro state hstate
    unfold clippedRawRowRatio
    apply (Q'.le_min'_iff lower _ _).mpr
    refine ⟨hlowerOne, ?_⟩
    unfold rawRowRatio
    apply Q'.le_divPos_of_mul_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv lower
          (centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K half replication.reference)))
      (hscaled state hstate)

/-- If the selected reference raw row is no larger than every replica raw
row, clipping makes every exact replica/reference ratio equal to one and the
computed finite floor is exactly one. -/
theorem rawRowRatioFloor_eq_one_of_reference_le
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    (hrow : ∀ state, state ∈ replication.replicas →
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half replication.reference ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half state) :
    replication.rawRowRatioFloor = 1 := by
  unfold rawRowRatioFloor
  apply listQMinOne_eq_one_local
  intro state hstate
  have honeMul :
      (1 : Q') *
          centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K half replication.reference ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half state := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.one_mul_eqv
          (centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K half replication.reference)))
      (hrow state hstate)
  have hratio : (1 : Q') ≤ replication.rawRowRatio state := by
    unfold rawRowRatio
    exact Q'.le_divPos_of_mul_le
      (centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K half state)
      (centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K half replication.reference)
      replication.referenceRawRow_pos honeMul
  unfold clippedRawRowRatio Q'.min'
  simp only [hratio, if_true]

/-- Every selected replica row dominates the computed ratio floor times the
common reference row. -/
theorem scaledReferenceRawRow_le_replica
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half)
    {state : EdgeLabelling} (hstate : state ∈ replication.replicas) :
    centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K half replication.reference *
        replication.rawRowRatioFloor ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K half state := by
  let referenceRow := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw0) K half replication.reference
  let targetRow := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw0) K half state
  let ratio := Q'.divPos targetRow referenceRow
    replication.referenceRawRow_pos
  have hfloorClip := replication.rawRowRatioFloor_le_clipped hstate
  have hclipRatio : replication.clippedRawRowRatio state ≤ ratio := by
    unfold clippedRawRowRatio rawRowRatio ratio targetRow referenceRow
    exact Q'.min_le_right
  have hfloorRatio : replication.rawRowRatioFloor ≤ ratio :=
    Q'.le_trans' _ _ _ hfloorClip hclipRatio
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    replication.rawRowRatioFloor ratio referenceRow hfloorRatio
    (Q'.le_of_lt replication.referenceRawRow_pos)
  have hcollapse : referenceRow * ratio ≈ targetRow := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv referenceRow ratio)
      (Q'.divPos_mul_eqv targetRow referenceRow
        replication.referenceRawRow_pos)
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

/-! ## 3. Effective multiplicity and partition payment -/

def effectiveMultiplicity
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) : Q' :=
  Q'.ofNat replication.replicas.length * replication.rawRowRatioFloor

theorem effectiveMultiplicity_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    (0 : Q') < replication.effectiveMultiplicity := by
  exact Q'.mul_pos
    (ofNat_pos_of_pos_local replication.replicaCount_pos)
    replication.rawRowRatioFloor_pos

/-- The duplicate-free selected replica sum injects into the complete raw
source budget. -/
theorem scaledReferenceRawRowSum_le_fullRawSourceMass
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    listQSum
        (fun _state : EdgeLabelling =>
          centralPhysicalPositiveRawRowMass
              w (Q'.le_of_lt hw0) K half replication.reference *
            replication.rawRowRatioFloor)
        replication.replicas ≤
      centralPhysicalPositiveRawSourceMass
        w (Q'.le_of_lt hw0) K half := by
  unfold centralPhysicalPositiveRawSourceMass
  apply listQSum_le_of_injective_nodup
    replication.replicas (centralHalfStates K half)
    (fun _state : EdgeLabelling =>
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half replication.reference *
        replication.rawRowRatioFloor)
    (centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K half)
    (fun state => state)
  · exact replication.replicas_nodup
  · exact centralHalfStates_nodup K half
  · intro state hstate
    exact (mem_centralPositiveHalfStates_iff.mp
      (replication.replicas_mem state hstate)).1
  · intro left _hleft right _hright heq
    exact heq
  · intro state hstate
    exact replication.scaledReferenceRawRow_le_replica hstate
  · intro state _hstate
    exact centralPhysicalPositiveRawRowMass_nonnegative
      (Q'.le_of_lt hw0) K half state

/-- The scalar effective-multiplicity product is exactly the selected
constant scaled-row sum. -/
theorem referenceRawRow_mul_effectiveMultiplicity_eqv_scaledSum
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half replication.reference *
        replication.effectiveMultiplicity ≈
      listQSum
        (fun _state : EdgeLabelling =>
          centralPhysicalPositiveRawRowMass
              w (Q'.le_of_lt hw0) K half replication.reference *
            replication.rawRowRatioFloor)
        replication.replicas := by
  unfold effectiveMultiplicity
  exact Q'.eqv_trans _ _ _
    (reference_mul_count_mul_floor_eqv
      (centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K half replication.reference)
      replication.rawRowRatioFloor replication.replicas.length)
    (Q'.eqv_symm
      (listQSum_const_local
        (centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K half replication.reference *
          replication.rawRowRatioFloor)
        replication.replicas))

/-- The complete physical partition pays the reference raw row multiplied by
the computed volume-parametric effective multiplicity. -/
theorem referenceRawRow_mul_effectiveMultiplicity_le_partition
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K half replication.reference *
        replication.effectiveMultiplicity ≤
      slabParametricKPhysicalPartition w K (centralExtent half) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      replication.referenceRawRow_mul_effectiveMultiplicity_eqv_scaledSum)
    (Q'.le_trans' _ _ _
      replication.scaledReferenceRawRowSum_le_fullRawSourceMass
      (Q'.le_of_eqv
        (centralPhysicalPositiveRawSourceMass_eqv_partition
          w (Q'.le_of_lt hw0) K half)))

/-- After the common physical partition normalization cancels, the reference
state marginal is bounded by the reciprocal computed effective
multiplicity. -/
theorem referenceMarginal_le_reciprocalEffectiveMultiplicity
    {w : Q'} {hw0 : (0 : Q') < w} {K half : Nat}
    (replication : CentralPositiveRawReplicationListAt w hw0 K half) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw0) K half replication.reference ≤
      Q'.divPos 1 replication.effectiveMultiplicity
        replication.effectiveMultiplicity_pos := by
  let raw := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw0) K half replication.reference
  let partition := slabParametricKPhysicalPartition
    w K (centralExtent half)
  let hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw0) K (centralExtent half)
  let effective := replication.effectiveMultiplicity
  let heffective : (0 : Q') < effective :=
    replication.effectiveMultiplicity_pos
  let epsilon := Q'.divPos 1 effective heffective
  have hmul : raw * effective ≤ partition :=
    replication.referenceRawRow_mul_effectiveMultiplicity_le_partition
  have hdiv : raw ≤ Q'.divPos partition effective heffective :=
    Q'.le_divPos_of_mul_le partition effective heffective hmul
  have hreassociate :
      Q'.divPos partition effective heffective ≈
        epsilon * partition := by
    unfold epsilon Q'.divPos
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv partition (Q'.recipPos effective heffective))
      (Q'.eqv_symm
        (Q'.mul_eqv_congr_right
          (1 * Q'.recipPos effective heffective)
          (Q'.recipPos effective heffective) partition
          (Q'.one_mul_eqv (Q'.recipPos effective heffective))))
  have hraw : raw ≤ epsilon * partition :=
    Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv hreassociate)
  have hquotient : Q'.divPos raw partition hpartition ≤ epsilon :=
    Q'.divPos_le_of_le_mul raw partition hpartition hraw
  have hrow :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw0) K half replication.reference ≈
        Q'.divPos raw partition hpartition := by
    exact Q'.eqv_trans _ _ _
      (centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
        (w := w) (hw := Q'.le_of_lt hw0) (K := K) (half := half)
        (source := replication.reference)
        (mem_centralPositiveHalfStates_iff.mp
          replication.reference_mem).1)
      (by
        unfold raw partition
          centralPhysicalPositiveRawRowMass
          centralPhysicalFiniteVacuumSectorPartitionReciprocal
          Q'.divPos
        exact Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrow) hquotient

end CentralPositiveRawReplicationListAt

end YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate

#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.rawRowRatioFloor_pos
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.scaledReferenceRawRow_le_replica
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.lower_le_rawRowRatioFloor_of_scaledReferenceRawRow_le
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.rawRowRatioFloor_eq_one_of_reference_le
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.effectiveMultiplicity_pos
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.referenceRawRow_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt.referenceMarginal_le_reciprocalEffectiveMultiplicity
