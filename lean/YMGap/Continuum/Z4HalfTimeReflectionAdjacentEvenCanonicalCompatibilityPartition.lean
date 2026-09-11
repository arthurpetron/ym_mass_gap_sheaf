/-
# Choice-free canonical compatibility partitions

The canonical fixed-incidence carrier contains every bounded incoming and
outgoing trajectory field, but existential membership witnesses cannot be
chosen under a finite sum intuitionistically.  This leaf replaces that
temptation by an exact Kronecker partition of unity over the literal symbolic
carrier.  It also proves the corresponding weighted collapse for every
quantity depending only on the physical incidence coordinates.

No carrier is evaluated and no function-space equality is searched.  The
proof is the existing bounded-labelling Fubini theorem followed by one-hot
delta collapse on each natural-number coordinate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryTerminalField

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite one-hot partition on bounded labellings -/

/-- Exact equality delta for one natural-number channel. -/
def channelEqualityDelta (candidate target : Nat) : Q' :=
  if candidate = target then 1 else 0

/-- Product delta asserting agreement on every key in a finite list. -/
def boundedLabellingEqualityDelta {A : Type} [DecidableEq A]
    (keys : List A) (candidate target : A → Nat) : Q' :=
  listQProduct
    (fun key => channelEqualityDelta (candidate key) (target key)) keys

private theorem fsum_eqv_zero_of_zero_below (value : Nat → Q') :
    ∀ count,
      (∀ index, index < count → value index ≈ 0) →
      fsum value count ≈ 0
  | 0, _ => Q'.eqv_refl 0
  | count + 1, hzero => by
      rw [fsum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (fsum_eqv_zero_of_zero_below value count
            (fun index hindex =>
              hzero index (Nat.lt_succ_of_lt hindex)))
          (hzero count (Nat.lt_succ_self count))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- A one-hot channel delta sums to one when its target lies in the finite
window. -/
theorem fsum_channelEqualityDelta_eqv_one : ∀ count target,
    target < count →
      fsum (fun candidate => channelEqualityDelta candidate target) count ≈ 1
  | 0, target, htarget => False.elim (Nat.not_lt_zero target htarget)
  | count + 1, target, htarget => by
      by_cases hprefix : target < count
      · have hlast : count ≠ target := by
          intro heq
          subst target
          exact Nat.lt_irrefl count hprefix
        rw [fsum_succ]
        unfold channelEqualityDelta
        rw [if_neg hlast]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (fsum_channelEqualityDelta_eqv_one count target hprefix)
            (Q'.eqv_refl 0)) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' 1)
      · have htargetEq : target = count :=
          Nat.le_antisymm (Nat.lt_succ_iff.mp htarget)
            (Nat.not_lt.mp hprefix)
        subst target
        rw [fsum_succ]
        have hzero :
            fsum (fun candidate =>
              channelEqualityDelta candidate count) count ≈ 0 :=
          fsum_eqv_zero_of_zero_below _ count (fun candidate hcandidate => by
            unfold channelEqualityDelta
            rw [if_neg (Nat.ne_of_lt hcandidate)]
            exact Q'.eqv_refl 0)
        unfold channelEqualityDelta
        rw [if_pos rfl]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hzero (Q'.eqv_refl 1)) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' 1)

private theorem listQProduct_one_eqv {A : Type} : ∀ keys : List A,
    listQProduct (fun _ : A => (1 : Q')) keys ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: rest => by
      change (1 : Q') * listQProduct (fun _ : A => (1 : Q')) rest ≈ 1
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 _ _ (listQProduct_one_eqv rest))
        (Q'.one_mul_eqv 1)

/-- The complete bounded-labelling carrier is an exact Kronecker partition
of unity around every bounded target.  Multiplicities in later trajectory
sums are therefore retained rather than quotiented away. -/
theorem boundedLabellingsOn_equalityDelta_partition
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (target : A → Nat)
    (hnodup : keys.Nodup)
    (hbounded : ∀ key, key ∈ keys → target key ≤ cutoff) :
    listQSum
        (fun candidate =>
          boundedLabellingEqualityDelta keys candidate target)
        (boundedLabellingsOn cutoff keys) ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (boundedLabellingsOn_product_fubini cutoff
      (fun key candidate =>
        channelEqualityDelta candidate (target key))
      keys hnodup) ?_
  refine Q'.eqv_trans _ _ _
    (listQProduct_congr_eqv
      (fun key => fsum
        (fun candidate => channelEqualityDelta candidate (target key))
        (cutoff + 1))
      (fun _ => (1 : Q')) keys
      (fun key hkey =>
        fsum_channelEqualityDelta_eqv_one (cutoff + 1) (target key)
          (Nat.lt_succ_iff.mpr (hbounded key hkey)))) ?_
  exact listQProduct_one_eqv keys

/-! ## 2. Delta support and weighted collapse -/

/-- A product delta either vanishes or its two labellings agree on every
listed key.  The disjunction is obtained by recursion over the key list, not
by deciding equality of functions. -/
theorem boundedLabellingEqualityDelta_zero_or_agree
    {A : Type} [DecidableEq A]
    (candidate target : A → Nat) : ∀ keys : List A,
    boundedLabellingEqualityDelta keys candidate target ≈ 0 ∨
      ∀ key, key ∈ keys → candidate key = target key
  | [] => Or.inr (fun key hkey => False.elim (List.not_mem_nil hkey))
  | head :: rest => by
      by_cases hhead : candidate head = target head
      · rcases boundedLabellingEqualityDelta_zero_or_agree
          candidate target rest with hzero | hagree
        · apply Or.inl
          change channelEqualityDelta (candidate head) (target head) *
              boundedLabellingEqualityDelta rest candidate target ≈ 0
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (channelEqualityDelta (candidate head) (target head))
              _ _ hzero) ?_
          exact Q'.mul_zero_eqv _
        · apply Or.inr
          intro key hkey
          rcases List.mem_cons.mp hkey with heq | hrest
          · subst key
            exact hhead
          · exact hagree key hrest
      · apply Or.inl
        change channelEqualityDelta (candidate head) (target head) *
            boundedLabellingEqualityDelta rest candidate target ≈ 0
        unfold channelEqualityDelta
        rw [if_neg hhead]
        exact Q'.zero_mul_eqv _

/-- Multiplying by the finite product delta permits replacement by any
quantity which depends only on the listed coordinates. -/
theorem boundedLabellingEqualityDelta_mul_congr
    {A : Type} [DecidableEq A]
    (keys : List A) (target candidate : A → Nat)
    (value : (A → Nat) → Q')
    (hlocal : (∀ key, key ∈ keys → candidate key = target key) →
      value candidate ≈ value target) :
    boundedLabellingEqualityDelta keys candidate target * value candidate ≈
      boundedLabellingEqualityDelta keys candidate target * value target := by
  rcases boundedLabellingEqualityDelta_zero_or_agree
      candidate target keys with hzero | hagree
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (boundedLabellingEqualityDelta keys candidate target) 0
        (value candidate) hzero) ?_
    refine Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv (value candidate)) ?_
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (boundedLabellingEqualityDelta keys candidate target) 0
        (value target) hzero) ?_)
    exact Q'.zero_mul_eqv (value target)
  · exact Q'.mul_eqv_congr_left
      (boundedLabellingEqualityDelta keys candidate target)
      (value candidate) (value target) (hlocal hagree)

/-- Weighted partition of unity.  Any incidence-local value collapses to its
target value without selecting a target index in the function-valued list. -/
theorem boundedLabellingsOn_equalityDelta_weighted_collapse
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (target : A → Nat)
    (hnodup : keys.Nodup)
    (hbounded : ∀ key, key ∈ keys → target key ≤ cutoff)
    (value : (A → Nat) → Q')
    (hlocal : ∀ candidate,
      (∀ key, key ∈ keys → candidate key = target key) →
        value candidate ≈ value target) :
    listQSum
        (fun candidate =>
          boundedLabellingEqualityDelta keys candidate target *
            value candidate)
        (boundedLabellingsOn cutoff keys) ≈ value target := by
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun candidate =>
        boundedLabellingEqualityDelta_mul_congr
          keys target candidate value (hlocal candidate))
      (boundedLabellingsOn cutoff keys)) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_right
      (fun candidate =>
        boundedLabellingEqualityDelta keys candidate target)
      (value target) (boundedLabellingsOn cutoff keys)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 1 (value target)
      (boundedLabellingsOn_equalityDelta_partition
        cutoff keys target hnodup hbounded)) ?_
  exact Q'.one_mul_eqv (value target)

/-! ## 3. The canonical fixed-incidence specializations -/

/-- Equality delta on the literal adjacent-even fixed-face/link incidences. -/
def adjacentEvenCanonicalIncidenceDelta
    (radius : Nat)
    (candidate target : FixedFaceLinkIncidence → Nat) : Q' :=
  boundedLabellingEqualityDelta
    (adjacentEvenFixedFaceMajorIncidences radius) candidate target

theorem adjacentEvenCanonicalIncidenceDelta_partition
    (K radius : Nat) (target : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        target incidence ≤ linkAuxiliaryCutoff K) :
    listQSum
        (fun candidate =>
          adjacentEvenCanonicalIncidenceDelta radius candidate target)
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈ 1 := by
  exact boundedLabellingsOn_equalityDelta_partition
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius) target
    (adjacentEvenFixedFaceMajorIncidences_nodup radius) hbounded

theorem adjacentEvenTrajectoryOutgoingIncidenceDelta_partition
    {K radius : Nat} {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    listQSum
        (fun candidate =>
          adjacentEvenCanonicalIncidenceDelta radius candidate
            (adjacentEvenTrajectoryOutgoingIncidenceAssignment
              radius trajectory))
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈ 1 := by
  exact adjacentEvenCanonicalIncidenceDelta_partition K radius _
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment_le htrajectory)

theorem adjacentEvenTrajectoryIncomingIncidenceDelta_partition
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    listQSum
        (fun candidate =>
          adjacentEvenCanonicalIncidenceDelta radius candidate
            (adjacentEvenTrajectoryIncomingIncidenceAssignment
              radius source trajectory))
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈ 1 := by
  exact adjacentEvenCanonicalIncidenceDelta_partition K radius _
    (adjacentEvenTrajectoryIncomingIncidenceAssignment_le
      hsource htrajectory)

theorem adjacentEvenCanonicalIncidenceDelta_weighted_collapse
    (K radius : Nat) (target : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        target incidence ≤ linkAuxiliaryCutoff K)
    (value : (FixedFaceLinkIncidence → Nat) → Q')
    (hlocal : ∀ candidate,
      (∀ incidence,
        incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
          candidate incidence = target incidence) →
        value candidate ≈ value target) :
    listQSum
        (fun candidate =>
          adjacentEvenCanonicalIncidenceDelta radius candidate target *
            value candidate)
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈
      value target := by
  exact boundedLabellingsOn_equalityDelta_weighted_collapse
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius) target
    (adjacentEvenFixedFaceMajorIncidences_nodup radius) hbounded
    value hlocal

#print axioms fsum_channelEqualityDelta_eqv_one
#print axioms boundedLabellingsOn_equalityDelta_partition
#print axioms boundedLabellingEqualityDelta_zero_or_agree
#print axioms boundedLabellingsOn_equalityDelta_weighted_collapse
#print axioms adjacentEvenTrajectoryOutgoingIncidenceDelta_partition
#print axioms adjacentEvenTrajectoryIncomingIncidenceDelta_partition
#print axioms adjacentEvenCanonicalIncidenceDelta_weighted_collapse

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityPartition
