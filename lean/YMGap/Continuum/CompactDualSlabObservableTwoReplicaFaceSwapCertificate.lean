/-
# Facewise transposition removes the weight field from the SU(2) switch

The open two-replica switch certificate asks for exact preservation of the
expanded product weight.  That equality is not an independent analytic
obligation.  Every accepted fine-intertwiner assignment has unit raw fiber
weight, while the physical factor is a product over faces.  Consequently a
pointwise transposition of the two physical spin labels preserves the product
weight exactly at every coupling and cutoff.

This module proves that fact and replaces the earlier weight-bearing switch
input by a smaller geometric/admissibility certificate.  The refined
certificate supplies a Boolean face mask, accepted encoded outputs, a decoder,
and proofs that the root face is fixed while the target face is swapped.  Its
physical projections must be exactly the two mask-controlled transpositions.
Target-cell membership and full product-weight preservation are then theorems,
not fields.

No refined certificate inhabitant is constructed here.  Building accepted
output intertwiner assignments and the recoverable component exchange remains
the finite combinatorial frontier.

Constructive contract: Boolean case analysis, finite products, explicit
encode/decode data, and exact rational algebra only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, `noncomputable`, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction

namespace YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableConnectedComponent
open YMGap.Continuum.CompactDualSlabObservableConnectedDecay
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal facewise transposition of two physical replicas -/

/-- At selected faces, take the second replica's spin; elsewhere retain the
first replica's spin. -/
def twoReplicaFaceSwapLeft
    (selected : Nat → Bool)
    (left right : SlabLabelling) : SlabLabelling :=
  fun faceId => if selected faceId then right faceId else left faceId

/-- The complementary output of the same facewise transposition. -/
def twoReplicaFaceSwapRight
    (selected : Nat → Bool)
    (left right : SlabLabelling) : SlabLabelling :=
  fun faceId => if selected faceId then left faceId else right faceId

@[simp] theorem twoReplicaFaceSwapLeft_of_false
    (selected : Nat → Bool) (left right : SlabLabelling)
    (faceId : Nat) (hselected : selected faceId = false) :
    twoReplicaFaceSwapLeft selected left right faceId = left faceId := by
  simp [twoReplicaFaceSwapLeft, hselected]

@[simp] theorem twoReplicaFaceSwapRight_of_false
    (selected : Nat → Bool) (left right : SlabLabelling)
    (faceId : Nat) (hselected : selected faceId = false) :
    twoReplicaFaceSwapRight selected left right faceId = right faceId := by
  simp [twoReplicaFaceSwapRight, hselected]

@[simp] theorem twoReplicaFaceSwapLeft_of_true
    (selected : Nat → Bool) (left right : SlabLabelling)
    (faceId : Nat) (hselected : selected faceId = true) :
    twoReplicaFaceSwapLeft selected left right faceId = right faceId := by
  simp [twoReplicaFaceSwapLeft, hselected]

@[simp] theorem twoReplicaFaceSwapRight_of_true
    (selected : Nat → Bool) (left right : SlabLabelling)
    (faceId : Nat) (hselected : selected faceId = true) :
    twoReplicaFaceSwapRight selected left right faceId = left faceId := by
  simp [twoReplicaFaceSwapRight, hselected]

/-- Applying the same face mask twice recovers the first physical replica. -/
theorem twoReplicaFaceSwapLeft_involutive
    (selected : Nat → Bool) (left right : SlabLabelling) :
    twoReplicaFaceSwapLeft selected
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) = left := by
  funext faceId
  cases hselected : selected faceId <;>
    simp [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight, hselected]

/-- Applying the same face mask twice recovers the second physical replica. -/
theorem twoReplicaFaceSwapRight_involutive
    (selected : Nat → Bool) (left right : SlabLabelling) :
    twoReplicaFaceSwapRight selected
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) = right := by
  funext faceId
  cases hselected : selected faceId <;>
    simp [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight, hselected]

/-- A pointwise transposition preserves the product of any scalar function of
the two labels. -/
theorem twoReplicaFaceSwap_pointwise_product
    (value : Nat → Q') (selected : Nat → Bool)
    (left right : SlabLabelling) (faceId : Nat) :
    value (twoReplicaFaceSwapLeft selected left right faceId) *
        value (twoReplicaFaceSwapRight selected left right faceId) ≈
      value (left faceId) * value (right faceId) := by
  cases hselected : selected faceId with
  | false =>
      simp only [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight,
        hselected]
      exact Q'.eqv_refl _
  | true =>
      simp only [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight,
        hselected, if_true]
      exact Q'.mul_comm_eqv _ _

/-! ## 2. Finite face products and expanded-fiber weights -/

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' := by
  exact Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem rearrange_pointwise_products
    (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num *
      (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem eliminateLinks_congr_local
    (left right : Nat → Q')
    (hpoint : ∀ faceId, left faceId ≈ right faceId) :
    ∀ faces : List Nat,
      eliminateLinks left faces ≈ eliminateLinks right faces
  | [] => Q'.eqv_refl _
  | faceId :: rest =>
      qmul_congr_local (hpoint faceId)
        (eliminateLinks_congr_local left right hpoint rest)

private theorem eliminateLinks_pointwise_mul_local
    (left right : Nat → Q') : ∀ faces : List Nat,
    eliminateLinks (fun faceId => left faceId * right faceId) faces ≈
      eliminateLinks left faces * eliminateLinks right faces
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | faceId :: rest => by
      unfold eliminateLinks
      refine Q'.eqv_trans _
        ((left faceId * right faceId) *
          (eliminateLinks left rest * eliminateLinks right rest)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_pointwise_mul_local left right rest)
      · exact rearrange_pointwise_products
          (left faceId) (right faceId)
          (eliminateLinks left rest) (eliminateLinks right rest)

/-- The complete heat-kernel face-factor product is exactly invariant under
an arbitrary facewise transposition of the two physical replicas. -/
theorem slabParametricKPhysicalFaceFactor_pair_faceSwap
    (coupling : Q') (cutoff extent : Nat)
    (selected : Nat → Bool) (left right : SlabLabelling) :
    slabParametricKPhysicalFaceFactor coupling cutoff extent
          (twoReplicaFaceSwapLeft selected left right) *
        slabParametricKPhysicalFaceFactor coupling cutoff extent
          (twoReplicaFaceSwapRight selected left right) ≈
      slabParametricKPhysicalFaceFactor coupling cutoff extent left *
        slabParametricKPhysicalFaceFactor coupling cutoff extent right := by
  let coefficient : Nat → Q' :=
    coeffAt (heatKernelPacket cutoff coupling)
  let leftValue : Nat → Q' := fun faceId => coefficient (left faceId)
  let rightValue : Nat → Q' := fun faceId => coefficient (right faceId)
  let swappedLeftValue : Nat → Q' := fun faceId =>
    coefficient (twoReplicaFaceSwapLeft selected left right faceId)
  let swappedRightValue : Nat → Q' := fun faceId =>
    coefficient (twoReplicaFaceSwapRight selected left right faceId)
  unfold slabParametricKPhysicalFaceFactor
  change eliminateLinks swappedLeftValue (slabPhysicalFaceEdges extent) *
      eliminateLinks swappedRightValue (slabPhysicalFaceEdges extent) ≈
    eliminateLinks leftValue (slabPhysicalFaceEdges extent) *
      eliminateLinks rightValue (slabPhysicalFaceEdges extent)
  refine Q'.eqv_trans _
    (eliminateLinks
      (fun faceId => swappedLeftValue faceId * swappedRightValue faceId)
      (slabPhysicalFaceEdges extent)) _ ?_ ?_
  · exact Q'.eqv_symm
      (eliminateLinks_pointwise_mul_local
        swappedLeftValue swappedRightValue
        (slabPhysicalFaceEdges extent))
  refine Q'.eqv_trans _
    (eliminateLinks
      (fun faceId => leftValue faceId * rightValue faceId)
      (slabPhysicalFaceEdges extent)) _ ?_ ?_
  · apply eliminateLinks_congr_local
    intro faceId
    exact twoReplicaFaceSwap_pointwise_product
      coefficient selected left right faceId
  · exact eliminateLinks_pointwise_mul_local
      leftValue rightValue (slabPhysicalFaceEdges extent)

/-- Because every accepted fine-intertwiner fiber has raw weight one, the
full expanded two-replica product weight is invariant under facewise physical
transposition for arbitrary output assignments. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
    (D : SlabPhysicalData) (selected : Nat → Bool)
    (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment
      swappedLeftAssignment swappedRightAssignment :
        SlabFusionWitnessAssignment) :
    retainedFineIntertwinerPhysicalFiberWeight D
          (twoReplicaFaceSwapLeft selected leftPhysical rightPhysical)
          swappedLeftAssignment *
        retainedFineIntertwinerPhysicalFiberWeight D
          (twoReplicaFaceSwapRight selected leftPhysical rightPhysical)
          swappedRightAssignment ≈
      retainedFineIntertwinerPhysicalFiberWeight D
          leftPhysical leftAssignment *
        retainedFineIntertwinerPhysicalFiberWeight D
          rightPhysical rightAssignment := by
  unfold retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        (twoReplicaFaceSwapLeft selected leftPhysical rightPhysical) *
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        (twoReplicaFaceSwapRight selected leftPhysical rightPhysical)) _ ?_ ?_
  · exact qmul_congr_local (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        leftPhysical *
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        rightPhysical) _ ?_ ?_
  · exact slabParametricKPhysicalFaceFactor_pair_faceSwap
      D.coupling D.cutoff D.extent selected leftPhysical rightPhysical
  · exact Q'.eqv_symm
      (qmul_congr_local (Q'.mul_one_eqv _) (Q'.mul_one_eqv _))

/-! ## 3. A strictly smaller open switch certificate -/

/-- **OPEN finite geometric/admissibility input.**  Construct accepted output
entries by transposing the two physical spin labellings along an explicit
face mask.  The mask fixes the root and swaps the target.  A decoder recovers
every separated source pair.

Unlike `SlabObservableDisconnectedSwitchCertificate`, this structure has no
target-membership field and no weight-preservation field; both are derived
below. -/
structure SlabObservableDisconnectedFaceSwapCertificate
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat)
    (_htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) : Type where
  swapMask : SlabObservableTwoReplicaPair D rootFaceId → Nat → Bool
  encode : SlabObservableTwoReplicaPair D rootFaceId →
    SlabObservableTwoReplicaPair D rootFaceId
  decode : SlabObservableTwoReplicaPair D rootFaceId →
    SlabObservableTwoReplicaPair D rootFaceId
  decode_encode : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      decode (encode pair) = pair
  encode_left_physical : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      (encode pair).1.1.1 =
        twoReplicaFaceSwapLeft (swapMask pair)
          pair.1.1.1 pair.2.1.1
  encode_right_physical : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      (encode pair).2.1.1 =
        twoReplicaFaceSwapRight (swapMask pair)
          pair.1.1.1 pair.2.1.1
  root_fixed : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      swapMask pair rootFaceId = false
  target_swapped : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      swapMask pair targetFaceId = true

/-- Root-fixed/target-swapped physical transposition forces every encoded
pair into the opposite Boolean four-cell. -/
theorem SlabObservableDisconnectedFaceSwapCertificate.encode_mem_target
    {D : SlabPhysicalData} {rootFaceId : Nat}
    {hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent}
    {targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservableDisconnectedFaceSwapCertificate
      D rootFaceId hroot targetFaceId htarget)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableSeparatedFourCellSourcePairs
      D rootFaceId hroot targetFaceId) :
    certificate.encode pair ∈
      slabObservableFourCellTargetPairs D rootFaceId targetFaceId := by
  have hsource := (List.mem_filter.mp hpair).1
  have hcells := (mem_cartesian_iff
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId) pair).mp hsource
  have hfirst := List.mem_filter.mp hcells.1
  have hsecond := List.mem_filter.mp hcells.2
  have hsecondParts := (Bool.and_eq_true _ _).mp hsecond.2
  apply (mem_cartesian_iff
    (slabObservableRootTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetEntries
      D rootFaceId targetFaceId)
    (certificate.encode pair)).mpr
  constructor
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ (certificate.encode pair).1
    · unfold SlabObservablePositiveSourceEntry.facePositiveB
      rw [certificate.encode_left_physical pair hpair]
      simp only [twoReplicaFaceSwapLeft,
        certificate.target_swapped pair hpair, if_true]
      exact hsecondParts.2
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ (certificate.encode pair).2
    · apply (Bool.and_eq_true _ _).mpr
      constructor
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [certificate.encode_right_physical pair hpair]
        simp only [twoReplicaFaceSwapRight,
          certificate.root_fixed pair hpair]
        exact hsecondParts.1
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [certificate.encode_right_physical pair hpair]
        simp only [twoReplicaFaceSwapRight,
          certificate.target_swapped pair hpair, if_true]
        exact hfirst.2

/-- Facewise transposition makes full two-replica product-weight preservation
automatic. -/
theorem SlabObservableDisconnectedFaceSwapCertificate.weight_preserved
    {D : SlabPhysicalData} {rootFaceId : Nat}
    {hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent}
    {targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservableDisconnectedFaceSwapCertificate
      D rootFaceId hroot targetFaceId htarget)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableSeparatedFourCellSourcePairs
      D rootFaceId hroot targetFaceId) :
    slabObservableTwoReplicaPairWeight D (certificate.encode pair) ≈
      slabObservableTwoReplicaPairWeight D pair := by
  unfold slabObservableTwoReplicaPairWeight
    slabObservablePositiveEntryWeight slabExpandedFineEntryWeight
    slabExpandedFineSourceWeight
  rw [certificate.encode_left_physical pair hpair,
    certificate.encode_right_physical pair hpair]
  exact retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
    D (certificate.swapMask pair)
    pair.1.1.1 pair.2.1.1
    pair.1.1.2 pair.2.1.2
    (certificate.encode pair).1.1.2
    (certificate.encode pair).2.1.2

/-- Every refined face-swap certificate compiles to the earlier minimal
recoverable switch interface. -/
def SlabObservableDisconnectedFaceSwapCertificate.toSwitchCertificate
    {D : SlabPhysicalData} {rootFaceId : Nat}
    {hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent}
    {targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservableDisconnectedFaceSwapCertificate
      D rootFaceId hroot targetFaceId htarget) :
    SlabObservableDisconnectedSwitchCertificate
      D rootFaceId hroot targetFaceId htarget where
  encode := certificate.encode
  decode := certificate.decode
  encode_mem_target := certificate.encode_mem_target
  decode_encode := certificate.decode_encode
  weight_preserved := certificate.weight_preserved

/-- The geometric four-cell defect follows from the smaller face-swap
certificate, with target transport and product-weight preservation discharged
by the preceding compilers. -/
theorem slabObservableFourCell_defect_le_anchorRate_of_faceSwap
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (certificate : SlabObservableDisconnectedFaceSwapCertificate
      (anchorSlabPhysicalData cutoff half) rootFaceId hroot
      targetFaceId htarget) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) ≤
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId) +
        (slabObservableConnectedAnchorRate D rootFaceId
            (slabPlaquetteAt D.extent targetFaceId) *
          D.physicalPartition) * D.physicalPartition := by
  exact slabObservableFourCell_defect_le_anchorRate_of_switch
    cutoff half rootFaceId hroot targetFaceId htarget
      certificate.toSwitchCertificate

#print axioms twoReplicaFaceSwapLeft
#print axioms twoReplicaFaceSwapRight
#print axioms twoReplicaFaceSwapLeft_involutive
#print axioms twoReplicaFaceSwapRight_involutive
#print axioms twoReplicaFaceSwap_pointwise_product
#print axioms slabParametricKPhysicalFaceFactor_pair_faceSwap
#print axioms retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
#print axioms SlabObservableDisconnectedFaceSwapCertificate.encode_mem_target
#print axioms SlabObservableDisconnectedFaceSwapCertificate.weight_preserved
#print axioms SlabObservableDisconnectedFaceSwapCertificate.toSwitchCertificate
#print axioms slabObservableFourCell_defect_le_anchorRate_of_faceSwap

end YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
