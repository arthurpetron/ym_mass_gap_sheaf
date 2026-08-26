/-
# Exact anchor weight payment for peeling one physical face strand

The global strand construction is useful analytically only if removing a
strand copy pays a cutoff-independent amount in the *actual expanded BF4
measure*.  This module proves that payment before constructing components.

At the production anchor `w = 1/400`, log-concavity of the complete SU(2)
heat-kernel coefficient sequence gives the sharp bottom-ratio bound

    c_(s+1) <= c_1 c_s,       c_1 = 1 / 32,000,000,

for every spin and every packet cutoff containing `s+1`.  Consequently,
lowering one positive physical face label by one changes the whole corrected-
slab face product by at most that same factor.  The retained fine-intertwiner
fiber has unit counting weight, so the identical comparison holds for any two
expanded fiber entries over the two physical labellings.

This is the analytic half of one component-peel step.  It does not construct
the lowered accepted fusion assignment; that is the next geometric theorem.

Constructive contract: exact `Q'` order algebra, finite product recursion, and
decidable equality only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.MultiLinkFusionDefect
import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact all-spin anchor ratio -/

/-- At the actual strong-coupling anchor, every successor coefficient costs
at most the exact fundamental coefficient `1 / 32,000,000`.  This is the
log-concave bottom-ratio theorem, not the much coarser `1/4` envelope. -/
theorem anchorCoeffW_succ_le (spin : Nat) :
    coeffW anchorCoupling (spin + 1) <=
      anchorFaceCoefficient * coeffW anchorCoupling spin := by
  have hratio := coeffW_ratio_le
    (w := anchorCoupling) (by decide) (by decide) spin
  rw [coeffW_zero] at hratio
  have hleft :
      coeffW anchorCoupling (spin + 1) <=
        coeffW anchorCoupling (spin + 1) * 1 :=
    Q'.ge_of_eqv (Q'.mul_one_eqv _)
  have hright :
      coeffW anchorCoupling spin * coeffW anchorCoupling 1 ≈
        anchorFaceCoefficient * coeffW anchorCoupling spin := by
    refine Q'.eqv_trans _
      (coeffW anchorCoupling spin * anchorFaceCoefficient) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ anchorFundamentalCoefficient
    · exact Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hright))

/-- The same sharp ratio holds inside every finite heat-kernel packet that
contains the successor spin. -/
theorem anchorPacketCoefficient_succ_le
    (cutoff spin : Nat) (hbounded : spin + 1 <= cutoff) :
    coeffAt (heatKernelPacket cutoff anchorCoupling) (spin + 1) <=
      anchorFaceCoefficient *
        coeffAt (heatKernelPacket cutoff anchorCoupling) spin := by
  rw [coeffAt_heatKernelPacket (K := cutoff) (spin := spin + 1)
      (w := anchorCoupling) (by omega)]
  rw [coeffAt_heatKernelPacket (K := cutoff) (spin := spin)
      (w := anchorCoupling) (by omega)]
  exact anchorCoeffW_succ_le spin

/-! ## 2. Lower one literal physical face -/

/-- Decrease one selected physical face label by one and leave every other
numerical coordinate unchanged. -/
def lowerSlabFace
    (physical : EdgeLabelling) (faceId : Nat) : EdgeLabelling :=
  fun id => if id = faceId then physical id - 1 else physical id

@[simp] theorem lowerSlabFace_selected
    (physical : EdgeLabelling) (faceId : Nat) :
    lowerSlabFace physical faceId faceId = physical faceId - 1 := by
  simp [lowerSlabFace]

theorem lowerSlabFace_other
    (physical : EdgeLabelling) {faceId id : Nat}
    (hne : id ≠ faceId) :
    lowerSlabFace physical faceId id = physical id := by
  simp [lowerSlabFace, hne]

private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ n ih =>
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = n := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem anchorPacketCoefficient_nonnegative
    (cutoff spin : Nat) :
    (0 : Q') <=
      coeffAt (heatKernelPacket cutoff anchorCoupling) spin := by
  by_cases hspin : spin < cutoff + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg (by decide) spin
  · have hlarge : cutoff < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket cutoff anchorCoupling) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_anchor_nonnegative
    (cutoff : Nat) (physical : EdgeLabelling) :
    forall ids : List Nat,
      (0 : Q') <=
        eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
            (physical id)) ids
  | [] => Q'.zero_le_one
  | item :: rest =>
      Q'.mul_nonneg _ _
        (anchorPacketCoefficient_nonnegative cutoff (physical item))
        (eliminateLinks_anchor_nonnegative cutoff physical rest)

private theorem eliminateLinks_lowerSlabFace_eq_of_not_mem
    (cutoff : Nat) (physical : EdgeLabelling) (faceId : Nat) :
    forall ids : List Nat, faceId ∉ ids ->
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
            (physical id)) ids =
        eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
            (lowerSlabFace physical faceId id)) ids := by
  intro ids hnot
  apply YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.eliminateLinks_congr_eq
  intro id hid
  rw [lowerSlabFace_other physical (faceId := faceId)
    (id := id) (by
      intro heq
      subst id
      exact hnot hid)]

private theorem eliminateLinks_anchor_lower_one_le
    (cutoff : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (hpositive : 0 < physical faceId)
    (hbounded : physical faceId <= cutoff) :
    forall ids : List Nat, ids.Nodup -> faceId ∈ ids ->
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
            (physical id)) ids <=
        anchorFaceCoefficient *
          eliminateLinks
            (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
              (lowerSlabFace physical faceId id)) ids := by
  intro ids hnodup hmem
  induction ids with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons head tail ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        have htailEq := eliminateLinks_lowerSlabFace_eq_of_not_mem
          cutoff physical faceId tail hnodupParts.1
        have hspin : physical faceId - 1 + 1 = physical faceId := by
          omega
        have hcoeff := anchorPacketCoefficient_succ_le
          cutoff (physical faceId - 1) (by omega)
        rw [hspin] at hcoeff
        simp only [eliminateLinks]
        rw [lowerSlabFace_selected, ← htailEq]
        have htailNonnegative :
            (0 : Q') <=
              eliminateLinks
                (fun id => coeffAt
                  (heatKernelPacket cutoff anchorCoupling)
                  (physical id)) tail :=
          eliminateLinks_anchor_nonnegative cutoff physical tail
        have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _
          hcoeff htailNonnegative
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv
            (Q'.mul_assoc_eqv anchorFaceCoefficient
              (coeffAt (heatKernelPacket cutoff anchorCoupling)
                (physical faceId - 1))
              (eliminateLinks
                (fun id => coeffAt
                  (heatKernelPacket cutoff anchorCoupling)
                  (physical id)) tail)))
      · have hheadNe : head ≠ faceId := by
          intro heq
          subst head
          exact hnodupParts.1 htail
        have htailBound := ih hnodupParts.2 htail
        simp only [eliminateLinks]
        rw [lowerSlabFace_other physical hheadNe]
        have hheadNonnegative :=
          anchorPacketCoefficient_nonnegative cutoff (physical head)
        have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _
          htailBound hheadNonnegative
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv (by
            refine Q'.eqv_trans _
              ((coeffAt (heatKernelPacket cutoff anchorCoupling)
                  (physical head) * anchorFaceCoefficient) *
                eliminateLinks
                  (fun id => coeffAt
                    (heatKernelPacket cutoff anchorCoupling)
                    (lowerSlabFace physical faceId id)) tail) _ ?_ ?_
            · exact Q'.eqv_symm
                (Q'.mul_assoc_eqv
                  (coeffAt (heatKernelPacket cutoff anchorCoupling)
                    (physical head))
                  anchorFaceCoefficient
                  (eliminateLinks
                    (fun id => coeffAt
                      (heatKernelPacket cutoff anchorCoupling)
                      (lowerSlabFace physical faceId id)) tail))
            · refine Q'.eqv_trans _
                ((anchorFaceCoefficient *
                    coeffAt (heatKernelPacket cutoff anchorCoupling)
                      (physical head)) *
                  eliminateLinks
                    (fun id => coeffAt
                      (heatKernelPacket cutoff anchorCoupling)
                      (lowerSlabFace physical faceId id)) tail) _ ?_ ?_
              · exact Q'.mul_eqv_congr_right _ _ _
                  (Q'.mul_comm_eqv _ _)
              · exact Q'.mul_assoc_eqv _ _ _))

/-- **One-face anchor payment on the literal corrected-slab product.**
If a displayed physical face has positive label within the packet cutoff,
then its unpeeled face product is at most `1 / 32,000,000` times the product
after lowering that face by one.  The constant is independent of cutoff,
extent, the selected spin, and every other face label. -/
theorem slabPhysicalFaceFactor_anchor_lower_one_le
    (cutoff extent : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hpositive : 0 < physical faceId)
    (hbounded : physical faceId <= cutoff) :
    slabParametricKPhysicalFaceFactor
        anchorCoupling cutoff extent physical <=
      anchorFaceCoefficient *
        slabParametricKPhysicalFaceFactor
          anchorCoupling cutoff extent
          (lowerSlabFace physical faceId) := by
  unfold slabParametricKPhysicalFaceFactor
  exact eliminateLinks_anchor_lower_one_le
    cutoff physical faceId hpositive hbounded
    (slabPhysicalFaceEdges extent)
    (by
      unfold slabPhysicalFaceEdges
      exact rangeNodupLocal _)
    hface

/-! ## 3. Compose a finite sequence of literal face-strand peels -/

/-- A constructive sequence of legal one-face peels.  Every step retains the
literal physical face identifier, positivity of the current label, and its
packet bound as data.  A global strand component will later construct exactly
this object from its distinct face-copy vertices. -/
inductive SlabFacePeelPath (cutoff extent : Nat) :
    EdgeLabelling -> List Nat -> EdgeLabelling -> Type
  | nil (physical : EdgeLabelling) :
      SlabFacePeelPath cutoff extent physical [] physical
  | cons {physical target : EdgeLabelling} {faces : List Nat}
      (faceId : Nat)
      (face_mem : faceId ∈ slabPhysicalFaceEdges extent)
      (positive : 0 < physical faceId)
      (bounded : physical faceId <= cutoff)
      (tail : SlabFacePeelPath cutoff extent
        (lowerSlabFace physical faceId) faces target) :
      SlabFacePeelPath cutoff extent physical (faceId :: faces) target

/-- **Finite component-payment theorem.**  A legal path of `m` literal
face-strand peels costs at most

    (1 / 32,000,000)^m

in the complete corrected-slab face product.  The constant is exact and
independent of cutoff, extent, the spin heights, and the path shape. -/
theorem SlabFacePeelPath.faceFactor_le
    {cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabFacePeelPath cutoff extent source faces target) :
    slabParametricKPhysicalFaceFactor
        anchorCoupling cutoff extent source <=
      anchorFaceCoefficient ^ faces.length *
        slabParametricKPhysicalFaceFactor
          anchorCoupling cutoff extent target := by
  induction path with
  | nil physical =>
      simp only [List.length_nil, Q'.pow_zero]
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (slabParametricKPhysicalFaceFactor
              anchorCoupling cutoff extent physical)))
  | @cons physical target faces faceId hface hpositive hbounded tail ih =>
      have hone := slabPhysicalFaceFactor_anchor_lower_one_le
        cutoff extent physical faceId hface hpositive hbounded
      have hanchorNonnegative : (0 : Q') <= anchorFaceCoefficient := by
        unfold anchorFaceCoefficient
        decide
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
        ih hanchorNonnegative
      have hchain := Q'.le_trans' _ _ _ hone hscaled
      simp only [List.length_cons, Q'.pow_succ]
      exact Q'.le_trans' _ _ _ hchain
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv anchorFaceCoefficient
              (anchorFaceCoefficient ^ faces.length)
              (slabParametricKPhysicalFaceFactor
                anchorCoupling cutoff extent target))))

/-! ## 4. The same payment on the actual expanded BF4 fiber -/

/-- Unit Haar counting means that one expanded fiber entry is exactly its
physical face product. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) :
    retainedFineIntertwinerPhysicalFiberWeight D physical witness ≈
      slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent physical := by
  unfold retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
  exact Q'.mul_one_eqv _

/-- **Expanded one-strand weight comparison.**  At the actual anchor, any
expanded entry over a physical labelling is paid for by the exact factor
`1 / 32,000,000` after one positive face is lowered.  The witnesses may be
different because each accepted fine-intertwiner assignment has unit Haar
counting weight; the future component theorem must construct the accepted
lower witness. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_anchor_lower_one_le
    (cutoff half : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (hpositive : 0 < physical faceId)
    (hbounded : physical faceId <= cutoff) :
    let source : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        source physical sourceWitness <=
      anchorFaceCoefficient *
        retainedFineIntertwinerPhysicalFiberWeight
          source (lowerSlabFace physical faceId) targetWitness := by
  dsimp only
  have hfaceWeight := slabPhysicalFaceFactor_anchor_lower_one_le
    cutoff (centralExtent half) physical faceId
    hface hpositive hbounded
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        { coupling := anchorCoupling
          coupling_nonnegative := by decide
          cutoff := cutoff
          half := half }
        physical sourceWitness))
    (Q'.le_trans' _ _ _ hfaceWeight
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left anchorFaceCoefficient _ _
          (Q'.eqv_symm
            (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
              { coupling := anchorCoupling
                coupling_nonnegative := by decide
                cutoff := cutoff
                half := half }
              (lowerSlabFace physical faceId) targetWitness)))))

/-- **Expanded finite component-payment theorem.**  Unit Haar counting lifts
the composed face-product estimate unchanged to arbitrary source and target
fine-intertwiner entries.  Once the geometric component theorem constructs
an accepted target witness and a `SlabFacePeelPath`, no multiplicity factor
remains in the analytic comparison. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_anchor_peelPath_le
    (cutoff half : Nat) {sourcePhysical targetPhysical : EdgeLabelling}
    {faces : List Nat}
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (path : SlabFacePeelPath cutoff (centralExtent half)
      sourcePhysical faces targetPhysical) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        D sourcePhysical sourceWitness <=
      anchorFaceCoefficient ^ faces.length *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetWitness := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        { coupling := anchorCoupling
          coupling_nonnegative := by decide
          cutoff := cutoff
          half := half }
        sourcePhysical sourceWitness))
    (Q'.le_trans' _ _ _ path.faceFactor_le
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (anchorFaceCoefficient ^ faces.length) _ _
          (Q'.eqv_symm
            (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
              { coupling := anchorCoupling
                coupling_nonnegative := by decide
                cutoff := cutoff
                half := half }
              targetPhysical targetWitness)))))

/-! ## 5. Exact arithmetic reserve against the physical animal count -/

/-- The candidate per-face ratio obtained by charging the existing `Z^4`
physical-plaquette animal constant directly against the expanded-fiber peel
payment.  This becomes a genuine component-summation ratio only after the
geometric theorem injects inverse peel records into that physical animal code
without an additional exponential multiplicity. -/
def anchorExpandedFaceAnimalCandidateRatio : Q' :=
  animalK z4Chain * anchorFaceCoefficient

/-- The exact candidate ratio is `625 / 32,000,000 = 1 / 51,200`. -/
theorem anchorExpandedFaceAnimalCandidateRatio_eqv_one_51200 :
    anchorExpandedFaceAnimalCandidateRatio ≈
      Q'.mkPos 1 51200 (by decide) := by
  decide

/-- The analytic suppression has strict room against the existing physical
animal count.  This arithmetic theorem does not supply the still-open inverse
component encoding. -/
theorem anchorExpandedFaceAnimalCandidateRatio_lt_one :
    anchorExpandedFaceAnimalCandidateRatio < (1 : Q') := by
  decide

#print axioms anchorCoeffW_succ_le
#print axioms anchorPacketCoefficient_succ_le
#print axioms lowerSlabFace
#print axioms lowerSlabFace_selected
#print axioms lowerSlabFace_other
#print axioms slabPhysicalFaceFactor_anchor_lower_one_le
#print axioms SlabFacePeelPath
#print axioms SlabFacePeelPath.faceFactor_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
#print axioms retainedFineIntertwinerPhysicalFiberWeight_anchor_lower_one_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_anchor_peelPath_le
#print axioms anchorExpandedFaceAnimalCandidateRatio
#print axioms anchorExpandedFaceAnimalCandidateRatio_eqv_one_51200
#print axioms anchorExpandedFaceAnimalCandidateRatio_lt_one

end YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
