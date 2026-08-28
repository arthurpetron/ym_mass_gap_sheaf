/-
# Threshold-sensitive face-strand payment at arbitrary SU(2) coupling

The anchor component peel pays every positive spin by the bottom coefficient
`1 / 32,000,000`.  That estimate is deliberately strong-coupling: at weak
coupling the bottom successor ratio is not small.  The Casimir increment is,
however, increasingly suppressive at high spin.  This module isolates that
fact on the actual corrected-slab face product.

For `0 <= w <= 1`, every successor above a threshold `S` obeys

    coeffW w (s + 1) <= (2 * w^(2*S+3)) * coeffW w s,   S <= s.

A `SlabHighSpinFacePeelPath S` records exactly the legal geometric regime:
each selected face is lowered only while its current label is strictly above
`S`.  Thus the path stops on the finite low-spin core rather than pretending
that the weak-coupling bottom ratio is small.  Its corrected-slab and expanded
BF4 weights telescope at any declared rate dominating the displayed Casimir
ratio.

Finally, for every fixed rational `0 < w < 1`, an executable `powBaseCutoff`
threshold makes this high-spin ratio no larger than the existing anchor face
coefficient.  This recovers the exact entropy-payment constant in the exterior
while leaving the finite core explicit.  It does not construct the canonical
exterior component path or prove a core spectral gap.

Constructive contract: `Nat`/`Q'` recursion and finite-list induction only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The arbitrary-coupling exterior ratio -/

/-- The explicit high-spin successor ratio at coupling `w` above threshold
`threshold`.  Unlike the bottom ratio, this tends to zero with the threshold
at every fixed `0 < w < 1`. -/
def exteriorFaceCoefficient (w : Q') (threshold : Nat) : Q' :=
  Q'.ofNat 2 * qpow w (2 * threshold + 3)

theorem exteriorFaceCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w) (threshold : Nat) :
    (0 : Q') ≤ exteriorFaceCoefficient w threshold := by
  unfold exteriorFaceCoefficient
  exact Q'.mul_nonneg _ _ (zero_le_ofNat 2)
    (qpow_nonneg w hw0 (2 * threshold + 3))

/-- The SU(2) Casimir increment gives the threshold-sensitive coefficient
comparison.  This is the degree-one instance of `tailTerm_ratio_gen`. -/
theorem coeffW_exterior_succ_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (threshold spin : Nat) (hthreshold : threshold ≤ spin) :
    coeffW w (spin + 1) ≤
      exteriorFaceCoefficient w threshold * coeffW w spin := by
  rw [coeffW_eq_tailTerm w (spin + 1), coeffW_eq_tailTerm w spin]
  exact tailTerm_ratio_gen hw0 hw1 1 threshold spin hthreshold

/-- The same high-spin ratio holds in every finite packet containing the
successor label. -/
theorem packetCoefficient_exterior_succ_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (cutoff threshold spin : Nat)
    (hthreshold : threshold ≤ spin) (hbounded : spin + 1 ≤ cutoff) :
    coeffAt (heatKernelPacket cutoff w) (spin + 1) ≤
      exteriorFaceCoefficient w threshold *
        coeffAt (heatKernelPacket cutoff w) spin := by
  rw [coeffAt_heatKernelPacket (K := cutoff) (spin := spin + 1)
      (w := w) (by omega)]
  rw [coeffAt_heatKernelPacket (K := cutoff) (spin := spin)
      (w := w) (by omega)]
  exact coeffW_exterior_succ_le hw0 hw1 threshold spin hthreshold

/-! ## 2. One literal corrected-slab face -/

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

private theorem packetCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w) (cutoff spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket cutoff w) spin := by
  by_cases hspin : spin < cutoff + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw0 spin
  · have hlarge : cutoff < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket cutoff w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (cutoff : Nat) (physical : EdgeLabelling) :
    forall ids : List Nat,
      (0 : Q') ≤
        eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff w)
            (physical id)) ids
  | [] => Q'.zero_le_one
  | item :: rest =>
      Q'.mul_nonneg _ _
        (packetCoefficient_nonnegative hw0 cutoff (physical item))
        (eliminateLinks_nonnegative hw0 cutoff physical rest)

private theorem eliminateLinks_lowerSlabFace_eq_of_not_mem
    (w : Q') (cutoff : Nat) (physical : EdgeLabelling) (faceId : Nat) :
    forall ids : List Nat, faceId ∉ ids ->
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff w)
            (physical id)) ids =
        eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff w)
            (lowerSlabFace physical faceId id)) ids := by
  intro ids hnot
  apply YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.eliminateLinks_congr_eq
  intro id hid
  rw [lowerSlabFace_other physical (faceId := faceId)
    (id := id) (by
      intro heq
      subst id
      exact hnot hid)]

private theorem eliminateLinks_exterior_lower_one_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (cutoff threshold : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (hexterior : threshold < physical faceId)
    (hbounded : physical faceId ≤ cutoff) :
    forall ids : List Nat, ids.Nodup -> faceId ∈ ids ->
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket cutoff w)
            (physical id)) ids ≤
        exteriorFaceCoefficient w threshold *
          eliminateLinks
            (fun id => coeffAt (heatKernelPacket cutoff w)
              (lowerSlabFace physical faceId id)) ids := by
  intro ids hnodup hmem
  induction ids with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons head tail ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        have htailEq := eliminateLinks_lowerSlabFace_eq_of_not_mem
          w cutoff physical faceId tail hnodupParts.1
        have hspin : physical faceId - 1 + 1 = physical faceId := by
          omega
        have hcoeff := packetCoefficient_exterior_succ_le
          hw0 hw1 cutoff threshold (physical faceId - 1)
          (by omega) (by omega)
        rw [hspin] at hcoeff
        simp only [eliminateLinks]
        rw [lowerSlabFace_selected, ← htailEq]
        have htailNonnegative :
            (0 : Q') ≤
              eliminateLinks
                (fun id => coeffAt (heatKernelPacket cutoff w)
                  (physical id)) tail :=
          eliminateLinks_nonnegative hw0 cutoff physical tail
        have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _
          hcoeff htailNonnegative
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv
            (Q'.mul_assoc_eqv (exteriorFaceCoefficient w threshold)
              (coeffAt (heatKernelPacket cutoff w)
                (physical faceId - 1))
              (eliminateLinks
                (fun id => coeffAt (heatKernelPacket cutoff w)
                  (physical id)) tail)))
      · have hheadNe : head ≠ faceId := by
          intro heq
          subst head
          exact hnodupParts.1 htail
        have htailBound := ih hnodupParts.2 htail
        simp only [eliminateLinks]
        rw [lowerSlabFace_other physical hheadNe]
        have hheadNonnegative :=
          packetCoefficient_nonnegative hw0 cutoff (physical head)
        have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _
          htailBound hheadNonnegative
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv (by
            refine Q'.eqv_trans _
              ((coeffAt (heatKernelPacket cutoff w)
                  (physical head) * exteriorFaceCoefficient w threshold) *
                eliminateLinks
                  (fun id => coeffAt (heatKernelPacket cutoff w)
                    (lowerSlabFace physical faceId id)) tail) _ ?_ ?_
            · exact Q'.eqv_symm
                (Q'.mul_assoc_eqv
                  (coeffAt (heatKernelPacket cutoff w) (physical head))
                  (exteriorFaceCoefficient w threshold)
                  (eliminateLinks
                    (fun id => coeffAt (heatKernelPacket cutoff w)
                      (lowerSlabFace physical faceId id)) tail))
            · refine Q'.eqv_trans _
                (((exteriorFaceCoefficient w threshold) *
                    coeffAt (heatKernelPacket cutoff w) (physical head)) *
                  eliminateLinks
                    (fun id => coeffAt (heatKernelPacket cutoff w)
                      (lowerSlabFace physical faceId id)) tail) _ ?_ ?_
              · exact Q'.mul_eqv_congr_right _ _ _
                  (Q'.mul_comm_eqv _ _)
              · exact Q'.mul_assoc_eqv _ _ _))

/-- Lowering a selected face while its label is above `threshold` costs at
most the explicit high-spin Casimir ratio on the literal corrected-slab face
product. -/
theorem slabPhysicalFaceFactor_exterior_lower_one_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (cutoff extent threshold : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hexterior : threshold < physical faceId)
    (hbounded : physical faceId ≤ cutoff) :
    slabParametricKPhysicalFaceFactor w cutoff extent physical ≤
      exteriorFaceCoefficient w threshold *
        slabParametricKPhysicalFaceFactor w cutoff extent
          (lowerSlabFace physical faceId) := by
  unfold slabParametricKPhysicalFaceFactor
  exact eliminateLinks_exterior_lower_one_le
    hw0 hw1 cutoff threshold physical faceId hexterior hbounded
    (slabPhysicalFaceEdges extent)
    (by
      unfold slabPhysicalFaceEdges
      exact rangeNodupLocal _)
    hface

/-- Any larger nonnegative declared rate may replace the exact exterior
coefficient in the one-face payment. -/
theorem slabPhysicalFaceFactor_exterior_lower_one_le_of_rate
    {w rate : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (cutoff extent threshold : Nat) (physical : EdgeLabelling) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hexterior : threshold < physical faceId)
    (hbounded : physical faceId ≤ cutoff)
    (hpay : exteriorFaceCoefficient w threshold ≤ rate) :
    slabParametricKPhysicalFaceFactor w cutoff extent physical ≤
      rate * slabParametricKPhysicalFaceFactor w cutoff extent
        (lowerSlabFace physical faceId) := by
  have hone := slabPhysicalFaceFactor_exterior_lower_one_le
    hw0 hw1 cutoff extent threshold physical faceId
    hface hexterior hbounded
  have htargetNonnegative :
      (0 : Q') ≤ slabParametricKPhysicalFaceFactor w cutoff extent
        (lowerSlabFace physical faceId) := by
    unfold slabParametricKPhysicalFaceFactor
    exact eliminateLinks_nonnegative hw0 cutoff
      (lowerSlabFace physical faceId) (slabPhysicalFaceEdges extent)
  exact Q'.le_trans' _ _ _ hone
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hpay htargetNonnegative)

/-! ## 3. Paths which stop at the finite low-spin core -/

/-- A legal face-strand peel path constrained to the exterior of the finite
spin core `label <= threshold`.  Every step carries the strict exterior test,
so a face reaching `threshold` cannot be lowered again. -/
inductive SlabHighSpinFacePeelPath (threshold cutoff extent : Nat) :
    EdgeLabelling -> List Nat -> EdgeLabelling -> Type
  | nil (physical : EdgeLabelling) :
      SlabHighSpinFacePeelPath threshold cutoff extent physical [] physical
  | cons {physical target : EdgeLabelling} {faces : List Nat}
      (faceId : Nat)
      (face_mem : faceId ∈ slabPhysicalFaceEdges extent)
      (exterior : threshold < physical faceId)
      (bounded : physical faceId ≤ cutoff)
      (tail : SlabHighSpinFacePeelPath threshold cutoff extent
        (lowerSlabFace physical faceId) faces target) :
      SlabHighSpinFacePeelPath threshold cutoff extent
        physical (faceId :: faces) target

/-- Forgetting the high-spin tests leaves an ordinary legal peel path. -/
def SlabHighSpinFacePeelPath.toFacePeelPath
    {threshold cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabHighSpinFacePeelPath threshold cutoff extent
      source faces target) :
    SlabFacePeelPath cutoff extent source faces target :=
  match path with
  | .nil physical => SlabFacePeelPath.nil physical
  | .cons faceId hface hexterior hbounded tail =>
      SlabFacePeelPath.cons faceId hface (by omega) hbounded
        tail.toFacePeelPath

/-- A threshold-respecting path telescopes at any nonnegative rate dominating
the explicit exterior coefficient. -/
theorem SlabHighSpinFacePeelPath.faceFactor_le_of_rate
    {w rate : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hrate : (0 : Q') ≤ rate)
    {threshold cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabHighSpinFacePeelPath threshold cutoff extent
      source faces target)
    (hpay : exteriorFaceCoefficient w threshold ≤ rate) :
    slabParametricKPhysicalFaceFactor w cutoff extent source ≤
      rate ^ faces.length *
        slabParametricKPhysicalFaceFactor w cutoff extent target := by
  induction path with
  | nil physical =>
      simp only [List.length_nil, Q'.pow_zero]
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (slabParametricKPhysicalFaceFactor
              w cutoff extent physical)))
  | @cons physical target faces faceId hface hexterior hbounded tail ih =>
      have hone := slabPhysicalFaceFactor_exterior_lower_one_le_of_rate
        hw0 hw1 cutoff extent threshold physical faceId
        hface hexterior hbounded hpay
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ ih hrate
      have hchain := Q'.le_trans' _ _ _ hone hscaled
      simp only [List.length_cons, Q'.pow_succ]
      exact Q'.le_trans' _ _ _ hchain
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv rate (rate ^ faces.length)
              (slabParametricKPhysicalFaceFactor
                w cutoff extent target))))

/-- The exact coefficient is itself an admissible telescope rate. -/
theorem SlabHighSpinFacePeelPath.faceFactor_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {threshold cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabHighSpinFacePeelPath threshold cutoff extent
      source faces target) :
    slabParametricKPhysicalFaceFactor w cutoff extent source ≤
      exteriorFaceCoefficient w threshold ^ faces.length *
        slabParametricKPhysicalFaceFactor w cutoff extent target := by
  exact path.faceFactor_le_of_rate hw0 hw1
    (exteriorFaceCoefficient_nonnegative hw0 threshold)
    (Q'.le_refl' _)

/-! ## 4. Lift the exterior telescope to the expanded BF4 fiber -/

/-- Unit Haar counting lifts the arbitrary-coupling exterior path payment to
any source and target retained fine-intertwiner witnesses. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_exterior_peelPath_le_of_rate
    {w rate : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hrate : (0 : Q') ≤ rate)
    (cutoff half threshold : Nat)
    {sourcePhysical targetPhysical : EdgeLabelling} {faces : List Nat}
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (path : SlabHighSpinFacePeelPath threshold cutoff (centralExtent half)
      sourcePhysical faces targetPhysical)
    (hpay : exteriorFaceCoefficient w threshold ≤ rate) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        D sourcePhysical sourceWitness ≤
      rate ^ faces.length *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetWitness := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        { coupling := w
          coupling_nonnegative := hw0
          cutoff := cutoff
          half := half }
        sourcePhysical sourceWitness))
    (Q'.le_trans' _ _ _
      (path.faceFactor_le_of_rate hw0 hw1 hrate hpay)
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left (rate ^ faces.length) _ _
          (Q'.eqv_symm
            (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
              { coupling := w
                coupling_nonnegative := hw0
                cutoff := cutoff
                half := half }
              targetPhysical targetWitness)))))

/-! ## 5. An executable threshold recovering the anchor entropy payment -/

/-- Power target whose double is the exact anchor face coefficient. -/
def anchorPaidExteriorPowerTarget : Q' :=
  Q'.mkPos 1 64000000 (by decide)

/-- At fixed `0 < w < 1`, this executable threshold pushes the high-spin
successor ratio below the existing anchor payment. -/
def anchorPaidExteriorThreshold (w : Q') : Nat :=
  powBaseCutoff w anchorPaidExteriorPowerTarget

theorem anchorPaidExteriorThreshold_power_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    qpow w (anchorPaidExteriorThreshold w) ≤
      anchorPaidExteriorPowerTarget := by
  have hpow :
      w ^ anchorPaidExteriorThreshold w ≤
        anchorPaidExteriorPowerTarget := by
    exact pow_base_le_cutoff hw0 hw1 (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.SU2PointwiseHeatSpacingCompletion.qpow_eqv_pow
        w (anchorPaidExteriorThreshold w)))
    hpow

/-- The explicit fixed-coupling threshold makes the exterior successor ratio
no larger than `1 / 32,000,000`, exactly the rate already paid by the adaptive
component entropy carrier. -/
theorem exteriorFaceCoefficient_anchorPaidThreshold_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    exteriorFaceCoefficient w (anchorPaidExteriorThreshold w) ≤
      anchorFaceCoefficient := by
  have hmono :
      qpow w (2 * anchorPaidExteriorThreshold w + 3) ≤
        qpow w (anchorPaidExteriorThreshold w) :=
    qpow_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (anchorPaidExteriorThreshold w)
      (2 * anchorPaidExteriorThreshold w + 3) (by omega)
  have hpower := anchorPaidExteriorThreshold_power_le hw0 hw1
  have hscaled :
      Q'.ofNat 2 * qpow w (2 * anchorPaidExteriorThreshold w + 3) ≤
        Q'.ofNat 2 * anchorPaidExteriorPowerTarget :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hmono hpower) (zero_le_ofNat 2)
  refine Q'.le_trans' _ _ _ hscaled ?_
  unfold anchorPaidExteriorPowerTarget anchorFaceCoefficient
  decide

/-- At the executable threshold, every high-spin peel path pays the same
per-copy rate as the strong-coupling anchor theorem, now for arbitrary fixed
`0 < w < 1`.  The target is the finite low-spin core at that threshold. -/
theorem SlabHighSpinFacePeelPath.faceFactor_anchorPaid_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {cutoff extent : Nat} {source target : EdgeLabelling} {faces : List Nat}
    (path : SlabHighSpinFacePeelPath
      (anchorPaidExteriorThreshold w) cutoff extent source faces target) :
    slabParametricKPhysicalFaceFactor w cutoff extent source ≤
      anchorFaceCoefficient ^ faces.length *
        slabParametricKPhysicalFaceFactor w cutoff extent target := by
  exact path.faceFactor_le_of_rate
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (by decide)
    (exteriorFaceCoefficient_anchorPaidThreshold_le hw0 hw1)

/-- Expanded-fiber form of the fixed-coupling exterior payment at the anchor
entropy rate. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_exterior_anchorPaid_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat)
    {sourcePhysical targetPhysical : EdgeLabelling} {faces : List Nat}
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (path : SlabHighSpinFacePeelPath
      (anchorPaidExteriorThreshold w) cutoff (centralExtent half)
      sourcePhysical faces targetPhysical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        D sourcePhysical sourceWitness ≤
      anchorFaceCoefficient ^ faces.length *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetWitness := by
  exact retainedFineIntertwinerPhysicalFiberWeight_exterior_peelPath_le_of_rate
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (by decide)
    cutoff half (anchorPaidExteriorThreshold w)
    sourceWitness targetWitness path
    (exteriorFaceCoefficient_anchorPaidThreshold_le hw0 hw1)

#print axioms exteriorFaceCoefficient
#print axioms exteriorFaceCoefficient_nonnegative
#print axioms coeffW_exterior_succ_le
#print axioms packetCoefficient_exterior_succ_le
#print axioms slabPhysicalFaceFactor_exterior_lower_one_le
#print axioms slabPhysicalFaceFactor_exterior_lower_one_le_of_rate
#print axioms SlabHighSpinFacePeelPath
#print axioms SlabHighSpinFacePeelPath.toFacePeelPath
#print axioms SlabHighSpinFacePeelPath.faceFactor_le_of_rate
#print axioms SlabHighSpinFacePeelPath.faceFactor_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_exterior_peelPath_le_of_rate
#print axioms anchorPaidExteriorPowerTarget
#print axioms anchorPaidExteriorThreshold
#print axioms anchorPaidExteriorThreshold_power_le
#print axioms exteriorFaceCoefficient_anchorPaidThreshold_le
#print axioms SlabHighSpinFacePeelPath.faceFactor_anchorPaid_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_exterior_anchorPaid_le

end YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
