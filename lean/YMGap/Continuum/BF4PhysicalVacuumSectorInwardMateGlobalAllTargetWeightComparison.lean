/-
# Six-face anchor weight comparison for the global inward mate

The global all-target source and its realized target differ on exactly the
six central lower cube faces.  This module factors the complete extent-one
face product into those six coordinates and their unchanged complement.  A
general finite-product lemma then multiplies the exact anchor comparison only
six times, yielding

  source atom weight <= 32,000,000^6 * target atom weight.

The constant explicitly belongs to the `w = 1/400` anchor and is independent
of the representation cutoff.  It is not asserted uniformly in beta or
lattice spacing.  No target-fiber capacity, summed transport, posterior
variance, OS form bound, or spectral gap is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
import YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
import YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
import YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeightComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A reusable finite-product cost lemma -/

private theorem rearrange_pointwise_products
    (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num *
      (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem eliminateLinks_nonnegative
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') ≤ value id) :
    ∀ ids : List Nat, (0 : Q') ≤ eliminateLinks value ids
  | [] => Q'.zero_le_one
  | id :: rest =>
      Q'.mul_nonneg _ _ (hvalue id)
        (eliminateLinks_nonnegative value hvalue rest)

/-- Multiplying a pointwise cost over a displayed finite list pays exactly
one power per displayed coordinate. -/
private theorem eliminateLinks_le_cost_pow_mul
    (source target : Nat → Q') (cost : Q')
    (hsource : ∀ id, (0 : Q') ≤ source id)
    (htarget : ∀ id, (0 : Q') ≤ target id)
    (hcost : (0 : Q') ≤ cost) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → source id ≤ cost * target id) →
      eliminateLinks source ids ≤
        cost ^ ids.length * eliminateLinks target ids
  | [], _ => by
      change (1 : Q') ≤ 1 * 1
      exact Q'.ge_of_eqv (Q'.one_mul_eqv 1)
  | id :: rest, hpoint => by
      have htail := eliminateLinks_le_cost_pow_mul
        source target cost hsource htarget hcost rest
        (fun item hitem =>
          hpoint item (List.mem_cons_of_mem id hitem))
      have hsourceTail : (0 : Q') ≤ eliminateLinks source rest :=
        eliminateLinks_nonnegative source hsource rest
      have hcostTarget : (0 : Q') ≤ cost * target id :=
        Q'.mul_nonneg _ _ hcost (htarget id)
      have hhead := Q'.mul_le_mul_of_nonneg_right _ _ _
        (hpoint id List.mem_cons_self) hsourceTail
      have htailScaled := Q'.mul_le_mul_of_nonneg_left _ _ _
        htail hcostTarget
      simp only [eliminateLinks, List.length_cons, Q'.pow_succ]
      exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hhead htailScaled)
        (Q'.le_of_eqv
          (rearrange_pointwise_products cost (target id)
            (cost ^ rest.length) (eliminateLinks target rest)))

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
        eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hagree =>
      qmul_congr
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

/-! ## 2. Exact central-cube/complement factorization -/

/-- The displayed extent-one faces are exactly the six selected cube faces
followed by their literal complement, up to finite permutation. -/
theorem slabPhysicalFaceEdges_one_perm_cube_append_complement :
    (slabPhysicalFaceEdges 1).Perm
      (centralLowerCubeFaceIds ++ centralSpinCubeNonSourceFaceIds) := by
  exact natListPerm_of_check _ _ (by decide)

/-- For any bounded physical field, split its actual anchor face factor into
the selected six-face product and the unchanged complement product. -/
theorem slabAnchorPhysicalFaceFactor_eqv_cube_mul_complement
    {K : Nat} (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 physical) :
    slabParametricKPhysicalFaceFactor anchorCoupling K 1 physical ≈
      eliminateLinks
          (fun id => coeffW anchorCoupling (physical id))
          centralLowerCubeFaceIds *
        eliminateLinks
          (fun id => coeffW anchorCoupling (physical id))
          centralSpinCubeNonSourceFaceIds := by
  unfold slabParametricKPhysicalFaceFactor
  have hcoeff :
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket K anchorCoupling)
            (physical id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks
          (fun id => coeffW anchorCoupling (physical id))
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on
    intro id hid
    exact Q'.eqv_of_eq
      (coeffAt_heatKernelPacket (by
        have hle := hbounded id hid
        omega))
  exact Q'.eqv_trans _ _ _ hcoeff
    (Q'.eqv_trans _ _ _
      (eliminateLinks_perm _
        slabPhysicalFaceEdges_one_perm_cube_append_complement)
      (eliminateLinks_append _ centralLowerCubeFaceIds
        centralSpinCubeNonSourceFaceIds))

/-- The physical mate is literally unchanged on the complementary face
product. -/
theorem target_complement_heat_eqv_source
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    eliminateLinks
        (fun id => coeffW anchorCoupling
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
            source id))
        centralSpinCubeNonSourceFaceIds ≈
      eliminateLinks
        (fun id => coeffW anchorCoupling (source.physical id))
        centralSpinCubeNonSourceFaceIds := by
  apply eliminateLinks_congr_on
  intro id hid
  have hnot : id ∉ centralLowerCubeFaceIds := by
    have htest := (List.mem_filter.mp hid).2
    simpa [centralSpinCubeNonSourceFaceIds] using htest
  rw [GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical,
    centralLowerCubeEvenInwardMatePhysical_off_cube source.physical hnot]
  exact Q'.eqv_refl _

/-! ## 3. Pay the anchor cost on exactly six faces -/

/-- The selected cube-face heat product pays precisely six copies of the
actual anchor mate cost. -/
theorem source_cube_heat_le_six_mate_cost
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    eliminateLinks
        (fun id => coeffW anchorCoupling (source.physical id))
        centralLowerCubeFaceIds ≤
      anchorInwardMateCost ^ 6 *
        eliminateLinks
          (fun id => coeffW anchorCoupling
            (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
              source id))
          centralLowerCubeFaceIds := by
  have hproduct := eliminateLinks_le_cost_pow_mul
    (fun id => coeffW anchorCoupling (source.physical id))
    (fun id => coeffW anchorCoupling
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source id))
    anchorInwardMateCost
    (fun id => coeffW_nonneg (w := anchorCoupling) (by decide)
      (source.physical id))
    (fun id => coeffW_nonneg (w := anchorCoupling) (by decide)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source id))
    (by
      unfold anchorInwardMateCost
      decide)
    centralLowerCubeFaceIds
    (fun id hid => by
      change coeffW anchorCoupling (source.physical id) ≤
        anchorInwardMateCost *
          coeffW anchorCoupling
            (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
              source id)
      rw [GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical,
        centralLowerCubeEvenInwardMatePhysical_on_cube source.physical hid]
      exact coeffW_anchor_le_cost_evenInwardMate (source.physical id))
  have hlength : centralLowerCubeFaceIds.length = 6 := by decide
  simpa only [hlength] using hproduct

/-- **Complete six-face anchor comparison.**  The genuine source face factor
is at most `32,000,000^6` times the realized target face factor. -/
theorem source_faceFactor_le_six_mate_cost_mul_target
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    slabParametricKPhysicalFaceFactor anchorCoupling K 1 source.physical ≤
      anchorInwardMateCost ^ 6 *
        slabParametricKPhysicalFaceFactor anchorCoupling K 1
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
            source) := by
  let sourceCube := eliminateLinks
    (fun id => coeffW anchorCoupling (source.physical id))
    centralLowerCubeFaceIds
  let targetCube := eliminateLinks
    (fun id => coeffW anchorCoupling
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source id))
    centralLowerCubeFaceIds
  let sourceComplement := eliminateLinks
    (fun id => coeffW anchorCoupling (source.physical id))
    centralSpinCubeNonSourceFaceIds
  let targetComplement := eliminateLinks
    (fun id => coeffW anchorCoupling
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source id))
    centralSpinCubeNonSourceFaceIds
  have hsourceSplit :=
    slabAnchorPhysicalFaceFactor_eqv_cube_mul_complement source.physical
      (cubeInwardMatePhysicalBoundedOfMem
        K source.physical source.physicalSource.2)
  have htargetSplit :=
    slabAnchorPhysicalFaceFactor_eqv_cube_mul_complement
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded
        source)
  have hcube : sourceCube ≤ anchorInwardMateCost ^ 6 * targetCube :=
    source_cube_heat_le_six_mate_cost source
  have hcomplement : targetComplement ≈ sourceComplement :=
    target_complement_heat_eqv_source source
  have hsourceComplement0 : (0 : Q') ≤ sourceComplement :=
    eliminateLinks_nonnegative _
      (fun id => coeffW_nonneg (w := anchorCoupling) (by decide)
        (source.physical id)) _
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcube
    hsourceComplement0
  have hright :
      (anchorInwardMateCost ^ 6 * targetCube) * sourceComplement ≈
        anchorInwardMateCost ^ 6 *
          slabParametricKPhysicalFaceFactor anchorCoupling K 1
            (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
              source) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left (anchorInwardMateCost ^ 6) _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left targetCube _ _
            (Q'.eqv_symm hcomplement))
          (Q'.eqv_symm htargetSplit)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsourceSplit)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- The same comparison on the actual source and target BF4 retained-fiber
atoms. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.weight_le_six_mate_cost_mul_targetWeight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    source.weight ≤ anchorInwardMateCost ^ 6 *
      GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight source := by
  have hface := source_faceFactor_le_six_mate_cost_mul_target source
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.weight
    cubeInwardMateCertifiedTargetFullSourceWeight
  exact Q'.le_trans' _ _ _ hface
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (anchorInwardMateCost ^ 6) _ _
        (Q'.eqv_symm
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
            source))))

#print axioms slabPhysicalFaceEdges_one_perm_cube_append_complement
#print axioms slabAnchorPhysicalFaceFactor_eqv_cube_mul_complement
#print axioms target_complement_heat_eqv_source
#print axioms source_cube_heat_le_six_mate_cost
#print axioms source_faceFactor_le_six_mate_cost_mul_target
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.weight_le_six_mate_cost_mul_targetWeight

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeightComparison
