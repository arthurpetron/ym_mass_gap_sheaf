/-
# Production target congestion for the all-source inward-mate transport

The all-source production transport retains every successful source and hence
the full `41/425` source mass.  Its target marginal is necessarily many-to-one.
This module proves that those collisions are exactly controlled by the
previous finite target key.

Equality of production target atoms recovers equality of the positional
residual codes.  Their auxiliary-word coordinate, together with the physical
coordinate of the atom, reconstructs the exact target key.  Conversely, equal
exact target keys compile to equal production atoms.  Therefore the production
target fibers are literally the previously bounded key fibers: their
cardinality is at most sixty-four and their incoming production source weight
is bounded by the existing six-face mate cost.

This is still a full-slab transport congestion theorem, not an identification
with the actual BF4 conditional/OS joint.  No posterior variance, OS form
bound, spectral gap, beta/lattice-spacing uniformity, or continuum theorem is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem prod_eq_of_fields_eq_local
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hleft : leftA = rightA) (hright : leftB = rightB) :
    (leftA, leftB) = (rightA, rightB) := by
  cases hleft
  cases hright
  rfl

/-! ## 1. Production target atoms and exact target keys agree -/

/-- Equal compiled production target atoms have equal original exact target
keys, on arbitrary successful sources. -/
theorem globalInwardMateTargetKey_eq_of_targetProductionAtom_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hatom :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom right) :
    globalInwardMateTargetKey left = globalInwardMateTargetKey right := by
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right := by
    have hprojection := congrArg Prod.fst hatom
    simpa only [
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom]
      using hprojection
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw right := by
    have hprojection := congrArg Prod.snd hatom
    simpa only [
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom]
      using hprojection
  have hleftCode :=
    GlobalCubeInwardMateCertifiedTargetFullSource.targetResidualCode_mem_allSources
      left
  have hrightCode :=
    GlobalCubeInwardMateCertifiedTargetFullSource.targetResidualCode_mem_allSources
      right
  rw [← hphysical] at hrightCode
  have hcode :
      globalInwardMateTargetRepresentativeResidualCode left =
        globalInwardMateTargetRepresentativeResidualCode right := by
    apply globalInwardMateProductionRawAt_injective
      K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded left)
      hleftCode hrightCode
    unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw at hraw
    rw [← hphysical] at hraw
    exact hraw
  have hpresentedWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right) := by
    have hprojection := congrArg Prod.snd hcode
    simpa only [globalInwardMateTargetRepresentativeResidualCode] using
      hprojection
  have htargetRaw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right :=
    globalTargetRaw_eq_of_auxiliaryWords_eq left right hpresentedWords
  apply globalTargetKey_eq_of_targetAtom_eq left right
  calc
    GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) :=
      globalTargetAtom_eq left
    _ = (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) := by
      exact prod_eq_of_fields_eq_local hphysical htargetRaw
    _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right :=
      (globalTargetAtom_eq right).symm

/-- Conversely, equal exact target keys compile to equal production target
atoms. -/
theorem globalInwardMateTargetProductionAtom_eq_of_targetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateTargetKey left =
      globalInwardMateTargetKey right) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom left =
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom right := by
  have hatom := globalTargetAtom_eq_of_targetKey_eq left right hkey
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right := by
    have hpair :
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
            GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) =
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
            GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) := by
      calc
        _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left :=
          (globalTargetAtom_eq left).symm
        _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right := hatom
        _ = _ := globalTargetAtom_eq right
    exact congrArg Prod.fst hpair
  have hauxiliaryWords :
      globalInwardMateTargetAuxiliaryWords left =
        globalInwardMateTargetAuxiliaryWords right :=
    congrArg GlobalInwardMateTargetKey.auxiliaryWords hkey
  have hpresentedWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right) := by
    calc
      _ = globalInwardMateTargetAuxiliaryWords left :=
        (globalInwardMateTargetAuxiliaryWords_eq left).symm
      _ = globalInwardMateTargetAuxiliaryWords right := hauxiliaryWords
      _ = _ := globalInwardMateTargetAuxiliaryWords_eq right
  have hcode :
      globalInwardMateTargetRepresentativeResidualCode left =
        globalInwardMateTargetRepresentativeResidualCode right := by
    unfold globalInwardMateTargetRepresentativeResidualCode
    exact prod_eq_of_fields_eq_local rfl hpresentedWords
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
  apply Prod.ext
  · exact hphysical
  · unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw
    rw [hphysical, hcode]

/-- Equality of compiled production targets is exactly equality of the
established finite target key. -/
theorem globalInwardMateTargetProductionAtom_eq_iff_targetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom right ↔
      globalInwardMateTargetKey left = globalInwardMateTargetKey right :=
  ⟨globalInwardMateTargetKey_eq_of_targetProductionAtom_eq left right,
    globalInwardMateTargetProductionAtom_eq_of_targetKey_eq left right⟩

/-! ## 2. A decidable production-target key and its exact fiber -/

/-- The finite production-support key of the target compiled from one
successful source. -/
def globalInwardMateProductionTargetKey
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabExpandedFineTargetKey :=
  slabExpandedFineTargetKey (globalInwardMateAnchorSlabData K)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source).1
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source).2

/-- Equality of production-support keys recovers equality of the original
exact target keys. -/
theorem globalInwardMateTargetKey_eq_of_productionTargetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateProductionTargetKey left =
      globalInwardMateProductionTargetKey right) :
    globalInwardMateTargetKey left = globalInwardMateTargetKey right := by
  apply globalInwardMateTargetKey_eq_of_targetProductionAtom_eq left right
  exact slabExpandedFineTargetKey_eq_source_eq
    (globalInwardMateAnchorSlabData K)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem_allSources
      left)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem_allSources
      right)
    hkey

/-- Equal original target keys have equal finite production-support keys. -/
theorem globalInwardMateProductionTargetKey_eq_of_targetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateTargetKey left =
      globalInwardMateTargetKey right) :
    globalInwardMateProductionTargetKey left =
      globalInwardMateProductionTargetKey right := by
  exact congrArg
    (fun atom : SlabLabelling × SlabFusionWitnessAssignment =>
      slabExpandedFineTargetKey (globalInwardMateAnchorSlabData K)
        atom.1 atom.2)
    (globalInwardMateTargetProductionAtom_eq_of_targetKey_eq left right hkey)

/-- The production-target key and the original exact target key induce the
same equivalence relation on successful sources. -/
theorem globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateProductionTargetKey left =
        globalInwardMateProductionTargetKey right ↔
      globalInwardMateTargetKey left = globalInwardMateTargetKey right :=
  ⟨globalInwardMateTargetKey_eq_of_productionTargetKey_eq left right,
    globalInwardMateProductionTargetKey_eq_of_targetKey_eq left right⟩

/-- The literal successful-source fiber over one compiled production target. -/
def globalInwardMateProductionTargetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (globalCubeInwardMateCertifiedTargetFullSources K hK).filter
    (fun source => decide
      (globalInwardMateProductionTargetKey source =
        globalInwardMateProductionTargetKey representative))

/-- Production-target fibers are literally the established exact-key fibers. -/
theorem globalInwardMateProductionTargetFiber_eq_targetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateProductionTargetFiber representative =
      globalInwardMateTargetFiber representative := by
  unfold globalInwardMateProductionTargetFiber globalInwardMateTargetFiber
  apply List.filter_congr
  intro source _hsource
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hproduction
    apply decide_eq_true
    exact
      (globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
        source representative).mp (of_decide_eq_true hproduction)
  · intro hexact
    apply decide_eq_true
    exact
      (globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
        source representative).mpr (of_decide_eq_true hexact)

/-! ## 3. Transfer cardinal and weighted congestion -/

/-- Every compiled production target has at most sixty-four successful source
preimages. -/
theorem globalInwardMateProductionTargetFiber_length_le_sixtyFour
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (globalInwardMateProductionTargetFiber representative).length ≤ 64 := by
  rw [globalInwardMateProductionTargetFiber_eq_targetFiber representative]
  exact globalInwardMateTargetFiber_length_le_sixtyFour representative

/-- Summed production source weight over one compiled target fiber is bounded
by sixty-four copies of the six-face mate cost times that production target's
weight. -/
theorem globalInwardMateProductionTargetFiber_sourceWeight_le_sixtyFour_mateCost
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        (globalInwardMateProductionTargetFiber representative) ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative) := by
  have hsourceWeights :
      listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
          (globalInwardMateProductionTargetFiber representative) ≈
        listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.weight
          (globalInwardMateProductionTargetFiber representative) := by
    apply listQSum_congr
    intro source
    exact
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
        source
  have hcongestion :
      listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.weight
          (globalInwardMateProductionTargetFiber representative) ≤
        Q'.ofNat 64 *
          (anchorInwardMateCost ^ 6 *
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
              representative) := by
    rw [globalInwardMateProductionTargetFiber_eq_targetFiber representative]
    exact globalInwardMateTargetFiber_weight_le_sixtyFour_mateCost
      representative
  have htargetWeight :
      Q'.ofNat 64 *
          (anchorInwardMateCost ^ 6 *
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
              representative) ≈
        Q'.ofNat 64 *
          (anchorInwardMateCost ^ 6 *
            GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
              representative) :=
    Q'.mul_eqv_congr_left (Q'.ofNat 64) _ _
      (Q'.mul_eqv_congr_left (anchorInwardMateCost ^ 6) _ _
        (Q'.eqv_symm
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight_eqv_targetWeight
            representative)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsourceWeights)
    (Q'.le_trans' _ _ _ hcongestion (Q'.le_of_eqv htargetWeight))

/-- Type-level certificate for exact compiled-target collision control. -/
structure GlobalInwardMateProductionTargetCongestionCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  targetKey : GlobalCubeInwardMateCertifiedTargetFullSource K hK →
    SlabExpandedFineTargetKey
  fiber : GlobalCubeInwardMateCertifiedTargetFullSource K hK →
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  key_exact : ∀ left right,
    targetKey left = targetKey right ↔
      globalInwardMateTargetKey left = globalInwardMateTargetKey right
  fiber_eq : ∀ representative,
    fiber representative = globalInwardMateTargetFiber representative
  capacity : ∀ representative, (fiber representative).length ≤ 64
  incomingSourceWeight_le : ∀ representative,
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        (fiber representative) ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative)

/-- Construct the all-source production-target congestion certificate. -/
def globalInwardMateProductionTargetCongestionCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateProductionTargetCongestionCertificate K hK where
  targetKey := globalInwardMateProductionTargetKey
  fiber := globalInwardMateProductionTargetFiber
  key_exact := globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
  fiber_eq := globalInwardMateProductionTargetFiber_eq_targetFiber
  capacity := globalInwardMateProductionTargetFiber_length_le_sixtyFour
  incomingSourceWeight_le :=
    globalInwardMateProductionTargetFiber_sourceWeight_le_sixtyFour_mateCost

#print axioms globalInwardMateTargetKey_eq_of_targetProductionAtom_eq
#print axioms globalInwardMateTargetProductionAtom_eq_of_targetKey_eq
#print axioms globalInwardMateTargetProductionAtom_eq_iff_targetKey_eq
#print axioms globalInwardMateProductionTargetKey
#print axioms globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
#print axioms globalInwardMateProductionTargetFiber_eq_targetFiber
#print axioms globalInwardMateProductionTargetFiber_length_le_sixtyFour
#print axioms globalInwardMateProductionTargetFiber_sourceWeight_le_sixtyFour_mateCost
#print axioms GlobalInwardMateProductionTargetCongestionCertificate
#print axioms globalInwardMateProductionTargetCongestionCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
