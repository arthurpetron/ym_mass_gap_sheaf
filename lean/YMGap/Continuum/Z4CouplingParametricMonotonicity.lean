/-
# Monotonicity of finite physical laws in the heat-kernel coupling

Every coefficient, physical spin-foam term, finite partition, and Boolean
event numerator is monotone when the nonnegative rational coupling increases.
The proof is entirely termwise and keeps the physical cutoff and volume fixed.

This is the comparison input needed by the coupling-shifted block law.  It is
not itself an RG defect estimate: normalization divides two monotone
quantities, so probability monotonicity does not follow without an additional
insertion/deletion or correlation argument.
-/

import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw

namespace YMGap.Continuum.Z4CouplingParametricMonotonicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem parametricCoefficient_nonnegative_local
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket cutoff coupling) spin := by
  by_cases hspin : spin < cutoff + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hcoupling spin
  · have hlarge : cutoff < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket cutoff coupling) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem eliminateLinks_mono_local
    (lower upper : Nat → Q')
    (hlower0 : ∀ edge, (0 : Q') ≤ lower edge)
    (hupper0 : ∀ edge, (0 : Q') ≤ upper edge) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → lower edge ≤ upper edge) →
      eliminateLinks lower edges ≤ eliminateLinks upper edges
  | [], _ => Q'.le_refl' 1
  | edge :: rest, hle => by
      have htail := eliminateLinks_mono_local lower upper hlower0 hupper0 rest
        (fun item hitem => hle item (List.mem_cons_of_mem edge hitem))
      have hlowerTail0 := eliminateLinks_nonnegative_local lower hlower0 rest
      have hupperHead0 := hupper0 edge
      have hhead : lower edge * eliminateLinks lower rest ≤
          upper edge * eliminateLinks lower rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (hle edge List.mem_cons_self) hlowerTail0
      have hrest : upper edge * eliminateLinks lower rest ≤
          upper edge * eliminateLinks upper rest :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail hupperHead0
      exact Q'.le_trans' _ _ _ hhead hrest

/-! ## 1. Termwise coupling monotonicity -/

theorem parametricKPhysicalFaceFactor_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    {cutoff n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalFaceFactor lower cutoff n physical ≤
      parametricKPhysicalFaceFactor upper cutoff n physical := by
  have hupper : (0 : Q') ≤ upper := Q'.le_trans' _ _ _ hlower hle
  unfold parametricKPhysicalFaceFactor
  apply eliminateLinks_mono_local
  · intro edge
    exact parametricCoefficient_nonnegative_local hlower cutoff (physical edge)
  · intro edge
    exact parametricCoefficient_nonnegative_local hupper cutoff (physical edge)
  · intro edge hedge
    have hsound := boundedEdgeLabellings_sound cutoff
      (List.range (plaquetteEdgeCount n)) physical hphysical
    have hspin := hsound.1 edge hedge
    rw [coeffAt_heatKernelPacket hspin, coeffAt_heatKernelPacket hspin]
    exact coeffW_mono_w hlower hle (physical edge)

theorem parametricKPhysicalTerm_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    {cutoff n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm lower cutoff n physical ≤
      parametricKPhysicalTerm upper cutoff n physical := by
  unfold parametricKPhysicalTerm
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (parametricKPhysicalFaceFactor_mono_coupling hlower hle hphysical)
    (explicitLinkMultiplicityProduct_nonnegative cutoff n physical
      (enumerate (distinctBoxLinks n)))

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

/-! ## 2. Partitions and event numerators -/

theorem parametricKPhysicalPartition_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (cutoff n : Nat) :
    parametricKPhysicalPartition lower cutoff n ≤
      parametricKPhysicalPartition upper cutoff n := by
  unfold parametricKPhysicalPartition
  apply listQSum_mono_local
  intro physical hphysical
  exact parametricKPhysicalTerm_mono_coupling hlower hle hphysical

/-- The canonical cutoff-one connected-polymer activity inherits the same
coupling monotonicity. -/
theorem canonicalSurfaceActivity_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity lower n polymer ≤
      canonicalSurfaceActivity upper n polymer := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hpolymer
  have hphysical := componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hterm := parametricKPhysicalTerm_mono_coupling
    hlower hle hphysical
  have hlowerEq :
      parametricKPhysicalTerm lower 1 n (componentLabel polymer) ≈
        canonicalSurfaceActivity lower n polymer := by
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized
      lower n (componentLabel polymer)
  have hupperEq :
      parametricKPhysicalTerm upper 1 n (componentLabel polymer) ≈
        canonicalSurfaceActivity upper n polymer := by
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized
      upper n (componentLabel polymer)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hlowerEq))
    (Q'.le_trans' _ _ _ hterm (Q'.le_of_eqv hupperEq))

theorem parametricKEventTerm_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    {cutoff n : Nat} {event : EdgeLabelling → Bool}
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))) :
    parametricKEventTerm lower cutoff n event physical ≤
      parametricKEventTerm upper cutoff n event physical := by
  unfold parametricKEventTerm
  by_cases hevent : event physical = true
  · rw [if_pos hevent, if_pos hevent]
    exact parametricKPhysicalTerm_mono_coupling hlower hle hphysical
  · rw [if_neg hevent, if_neg hevent]
    exact Q'.le_refl' 0

theorem parametricKEventNumerator_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (cutoff n : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator lower cutoff n event ≤
      parametricKEventNumerator upper cutoff n event := by
  unfold parametricKEventNumerator
  apply listQSum_mono_local
  intro physical hphysical
  exact parametricKEventTerm_mono_coupling hlower hle hphysical

/-! ## 3. The exact unit-cube shift stays below the anchor law -/

theorem shiftedAnchorPhysicalPartition_le_anchor
    (cutoff n : Nat) :
    parametricKPhysicalPartition
        (unitCubeBlockCoupling anchorCoupling) cutoff n ≤
      parametricKPhysicalPartition anchorCoupling cutoff n :=
  parametricKPhysicalPartition_mono_coupling
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le cutoff n

theorem shiftedAnchorEventNumerator_le_anchor
    (cutoff n : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventNumerator
        (unitCubeBlockCoupling anchorCoupling) cutoff n event ≤
      parametricKEventNumerator anchorCoupling cutoff n event :=
  parametricKEventNumerator_mono_coupling
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le cutoff n event

#print axioms parametricKPhysicalFaceFactor_mono_coupling
#print axioms parametricKPhysicalTerm_mono_coupling
#print axioms parametricKPhysicalPartition_mono_coupling
#print axioms canonicalSurfaceActivity_mono_coupling
#print axioms parametricKEventTerm_mono_coupling
#print axioms parametricKEventNumerator_mono_coupling
#print axioms shiftedAnchorPhysicalPartition_le_anchor
#print axioms shiftedAnchorEventNumerator_le_anchor

end YMGap.Continuum.Z4CouplingParametricMonotonicity
