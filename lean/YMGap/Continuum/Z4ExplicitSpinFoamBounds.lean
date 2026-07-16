/-
# First derived bounds for the explicit finite-box spin-foam formula

This file begins the analytic layer after exact assembly.  It proves that
every face factor, local multiplicity factor, summand, and finite partition
sum is nonnegative.  It also records the exact polynomial cardinality bounds
for the one-, two-, and three-channel local path sets.  These bounds are
derived from the finite enumerations; no measured constant enters.
-/

import YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction

namespace YMGap.Continuum.Z4ExplicitSpinFoamBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive nonnegativity -/

private theorem ofNat_nonnegative (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.ofNat n).num
  exact Int.natCast_nonneg n

private theorem eliminateLinks_nonnegative (value : Nat → Q')
    (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest =>
      Q'.mul_nonneg _ _ (hvalue edge)
        (eliminateLinks_nonnegative value hvalue rest)

private theorem listQSum_nonnegative {A : Type} (value : A → Q')
    (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | x :: rest => Q'.zero_le_add _ _ (hvalue x)
      (listQSum_nonnegative value hvalue rest)

theorem heatKernelPacketCoefficient_nonnegative
    (K spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket K coupling) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg (Q'.le_of_lt coupling_window.1) spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K coupling) hlarge]
    exact Q'.le_refl' 0

theorem explicitPhysicalFaceFactor_nonnegative
    (K n : Nat) (physical : EdgeLabelling) :
    (0 : Q') ≤ explicitPhysicalFaceFactor K n physical := by
  unfold explicitPhysicalFaceFactor
  exact eliminateLinks_nonnegative _
    (fun edge => heatKernelPacketCoefficient_nonnegative K (physical edge))
    (List.range (plaquetteEdgeCount n))

theorem explicitLinkMultiplicityProduct_nonnegative
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link), (0 : Q') ≤
      explicitLinkMultiplicityProduct K n physical links
  | [] => Q'.zero_le_one
  | _ :: rest =>
      Q'.mul_nonneg _ _ (ofNat_nonnegative _)
        (explicitLinkMultiplicityProduct_nonnegative K n physical rest)

theorem explicitSpinFoamSummand_nonnegative
    (K n : Nat) (physical : EdgeLabelling) :
    (0 : Q') ≤
      explicitPhysicalFaceFactor K n physical *
        explicitLinkMultiplicityProduct K n physical
          (enumerate (distinctBoxLinks n)) :=
  Q'.mul_nonneg _ _
    (explicitPhysicalFaceFactor_nonnegative K n physical)
    (explicitLinkMultiplicityProduct_nonnegative K n physical _)

theorem explicitPhysicalCutoffSpinFoamSum_nonnegative
    (K n : Nat) :
    (0 : Q') ≤
      listQSum
        (fun physical =>
          explicitPhysicalFaceFactor K n physical *
            explicitLinkMultiplicityProduct K n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n))) :=
  listQSum_nonnegative _
    (fun physical => explicitSpinFoamSummand_nonnegative K n physical) _

theorem fusionCompleteBoxVertexCartesianSum_nonnegative
    (K n : Nat) :
    (0 : Q') ≤ fusionCompleteBoxVertexCartesianSum K n := by
  let explicitSum :=
    listQSum
      (fun physical =>
        explicitPhysicalFaceFactor K n physical *
          explicitLinkMultiplicityProduct K n physical
            (enumerate (distinctBoxLinks n)))
      (boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount n)))
  exact Q'.le_trans' 0 explicitSum _
    (explicitPhysicalCutoffSpinFoamSum_nonnegative K n)
    (Q'.ge_of_eqv
      (fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam K n))

/-! ## 2. Derived local cardinality bounds -/

theorem oneValentMultiplicity_le (cutoff a : Nat) :
    oneValentMultiplicity cutoff a ≤ cutoff + 1 := by
  unfold oneValentMultiplicity
  simpa using List.length_filter_le
    (fun vacuum => fusionOK a vacuum vacuum && decide (vacuum = 0))
    (List.range (cutoff + 1))

theorem twoValentMultiplicity_le (cutoff a b : Nat) :
    twoValentMultiplicity cutoff a b ≤ cutoff + 1 := by
  unfold twoValentMultiplicity
  simpa using List.length_filter_le
    (fun vacuum => fusionOK a b vacuum && decide (vacuum = 0))
    (List.range (cutoff + 1))

theorem oneChannelMultiplicity_le (cutoff a b c d : Nat) :
    oneChannelMultiplicity cutoff a b c d ≤ cutoff + 1 := by
  unfold oneChannelMultiplicity
  simpa using List.length_filter_le
    (fun x => fusionOK a b x && fusionOK x c d)
    (List.range (cutoff + 1))

theorem twoChannelMultiplicity_le (cutoff a b c d e : Nat) :
    twoChannelMultiplicity cutoff a b c d e ≤
      (cutoff + 1) * (cutoff + 1) := by
  unfold twoChannelMultiplicity
  have hfilter := List.length_filter_le
    (fun xy : Nat × Nat => fusionOK a b xy.1 &&
      (fusionOK xy.1 c xy.2 && fusionOK xy.2 d e))
    ((List.range (cutoff + 1)).flatMap fun x =>
      (List.range (cutoff + 1)).map fun y => (x, y))
  have hlength := length_flatMap_fixed
    (List.range (cutoff + 1))
    (fun x => (List.range (cutoff + 1)).map fun y => (x, y))
    (cutoff + 1) (fun _ => by simp)
  rw [hlength, List.length_range] at hfilter
  exact hfilter

theorem threeChannelMultiplicity_le (cutoff a b c d e f : Nat) :
    threeChannelMultiplicity cutoff a b c d e f ≤
      (cutoff + 1) * ((cutoff + 1) * (cutoff + 1)) := by
  unfold threeChannelMultiplicity
  let inner := fun x : Nat =>
    (List.range (cutoff + 1)).flatMap fun y =>
      (List.range (cutoff + 1)).map fun z => (x, y, z)
  have hinner : ∀ x, (inner x).length =
      (cutoff + 1) * (cutoff + 1) := by
    intro x
    unfold inner
    have h := length_flatMap_fixed
      (List.range (cutoff + 1))
      (fun y => (List.range (cutoff + 1)).map fun z => (x, y, z))
      (cutoff + 1) (fun _ => by simp)
    simpa using h
  have hfilter := List.length_filter_le
    (fun xyz : Nat × Nat × Nat => fusionOK a b xyz.1 &&
      (fusionOK xyz.1 c xyz.2.1 &&
        (fusionOK xyz.2.1 d xyz.2.2 && fusionOK xyz.2.2 e f)))
    ((List.range (cutoff + 1)).flatMap inner)
  have hlength := length_flatMap_fixed
    (List.range (cutoff + 1)) inner
    ((cutoff + 1) * (cutoff + 1)) hinner
  rw [hlength, List.length_range] at hfilter
  exact hfilter

end YMGap.Continuum.Z4ExplicitSpinFoamBounds

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.heatKernelPacketCoefficient_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.explicitPhysicalFaceFactor_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.explicitLinkMultiplicityProduct_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.explicitPhysicalCutoffSpinFoamSum_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.fusionCompleteBoxVertexCartesianSum_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.oneChannelMultiplicity_le
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.twoChannelMultiplicity_le
#print axioms YMGap.Continuum.Z4ExplicitSpinFoamBounds.threeChannelMultiplicity_le
