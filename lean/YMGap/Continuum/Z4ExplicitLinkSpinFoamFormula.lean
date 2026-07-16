/-
# The finite-box spin-foam formula with literal local fusion counts

The preceding assembly theorem still names each local factor through
`linkAuxiliaryMultiplicity`.  This file substitutes the exact valence-zero
through-six formulas into the global product and also expands the physical
factor to one heat-kernel coefficient per plaquette.  The resulting identity
contains no hidden auxiliary-coordinate or graph-projector sum.
-/

import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Product of literal local fusion-path cardinalities -/

def explicitLinkMultiplicityProduct (K n : Nat)
    (physical : EdgeLabelling) : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link) → Q'
  | [] => 1
  | indexed :: rest =>
      Q'.ofNat
          (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            (incidentPlaqIds n indexed.2).length
            (fun position => physical
              (localIdentifierRename (incidentPlaqIds n indexed.2)
                (linkBlockBase n indexed.1) position))) *
        explicitLinkMultiplicityProduct K n physical rest

theorem linkAuxiliaryMultiplicityProduct_eq_explicit
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      (∀ indexed, indexed ∈ links →
        indexed ∈ enumerate (distinctBoxLinks n)) →
      linkAuxiliaryMultiplicityProduct K n physical links ≈
        explicitLinkMultiplicityProduct K n physical links
  | [], _ => Q'.eqv_refl 1
  | indexed :: rest, hsubset => by
      have hindexed : indexed ∈ enumerate (distinctBoxLinks n) :=
        hsubset indexed List.mem_cons_self
      have hfactor : linkAuxiliaryMultiplicity K n physical indexed ≈
          Q'.ofNat
            (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
              (incidentPlaqIds n indexed.2).length
              (fun position => physical
                (localIdentifierRename (incidentPlaqIds n indexed.2)
                  (linkBlockBase n indexed.1) position))) := by
        exact Q'.eqv_trans _
          (Q'.ofNat
            (linkInvariantMultiplicityCount K n physical indexed)) _
          (linkAuxiliaryMultiplicity_eq_invariantCount
            K n physical indexed)
          (Q'.eqv_of_eq (congrArg Q'.ofNat
            (linkInvariantMultiplicityCount_eq_explicit
              hindexed physical)))
      have hrest := linkAuxiliaryMultiplicityProduct_eq_explicit
        K n physical rest
        (fun item hitem =>
          hsubset item (List.mem_cons_of_mem indexed hitem))
      exact qmul_congr hfactor hrest

theorem enumeratedLinkMultiplicityProduct_eq_explicit
    (K n : Nat) (physical : EdgeLabelling) :
    linkAuxiliaryMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) ≈
      explicitLinkMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) := by
  apply linkAuxiliaryMultiplicityProduct_eq_explicit
  intro indexed hindexed
  exact hindexed

/-! ## 2. Fully explicit finite-box formula -/

def explicitPhysicalFaceFactor (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun edge => coeffAt (heatKernelPacket K coupling) (physical edge))
    (List.range (plaquetteEdgeCount n))

theorem physicalBoxPacketFactor_eq_explicit
    (K n : Nat) (physical : EdgeLabelling) :
    physicalBoxPacketFactor K n physical =
      explicitPhysicalFaceFactor K n physical := by
  exact physicalBoxPacketFactor_eq_heatKernelProduct K n physical

/-- **Literal finite-box SU(2) spin-foam identity.**  The right side is one
finite sum over physical face spins, one heat-kernel coefficient per face,
and one explicit valence-`0`--`6` fusion-path cardinality per link. -/
theorem fusionCompleteBoxVertexCartesianSum_eq_explicitSpinFoam
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      listQSum
        (fun physical =>
          explicitPhysicalFaceFactor K n physical *
            explicitLinkMultiplicityProduct K n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (List.range (plaquetteEdgeCount n))) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        physicalBoxPacketFactor K n physical *
          linkAuxiliaryMultiplicityProduct K n physical
            (enumerate (distinctBoxLinks n)))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)))) _
    (fusionCompleteBoxVertexCartesianSum_eq_linkSpinFoam K n) ?_
  apply listQSum_congr
  intro physical
  exact qmul_congr
    (Q'.eqv_of_eq
      (physicalBoxPacketFactor_eq_explicit K n physical))
    (enumeratedLinkMultiplicityProduct_eq_explicit K n physical)

end YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula.linkAuxiliaryMultiplicityProduct_eq_explicit
#print axioms YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula.enumeratedLinkMultiplicityProduct_eq_explicit
#print axioms YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula.fusionCompleteBoxVertexCartesianSum_eq_explicitSpinFoam
