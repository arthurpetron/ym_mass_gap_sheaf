/-
# Rooted components of a heterogeneous presented strand graph

The finite component engine depends only on the common global face-copy
carrier and its edge list.  It therefore applies unchanged when different
links use different certified fusion-tree presentations.  This file records
the missing local interface: component membership pulls back to a Boolean
selection on every presented link, and that selection is closed under the
actual ordered terminal partner.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
import YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges

/-! ## 1. Ordered local partner closure -/

/-- A global face-copy selection closed under the physical partner in one
certified ordered link presentation. -/
structure OrderedSlabLinkPartnerClosedFaceSelection
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (witness : PresentedSlabLinkFusionWitness
      K extent physical link) : Type where
  selected : SlabFaceStrandCopy physical → Bool
  partner_closed :
    ∀ terminal : OrderedSlabLinkPhysicalStrandTerminal
        K physical witness.order witness.auxiliary witness.auxiliary_mem,
      selected
          (orderedSlabLinkPhysicalTerminalFaceStrandCopy
            K physical witness.order witness.auxiliary
              witness.auxiliary_mem
              (orderedSlabLinkPhysicalStrandPartner
                K physical witness.order witness.auxiliary
                  witness.auxiliary_mem terminal)) =
        selected
          (orderedSlabLinkPhysicalTerminalFaceStrandCopy
            K physical witness.order witness.auxiliary
              witness.auxiliary_mem terminal)

/-! ## 2. Pull a heterogeneous component back to every presented link -/

/-- Seed data for the global edge list of a dependent field of certified link
presentations. -/
abbrev PresentedSlabFusionWitnessFaceStrandSeed
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) :=
  SlabFaceStrandSeed
    (presentedSlabFusionWitnessAssignmentFaceStrandEdges
      K extent physical links assignment)

/-- Component closure of the common global graph is exactly ordered-partner
closure at each displayed local presentation. -/
def PresentedSlabFusionWitnessFaceStrandSeed.atLinkSelection
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (linked : {link // link ∈ links}) :
    OrderedSlabLinkPartnerClosedFaceSelection K (assignment linked) where
  selected := seed.selected
  partner_closed := by
    intro terminal
    let edge := orderedSlabLinkFaceStrandEdgeOfTerminal K physical
      (assignment linked).order (assignment linked).auxiliary
      (assignment linked).auxiliary_mem terminal
    have hedge : edge ∈
        presentedSlabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment :=
      presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
        K extent physical links assignment linked terminal
    exact seed.selected_eq_of_edge_mem hedge

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.PresentedSlabFusionWitnessFaceStrandSeed
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.PresentedSlabFusionWitnessFaceStrandSeed.atLinkSelection
