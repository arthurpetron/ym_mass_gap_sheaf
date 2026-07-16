/-
# Exact multiplicity semantics of the conditional Z4 auxiliary sum

After the physical/auxiliary finite-Fubini split, every physical plaquette
coefficient occurs exactly once.  This module identifies the remaining
auxiliary packet product with a Boolean indicator: open-link terminators are
forced to the vacuum label, while every internal fusion carrier contributes
the exact coefficient one.  Consequently the conditional auxiliary sum is
an exact rational cardinality of admissible auxiliary-channel labellings.

This is the finite spin-foam multiplicity semantics needed before the local
link blocks can be factored.  No numerical estimate, measured constant, or
independence assumption enters the construction.
-/

import YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination

namespace YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One heat-kernel coefficient per physical face -/

theorem eliminateLinks_congr_eq (left right : Nat → Q') :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → left edge = right edge) →
      eliminateLinks left edges = eliminateLinks right edges
  | [], _ => rfl
  | edge :: rest, hagree => by
      simp only [eliminateLinks]
      rw [hagree edge List.mem_cons_self]
      apply congrArg (fun q => right edge * q)
      exact eliminateLinks_congr_eq left right rest
        (fun e he => hagree e (List.mem_cons_of_mem edge he))

/-- The physical factor in the conditional formula is literally one padded
heat-kernel character coefficient for every plaquette identifier. -/
theorem physicalBoxPacketFactor_eq_heatKernelProduct
    (K n : Nat) (physical : EdgeLabelling) :
    physicalBoxPacketFactor K n physical =
      eliminateLinks
        (fun edge => coeffAt (heatKernelPacket K coupling) (physical edge))
        (List.range (plaquetteEdgeCount n)) := by
  unfold physicalBoxPacketFactor packetGraphBareAmplitude
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hedgeLt : edge < plaquetteEdgeCount n := List.mem_range.mp hedge
  unfold gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_pos hedgeLt, coeffAt_padPacket]

/-! ## 2. Auxiliary packets are exact zero-one constraints -/

/-- An auxiliary edge is allowed unless it is a reserved open-link
terminator, in which case its spin must be exactly zero. -/
def auxiliaryEdgeAllowedB (n : Nat) (label : EdgeLabelling)
    (edge : Nat) : Bool :=
  if edge ∈ vacuumBaseEdgeIds n then decide (label edge = 0) else true

def auxiliaryPacketAllowedB (n : Nat) (label : EdgeLabelling) : Bool :=
  (usedAuxiliaryEdges n).all (auxiliaryEdgeAllowedB n label)

/-- Every identifier in the production auxiliary list lies beyond the
physical plaquette range. -/
theorem usedAuxiliaryEdge_ge_count {n edge : Nat}
    (hedge : edge ∈ usedAuxiliaryEdges n) :
    plaquetteEdgeCount n ≤ edge := by
  unfold usedAuxiliaryEdges at hedge
  have hfilter := List.mem_filter.mp (List.mem_eraseDups.mp hedge)
  simpa only [decide_eq_true_eq] using hfilter.2

/-- On a bounded auxiliary label, the production packet coefficient is
exactly the zero-one edge constraint. -/
theorem auxiliaryEdgeCoefficient_eq_indicator
    {K n edge : Nat} {label : EdgeLabelling}
    (hge : plaquetteEdgeCount n ≤ edge)
    (hbound : label edge < linkAuxiliaryCutoff K + 1) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge)
        (label edge) =
      if auxiliaryEdgeAllowedB n label edge then 1 else 0 := by
  have hnotPhysical : ¬ edge < plaquetteEdgeCount n := by omega
  unfold gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_neg hnotPhysical]
  by_cases hvacuum : edge ∈ vacuumBaseEdgeIds n
  · rw [if_pos hvacuum, coeffAt_vacuumPacket]
    unfold auxiliaryEdgeAllowedB
    rw [if_pos hvacuum]
    by_cases hzero : label edge = 0 <;> simp [hzero]
  · rw [if_neg hvacuum, coeffAt_allOnesPacket hbound]
    unfold auxiliaryEdgeAllowedB
    rw [if_neg hvacuum]
    rfl

/-- A product of zero-one edge indicators is the indicator that `List.all`
accepts every edge. -/
theorem eliminateLinks_indicator_eq_all
    (allowed : Nat → Bool) : ∀ edges : List Nat,
    eliminateLinks (fun edge => if allowed edge then (1 : Q') else 0)
        edges ≈
      if edges.all allowed then 1 else 0
  | [] => Q'.eqv_refl 1
  | edge :: rest => by
      simp only [eliminateLinks, List.all_cons]
      by_cases hedge : allowed edge = true
      · simp only [hedge, if_true, Bool.true_and]
        exact Q'.eqv_trans _ _ _
          (Q'.one_mul_eqv _)
          (eliminateLinks_indicator_eq_all allowed rest)
      · have hfalse : allowed edge = false := by
          cases hvalue : allowed edge
          · rfl
          · exact False.elim (hedge hvalue)
        simp only [hfalse, Bool.false_eq_true, if_false, Bool.false_and]
        exact Q'.zero_mul_eqv _

/-- The complete production auxiliary packet product is a single exact
Boolean indicator. -/
theorem auxiliaryPacketBareAmplitude_eq_indicator
    (K n : Nat) (label : EdgeLabelling)
    (hbound : ∀ edge, edge ∈ usedAuxiliaryEdges n →
      label edge < linkAuxiliaryCutoff K + 1) :
    packetGraphBareAmplitude (usedAuxiliaryEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n) label ≈
      if auxiliaryPacketAllowedB n label then 1 else 0 := by
  unfold packetGraphBareAmplitude auxiliaryPacketAllowedB
  refine Q'.eqv_trans _
    (eliminateLinks
      (fun edge => if auxiliaryEdgeAllowedB n label edge
        then (1 : Q') else 0)
      (usedAuxiliaryEdges n)) _ ?_
    (eliminateLinks_indicator_eq_all
      (auxiliaryEdgeAllowedB n label) (usedAuxiliaryEdges n))
  exact Q'.eqv_of_eq
    (eliminateLinks_congr_eq
      (fun edge => coeffAt
        (gaugeHeatKernelBoxPacketsFusionComplete K n edge) (label edge))
      (fun edge => if auxiliaryEdgeAllowedB n label edge
        then (1 : Q') else 0)
      (usedAuxiliaryEdges n)
      (fun edge hedge =>
        auxiliaryEdgeCoefficient_eq_indicator
          (usedAuxiliaryEdge_ge_count hedge) (hbound edge hedge)))

/-! ## 3. Conditional multiplicity as an exact cardinality -/

def conditionalAuxiliaryAllowedB (n : Nat)
    (physical auxiliary : EdgeLabelling) : Bool :=
  let label := overlayOn (List.range (plaquetteEdgeCount n))
    physical auxiliary
  verticesAdmissibleB (resolutionVertices n) label &&
    auxiliaryPacketAllowedB n label

def conditionalAuxiliaryMultiplicityTerm (n : Nat)
    (physical auxiliary : EdgeLabelling) : Q' :=
  if conditionalAuxiliaryAllowedB n physical auxiliary then 1 else 0

def conditionalAuxiliaryMultiplicity (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  listQSum
    (conditionalAuxiliaryMultiplicityTerm n physical)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedAuxiliaryEdges n))

def conditionalAuxiliaryMultiplicityCount (K n : Nat)
    (physical : EdgeLabelling) : Nat :=
  ((boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedAuxiliaryEdges n)).filter
    (conditionalAuxiliaryAllowedB n physical)).length

theorem overlayOn_apply_of_not_mem {edge : Nat} {edges : List Nat}
    {outer inner : EdgeLabelling} (hedge : edge ∉ edges) :
    overlayOn edges outer inner edge = inner edge := by
  simp [overlayOn, hedge]

theorem usedAuxiliaryEdge_not_physical {n edge : Nat}
    (hedge : edge ∈ usedAuxiliaryEdges n) :
    edge ∉ List.range (plaquetteEdgeCount n) := by
  intro hphysical
  have hlt := List.mem_range.mp hphysical
  have hge := usedAuxiliaryEdge_ge_count hedge
  omega

theorem conditionalAuxiliaryIntegrand_eq_indicator
    {K n : Nat} (physical auxiliary : EdgeLabelling)
    (hauxiliary : auxiliary ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (usedAuxiliaryEdges n)) :
    graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (gaugeHeatKernelBoxPacketsFusionComplete K n))
        (overlayOn (List.range (plaquetteEdgeCount n))
          physical auxiliary) ≈
      conditionalAuxiliaryMultiplicityTerm n physical auxiliary := by
  let label := overlayOn (List.range (plaquetteEdgeCount n))
    physical auxiliary
  have hsound := boundedEdgeLabellings_sound
    (linkAuxiliaryCutoff K) (usedAuxiliaryEdges n)
    auxiliary hauxiliary
  have hbound : ∀ edge, edge ∈ usedAuxiliaryEdges n →
      label edge < linkAuxiliaryCutoff K + 1 := by
    intro edge hedge
    have hover : label edge = auxiliary edge := by
      dsimp [label]
      exact overlayOn_apply_of_not_mem
        (usedAuxiliaryEdge_not_physical hedge)
    rw [hover]
    exact hsound.1 edge hedge
  have hpacket := auxiliaryPacketBareAmplitude_eq_indicator
    K n label hbound
  by_cases hvertices :
      verticesAdmissibleB (resolutionVertices n) label = true
  · unfold graphVertexProject conditionalAuxiliaryMultiplicityTerm
      conditionalAuxiliaryAllowedB
    dsimp only [label] at hvertices hpacket ⊢
    rw [if_pos hvertices]
    simp only [hvertices, Bool.true_and]
    exact hpacket
  · unfold graphVertexProject conditionalAuxiliaryMultiplicityTerm
      conditionalAuxiliaryAllowedB
    dsimp only [label] at hvertices ⊢
    rw [if_neg hvertices]
    simp [hvertices]
    exact Q'.eqv_refl 0

theorem listQSum_congr_on {A : Type} (f g : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, hagree => by
      simp only [listQSum]
      exact Q'.add_eqv_congr'
        (hagree x List.mem_cons_self)
        (listQSum_congr_on f g xs
          (fun y hy => hagree y (List.mem_cons_of_mem x hy)))

/-- The conditional packet sum is exactly the rational multiplicity sum. -/
theorem conditionalBoxAuxiliarySum_eq_multiplicity
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalBoxAuxiliarySum K n physical ≈
      conditionalAuxiliaryMultiplicity K n physical := by
  unfold conditionalBoxAuxiliarySum conditionalAuxiliaryMultiplicity
  apply listQSum_congr_on
  intro auxiliary hauxiliary
  exact conditionalAuxiliaryIntegrand_eq_indicator
    physical auxiliary hauxiliary

theorem listQSum_boolIndicator_eq_count {A : Type}
    (allowed : A → Bool) : ∀ xs : List A,
    listQSum (fun x => if allowed x then (1 : Q') else 0) xs ≈
      Q'.ofNat (xs.filter allowed).length
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      cases hx : allowed x with
      | false =>
          simp only [listQSum, hx, Bool.false_eq_true, if_false,
            List.filter]
          exact Q'.eqv_trans _ _ _
            (Q'.eqv_of_eq (Q'.zero_add' _))
            (listQSum_boolIndicator_eq_count allowed xs)
      | true =>
          simp only [listQSum, hx, if_true, List.filter, List.length_cons]
          refine Q'.eqv_trans _
            ((1 : Q') + Q'.ofNat (xs.filter allowed).length) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 1)
              (listQSum_boolIndicator_eq_count allowed xs)) ?_
          simpa [Nat.add_comm] using
            (Q'.eqv_symm
              (Q'.ofNat_add_eqv 1 (xs.filter allowed).length))

/-- The conditional auxiliary multiplicity is an exact natural-number
cardinality embedded into constructive rationals. -/
theorem conditionalAuxiliaryMultiplicity_eq_count
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalAuxiliaryMultiplicity K n physical ≈
      Q'.ofNat (conditionalAuxiliaryMultiplicityCount K n physical) := by
  unfold conditionalAuxiliaryMultiplicity
    conditionalAuxiliaryMultiplicityTerm
    conditionalAuxiliaryMultiplicityCount
  exact listQSum_boolIndicator_eq_count
    (conditionalAuxiliaryAllowedB n physical)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedAuxiliaryEdges n))

/-- The exact finite-volume formula now has one face-weight product and one
natural invariant-multiplicity count for every physical labelling. -/
theorem fusionCompleteBoxVertexCartesianSum_eq_countedSpinFoam
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      listQSum
        (fun physical =>
          physicalBoxPacketFactor K n physical *
            Q'.ofNat
              (conditionalAuxiliaryMultiplicityCount K n physical))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (List.range (plaquetteEdgeCount n))) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        physicalBoxPacketFactor K n physical *
          conditionalBoxAuxiliarySum K n physical)
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)))) _
    (fusionCompleteBoxVertexCartesianSum_eq_conditional K n) ?_
  apply listQSum_congr
  intro physical
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_trans _
    (conditionalAuxiliaryMultiplicity K n physical) _
    (conditionalBoxAuxiliarySum_eq_multiplicity K n physical)
    (conditionalAuxiliaryMultiplicity_eq_count K n physical)

end YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.physicalBoxPacketFactor_eq_heatKernelProduct
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.usedAuxiliaryEdge_ge_count
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.auxiliaryEdgeCoefficient_eq_indicator
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.auxiliaryPacketBareAmplitude_eq_indicator
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.conditionalAuxiliaryIntegrand_eq_indicator
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.conditionalBoxAuxiliarySum_eq_multiplicity
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.conditionalAuxiliaryMultiplicity_eq_count
#print axioms YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity.fusionCompleteBoxVertexCartesianSum_eq_countedSpinFoam
