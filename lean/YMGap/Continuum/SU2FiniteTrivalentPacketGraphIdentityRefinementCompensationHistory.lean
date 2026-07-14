/-
# Composable compensation histories for graph identity refinement

Each trivalent identity subdivision inserts one copied-edge Wilson
eigenvalue.  A refinement history therefore carries the product of the
constructive reciprocals of all previously copied edges.  This module proves
that adding the next reciprocal makes the history eigenvalue strictly
compatible with the next refinement.

The result is an exact finite composition law.  It does not by itself supply
the directed graph system or its thermodynamic limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem q_pow_congr {a b : Q'} (h : a ≈ b) : ∀ n : Nat,
    a ^ n ≈ b ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      exact q_mul_congr h (q_pow_congr h n)

/-- The exact reciprocal Wilson factor attached to one previously copied
edge. -/
def edgeCompensation (label : EdgeLabelling) (edge : Nat) : Q' :=
  Q'.recipPos (eigA SU2PeterWeylWilsonBlock.coupling (label edge))
    (copiedEdgeEigen_pos label edge)

/-- Product of the reciprocal factors accumulated by a refinement history. -/
def compensationProduct (copiedEdges : List Nat)
    (label : EdgeLabelling) : Q' :=
  eliminateLinks (edgeCompensation label) copiedEdges

/-- The graph transfer eigenvalue after all reciprocal factors in a
refinement history have been installed. -/
def historyGraphEigen (copiedEdges : List Nat) (edges : List Nat)
    (label : EdgeLabelling) : Q' :=
  graphEigen edges label * compensationProduct copiedEdges label

private theorem recipPos_eq_of_eq {a b : Q'} (h : a = b)
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    Q'.recipPos a ha = Q'.recipPos b hb := by
  subst b
  rfl

theorem edgeCompensation_eq_of_label_eq
    (a b : EdgeLabelling) (edge : Nat) (h : a edge = b edge) :
    edgeCompensation a edge = edgeCompensation b edge := by
  unfold edgeCompensation
  exact recipPos_eq_of_eq
    (congrArg (eigA SU2PeterWeylWilsonBlock.coupling) h) _ _

/-- Every old accumulated reciprocal is unchanged by a fresh refinement,
provided its edge belongs to the old graph. -/
theorem compensationProduct_identity_refinement
    (oldEdge newEdge vacuumEdge : Nat) (edges copiedEdges : List Nat)
    (label : EdgeLabelling)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hcopied : ∀ edge, edge ∈ copiedEdges → edge ∈ edges) :
    compensationProduct copiedEdges
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) =
      compensationProduct copiedEdges label := by
  unfold compensationProduct
  induction copiedEdges with
  | nil => rfl
  | cons edge rest ih =>
      simp only [eliminateLinks]
      have hedgeMem : edge ∈ edges :=
        hcopied edge List.mem_cons_self
      have hedgeLabel := identityRefinedLabel_eq_on_old_edges
        oldEdge newEdge vacuumEdge label hnew hvac edge hedgeMem
      have hedgeComp :
          edgeCompensation
              (identityRefinedLabel oldEdge newEdge vacuumEdge label) edge =
            edgeCompensation label edge :=
        edgeCompensation_eq_of_label_eq _ _ edge hedgeLabel
      rw [hedgeComp]
      apply congrArg (fun x => edgeCompensation label edge * x)
      exact ih (fun e he => hcopied e (List.mem_cons_of_mem edge he))

/-- With no previous subdivisions, the history eigenvalue is the ordinary
graph eigenvalue. -/
theorem historyGraphEigen_nil (edges : List Nat) (label : EdgeLabelling) :
    historyGraphEigen [] edges label ≈ graphEigen edges label := by
  unfold historyGraphEigen compensationProduct eliminateLinks
  exact Q'.mul_one_eqv _

/-- A singleton history is exactly the one-step compensated eigenvalue. -/
theorem historyGraphEigen_singleton (oldEdge : Nat) (edges : List Nat)
    (label : EdgeLabelling) :
    historyGraphEigen [oldEdge] edges label ≈
      compensatedGraphEigen oldEdge edges label := by
  unfold historyGraphEigen compensationProduct compensatedGraphEigen
  change graphEigen edges label * (edgeCompensation label oldEdge * 1) ≈
    graphEigen edges label * edgeCompensation label oldEdge
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_one_eqv (edgeCompensation label oldEdge))

/-- Appending the new copied edge to the compensation history exactly
restores the old history eigenvalue on the fusion-selected label. -/
theorem historyGraphEigen_identity_refinement
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (label : EdgeLabelling)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hcopied : ∀ edge, edge ∈ copiedEdges → edge ∈ edges) :
    historyGraphEigen (oldEdge :: copiedEdges)
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      historyGraphEigen copiedEdges edges label := by
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have hlocal := compensatedGraphEigen_identity_refinement
    oldEdge newEdge vacuumEdge edges label hnew hvac hno hvo hnv
  have hrest := compensationProduct_identity_refinement
    oldEdge newEdge vacuumEdge edges copiedEdges label hnew hvac hcopied
  unfold historyGraphEigen compensationProduct at *
  change graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined *
      (edgeCompensation refined oldEdge *
        eliminateLinks (edgeCompensation refined) copiedEdges) ≈
    graphEigen edges label *
      eliminateLinks (edgeCompensation label) copiedEdges
  have holdCoord : refined oldEdge = label oldEdge :=
    identityRefinedLabel_old oldEdge newEdge vacuumEdge label hno hvo
  have hlocalComp : edgeCompensation refined oldEdge =
      edgeCompensation label oldEdge :=
    edgeCompensation_eq_of_label_eq _ _ _ holdCoord
  have hlocal' :
      graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined *
          edgeCompensation label oldEdge ≈
        graphEigen edges label := by
    unfold compensatedGraphEigen at hlocal
    change graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined *
        edgeCompensation refined oldEdge ≈ graphEigen edges label at hlocal
    rw [hlocalComp] at hlocal
    exact hlocal
  rw [hlocalComp, hrest]
  exact Q'.eqv_trans _
    ((graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined *
        edgeCompensation label oldEdge) *
      eliminateLinks (edgeCompensation label) copiedEdges) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined)
      (edgeCompensation label oldEdge)
      (eliminateLinks (edgeCompensation label) copiedEdges)))
    (q_mul_congr hlocal' (Q'.eqv_refl _))

/-- One full-support spectral summand carrying an arbitrary accumulated
refinement history. -/
def historyProjectedCorrTerm {K : Nat} (copiedEdges : List Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) : Q' :=
  projectedSquare edges vertices packet label *
    (historyGraphEigen copiedEdges edges label *
      historyGraphEigen copiedEdges edges label) ^ n

/-- The selected spectral term obeys the same exact history composition law
at every integer time. -/
theorem historyProjectedCorrTerm_identity_refinement {K : Nat}
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices)
    (hcopied : ∀ edge, edge ∈ copiedEdges → edge ∈ edges) :
    historyProjectedCorrTerm (oldEdge :: copiedEdges)
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      historyProjectedCorrTerm copiedEdges edges vertices P n label := by
  have ha := packetGraphProjectedAmplitude_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices P label hold holdBound
      hnew hvac hno hvo hnv hnewV hvacV
  have he := historyGraphEigen_identity_refinement copiedEdges
    oldEdge newEdge vacuumEdge edges label hnew hvac hno hvo hnv hcopied
  unfold historyProjectedCorrTerm projectedSquare
  exact q_mul_congr (q_mul_congr ha ha)
    (q_pow_congr (q_mul_congr he he) n)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory.edgeCompensation_eq_of_label_eq
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory.compensationProduct_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory.historyGraphEigen_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory.historyProjectedCorrTerm_identity_refinement
