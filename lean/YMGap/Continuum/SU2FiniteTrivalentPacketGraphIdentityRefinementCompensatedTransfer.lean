/-
# Transfer-compensated trivalent identity refinement

Bare identity subdivision preserves the finite-graph state norm but inserts
one extra copied-edge Wilson eigenvalue.  Since the exact coupling is positive,
every such eigenvalue is constructively invertible.  This module defines the
local reciprocal compensation and proves that it restores the old transfer
eigenvalue and every selected spectral summand exactly.

The compensation is derived from the exact rational eigenvalue; it is not a
measured or assumed normalization.  A later graph-volume system must explain
this factor as its local time/coupling renormalization.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction
import YMGap.Continuum.BondMovingScaledNorm

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer

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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum

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

/-- Every copied-edge Wilson eigenvalue is strictly positive at the exact
coupling `1/2`. -/
theorem copiedEdgeEigen_pos (label : EdgeLabelling) (oldEdge : Nat) :
    (0 : Q') < eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) :=
  BondMovingScaledNorm.qpow_pos
    SU2PeterWeylWilsonBlock.coupling_window.1 _

/-- Divide a graph eigenvalue by the local Wilson eigenvalue on the edge being
subdivided.  The reciprocal is constructive because positivity is explicit. -/
def compensatedGraphEigen (oldEdge : Nat) (edges : List Nat)
    (label : EdgeLabelling) : Q' :=
  graphEigen edges label *
    Q'.recipPos (eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge))
      (copiedEdgeEigen_pos label oldEdge)

private theorem cancel_copied_edge (edgeEig oldEig : Q')
    (hpos : (0 : Q') < edgeEig) :
    (edgeEig * oldEig) * Q'.recipPos edgeEig hpos ≈ oldEig := by
  exact Q'.eqv_trans _ ((oldEig * edgeEig) * Q'.recipPos edgeEig hpos) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv edgeEig oldEig))
    (Q'.eqv_trans _ (oldEig *
        (edgeEig * Q'.recipPos edgeEig hpos)) _
      (Q'.mul_assoc_eqv oldEig edgeEig (Q'.recipPos edgeEig hpos))
      (Q'.eqv_trans _ (oldEig * 1) _
        (Q'.mul_eqv_congr_left oldEig _ _
          (Q'.mul_recipPos_eqv edgeEig hpos))
        (Q'.mul_one_eqv oldEig)))

private theorem recipPos_eq_of_eq {a b : Q'} (h : a = b)
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    Q'.recipPos a ha = Q'.recipPos b hb := by
  subst b
  rfl

/-- The local reciprocal compensation exactly restores the old graph
eigenvalue on every fusion-selected refined label. -/
theorem compensatedGraphEigen_identity_refinement
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (label : EdgeLabelling)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    compensatedGraphEigen oldEdge
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      graphEigen edges label := by
  have he := graphEigen_identity_refinement
    oldEdge newEdge vacuumEdge edges label hnew hvac hnv
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have hcoord : refined oldEdge = label oldEdge :=
    identityRefinedLabel_old oldEdge newEdge vacuumEdge label hno hvo
  have heig :
      eigA SU2PeterWeylWilsonBlock.coupling (refined oldEdge) =
        eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) :=
    congrArg (eigA SU2PeterWeylWilsonBlock.coupling) hcoord
  have hrec :
      Q'.recipPos
          (eigA SU2PeterWeylWilsonBlock.coupling (refined oldEdge))
          (copiedEdgeEigen_pos refined oldEdge) =
        Q'.recipPos
          (eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge))
          (copiedEdgeEigen_pos label oldEdge) :=
    recipPos_eq_of_eq heig _ _
  unfold compensatedGraphEigen
  change graphEigen (identityRefinedEdges newEdge vacuumEdge edges) refined *
      Q'.recipPos
        (eigA SU2PeterWeylWilsonBlock.coupling (refined oldEdge))
        (copiedEdgeEigen_pos refined oldEdge) ≈ graphEigen edges label
  rw [hrec]
  exact Q'.eqv_trans _
    ((eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) *
        graphEigen edges label) *
      Q'.recipPos
        (eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge))
        (copiedEdgeEigen_pos label oldEdge)) _
    (Q'.mul_eqv_congr_right _ _ _ he)
    (cancel_copied_edge
      (eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge))
      (graphEigen edges label) (copiedEdgeEigen_pos label oldEdge))

/-- One spectral term using the transfer-compensated graph eigenvalue. -/
def compensatedProjectedCorrTerm {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) : Q' :=
  projectedSquare edges vertices packet label *
    (compensatedGraphEigen oldEdge edges label *
      compensatedGraphEigen oldEdge edges label) ^ n

/-- Every fusion-selected compensated summand, at every integer time, is the
original graph summand exactly. -/
theorem compensatedProjectedCorrTerm_identity_refinement {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    compensatedProjectedCorrTerm oldEdge
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      projectedCorrTerm edges vertices P n label := by
  have ha := packetGraphProjectedAmplitude_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices P label hold holdBound
      hnew hvac hno hvo hnv hnewV hvacV
  have he := compensatedGraphEigen_identity_refinement
    oldEdge newEdge vacuumEdge edges label hnew hvac hno hvo hnv
  unfold compensatedProjectedCorrTerm projectedCorrTerm projectedSquare
  exact q_mul_congr (q_mul_congr ha ha)
    (q_pow_congr (q_mul_congr he he) n)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer.copiedEdgeEigen_pos
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer.compensatedGraphEigen_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer.compensatedProjectedCorrTerm_identity_refinement
