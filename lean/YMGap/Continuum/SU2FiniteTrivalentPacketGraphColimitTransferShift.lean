/-
# Transfer-time compatibility on the finite-graph packet colimit

The edgewise Wilson transfer on packet coefficients is the same diagonal
operator used by the finite graph spectral model.  This file proves that
identification before and after the gauge/vacuum projector, then shows that
one packet transfer shifts every exact correlator by one unit of discrete
time.  The identity descends to the actual cutoff quotient.

Honest scope: this is the transfer semigroup law on the cutoff colimit of one
fixed finite graph.  It does not supply graph-volume inclusions or a limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

local macro "mul_ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast,
               Int.mul_one, Int.one_mul, Int.zero_mul, Int.mul_zero];
             ac_rfl))

private theorem eliminateLinks_congr
    (f g : Nat → Q') (hfg : ∀ edge, f edge ≈ g edge) :
    ∀ edges, eliminateLinks f edges ≈ eliminateLinks g edges
  | [] => Q'.eqv_refl _
  | edge :: rest =>
      q_mul_congr (hfg edge) (eliminateLinks_congr f g hfg rest)

private theorem eliminateLinks_pointwise_mul (f g : Nat → Q') : ∀ edges,
    eliminateLinks (fun edge => f edge * g edge) edges ≈
      eliminateLinks f edges * eliminateLinks g edges
  | [] => by
      change (1 : Q') ≈ 1 * 1
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | edge :: rest => by
      change (f edge * g edge) *
          eliminateLinks (fun e => f e * g e) rest ≈
        (f edge * eliminateLinks f rest) *
          (g edge * eliminateLinks g rest)
      exact Q'.eqv_trans _
        ((f edge * g edge) *
          (eliminateLinks f rest * eliminateLinks g rest)) _
        (Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_pointwise_mul f g rest))
        (by mul_ring_qeqv)

/-- Simultaneously transferring every edge packet multiplies the bare graph
amplitude by the exact graph eigenvalue. -/
theorem packetGraphBareAmplitude_transfer {K : Nat}
    (edges : List Nat) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) :
    packetGraphBareAmplitude edges
        (fun edge => packetTransfer (P edge)) label ≈
      graphEigen edges label * packetGraphBareAmplitude edges P label := by
  unfold packetGraphBareAmplitude graphEigen
  exact Q'.eqv_trans _
    (eliminateLinks
      (fun edge => packetEigen (label edge) *
        coeffAt (P edge) (label edge)) edges) _
    (eliminateLinks_congr _ _
      (fun edge => coeffAt_packetTransfer (P edge) (label edge)) edges)
    (by
      unfold packetEigen
      exact eliminateLinks_pointwise_mul
        (fun edge => eigA SU2PeterWeylWilsonBlock.coupling (label edge))
        (fun edge => coeffAt (P edge) (label edge)) edges)

/-- The same identity after the gauge and global-vacuum projector. -/
theorem packetGraphProjectedAmplitude_transfer {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (label : EdgeLabelling) :
    packetGraphProjectedAmplitude edges vertices
        (fun edge => packetTransfer (P edge)) label ≈
      graphTransfer edges
        (packetGraphProjectedAmplitude edges vertices P) label := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject graphTransfer
  by_cases hp : GraphPhysical edges vertices label
  · simp only [if_pos hp]
    exact packetGraphBareAmplitude_transfer edges P label
  · simp only [if_neg hp]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- One edgewise packet transfer shifts a complete-support correlator
summand by one unit of discrete time. -/
theorem projectedCorrTerm_transfer_shift {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) :
    projectedCorrTerm edges vertices
        (fun edge => packetTransfer (P edge)) n label ≈
      projectedCorrTerm edges vertices P (n + 1) label := by
  let e := graphEigen edges label
  let a := packetGraphProjectedAmplitude edges vertices P label
  have ha : packetGraphProjectedAmplitude edges vertices
      (fun edge => packetTransfer (P edge)) label ≈ e * a :=
    packetGraphProjectedAmplitude_transfer edges vertices P label
  unfold projectedCorrTerm projectedSquare
  rw [Q'.pow_succ]
  change
    (packetGraphProjectedAmplitude edges vertices
      (fun edge => packetTransfer (P edge)) label *
      packetGraphProjectedAmplitude edges vertices
        (fun edge => packetTransfer (P edge)) label) *
        (e * e) ^ n ≈
      (a * a) * ((e * e) * (e * e) ^ n)
  exact Q'.eqv_trans _ (((e * a) * (e * a)) * (e * e) ^ n) _
    (Q'.mul_eqv_congr_right _ _ _ (q_mul_congr ha ha))
    (by mul_ring_qeqv)

/-- Fixed-stage transfer-time compatibility for every integer-time
correlator. -/
theorem packetGraph_corr_transfer_shift {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat) :
    corr (packetGraphSpectralModel edges vertices
        (fun edge => packetTransfer (P edge))) n ≈
      corr (packetGraphSpectralModel edges vertices P) (n + 1) := by
  exact Q'.eqv_trans _ _ _
    (packetGraph_corr_eq_full edges vertices _ n)
    (Q'.eqv_trans _ _ _
      (listQSum_congr
        (projectedCorrTerm_transfer_shift edges vertices P n)
        (boundedEdgeLabellings K edges))
      (Q'.eqv_symm
        (packetGraph_corr_eq_full edges vertices P (n + 1))))

theorem stagedGraphCorr_transfer_shift (edges : List Nat)
    (vertices : List TrivalentVertex) (A : StagedGraphPacket) (n : Nat) :
    stagedGraphCorr edges vertices (stagedGraphTransfer A) n ≈
      stagedGraphCorr edges vertices A (n + 1) :=
  packetGraph_corr_transfer_shift edges vertices A.packet n

/-- On the actual cutoff quotient, graph transfer and one-unit time
translation agree literally in the rational quotient. -/
theorem colimitGraphCorr_transfer_shift (edges : List Nat)
    (hnodup : edges.Nodup) (vertices : List TrivalentVertex)
    (x : GraphPacketColimit) (n : Nat) :
    colimitGraphCorr edges hnodup vertices n (colimitGraphTransfer x) =
      colimitGraphCorr edges hnodup vertices (n + 1) x := by
  refine Quotient.inductionOn x ?_
  intro A
  apply Quotient.sound
  exact stagedGraphCorr_transfer_shift edges vertices A n

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.packetGraphBareAmplitude_transfer
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.packetGraphProjectedAmplitude_transfer
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.projectedCorrTerm_transfer_shift
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.packetGraph_corr_transfer_shift
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.stagedGraphCorr_transfer_shift
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift.colimitGraphCorr_transfer_shift
