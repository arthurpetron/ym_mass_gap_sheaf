/-
# Exact cutoff invariance of finite trivalent packet-graph correlators

For a finite graph with distinct edge identifiers, padding every character
packet from cutoff `K` to `L` preserves both complete-support norm formulas.
The larger Cartesian enumeration filters exactly to the old enumeration;
every complementary labelling contains an above-`K` edge coefficient and is
killed exactly by the padded packet.  No retained-mode indices are selected
or matched.

Consequently the actual time-zero norm, transferred norm, and the exact
spectral correlators at times zero and one are cutoff invariant.

Honest scope: this is exact cutoff coherence for one fixed finite graph.  It
does not construct a graph-size, thermodynamic, or continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_zero_of_mem
    (f : Nat → Q') {edge : Nat} : ∀ {edges : List Nat},
    edge ∈ edges → f edge ≈ 0 → eliminateLinks f edges ≈ 0
  | [], hmem, _ => by cases hmem
  | head :: rest, hmem, hz => by
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · subst head
        exact Q'.eqv_trans _ (0 * eliminateLinks f rest) _
          (q_mul_congr hz (Q'.eqv_refl _)) (Q'.zero_mul_eqv _)
      · exact Q'.eqv_trans _ (f head * 0) _
          (q_mul_congr (Q'.eqv_refl _)
            (eliminateLinks_zero_of_mem f hrest hz))
          (Q'.mul_zero_eqv _)

private theorem outside_old_has_above (K : Nat) (label : EdgeLabelling) :
    ∀ edges : List Nat, labelWithinB K edges label = false →
      ∃ edge, edge ∈ edges ∧ K < label edge
  | [], hout => by cases hout
  | edge :: rest, hout => by
      by_cases he : label edge < K + 1
      · have hrest : labelWithinB K rest label = false := by
          simpa only [labelWithinB, he, decide_true, Bool.true_and]
            using hout
        rcases outside_old_has_above K label rest hrest with
          ⟨e, hmem, habove⟩
        exact ⟨e, List.mem_cons_of_mem edge hmem, habove⟩
      · exact ⟨edge, List.mem_cons_self, by omega⟩

/-- A padded packet amplitude vanishes on every labelling outside the old
edgewise cutoff, independently of whether the graph projector accepts it. -/
theorem packetGraphProjectedAmplitude_pad_zero_of_outside {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hout : labelWithinB K edges label = false) :
    packetGraphProjectedAmplitude edges vertices
      (fun edge => padPacket hKL (packet edge)) label ≈ 0 := by
  rcases outside_old_has_above K label edges hout with
    ⟨edge, hmem, habove⟩
  by_cases hp : GraphPhysical edges vertices label
  · unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
    rw [if_pos hp]
    unfold packetGraphBareAmplitude
    apply eliminateLinks_zero_of_mem _ hmem
    rw [coeffAt_padPacket, coeffAt_of_gt (packet edge) habove]
    exact Q'.eqv_refl _
  · unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
    rw [if_neg hp]
    exact Q'.eqv_refl _

theorem projectedSquare_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling) :
    projectedSquare edges vertices
        (fun edge => padPacket hKL (packet edge)) label ≈
      projectedSquare edges vertices packet label := by
  unfold projectedSquare
  have ha := packetGraphProjectedAmplitude_pad hKL edges vertices packet label
  exact q_mul_congr ha ha

theorem projectedSquare_pad_zero_of_outside {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hout : labelWithinB K edges label = false) :
    projectedSquare edges vertices
      (fun edge => padPacket hKL (packet edge)) label ≈ 0 := by
  unfold projectedSquare
  have ha := packetGraphProjectedAmplitude_pad_zero_of_outside hKL
    edges vertices packet label hout
  exact Q'.eqv_trans _ (0 * 0) _ (q_mul_congr ha ha)
    (Q'.zero_mul_eqv _)

theorem transferredProjectedSquare_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling) :
    transferredProjectedSquare edges vertices
        (fun edge => padPacket hKL (packet edge)) label ≈
      transferredProjectedSquare edges vertices packet label := by
  unfold transferredProjectedSquare graphTransfer
  have ha := packetGraphProjectedAmplitude_pad hKL edges vertices packet label
  have hy := q_mul_congr (Q'.eqv_refl (graphEigen edges label)) ha
  exact q_mul_congr hy hy

theorem transferredProjectedSquare_pad_zero_of_outside {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hout : labelWithinB K edges label = false) :
    transferredProjectedSquare edges vertices
      (fun edge => padPacket hKL (packet edge)) label ≈ 0 := by
  unfold transferredProjectedSquare graphTransfer
  have ha := packetGraphProjectedAmplitude_pad_zero_of_outside hKL
    edges vertices packet label hout
  have hy : graphEigen edges label *
      packetGraphProjectedAmplitude edges vertices
        (fun edge => padPacket hKL (packet edge)) label ≈ 0 :=
    Q'.eqv_trans _ (graphEigen edges label * 0) _
      (q_mul_congr (Q'.eqv_refl _) ha) (Q'.mul_zero_eqv _)
  exact Q'.eqv_trans _ (0 * 0) _ (q_mul_congr hy hy)
    (Q'.zero_mul_eqv _)

private theorem listQSum_eq_filter_of_zero
    (f : EdgeLabelling → Q') (p : EdgeLabelling → Bool) :
    ∀ xs : List EdgeLabelling,
      (∀ x, x ∈ xs → p x = false → f x ≈ 0) →
      listQSum f xs ≈ listQSum f (xs.filter p)
  | [], _ => Q'.eqv_refl _
  | x :: xs, hz => by
      have htail : ∀ y, y ∈ xs → p y = false → f y ≈ 0 := by
        intro y hmem hp
        exact hz y (List.mem_cons_of_mem x hmem) hp
      cases hp : p x with
      | false =>
          simp only [List.filter, hp, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum f (xs.filter p)) _
            (Q'.add_eqv_congr' (hz x List.mem_cons_self hp)
              (listQSum_eq_filter_of_zero f p xs htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter, hp, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero f p xs htail)

/-- The complete Cartesian time-zero norm is exactly invariant under cutoff
padding.  Distinct edge identifiers are the graph well-formedness condition
needed by the explicit Cartesian enumeration. -/
theorem packetGraphFullExactNorm_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphFullExactNorm edges vertices
        (fun edge => padPacket hKL (packet edge)) ≈
      packetGraphFullExactNorm edges vertices packet := by
  unfold packetGraphFullExactNorm
  refine Q'.eqv_trans _
    (listQSum
      (projectedSquare edges vertices
        (fun edge => padPacket hKL (packet edge)))
      ((boundedEdgeLabellings L edges).filter (labelWithinB K edges))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro label _ hout
    exact projectedSquare_pad_zero_of_outside hKL edges vertices packet
      label hout
  · rw [boundedEdgeLabellings_filter_cutoff hKL edges hnodup]
    exact listQSum_congr
      (projectedSquare_pad hKL edges vertices packet) _

/-- The complete Cartesian transferred norm is exactly invariant under the
same cutoff padding. -/
theorem packetGraphFullTransferredNorm_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphFullTransferredNorm edges vertices
        (fun edge => padPacket hKL (packet edge)) ≈
      packetGraphFullTransferredNorm edges vertices packet := by
  unfold packetGraphFullTransferredNorm
  refine Q'.eqv_trans _
    (listQSum
      (transferredProjectedSquare edges vertices
        (fun edge => padPacket hKL (packet edge)))
      ((boundedEdgeLabellings L edges).filter (labelWithinB K edges))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro label _ hout
    exact transferredProjectedSquare_pad_zero_of_outside hKL edges vertices
      packet label hout
  · rw [boundedEdgeLabellings_filter_cutoff hKL edges hnodup]
    exact listQSum_congr
      (transferredProjectedSquare_pad hKL edges vertices packet) _

/-- The actual projected time-zero norm is independent of the chosen packet
cutoff once the packet family is padded. -/
theorem packetGraphExactNorm_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphExactNorm edges vertices
        (fun edge => padPacket hKL (packet edge)) ≈
      packetGraphExactNorm edges vertices packet := by
  exact Q'.eqv_trans _
    (packetGraphFullExactNorm edges vertices
      (fun edge => padPacket hKL (packet edge))) _
    (packetGraphExactNorm_eq_full edges vertices _)
    (Q'.eqv_trans _
      (packetGraphFullExactNorm edges vertices packet) _
      (packetGraphFullExactNorm_pad hKL edges hnodup vertices packet)
      (Q'.eqv_symm
        (packetGraphExactNorm_eq_full edges vertices packet)))

/-- The actual transferred norm is independent of the packet cutoff. -/
theorem packetGraphExactTransferredNorm_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphExactTransferredNorm edges vertices
        (fun edge => padPacket hKL (packet edge)) ≈
      packetGraphExactTransferredNorm edges vertices packet := by
  exact Q'.eqv_trans _
    (packetGraphOperatorTransferredNorm edges vertices
      (fun edge => padPacket hKL (packet edge))) _
    (Q'.eqv_symm
      (packetGraphOperatorTransferredNorm_eq edges vertices _))
    (Q'.eqv_trans _
      (packetGraphFullTransferredNorm edges vertices
        (fun edge => padPacket hKL (packet edge))) _
      (packetGraphOperatorTransferredNorm_eq_full edges vertices _)
      (Q'.eqv_trans _
        (packetGraphFullTransferredNorm edges vertices packet) _
        (packetGraphFullTransferredNorm_pad hKL edges hnodup vertices packet)
        (Q'.eqv_trans _
          (packetGraphOperatorTransferredNorm edges vertices packet) _
          (Q'.eqv_symm
            (packetGraphOperatorTransferredNorm_eq_full edges vertices packet))
          (packetGraphOperatorTransferredNorm_eq edges vertices packet))))

/-- Exact time-zero spectral correlators agree across the cutoff inclusion. -/
theorem packetGraph_corr_zero_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    corr (packetGraphSpectralModel edges vertices
        (fun edge => padPacket hKL (packet edge))) 0 ≈
      corr (packetGraphSpectralModel edges vertices packet) 0 := by
  exact Q'.eqv_trans _
    (packetGraphExactNorm edges vertices
      (fun edge => padPacket hKL (packet edge))) _
    (packetGraph_corr_zero_eq_exactNorm edges vertices _)
    (Q'.eqv_trans _
      (packetGraphExactNorm edges vertices packet) _
      (packetGraphExactNorm_pad hKL edges hnodup vertices packet)
      (Q'.eqv_symm
        (packetGraph_corr_zero_eq_exactNorm edges vertices packet)))

/-- Exact time-one spectral correlators agree across the cutoff inclusion. -/
theorem packetGraph_corr_one_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    corr (packetGraphSpectralModel edges vertices
        (fun edge => padPacket hKL (packet edge))) 1 ≈
      corr (packetGraphSpectralModel edges vertices packet) 1 := by
  exact Q'.eqv_trans _
    (packetGraphExactTransferredNorm edges vertices
      (fun edge => padPacket hKL (packet edge))) _
    (packetGraph_corr_one_eq_exactTransferredNorm edges vertices _)
    (Q'.eqv_trans _
      (packetGraphExactTransferredNorm edges vertices packet) _
      (packetGraphExactTransferredNorm_pad hKL edges hnodup vertices packet)
      (Q'.eqv_symm
        (packetGraph_corr_one_eq_exactTransferredNorm edges vertices packet)))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraphProjectedAmplitude_pad_zero_of_outside
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.projectedSquare_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.projectedSquare_pad_zero_of_outside
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.transferredProjectedSquare_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.transferredProjectedSquare_pad_zero_of_outside
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraphFullExactNorm_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraphFullTransferredNorm_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraphExactNorm_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraphExactTransferredNorm_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraph_corr_zero_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance.packetGraph_corr_one_pad
