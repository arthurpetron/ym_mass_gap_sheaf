/-
# All-time cutoff coherence for finite trivalent packet graphs

Cutoff padding was previously shown to preserve the time-zero norm and the
one-step transferred norm.  Here the same exact-zero support argument is
applied to every integer-time spectral correlator.  The finite spectral sum
is first rewritten as a complete Cartesian sum: rejected gauge modes vanish
because the projector is already part of the amplitude.  Padding then leaves
every old summand unchanged and kills every complementary higher-cutoff mode.

Honest scope: this proves coherence of the whole discrete-time correlator
sequence for one fixed finite graph.  It does not enlarge the graph or take a
thermodynamic or continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffNormInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

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

/-- One full-support summand of the time-`n` spectral correlator. -/
def projectedCorrTerm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) : Q' :=
  projectedSquare edges vertices packet label *
    (graphEigen edges label * graphEigen edges label) ^ n

theorem projectedCorrTerm_zero_of_unphysical {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling)
    (h : graphPhysicalB edges vertices label = false) :
    projectedCorrTerm edges vertices packet n label ≈ 0 := by
  unfold projectedCorrTerm
  exact Q'.eqv_trans _
    (0 * (graphEigen edges label * graphEigen edges label) ^ n) _
    (q_mul_congr
      (projectedSquare_zero_of_unphysical edges vertices packet label h)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

private theorem physical_filter_corr_eq_full {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    listQSum (projectedCorrTerm edges vertices packet n)
        (physicalEdgeLabellings K edges vertices) ≈
      listQSum (projectedCorrTerm edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  unfold physicalEdgeLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun label => if graphPhysicalB edges vertices label then
        projectedCorrTerm edges vertices packet n label else 0)
      (boundedEdgeLabellings K edges)) _
    (listQSum_filter _ _ _) ?_
  apply listQSum_congr
  intro label
  cases h : graphPhysicalB edges vertices label with
  | false =>
      exact Q'.eqv_symm
        (projectedCorrTerm_zero_of_unphysical
          edges vertices packet n label h)
  | true => exact Q'.eqv_refl _

/-- Every finite-graph correlator is a complete Cartesian label sum. -/
theorem packetGraph_corr_eq_full {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    corr (packetGraphSpectralModel edges vertices packet) n ≈
      listQSum (projectedCorrTerm edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  let support := physicalEdgeLabellings K edges vertices
  let term := projectedCorrTerm edges vertices packet n
  have hindexed :
      corr (packetGraphSpectralModel edges vertices packet) n ≈
        fsum (fun i => term (supportLabel support i)) support.length := by
    unfold corr packetGraphSpectralModel finiteNetworkFamilyModel
      CompactTransferGNS.diagOp.toSpectralModel
    rw [← YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
    intro i hi
    unfold term projectedCorrTerm packetGraphModeWeight physicalModeLabel
    simp only [familySquaredEigen, if_pos hi]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hindexed
    (Q'.eqv_trans _ _ _
      (fsum_supportLabel_eq_listQSum term support)
      (physical_filter_corr_eq_full edges vertices packet n))

theorem projectedCorrTerm_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) :
    projectedCorrTerm edges vertices
        (fun edge => padPacket hKL (packet edge)) n label ≈
      projectedCorrTerm edges vertices packet n label := by
  unfold projectedCorrTerm
  exact q_mul_congr
    (projectedSquare_pad hKL edges vertices packet label)
    (Q'.eqv_refl _)

theorem projectedCorrTerm_pad_zero_of_outside {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling)
    (hout : labelWithinB K edges label = false) :
    projectedCorrTerm edges vertices
      (fun edge => padPacket hKL (packet edge)) n label ≈ 0 := by
  unfold projectedCorrTerm
  exact Q'.eqv_trans _
    (0 * (graphEigen edges label * graphEigen edges label) ^ n) _
    (q_mul_congr
      (projectedSquare_pad_zero_of_outside hKL edges vertices packet
        label hout)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

theorem projectedCorrTerm_edge_perm {K : Nat}
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    projectedCorrTerm A vertices packet n label ≈
      projectedCorrTerm B vertices packet n label := by
  unfold projectedCorrTerm
  have he := graphEigen_order_independent label h
  exact q_mul_congr
    (projectedSquare_edge_perm vertices packet label h)
    (q_pow_congr (q_mul_congr he he) n)

theorem projectedCorrTerm_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) {A B : List TrivalentVertex} (h : A.Perm B) :
    projectedCorrTerm edges A packet n label ≈
      projectedCorrTerm edges B packet n label := by
  unfold projectedCorrTerm
  exact q_mul_congr
    (projectedSquare_vertex_perm edges packet label h)
    (Q'.eqv_refl _)

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

/-- The whole discrete-time correlator sequence is exactly coherent under
cutoff padding. -/
theorem packetGraph_corr_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    corr (packetGraphSpectralModel edges vertices
        (fun edge => padPacket hKL (packet edge))) n ≈
      corr (packetGraphSpectralModel edges vertices packet) n := by
  refine Q'.eqv_trans _
    (listQSum
      (projectedCorrTerm edges vertices
        (fun edge => padPacket hKL (packet edge)) n)
      (boundedEdgeLabellings L edges)) _
    (packetGraph_corr_eq_full edges vertices _ n) ?_
  refine Q'.eqv_trans _
    (listQSum
      (projectedCorrTerm edges vertices
        (fun edge => padPacket hKL (packet edge)) n)
      ((boundedEdgeLabellings L edges).filter (labelWithinB K edges))) _
    ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro label _ hout
    exact projectedCorrTerm_pad_zero_of_outside hKL edges vertices packet
      n label hout
  · rw [boundedEdgeLabellings_filter_cutoff hKL edges hnodup]
    exact Q'.eqv_trans _
      (listQSum (projectedCorrTerm edges vertices packet n)
        (boundedEdgeLabellings K edges)) _
      (listQSum_congr
        (projectedCorrTerm_pad hKL edges vertices packet n) _)
      (Q'.eqv_symm
        (packetGraph_corr_eq_full edges vertices packet n))

/-- Every integer-time correlator is independent of the edge enumeration
order, including the Cartesian reindexing of the full support. -/
theorem packetGraph_corr_edge_perm {K : Nat}
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    {A B : List Nat} (h : A.Perm B) :
    corr (packetGraphSpectralModel A vertices packet) n ≈
      corr (packetGraphSpectralModel B vertices packet) n := by
  exact Q'.eqv_trans _ _ _
    (packetGraph_corr_eq_full A vertices packet n)
    (Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun label => projectedCorrTerm_edge_perm
          vertices packet n label h)
        (boundedEdgeLabellings K A))
      (Q'.eqv_trans _ _ _
        (listQSum_bounded_perm K
          (projectedCorrTerm B vertices packet n) h)
        (Q'.eqv_symm
          (packetGraph_corr_eq_full B vertices packet n))))

/-- Every integer-time correlator is independent of the vertex enumeration
order. -/
theorem packetGraph_corr_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) (n : Nat)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    corr (packetGraphSpectralModel edges A packet) n ≈
      corr (packetGraphSpectralModel edges B packet) n := by
  exact Q'.eqv_trans _ _ _
    (packetGraph_corr_eq_full edges A packet n)
    (Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun label => projectedCorrTerm_vertex_perm
          edges packet n label h)
        (boundedEdgeLabellings K edges))
      (Q'.eqv_symm
        (packetGraph_corr_eq_full edges B packet n)))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.projectedCorrTerm_zero_of_unphysical
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.packetGraph_corr_eq_full
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.projectedCorrTerm_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.projectedCorrTerm_pad_zero_of_outside
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.packetGraph_corr_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.projectedCorrTerm_edge_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.projectedCorrTerm_vertex_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.packetGraph_corr_edge_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance.packetGraph_corr_vertex_perm
