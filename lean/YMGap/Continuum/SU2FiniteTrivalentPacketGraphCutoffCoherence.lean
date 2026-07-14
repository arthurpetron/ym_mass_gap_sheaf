/-
# Cutoff coherence for actual finite trivalent packet graphs

Padding every edge packet from cutoff `K` to `L` leaves the derived graph
amplitude unchanged on every old labelling.  A physical `L`-labelling absent
at cutoff `K` necessarily contains an edge label above `K`; the padded old
packet coefficient on that edge is exactly zero.  Thus genuinely new modes
have zero projected amplitude and zero spectral weight.

For edge lists without repetitions (the graph case), the enumeration at the
larger cutoff filters back to the old enumeration exactly.  This identifies
the finite sums and proves exact norm and correlator invariance.

Honest scope: this is cutoff coherence for each fixed finite trivalent graph.
It does not take a graph-size or continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
import YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr
    (f g : Nat → Q') (hfg : ∀ edge, f edge ≈ g edge) :
    ∀ edges, eliminateLinks f edges ≈ eliminateLinks g edges
  | [] => Q'.eqv_refl _
  | edge :: rest =>
      q_mul_congr (hfg edge) (eliminateLinks_congr f g hfg rest)

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

/-! ## Pointwise padding coherence -/

theorem packetGraphBareAmplitude_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) :
    packetGraphBareAmplitude edges (fun edge => padPacket hKL (packet edge))
        label ≈
      packetGraphBareAmplitude edges packet label := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_congr _ _ (fun edge => by
    rw [coeffAt_padPacket]
    exact Q'.eqv_refl _) edges

/-- The actual gauge/vacuum-projected amplitude is unchanged pointwise, not
only on the enumerated support. -/
theorem packetGraphProjectedAmplitude_pad {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling) :
    packetGraphProjectedAmplitude edges vertices
        (fun edge => padPacket hKL (packet edge)) label ≈
      packetGraphProjectedAmplitude edges vertices packet label := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical edges vertices label
  · rw [if_pos hp, if_pos hp]
    exact packetGraphBareAmplitude_pad hKL edges packet label
  · rw [if_neg hp, if_neg hp]
    exact Q'.eqv_refl _

theorem packetGraphProjectedAmplitude_pad_old_mode {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (i : Nat) :
    packetGraphProjectedAmplitude edges vertices
        (fun edge => padPacket hKL (packet edge))
        (physicalModeLabel K edges vertices i) ≈
      packetGraphProjectedAmplitude edges vertices packet
        (physicalModeLabel K edges vertices i) :=
  packetGraphProjectedAmplitude_pad hKL edges vertices packet _

/-! ## New physical modes have exactly zero amplitude -/

private theorem edge_bounds_or_above (K : Nat) (label : EdgeLabelling) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → label edge < K + 1) ∨
      ∃ edge, edge ∈ edges ∧ K < label edge
  | [] => Or.inl (fun edge hmem => by cases hmem)
  | edge :: rest => by
      by_cases he : label edge < K + 1
      · rcases edge_bounds_or_above K label rest with hrest | hrest
        · exact Or.inl (fun e hmem => by
            simp only [List.mem_cons] at hmem
            exact hmem.elim (fun h => h ▸ he) (hrest e))
        · rcases hrest with ⟨e, hemem, heabove⟩
          exact Or.inr ⟨e, List.mem_cons_of_mem edge hemem, heabove⟩
      · exact Or.inr ⟨edge, List.mem_cons_self, by omega⟩

private theorem physical_new_has_above {K L : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (label : EdgeLabelling)
    (hnew : label ∈ physicalEdgeLabellings L edges vertices)
    (hold : label ∉ physicalEdgeLabellings K edges vertices) :
    ∃ edge, edge ∈ edges ∧ K < label edge := by
  have hnew' := List.mem_filter.mp hnew
  have hs := boundedEdgeLabellings_sound L edges label hnew'.1
  rcases edge_bounds_or_above K label edges with hbounded | habove
  · have hmemK : label ∈ boundedEdgeLabellings K edges :=
      boundedEdgeLabellings_complete K edges label hbounded hs.2
    exact (hold (List.mem_filter.mpr ⟨hmemK, hnew'.2⟩)).elim
  · exact habove

/-- Every larger-cutoff physical labelling not already present at the old
cutoff contains an above-cutoff edge coefficient and is killed exactly by
padding the old packet family. -/
theorem packetGraphProjectedAmplitude_pad_extra_zero {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hnew : label ∈ physicalEdgeLabellings L edges vertices)
    (hold : label ∉ physicalEdgeLabellings K edges vertices) :
    packetGraphProjectedAmplitude edges vertices
      (fun edge => padPacket hKL (packet edge)) label ≈ 0 := by
  have hp : GraphPhysical edges vertices label := (List.mem_filter.mp hnew).2
  rcases physical_new_has_above edges vertices label hnew hold with
    ⟨edge, hmem, habove⟩
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos hp]
  unfold packetGraphBareAmplitude
  apply eliminateLinks_zero_of_mem _ hmem
  rw [coeffAt_padPacket, coeffAt_of_gt (packet edge) habove]
  exact Q'.eqv_refl _

theorem packetGraphModeWeight_pad_extra_zero {K L : Nat}
    (hKL : K ≤ L) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) {i : Nat}
    (hi : i < (physicalEdgeLabellings L edges vertices).length)
    (hold : physicalModeLabel L edges vertices i ∉
      physicalEdgeLabellings K edges vertices) :
    packetGraphModeWeight edges vertices
      (fun edge => padPacket hKL (packet edge)) i ≈ 0 := by
  have hnew : physicalModeLabel L edges vertices i ∈
      physicalEdgeLabellings L edges vertices := by
    exact supportLabel_mem hi
  have ha := packetGraphProjectedAmplitude_pad_extra_zero hKL edges vertices
    packet (physicalModeLabel L edges vertices i) hnew hold
  unfold packetGraphModeWeight
  exact Q'.eqv_trans _ (0 * 0) _ (q_mul_congr ha ha) (Q'.zero_mul_eqv _)

/-! ## Exact filtering of the larger enumeration -/

def labelWithinB (K : Nat) : List Nat → EdgeLabelling → Bool
  | [], _ => true
  | edge :: rest, label =>
      decide (label edge < K + 1) && labelWithinB K rest label

theorem labelWithinB_true_iff (K : Nat) : ∀ edges label,
    labelWithinB K edges label = true ↔
      ∀ edge, edge ∈ edges → label edge < K + 1
  | [], label => by simp [labelWithinB]
  | edge :: rest, label => by
      rw [labelWithinB, Bool.and_eq_true]
      simp only [decide_eq_true_eq, labelWithinB_true_iff K rest label]
      constructor
      · rintro ⟨he, hr⟩ e hmem
        simp only [List.mem_cons] at hmem
        exact hmem.elim (fun h => h ▸ he) (hr e)
      · intro h
        exact ⟨h edge List.mem_cons_self,
          fun e he => h e (List.mem_cons_of_mem edge he)⟩

private theorem labelWithinB_set_fresh (K : Nat)
    (label : EdgeLabelling) (edge spin : Nat) : ∀ rest,
    edge ∉ rest →
      labelWithinB K rest (setEdgeLabel label edge spin) =
        labelWithinB K rest label
  | [], _ => rfl
  | head :: rest, hnot => by
      have hne : head ≠ edge := by
        intro h
        apply hnot
        subst head
        exact List.mem_cons_self
      have hrest : edge ∉ rest := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [labelWithinB, setEdgeLabel, if_neg hne]
      rw [labelWithinB_set_fresh K label edge spin rest hrest]

private theorem filter_setEdgeLabel_block (K : Nat)
    (edge spin : Nat) (rest : List Nat) (hfresh : edge ∉ rest) :
    ∀ tails : List EdgeLabelling,
    List.filter (labelWithinB K (edge :: rest))
        (tails.map (fun label => setEdgeLabel label edge spin)) =
      if spin < K + 1 then
        (List.filter (labelWithinB K rest) tails).map
          (fun label => setEdgeLabel label edge spin)
      else []
  | [] => by simp
  | label :: tails => by
      rw [List.map_cons, List.filter_cons]
      have hhead :
          labelWithinB K (edge :: rest)
              (setEdgeLabel label edge spin) =
            (decide (spin < K + 1) && labelWithinB K rest label) := by
        simp only [labelWithinB, setEdgeLabel,
          if_true,
          labelWithinB_set_fresh K label edge spin rest hfresh]
      rw [hhead,
        filter_setEdgeLabel_block K edge spin rest hfresh tails]
      by_cases hs : spin < K + 1
      · rw [if_pos hs]
        simp only [hs, decide_true, Bool.true_and, List.filter_cons]
        by_cases ht : labelWithinB K rest label = true
        · simp only [ht, if_true, List.map_cons]
        · simp only [ht, Bool.false_eq_true, if_false, if_true]
      · rw [if_neg hs]
        simp only [hs, decide_false, Bool.false_and,
          Bool.false_eq_true, if_false]

private theorem flatMap_if_lt_eq_filter (K : Nat)
    (g : Nat → List EdgeLabelling) : ∀ spins : List Nat,
    spins.flatMap (fun spin => if spin < K + 1 then g spin else []) =
      (spins.filter (fun spin => decide (spin < K + 1))).flatMap g
  | [] => rfl
  | spin :: spins => by
      simp only [List.flatMap_cons, List.filter_cons]
      by_cases hs : spin < K + 1
      · simp only [hs, if_true, decide_true, List.flatMap_cons,
          flatMap_if_lt_eq_filter K g spins]
      · simp only [hs, if_false, decide_false, Bool.false_eq_true,
          List.nil_append,
          flatMap_if_lt_eq_filter K g spins]

private theorem range_filter_cutoff {K L : Nat} (hKL : K ≤ L) :
    (List.range (L + 1)).filter (fun spin => decide (spin < K + 1)) =
      List.range (K + 1) := by
  induction L generalizing K with
  | zero =>
      have hK : K = 0 := by omega
      subst K
      rfl
  | succ L ih =>
      by_cases hprev : K ≤ L
      · rw [show Nat.succ L + 1 = (L + 1) + 1 by omega,
          List.range_succ, List.filter_append, ih hprev]
        have hnot : ¬ L + 1 < K + 1 := by omega
        simp only [List.filter_cons, hnot, decide_false,
          Bool.false_eq_true, if_false, List.filter_nil,
          List.append_nil]
      · have hK : K = L + 1 := by omega
        subst K
        apply (List.filter_eq_self).2
        intro spin hmem
        exact decide_eq_true (List.mem_range.mp hmem)

private theorem listFlatMap_congr {A B : Type} (xs : List A)
    (f g : A → List B) (h : ∀ x, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, h x, ih]

/-- With distinct edge identifiers, filtering the larger Cartesian
enumeration by the old bound recovers the old enumeration exactly. -/
theorem boundedEdgeLabellings_filter_cutoff {K L : Nat} (hKL : K ≤ L) :
    ∀ edges : List Nat, edges.Nodup →
      (boundedEdgeLabellings L edges).filter (labelWithinB K edges) =
        boundedEdgeLabellings K edges
  | [], _ => by simp [boundedEdgeLabellings, labelWithinB]
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      rw [boundedEdgeLabellings, boundedEdgeLabellings,
        List.filter_flatMap]
      refine Eq.trans
        (listFlatMap_congr _ _ _ (fun spin =>
          filter_setEdgeLabel_block K edge spin rest hfresh _)) ?_
      rw [flatMap_if_lt_eq_filter K, range_filter_cutoff hKL,
        boundedEdgeLabellings_filter_cutoff hKL rest hrest]

private theorem filter_comm (p q : EdgeLabelling → Bool)
    (support : List EdgeLabelling) :
    (support.filter q).filter p = (support.filter p).filter q := by
  simp only [List.filter_filter]
  congr 1
  funext label
  exact Bool.and_comm _ _

/-- The physical support at cutoff `K` is exactly the old-bound filter of
the physical support at cutoff `L`. -/
theorem physicalEdgeLabellings_filter_cutoff {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) :
    (physicalEdgeLabellings L edges vertices).filter (labelWithinB K edges) =
      physicalEdgeLabellings K edges vertices := by
  unfold physicalEdgeLabellings
  rw [filter_comm, boundedEdgeLabellings_filter_cutoff hKL edges hnodup]

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.packetGraphBareAmplitude_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.packetGraphProjectedAmplitude_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.packetGraphProjectedAmplitude_pad_old_mode
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.packetGraphProjectedAmplitude_pad_extra_zero
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.packetGraphModeWeight_pad_extra_zero
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.labelWithinB_true_iff
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.boundedEdgeLabellings_filter_cutoff
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence.physicalEdgeLabellings_filter_cutoff
