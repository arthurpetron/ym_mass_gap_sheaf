/-
# Vacuum-cylinder coherence for finite trivalent packet graphs

Adjoining a fresh edge carrying the normalized vacuum packet leaves every
integer-time graph correlator unchanged.  The proof is a constructive finite
Fubini calculation: the new Cartesian spin sum collapses exactly to its
spin-zero term, all nonzero spins being killed by the vacuum coefficient.

This is the first graph-volume cylinder map compatible with the cutoff
colimit and transfer evolution.  It is intentionally only the normalized
vacuum extension.  It does not yet integrate an interacting boundary layer
or construct a thermodynamic limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphColimitTransferShift

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

private theorem listQSum_zero {A : Type} {f : A → Q'}
    (hf : ∀ x, f x ≈ 0) : ∀ xs, listQSum f xs ≈ 0
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      change f x + listQSum f xs ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (hf x) (listQSum_zero hf xs))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      change f x + listQSum f xs ≈ g x + listQSum g xs
      exact Q'.add_eqv_congr'
        (h x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Replace one fresh edge coordinate by the normalized vacuum packet. -/
def extendByVacuum {K : Nat} (newEdge : Nat)
    (P : Nat → CharacterPacket K) : Nat → CharacterPacket K :=
  fun edge => if edge = newEdge then vacuumPacket K else P edge

theorem coeffAt_vacuumPacket (K spin : Nat) :
    coeffAt (vacuumPacket K) spin = if spin = 0 then 1 else 0 := by
  by_cases hs : spin < K + 1
  · simp [coeffAt, vacuumPacket, hs]
  · have hne : spin ≠ 0 := by
      intro h
      subst spin
      exact hs (Nat.succ_pos K)
    simp [coeffAt, hs, hne]

theorem coeffAt_extendByVacuum_newEdge {K : Nat} (newEdge spin : Nat)
    (P : Nat → CharacterPacket K) :
    coeffAt (extendByVacuum newEdge P newEdge) spin =
      if spin = 0 then 1 else 0 := by
  rw [extendByVacuum, if_pos rfl]
  exact coeffAt_vacuumPacket K spin

private theorem setEdgeLabel_zero_of_eq (label : EdgeLabelling)
    (edge : Nat) (hzero : label edge = 0) :
    setEdgeLabel label edge 0 = label := by
  funext e
  by_cases he : e = edge
  · subst e
    simp [setEdgeLabel, hzero]
  · simp [setEdgeLabel, he]

private theorem eliminateLinks_zero_of_head
    (f : Nat → Q') (edge : Nat) (rest : List Nat)
    (hz : f edge ≈ 0) : eliminateLinks f (edge :: rest) ≈ 0 := by
  change f edge * eliminateLinks f rest ≈ 0
  exact Q'.eqv_trans _ (0 * eliminateLinks f rest) _
    (Q'.mul_eqv_congr_right _ _ _ hz)
    (Q'.zero_mul_eqv _)

private theorem bareAmplitude_vacuum_nonzero_spin {K : Nat}
    (newEdge : Nat) (edges : List Nat) (P : Nat → CharacterPacket K)
    (tail : EdgeLabelling) {spin : Nat} (hspin : spin ≠ 0) :
    packetGraphBareAmplitude (newEdge :: edges)
        (extendByVacuum newEdge P) (setEdgeLabel tail newEdge spin) ≈ 0 := by
  unfold packetGraphBareAmplitude
  apply eliminateLinks_zero_of_head
  rw [coeffAt_extendByVacuum_newEdge]
  simp [setEdgeLabel, hspin]
  exact Q'.eqv_refl 0

private theorem projectedCorrTerm_vacuum_nonzero_spin {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat) (tail : EdgeLabelling)
    {spin : Nat} (hspin : spin ≠ 0) :
    projectedCorrTerm (newEdge :: edges) vertices
        (extendByVacuum newEdge P) n
        (setEdgeLabel tail newEdge spin) ≈ 0 := by
  have hbare := bareAmplitude_vacuum_nonzero_spin
    newEdge edges P tail hspin
  unfold projectedCorrTerm projectedSquare packetGraphProjectedAmplitude
    graphGaugeVacuumProject
  by_cases hp : GraphPhysical (newEdge :: edges) vertices
      (setEdgeLabel tail newEdge spin)
  · rw [if_pos hp]
    exact Q'.eqv_trans _
      ((0 * 0) *
        (graphEigen (newEdge :: edges)
            (setEdgeLabel tail newEdge spin) *
          graphEigen (newEdge :: edges)
            (setEdgeLabel tail newEdge spin)) ^ n) _
      (q_mul_congr (q_mul_congr hbare hbare) (Q'.eqv_refl _))
      (Q'.zero_mul_eqv _)
  · rw [if_neg hp]
    exact Q'.zero_mul_eqv _

private theorem graphPhysical_vacuum_head (newEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (label : EdgeLabelling) (hzero : label newEdge = 0) :
    graphPhysicalB (newEdge :: edges) vertices label =
      graphPhysicalB edges vertices label := by
  have hnot : ¬ 1 ≤ label newEdge := by omega
  unfold graphPhysicalB
  simp only [hasExcitedB]
  rw [if_neg hnot]

private theorem eliminateLinks_extendByVacuum_fresh {K newEdge : Nat}
    (P : Nat → CharacterPacket K) (label : EdgeLabelling) :
    ∀ edges, newEdge ∉ edges →
      eliminateLinks
          (fun edge => coeffAt (extendByVacuum newEdge P edge) (label edge))
          edges =
        eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges
  | [], _ => rfl
  | edge :: rest, hfresh => by
      have hne : edge ≠ newEdge := by
        intro h
        subst edge
        exact hfresh List.mem_cons_self
      have hrest : newEdge ∉ rest := by
        intro hmem
        exact hfresh (List.mem_cons_of_mem edge hmem)
      simp only [eliminateLinks]
      rw [eliminateLinks_extendByVacuum_fresh P label rest hrest]
      simp [extendByVacuum, hne]

private theorem bareAmplitude_vacuum_head_zero {K : Nat}
    (newEdge : Nat) (edges : List Nat) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hzero : label newEdge = 0)
    (hfresh : newEdge ∉ edges) :
    packetGraphBareAmplitude (newEdge :: edges)
        (extendByVacuum newEdge P) label ≈
      packetGraphBareAmplitude edges P label := by
  unfold packetGraphBareAmplitude
  change coeffAt (extendByVacuum newEdge P newEdge) (label newEdge) *
      eliminateLinks
        (fun edge => coeffAt (extendByVacuum newEdge P edge) (label edge))
        edges ≈
    eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges
  have hrest := eliminateLinks_extendByVacuum_fresh P label edges hfresh
  rw [hzero, coeffAt_extendByVacuum_newEdge, if_pos rfl, hrest]
  exact Q'.one_mul_eqv _

private theorem projectedAmplitude_vacuum_head_zero {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hzero : label newEdge = 0) (hfresh : newEdge ∉ edges) :
    packetGraphProjectedAmplitude (newEdge :: edges) vertices
        (extendByVacuum newEdge P) label ≈
      packetGraphProjectedAmplitude edges vertices P label := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical edges vertices label
  · have hpnew : GraphPhysical (newEdge :: edges) vertices label := by
      change graphPhysicalB (newEdge :: edges) vertices label = true
      rw [graphPhysical_vacuum_head newEdge edges vertices label hzero]
      exact hp
    rw [if_pos hpnew, if_pos hp]
    exact bareAmplitude_vacuum_head_zero newEdge edges P label hzero hfresh
  · have hpnew : ¬ GraphPhysical (newEdge :: edges) vertices label := by
      intro hnew
      apply hp
      change graphPhysicalB edges vertices label = true
      rw [← graphPhysical_vacuum_head newEdge edges vertices label hzero]
      exact hnew
    rw [if_neg hpnew, if_neg hp]
    exact Q'.eqv_refl 0

private theorem graphEigen_vacuum_head_zero (newEdge : Nat)
    (edges : List Nat) (label : EdgeLabelling)
    (hzero : label newEdge = 0) :
    graphEigen (newEdge :: edges) label ≈ graphEigen edges label := by
  change eliminateLinks
      (fun e => eigA SU2PeterWeylWilsonBlock.coupling (label e))
        (newEdge :: edges) ≈
    eliminateLinks
      (fun e => eigA SU2PeterWeylWilsonBlock.coupling (label e)) edges
  rw [eliminateLinks]
  rw [hzero, eigA_zero]
  exact Q'.one_mul_eqv _

private theorem projectedCorrTerm_vacuum_head_zero {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat) (label : EdgeLabelling)
    (hzero : label newEdge = 0) (hfresh : newEdge ∉ edges) :
    projectedCorrTerm (newEdge :: edges) vertices
        (extendByVacuum newEdge P) n label ≈
      projectedCorrTerm edges vertices P n label := by
  unfold projectedCorrTerm projectedSquare
  have ha := projectedAmplitude_vacuum_head_zero
    newEdge edges vertices P label hzero hfresh
  have he := graphEigen_vacuum_head_zero newEdge edges label hzero
  exact q_mul_congr (q_mul_congr ha ha)
    (q_pow_congr (q_mul_congr he he) n)

private theorem bounded_tail_zero {K newEdge : Nat} {edges : List Nat}
    (hfresh : newEdge ∉ edges) {label : EdgeLabelling}
    (hmem : label ∈ boundedEdgeLabellings K edges) :
    label newEdge = 0 :=
  (boundedEdgeLabellings_sound K edges label hmem).2 newEdge hfresh

private theorem vacuum_spin_zero_slice {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat)
    (hfresh : newEdge ∉ edges) :
    listQSum
        (fun label => projectedCorrTerm (newEdge :: edges) vertices
          (extendByVacuum newEdge P) n
          (setEdgeLabel label newEdge 0))
        (boundedEdgeLabellings K edges) ≈
      listQSum (projectedCorrTerm edges vertices P n)
        (boundedEdgeLabellings K edges) := by
  apply listQSum_congr_mem
  intro label hmem
  have hzero := bounded_tail_zero hfresh hmem
  rw [setEdgeLabel_zero_of_eq label newEdge hzero]
  exact projectedCorrTerm_vacuum_head_zero
    newEdge edges vertices P n label hzero hfresh

private theorem vacuum_nonzero_slice {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n spin : Nat) (hspin : spin ≠ 0) :
    listQSum
        (fun label => projectedCorrTerm (newEdge :: edges) vertices
          (extendByVacuum newEdge P) n
          (setEdgeLabel label newEdge spin))
        (boundedEdgeLabellings K edges) ≈ 0 := by
  apply listQSum_zero
  intro label
  exact projectedCorrTerm_vacuum_nonzero_spin
    newEdge edges vertices P n label hspin

/-- Adding a fresh normalized vacuum edge preserves every exact integer-time
correlator.  This is the finite-volume cylinder-consistency identity. -/
theorem packetGraph_corr_vacuum_cons {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat)
    (hfresh : newEdge ∉ edges) :
    corr (packetGraphSpectralModel (newEdge :: edges) vertices
        (extendByVacuum newEdge P)) n ≈
      corr (packetGraphSpectralModel edges vertices P) n := by
  let slice : Nat → Q' := fun spin =>
    listQSum
      (fun label => projectedCorrTerm (newEdge :: edges) vertices
        (extendByVacuum newEdge P) n
        (setEdgeLabel label newEdge spin))
      (boundedEdgeLabellings K edges)
  have hcollapse : fsum slice (K + 1) ≈ slice 0 := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro spin hspin
    exact vacuum_nonzero_slice newEdge edges vertices P n spin hspin
    exact Nat.succ_pos K
  exact Q'.eqv_trans _
    (listQSum (projectedCorrTerm (newEdge :: edges) vertices
      (extendByVacuum newEdge P) n)
      (boundedEdgeLabellings K (newEdge :: edges))) _
    (packetGraph_corr_eq_full (newEdge :: edges) vertices
      (extendByVacuum newEdge P) n)
    (Q'.eqv_trans _ (fsum slice (K + 1)) _
      (listQSum_bounded_cons K newEdge edges
        (projectedCorrTerm (newEdge :: edges) vertices
          (extendByVacuum newEdge P) n))
      (Q'.eqv_trans _ (slice 0) _ hcollapse
        (Q'.eqv_trans _
          (listQSum (projectedCorrTerm edges vertices P n)
            (boundedEdgeLabellings K edges)) _
          (vacuum_spin_zero_slice newEdge edges vertices P n hfresh)
          (Q'.eqv_symm
            (packetGraph_corr_eq_full edges vertices P n)))))

/-- Vacuum cylinder extension is fixed by edgewise Wilson transfer. -/
theorem packetTransfer_extendByVacuum {K : Nat}
    (newEdge edge : Nat) (P : Nat → CharacterPacket K) (spin : Nat) :
    coeffAt (packetTransfer (extendByVacuum newEdge P edge)) spin ≈
      coeffAt (extendByVacuum newEdge
        (fun e => packetTransfer (P e)) edge) spin := by
  by_cases he : edge = newEdge
  · subst edge
    rw [extendByVacuum, if_pos rfl, extendByVacuum, if_pos rfl]
    exact Q'.eqv_trans _
      (packetEigen spin * coeffAt (vacuumPacket K) spin) _
      (coeffAt_packetTransfer (vacuumPacket K) spin)
      (by
        rw [coeffAt_vacuumPacket]
        by_cases hs : spin = 0
        · subst spin
          rw [if_pos rfl, packetEigen_zero]
          exact Q'.one_mul_eqv 1
        · rw [if_neg hs]
          exact Q'.mul_zero_eqv _)
  · rw [extendByVacuum, if_neg he, extendByVacuum, if_neg he]
    exact Q'.eqv_refl _

/-! ## Descent to the actual cutoff quotient -/

def stagedVacuumCylinder (newEdge : Nat)
    (A : StagedGraphPacket) : StagedGraphPacket :=
  ⟨A.cutoff, extendByVacuum newEdge A.packet⟩

theorem stagedVacuumCylinder_congr (newEdge : Nat)
    {A B : StagedGraphPacket} (hAB : StagedGraphPacketEqv A B) :
    StagedGraphPacketEqv (stagedVacuumCylinder newEdge A)
      (stagedVacuumCylinder newEdge B) := by
  intro edge spin
  by_cases he : edge = newEdge
  · subst edge
    change coeffAt (extendByVacuum newEdge A.packet newEdge) spin ≈
      coeffAt (extendByVacuum newEdge B.packet newEdge) spin
    rw [coeffAt_extendByVacuum_newEdge,
      coeffAt_extendByVacuum_newEdge]
    exact Q'.eqv_refl _
  · simp only [stagedVacuumCylinder, extendByVacuum, if_neg he]
    exact hAB edge spin

/-- Adjoin a normalized vacuum coordinate directly on the graph-packet
cutoff colimit. -/
def colimitVacuumCylinder (newEdge : Nat) :
    GraphPacketColimit → GraphPacketColimit :=
  Quotient.lift
    (fun A => Quotient.mk stagedGraphPacketSetoid
      (stagedVacuumCylinder newEdge A))
    (fun _A _B hAB => Quotient.sound
      (stagedVacuumCylinder_congr newEdge hAB))

theorem colimitVacuumCylinder_include {K : Nat}
    (newEdge : Nat) (P : Nat → CharacterPacket K) :
    colimitVacuumCylinder newEdge (includeGraphPacket P) =
      includeGraphPacket (extendByVacuum newEdge P) := rfl

/-- Quotient-level cylinder consistency: all exact correlators are preserved
when a fresh normalized vacuum edge is adjoined. -/
theorem colimitGraphCorr_vacuum_cons (newEdge : Nat)
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (n : Nat)
    (hfresh : newEdge ∉ edges) (x : GraphPacketColimit) :
    colimitGraphCorr (newEdge :: edges)
        (List.nodup_cons.mpr ⟨hfresh, hnodup⟩) vertices n
        (colimitVacuumCylinder newEdge x) =
      colimitGraphCorr edges hnodup vertices n x := by
  refine Quotient.inductionOn x ?_
  intro A
  apply Quotient.sound
  exact packetGraph_corr_vacuum_cons
    newEdge edges vertices A.packet n hfresh

/-- The quotient vacuum-cylinder map intertwines the exact edgewise Wilson
transfer. -/
theorem colimitGraphTransfer_vacuumCylinder (newEdge : Nat)
    (x : GraphPacketColimit) :
    colimitGraphTransfer (colimitVacuumCylinder newEdge x) =
      colimitVacuumCylinder newEdge (colimitGraphTransfer x) := by
  refine Quotient.inductionOn x ?_
  intro A
  apply Quotient.sound
  intro edge spin
  exact packetTransfer_extendByVacuum newEdge edge A.packet spin

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_extendByVacuum_newEdge
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.packetGraph_corr_vacuum_cons
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.packetTransfer_extendByVacuum
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.stagedVacuumCylinder_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.colimitVacuumCylinder
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.colimitGraphCorr_vacuum_cons
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.colimitGraphTransfer_vacuumCylinder
