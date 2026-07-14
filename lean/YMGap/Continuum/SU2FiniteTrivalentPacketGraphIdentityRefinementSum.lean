/-
# Complete finite-sum collapse for trivalent identity refinement

The local identity-refinement amplitude is already exact on the label selected
by the vacuum fusion channel.  This module performs the two remaining finite
Cartesian sums.  The normalized vacuum packet kills every nonzero vacuum-leg
label, and `fusionOK a b 0` kills every copied-segment label except `b = a`.
Finite Fubini then collapses the refined time-zero correlator to the original
one with no multiplicity or normalization factor.

Honest scope: this is an exact finite-cutoff, finite-graph identity at time
zero.  At positive integer time the extra segment contributes one further
edge eigenvalue, so a continuum refinement still needs an explicit local
time/coupling rescaling.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum

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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude

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

private theorem eliminateLinks_zero_of_head
    (f : Nat → Q') (edge : Nat) (rest : List Nat)
    (hz : f edge ≈ 0) : eliminateLinks f (edge :: rest) ≈ 0 := by
  change f edge * eliminateLinks f rest ≈ 0
  exact Q'.eqv_trans _ (0 * eliminateLinks f rest) _
    (Q'.mul_eqv_congr_right _ _ _ hz)
    (Q'.zero_mul_eqv _)

private theorem listQSum_zero {A : Type} {f : A → Q'}
    (hz : ∀ x, f x ≈ 0) : ∀ xs, listQSum f xs ≈ 0
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      change f x + listQSum f xs ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (hz x) (listQSum_zero hz xs))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      change f x + listQSum f xs ≈ g x + listQSum g xs
      exact Q'.add_eqv_congr'
        (h x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- A finite Fubini identity between a structural list sum and `fsum`. -/
theorem fsum_listQSum_swap {A : Type} (g : Nat → A → Q') :
    ∀ (xs : List A) (n : Nat),
      fsum (fun spin => listQSum (g spin) xs) n ≈
        listQSum (fun x => fsum (fun spin => g spin x) n) xs
  | [], n =>
      YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below n
        (fun _ _ => Q'.eqv_refl 0)
  | x :: xs, n => by
      change fsum
          (fun spin => g spin x + listQSum (g spin) xs) n ≈
        fsum (fun spin => g spin x) n +
          listQSum (fun y => fsum (fun spin => g spin y) n) xs
      exact Q'.eqv_trans _ _ _
        (YMGap.Continuum.CubeRatioBounds.fsum_add
          (fun spin => g spin x)
          (fun spin => listQSum (g spin) xs) n)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (fsum_listQSum_swap g xs n))

private theorem refinedGenerated_old
    (oldEdge newEdge vacuumEdge spin : Nat) (label : EdgeLabelling)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge) :
    setEdgeLabel (setEdgeLabel label newEdge spin) vacuumEdge 0 oldEdge =
      label oldEdge := by
  simp [setEdgeLabel, Ne.symm hno, Ne.symm hvo]

private theorem refinedGenerated_new
    (newEdge vacuumEdge spin : Nat) (label : EdgeLabelling)
    (hnv : newEdge ≠ vacuumEdge) :
    setEdgeLabel (setEdgeLabel label newEdge spin) vacuumEdge 0 newEdge =
      spin := by
  simp [setEdgeLabel, hnv]

private theorem refinedGenerated_vacuum
    (newEdge vacuumEdge spin : Nat) (label : EdgeLabelling) :
    setEdgeLabel (setEdgeLabel label newEdge spin) vacuumEdge 0 vacuumEdge =
      0 := by
  simp [setEdgeLabel]

private theorem setEdgeLabel_current (label : EdgeLabelling) (edge : Nat) :
    setEdgeLabel label edge (label edge) = label := by
  funext e
  by_cases h : e = edge
  · subst e
    simp [setEdgeLabel]
  · simp [setEdgeLabel, h]

private theorem projectedCorrTerm_vacuum_spin_ne_zero {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (newSpin vacuumSpin : Nat)
    (hvacSpin : vacuumSpin ≠ 0) :
    projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel
          (setEdgeLabel tail newEdge newSpin) vacuumEdge vacuumSpin) ≈ 0 := by
  let label := setEdgeLabel
    (setEdgeLabel tail newEdge newSpin) vacuumEdge vacuumSpin
  have hcoeff : coeffAt
      (identityRefinedPacket newEdge vacuumEdge P vacuumEdge)
      (label vacuumEdge) ≈ 0 := by
    rw [show label vacuumEdge = vacuumSpin by
      simp [label, setEdgeLabel]]
    rw [identityRefinedPacket, if_pos rfl]
    rw [coeffAt_vacuumPacket]
    simp [hvacSpin]
    exact Q'.eqv_refl 0
  have hbare : packetGraphBareAmplitude
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedPacket newEdge vacuumEdge P) label ≈ 0 := by
    unfold packetGraphBareAmplitude identityRefinedEdges
    exact eliminateLinks_zero_of_head _ vacuumEdge (newEdge :: edges) hcoeff
  unfold projectedCorrTerm projectedSquare packetGraphProjectedAmplitude
    graphGaugeVacuumProject
  by_cases hp : GraphPhysical
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices) label
  · rw [if_pos hp]
    exact Q'.eqv_trans _
      ((0 * 0) *
        (graphEigen (identityRefinedEdges newEdge vacuumEdge edges) label *
          graphEigen (identityRefinedEdges newEdge vacuumEdge edges) label) ^ n) _
      (q_mul_congr (q_mul_congr hbare hbare) (Q'.eqv_refl _))
      (Q'.zero_mul_eqv _)
  · rw [if_neg hp]
    exact Q'.zero_mul_eqv _

private theorem refinedGenerated_unphysical_of_new_ne
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (tail : EdgeLabelling)
    (spin : Nat) (hspin : spin ≠ tail oldEdge)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    graphPhysicalB
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0) =
      false := by
  let label := setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0
  have hold : label oldEdge = tail oldEdge :=
    refinedGenerated_old oldEdge newEdge vacuumEdge spin tail hno hvo
  have hnew : label newEdge = spin :=
    refinedGenerated_new newEdge vacuumEdge spin tail hnv
  have hvac : label vacuumEdge = 0 :=
    refinedGenerated_vacuum newEdge vacuumEdge spin tail
  have hfusion : fusionOK (label oldEdge) (label newEdge)
      (label vacuumEdge) = false := by
    rw [hold, hnew, hvac]
    exact YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne
      (tail oldEdge) spin (Ne.symm hspin)
  unfold graphPhysicalB identityRefinedVertices identityRefinedVertex
    verticesAdmissibleB
  rw [hfusion]
  simp

private theorem projectedCorrTerm_new_spin_ne {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (spin : Nat)
    (hspin : spin ≠ tail oldEdge)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0) ≈ 0 := by
  apply projectedCorrTerm_zero_of_unphysical
  exact refinedGenerated_unphysical_of_new_ne
    oldEdge newEdge vacuumEdge edges vertices tail spin hspin hno hvo hnv

/-- For a fixed old labelling, the new-segment sum has exactly one surviving
fusion-diagonal term, and that term is the old time-zero integrand. -/
theorem identity_new_segment_slice {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (tail : EdgeLabelling) (hold : oldEdge ∈ edges)
    (htail : tail ∈ boundedEdgeLabellings K edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    fsum (fun spin => projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) 0
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1) ≈
      projectedCorrTerm edges vertices P 0 tail := by
  let slice : Nat → Q' := fun spin => projectedCorrTerm
    (identityRefinedEdges newEdge vacuumEdge edges)
    (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
    (identityRefinedPacket newEdge vacuumEdge P) 0
    (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0)
  have hbound : tail oldEdge < K + 1 :=
    (boundedEdgeLabellings_sound K edges tail htail).1 oldEdge hold
  have hcollapse : fsum slice (K + 1) ≈ slice (tail oldEdge) := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro spin hspin
    exact projectedCorrTerm_new_spin_ne oldEdge newEdge vacuumEdge
      edges vertices P 0 tail spin hspin hno hvo hnv
    exact hbound
  exact Q'.eqv_trans _ (slice (tail oldEdge)) _ hcollapse
    (projectedCorrTerm_identity_refinement_zero oldEdge newEdge vacuumEdge
      edges vertices P tail hold hbound hnew hvac hno hvo hnv hnewV hvacV)

/-- The complete time-zero correlator is exactly invariant under the
interacting trivalent identity refinement. -/
theorem packetGraph_corr_identity_refinement_zero {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (hold : oldEdge ∈ edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    corr (packetGraphSpectralModel
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P)) 0 ≈
      corr (packetGraphSpectralModel edges vertices P) 0 := by
  let refinedTerm : EdgeLabelling → Q' := projectedCorrTerm
    (identityRefinedEdges newEdge vacuumEdge edges)
    (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
    (identityRefinedPacket newEdge vacuumEdge P) 0
  let vacuumSlice : Nat → Q' := fun vacuumSpin =>
    listQSum
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge vacuumSpin))
      (boundedEdgeLabellings K (newEdge :: edges))
  have hvacCollapse : fsum vacuumSlice (K + 1) ≈ vacuumSlice 0 := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro vacuumSpin hspin
    apply listQSum_zero
    intro label
    have hz := projectedCorrTerm_vacuum_spin_ne_zero
      oldEdge newEdge vacuumEdge edges vertices P 0 label
        (label newEdge) vacuumSpin hspin
    rw [setEdgeLabel_current label newEdge] at hz
    exact hz
    exact Nat.succ_pos K
  have hnewExpand : vacuumSlice 0 ≈
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) := by
    exact listQSum_bounded_cons K newEdge edges
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge 0))
  have hswap :
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) ≈
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) :=
    fsum_listQSum_swap
      (fun spin tail => refinedTerm
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
      (boundedEdgeLabellings K edges) (K + 1)
  have hsliceCollapse :
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) ≈
      listQSum (projectedCorrTerm edges vertices P 0)
        (boundedEdgeLabellings K edges) := by
    apply listQSum_congr_mem
    intro tail htail
    exact identity_new_segment_slice oldEdge newEdge vacuumEdge
      edges vertices P tail hold htail hnew hvac hno hvo hnv hnewV hvacV
  exact Q'.eqv_trans _
    (listQSum refinedTerm
      (boundedEdgeLabellings K
        (identityRefinedEdges newEdge vacuumEdge edges))) _
    (packetGraph_corr_eq_full
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) 0)
    (Q'.eqv_trans _ (fsum vacuumSlice (K + 1)) _
      (listQSum_bounded_cons K vacuumEdge (newEdge :: edges) refinedTerm)
      (Q'.eqv_trans _ (vacuumSlice 0) _ hvacCollapse
        (Q'.eqv_trans _ _ _ hnewExpand
          (Q'.eqv_trans _ _ _ hswap
            (Q'.eqv_trans _
              (listQSum (projectedCorrTerm edges vertices P 0)
                (boundedEdgeLabellings K edges)) _
              hsliceCollapse
              (Q'.eqv_symm
                (packetGraph_corr_eq_full edges vertices P 0)))))))

/-! ## Exact positive-time reweighting -/

/-- The old-graph summand with the one extra copied-edge eigenvalue inserted.
This is the exact spectral effect of the local subdivision. -/
def identityRefinementReweightedTerm {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling) : Q' :=
  projectedSquare edges vertices P label *
    ((eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) *
        graphEigen edges label) *
      (eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) *
        graphEigen edges label)) ^ n

/-- On the fusion-selected label, the all-time refined summand is exactly the
old summand reweighted by one copied-edge eigenvalue on each transfer side. -/
theorem projectedCorrTerm_identity_refinement_selected {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      identityRefinementReweightedTerm oldEdge edges vertices P n label := by
  have ha := packetGraphProjectedAmplitude_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices P label hold holdBound
      hnew hvac hno hvo hnv hnewV hvacV
  have he := graphEigen_identity_refinement
    oldEdge newEdge vacuumEdge edges label hnew hvac hnv
  unfold projectedCorrTerm identityRefinementReweightedTerm projectedSquare
  exact q_mul_congr (q_mul_congr ha ha)
    (q_pow_congr (q_mul_congr he he) n)

/-- For a fixed old labelling, the copied-segment sum collapses at every
integer time to the explicitly reweighted old summand. -/
theorem identity_new_segment_slice_all_time {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (hold : oldEdge ∈ edges)
    (htail : tail ∈ boundedEdgeLabellings K edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    fsum (fun spin => projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1) ≈
      identityRefinementReweightedTerm oldEdge edges vertices P n tail := by
  let slice : Nat → Q' := fun spin => projectedCorrTerm
    (identityRefinedEdges newEdge vacuumEdge edges)
    (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
    (identityRefinedPacket newEdge vacuumEdge P) n
    (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0)
  have hbound : tail oldEdge < K + 1 :=
    (boundedEdgeLabellings_sound K edges tail htail).1 oldEdge hold
  have hcollapse : fsum slice (K + 1) ≈ slice (tail oldEdge) := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro spin hspin
    exact projectedCorrTerm_new_spin_ne oldEdge newEdge vacuumEdge
      edges vertices P n tail spin hspin hno hvo hnv
    exact hbound
  exact Q'.eqv_trans _ (slice (tail oldEdge)) _ hcollapse
    (projectedCorrTerm_identity_refinement_selected
      oldEdge newEdge vacuumEdge edges vertices P n tail hold hbound
        hnew hvac hno hvo hnv hnewV hvacV)

/-- The full refined correlator at every integer time is an exact old-label
sum with the copied-edge spectral factor displayed.  Thus time zero is
cylinder-consistent, while positive time records the precise local
time/coupling rescaling still required by continuum refinement. -/
theorem packetGraph_corr_identity_refinement_all_time {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (hold : oldEdge ∈ edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    corr (packetGraphSpectralModel
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P)) n ≈
      listQSum
        (identityRefinementReweightedTerm oldEdge edges vertices P n)
        (boundedEdgeLabellings K edges) := by
  let refinedTerm : EdgeLabelling → Q' := projectedCorrTerm
    (identityRefinedEdges newEdge vacuumEdge edges)
    (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
    (identityRefinedPacket newEdge vacuumEdge P) n
  let vacuumSlice : Nat → Q' := fun vacuumSpin =>
    listQSum
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge vacuumSpin))
      (boundedEdgeLabellings K (newEdge :: edges))
  have hvacCollapse : fsum vacuumSlice (K + 1) ≈ vacuumSlice 0 := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro vacuumSpin hspin
    apply listQSum_zero
    intro label
    have hz := projectedCorrTerm_vacuum_spin_ne_zero
      oldEdge newEdge vacuumEdge edges vertices P n label
        (label newEdge) vacuumSpin hspin
    rw [setEdgeLabel_current label newEdge] at hz
    exact hz
    exact Nat.succ_pos K
  have hnewExpand : vacuumSlice 0 ≈
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) := by
    exact listQSum_bounded_cons K newEdge edges
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge 0))
  have hswap :
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) ≈
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) :=
    fsum_listQSum_swap
      (fun spin tail => refinedTerm
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
      (boundedEdgeLabellings K edges) (K + 1)
  have hsliceCollapse :
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) ≈
      listQSum
        (identityRefinementReweightedTerm oldEdge edges vertices P n)
        (boundedEdgeLabellings K edges) := by
    apply listQSum_congr_mem
    intro tail htail
    exact identity_new_segment_slice_all_time oldEdge newEdge vacuumEdge
      edges vertices P n tail hold htail hnew hvac hno hvo hnv
        hnewV hvacV
  exact Q'.eqv_trans _
    (listQSum refinedTerm
      (boundedEdgeLabellings K
        (identityRefinedEdges newEdge vacuumEdge edges))) _
    (packetGraph_corr_eq_full
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) n)
    (Q'.eqv_trans _ (fsum vacuumSlice (K + 1)) _
      (listQSum_bounded_cons K vacuumEdge (newEdge :: edges) refinedTerm)
      (Q'.eqv_trans _ (vacuumSlice 0) _ hvacCollapse
        (Q'.eqv_trans _ _ _ hnewExpand
          (Q'.eqv_trans _ _ _ hswap hsliceCollapse))))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.fsum_listQSum_swap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.identity_new_segment_slice
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.packetGraph_corr_identity_refinement_zero
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.projectedCorrTerm_identity_refinement_selected
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.identity_new_segment_slice_all_time
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum.packetGraph_corr_identity_refinement_all_time
