/-
# Actual packet amplitudes and operators for arbitrary finite trivalent graphs

The earlier finite-graph envelope accepts a free function on edge labellings
and a free finite support.  Here both are constructed.  For a cutoff `K` and
an explicit finite edge list, `boundedEdgeLabellings` enumerates every
labelling supported on those edges with labels in `0, ..., K`; soundness and
completeness are proved.  Filtering by the exact trivalent fusion guards and
the global nonvacuum guard gives the physical spin-network modes.

An edge packet supplies the coefficient on each edge, so the bare graph
amplitude is their exact finite product.  The gauge/vacuum projector is then
applied to that derived amplitude.  Squaring these actual amplitudes gives a
concrete diagonal spectral model.  Its transfer eigenvalue is the product of
the exact heat-kernel eigenvalues on the graph edges, and its time-one
correlator is proved equal to the squared norm of the explicit graph
transfer.  Consequently every such finite physical packet graph has the
same exact `63/64` located squared-gap margin.

The tetrahedral graph with quadratic packets supplies a nonzero retained
mode of exact weight one, so the construction is not vacuous.

Honest scope: this constructs arbitrary finite trivalent packet graphs at a
fixed cutoff.  It does not yet identify the diagonal graph carrier with one
single completed colimit GNS quotient for every graph, nor take the
thermodynamic or continuum limit.
-/

import YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
import YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Exact enumeration of all bounded edge labellings -/

def zeroEdgeLabelling : EdgeLabelling := fun _ => 0

def setEdgeLabel (label : EdgeLabelling) (edge spin : Nat) : EdgeLabelling :=
  fun e => if e = edge then spin else label e

/-- Cartesian enumeration of all labels `0, ..., K` on the listed edges.
Every unlisted edge is fixed to zero. -/
def boundedEdgeLabellings (K : Nat) : List Nat → List EdgeLabelling
  | [] => [zeroEdgeLabelling]
  | edge :: rest =>
      (List.range (K + 1)).flatMap (fun spin =>
        (boundedEdgeLabellings K rest).map
          (fun label => setEdgeLabel label edge spin))

/-- Every enumerated labelling is bounded on the listed edges and vanishes
off their support. -/
theorem boundedEdgeLabellings_sound (K : Nat) : ∀ edges label,
    label ∈ boundedEdgeLabellings K edges →
      (∀ edge, edge ∈ edges → label edge < K + 1) ∧
      (∀ edge, edge ∉ edges → label edge = 0)
  | [], label, h => by
      simp only [boundedEdgeLabellings, List.mem_singleton] at h
      subst label
      constructor
      · intro edge hmem
        cases hmem
      · intro edge _
        rfl
  | edge :: rest, label, h => by
      rw [boundedEdgeLabellings, List.mem_flatMap] at h
      rcases h with ⟨spin, hspin, hmap⟩
      rw [List.mem_map] at hmap
      rcases hmap with ⟨tail, htail, hset⟩
      subst label
      have ih := boundedEdgeLabellings_sound K rest tail htail
      constructor
      · intro e he
        rw [List.mem_cons] at he
        rcases he with rfl | herest
        · simpa [setEdgeLabel] using (List.mem_range.mp hspin)
        · by_cases heq : e = edge
          · subst e
            simpa [setEdgeLabel] using (List.mem_range.mp hspin)
          · simp only [setEdgeLabel, if_neg heq]
            exact ih.1 e herest
      · intro e he
        have hne : e ≠ edge := by
          intro heq
          apply he
          subst e
          exact List.mem_cons_self
        have hnrest : e ∉ rest := by
          intro hmem
          exact he (List.mem_cons_of_mem edge hmem)
        simp only [setEdgeLabel, if_neg hne]
        exact ih.2 e hnrest

/-- Conversely, every bounded labelling supported on the listed edges occurs
in the explicit Cartesian enumeration. -/
theorem boundedEdgeLabellings_complete (K : Nat) : ∀ edges label,
    (∀ edge, edge ∈ edges → label edge < K + 1) →
    (∀ edge, edge ∉ edges → label edge = 0) →
      label ∈ boundedEdgeLabellings K edges
  | [], label, _, hzero => by
      have hlabel : label = zeroEdgeLabelling := by
        funext edge
        exact hzero edge (by simp)
      subst label
      exact List.mem_cons_self
  | edge :: rest, label, hbound, hzero => by
      let tail : EdgeLabelling := fun e => if e = edge then 0 else label e
      have htailBound : ∀ e, e ∈ rest → tail e < K + 1 := by
        intro e he
        by_cases heq : e = edge
        · simp [tail, heq]
        · simp only [tail, if_neg heq]
          exact hbound e (List.mem_cons_of_mem edge he)
      have htailZero : ∀ e, e ∉ rest → tail e = 0 := by
        intro e he
        by_cases heq : e = edge
        · simp [tail, heq]
        · simp only [tail, if_neg heq]
          exact hzero e (by
            intro hmem
            rw [List.mem_cons] at hmem
            exact hmem.elim heq he)
      have htail : tail ∈ boundedEdgeLabellings K rest :=
        boundedEdgeLabellings_complete K rest tail htailBound htailZero
      rw [boundedEdgeLabellings, List.mem_flatMap]
      refine ⟨label edge, List.mem_range.mpr
        (hbound edge List.mem_cons_self), ?_⟩
      rw [List.mem_map]
      refine ⟨tail, htail, ?_⟩
      funext e
      by_cases heq : e = edge
      · subst e
        simp [setEdgeLabel, tail]
      · simp [setEdgeLabel, tail, heq]

/-! ## Physical support and derived packet amplitudes -/

/-- Retain exactly the vertex-admissible, globally nonvacuum labellings from
the complete bounded enumeration. -/
def physicalEdgeLabellings (K : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) : List EdgeLabelling :=
  (boundedEdgeLabellings K edges).filter
    (graphPhysicalB edges vertices)

def supportLabel (support : List EdgeLabelling) (i : Nat) : EdgeLabelling :=
  (support[i]?).getD zeroEdgeLabelling

theorem supportLabel_mem {support : List EdgeLabelling} {i : Nat}
    (hi : i < support.length) : supportLabel support i ∈ support := by
  unfold supportLabel
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some]
  exact List.getElem_mem hi

private theorem hasExcitedB_exists (label : EdgeLabelling) : ∀ edges,
    hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by
      simp [hasExcitedB] at h
  | edge :: rest, h => by
      by_cases he : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, he⟩
      · have hr : hasExcitedB label rest = true := by
          simpa [hasExcitedB, he] using h
        rcases hasExcitedB_exists label rest hr with ⟨e, hmem, hexc⟩
        exact ⟨e, List.mem_cons_of_mem edge hmem, hexc⟩

theorem graphPhysical_exists_excited {edges : List Nat}
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (h : GraphPhysical edges vertices label) :
    ∃ edge, edge ∈ edges ∧ 1 ≤ label edge := by
  change graphPhysicalB edges vertices label = true at h
  unfold graphPhysicalB at h
  rw [Bool.and_eq_true] at h
  exact hasExcitedB_exists label edges h.1

def physicalModeLabel (K : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (i : Nat) : EdgeLabelling :=
  supportLabel (physicalEdgeLabellings K edges vertices) i

theorem physicalModeLabel_is_physical (K : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) {i : Nat}
    (hi : i < (physicalEdgeLabellings K edges vertices).length) :
    GraphPhysical edges vertices (physicalModeLabel K edges vertices i) := by
  have hmem := supportLabel_mem (support :=
    physicalEdgeLabellings K edges vertices) hi
  exact (List.mem_filter.mp hmem).2

theorem physicalModeExcitedSupport (K : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) :
    ExcitedSupport edges (physicalModeLabel K edges vertices)
      (physicalEdgeLabellings K edges vertices).length := by
  intro i hi
  exact graphPhysical_exists_excited
    (physicalModeLabel_is_physical K edges vertices hi)

/-- The coefficient of an edge labelling derived from actual character
packets, before the vertex and global-vacuum projection. -/
def packetGraphBareAmplitude {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) : GraphPacket :=
  fun label => eliminateLinks
    (fun edge => coeffAt (packet edge) (label edge)) edges

def packetGraphProjectedAmplitude {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : GraphPacket :=
  graphGaugeVacuumProject edges vertices
    (packetGraphBareAmplitude edges packet)

def packetGraphModeWeight {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (i : Nat) : Q' :=
  let a := packetGraphProjectedAmplitude edges vertices packet
    (physicalModeLabel K edges vertices i)
  a * a

theorem packetGraphModeWeight_nonneg {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (i : Nat) :
    (0 : Q') ≤ packetGraphModeWeight edges vertices packet i := by
  unfold packetGraphModeWeight
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

/-! ## The concrete diagonal operator and its exact correlators -/

def packetGraphSpectralModel {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : SpectralModel :=
  finiteNetworkFamilyModel edges (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)

def packetGraphFiniteOp {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex) : FiniteOp :=
  finiteNetworkFamilyOp edges (physicalModeLabel K edges vertices)
    (physicalEdgeLabellings K edges vertices).length

theorem packetGraph_lam_is_operator_eigen {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (i : Nat)
    (hi : i < (physicalEdgeLabellings K edges vertices).length) :
    (packetGraphSpectralModel edges vertices packet).lam i ≈
      (packetGraphFiniteOp (K := K) edges vertices).apply (basis i) i := by
  exact finiteNetworkFamily_lam_is_operator_eigen edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet) i hi

def packetGraphLocatedGap {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    LocatedSpectralGap (packetGraphSpectralModel edges vertices packet) :=
  finiteNetworkFamilyLocatedGap edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)
    (physicalModeExcitedSupport K edges vertices)

theorem packetGraph_gapMargin_exact {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    (packetGraphLocatedGap edges vertices packet).gapMargin ≈
      Q'.mkPos 63 64 (by decide) := by
  exact finiteNetworkFamily_gapMargin_exact edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)
    (physicalModeExcitedSupport K edges vertices)

def packetGraphExactNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  finiteNetworkFamilyNorm (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length

def packetGraphExactTransferredNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  finiteNetworkFamilyTransferredNorm edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length

theorem packetGraph_corr_zero_eq_exactNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    corr (packetGraphSpectralModel edges vertices packet) 0 ≈
      packetGraphExactNorm edges vertices packet := by
  exact finiteNetworkFamily_corr_zero_eq_norm edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)

theorem packetGraph_corr_one_eq_exactTransferredNorm {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    corr (packetGraphSpectralModel edges vertices packet) 1 ≈
      packetGraphExactTransferredNorm edges vertices packet := by
  exact finiteNetworkFamily_corr_one_eq_transferred_norm edges
    (physicalModeLabel K edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)

/-- Squared norm obtained by applying the explicit finite-graph transfer to
the derived projected packet amplitude on every enumerated physical mode. -/
def packetGraphOperatorTransferredNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  fsum (fun i =>
    let label := physicalModeLabel K edges vertices i
    let y := graphTransfer edges
      (packetGraphProjectedAmplitude edges vertices packet) label
    y * y) (physicalEdgeLabellings K edges vertices).length

/-- The diagonal spectral correlator uses exactly the eigenvalues of the
explicit graph transfer acting on the packet-derived amplitude. -/
theorem packetGraphOperatorTransferredNorm_eq {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphOperatorTransferredNorm edges vertices packet ≈
      packetGraphExactTransferredNorm edges vertices packet := by
  unfold packetGraphOperatorTransferredNorm
    packetGraphExactTransferredNorm finiteNetworkFamilyTransferredNorm
  exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun i => by
    let label := physicalModeLabel K edges vertices i
    let e := networkEigen edges label
    let a := packetGraphProjectedAmplitude edges vertices packet label
    change (e * a) * (e * a) ≈ (a * a) * (e * e)
    exact Q'.eqv_trans _ ((e * e) * (a * a)) _
      (YMGap.Continuum.FullModeAssembly.sq_regroup e a)
      (Q'.mul_comm_eqv (e * e) (a * a)))
    (physicalEdgeLabellings K edges vertices).length

/-! ## A nonzero tetrahedral packet graph -/

def tetraRestrictedSpinOne : EdgeLabelling :=
  tetraSpinOneLabel

theorem tetraRestrictedSpinOne_eq :
    tetraRestrictedSpinOne = tetraSpinOneLabel := rfl

theorem tetraRestrictedSpinOne_physical :
    GraphPhysical tetraEdges tetraVertices tetraRestrictedSpinOne := by
  rw [tetraRestrictedSpinOne_eq]
  exact tetra_spin_one_physical

theorem tetraRestrictedSpinOne_mem_bounded :
    tetraRestrictedSpinOne ∈ boundedEdgeLabellings 2 tetraEdges := by
  apply boundedEdgeLabellings_complete
  · intro edge he
    unfold tetraRestrictedSpinOne tetraSpinOneLabel
    unfold tetraEdges at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro edge he
    unfold tetraRestrictedSpinOne tetraSpinOneLabel
    have hm0 : 0 ∈ tetraEdges := List.mem_cons_self
    have hm1 : 1 ∈ tetraEdges :=
      List.mem_cons_of_mem 0 List.mem_cons_self
    have hm2 : 2 ∈ tetraEdges :=
      List.mem_cons_of_mem 0 (List.mem_cons_of_mem 1 List.mem_cons_self)
    have hm3 : 3 ∈ tetraEdges :=
      List.mem_cons_of_mem 0
        (List.mem_cons_of_mem 1 (List.mem_cons_of_mem 2 List.mem_cons_self))
    have hm4 : 4 ∈ tetraEdges :=
      List.mem_cons_of_mem 0 (List.mem_cons_of_mem 1
        (List.mem_cons_of_mem 2 (List.mem_cons_of_mem 3 List.mem_cons_self)))
    have hm5 : 5 ∈ tetraEdges :=
      List.mem_cons_of_mem 0 (List.mem_cons_of_mem 1
        (List.mem_cons_of_mem 2 (List.mem_cons_of_mem 3
          (List.mem_cons_of_mem 4 List.mem_cons_self))))
    cases edge with
    | zero => exact (he hm0).elim
    | succ e1 =>
        cases e1 with
        | zero => exact (he hm1).elim
        | succ e2 =>
            cases e2 with
            | zero => exact (he hm2).elim
            | succ e3 =>
                cases e3 with
                | zero => exact (he hm3).elim
                | succ e4 =>
                    cases e4 with
                    | zero => exact (he hm4).elim
                    | succ e5 =>
                        cases e5 with
                        | zero => exact (he hm5).elim
                        | succ e6 =>
                            rw [if_neg (by omega)]

theorem tetraRestrictedSpinOne_mem_physical :
    tetraRestrictedSpinOne ∈
      physicalEdgeLabellings 2 tetraEdges tetraVertices := by
  apply List.mem_filter.mpr
  exact ⟨tetraRestrictedSpinOne_mem_bounded,
    tetraRestrictedSpinOne_physical⟩

def tetraQuadraticPacket : CharacterPacket 2 :=
  basisPacket ⟨2, by omega⟩

def tetraQuadraticPackets : Nat → CharacterPacket 2 :=
  fun _ => tetraQuadraticPacket

theorem tetraQuadraticProjectedAmplitude_exact :
    packetGraphProjectedAmplitude tetraEdges tetraVertices
        tetraQuadraticPackets tetraRestrictedSpinOne ≈ 1 := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos tetraRestrictedSpinOne_physical]
  rw [tetraRestrictedSpinOne_eq]
  unfold packetGraphBareAmplitude tetraEdges tetraQuadraticPackets
    tetraQuadraticPacket tetraSpinOneLabel
  decide

/-- The actual tetrahedral model contains a retained mode of exact weight
one; its located gap is therefore not an empty-family artifact. -/
theorem tetraPacketGraph_nonzero_mode :
    ∃ i, i < (physicalEdgeLabellings 2 tetraEdges tetraVertices).length ∧
      packetGraphModeWeight tetraEdges tetraVertices tetraQuadraticPackets i ≈
        1 := by
  obtain ⟨i, hi, hget⟩ :=
    List.getElem_of_mem tetraRestrictedSpinOne_mem_physical
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel 2 tetraEdges tetraVertices i =
      tetraRestrictedSpinOne := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact Q'.eqv_trans _ (1 * 1) _
    (q_mul_congr tetraQuadraticProjectedAmplitude_exact
      tetraQuadraticProjectedAmplitude_exact)
    (Q'.one_mul_eqv 1)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.boundedEdgeLabellings_sound
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.boundedEdgeLabellings_complete
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.physicalModeExcitedSupport
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.packetGraph_lam_is_operator_eigen
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.packetGraph_gapMargin_exact
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.packetGraph_corr_zero_eq_exactNorm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.packetGraph_corr_one_eq_exactTransferredNorm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.packetGraphOperatorTransferredNorm_eq
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraRestrictedSpinOne_eq
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraRestrictedSpinOne_physical
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraRestrictedSpinOne_mem_bounded
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraRestrictedSpinOne_mem_physical
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraQuadraticProjectedAmplitude_exact
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.tetraPacketGraph_nonzero_mode
