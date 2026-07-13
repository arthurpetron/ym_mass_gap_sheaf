/-
# The fundamental constant-pentagon obstruction and finite trivalent graphs

The exact rational fundamental F-block from `SU2TrivalentThetaRecoupling` is a
genuine four-leg associator block, but it cannot be reused as a
label-independent associator at every edge of the pentagon.  The short
pentagon path would apply two copies of `F`, while the long path would apply
three.  Since `F^2 = I`, the two paths reduce to `I` and `F`; they already
disagree on the singlet channel.  This file freezes that failure exactly.

The obstruction identifies the missing datum: different pentagon edges have
different external and intermediate labels and therefore require a family of
dimension-rescaled F-blocks, with the correct embeddings into their distinct
fusion spaces.  A single 2-by-2 matrix is insufficient even though it is
itself involutive and Gram-isometric.

A fixed finite trivalent graph does not require changing fusion trees.  We
therefore also construct its exact coordinate projector directly.  A graph is
given by a finite edge list and a finite list of trivalent incidence triples.
The projector retains precisely the vertex-admissible labelings with at least
one excited listed edge, so it imposes gauge admissibility and removes the
unique vacuum in one step.  It is idempotent, commutes with diagonal transfer,
is independent of link-elimination order, and has the uniform `(1/8)^2`
squared-norm contraction on every finite packet support.  The four-vertex,
six-edge tetrahedral graph is supplied as the first concrete instance beyond
the theta graph.
-/

import YMGap.Continuum.SU2TrivalentThetaRecoupling

namespace YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2TrivalentThetaRecoupling

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## A kernel-checked obstruction to a constant 2-by-2 pentagon -/

/-- The two-associator side of the naive label-independent pentagon. -/
def constantPentagonShort (x : RecoupleVec) : RecoupleVec :=
  fundamentalFMove (fundamentalFMove x)

/-- The three-associator side of the naive label-independent pentagon. -/
def constantPentagonLong (x : RecoupleVec) : RecoupleVec :=
  fundamentalFMove (fundamentalFMove (fundamentalFMove x))

theorem constantPentagon_singlet_sides_exact :
    RecoupleEq (constantPentagonShort singletChannel) singletChannel ∧
    RecoupleEq (constantPentagonLong singletChannel)
      ((-oneHalf), oneHalf) := by
  unfold RecoupleEq constantPentagonShort constantPentagonLong
    fundamentalFMove fundamentalFMoveAt singletChannel oneHalf
  exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **Exact obstruction.**  Reusing the fundamental 2-by-2 block as a constant
associator fails the pentagon on the singlet vector. -/
theorem constant_fundamental_pentagon_fails :
    ¬ RecoupleEq (constantPentagonShort singletChannel)
      (constantPentagonLong singletChannel) := by
  unfold RecoupleEq constantPentagonShort constantPentagonLong
    fundamentalFMove fundamentalFMoveAt singletChannel oneHalf
  decide

/-! ## Arbitrary fixed finite trivalent graph projector -/

abbrev EdgeLabelling := Nat → Nat
abbrev TrivalentVertex := Nat × (Nat × Nat)
abbrev GraphPacket := EdgeLabelling → Q'

/-- At least one edge in the explicit finite edge list carries a nonvacuum
label. -/
def HasExcited (label : EdgeLabelling) : List Nat → Prop
  | [] => False
  | e :: rest => 1 ≤ label e ∨ HasExcited label rest

def hasExcitedB (label : EdgeLabelling) : List Nat → Bool
  | [] => false
  | e :: rest => if 1 ≤ label e then true else hasExcitedB label rest

private theorem hasExcitedB_true (label : EdgeLabelling) : ∀ order,
    hasExcitedB label order = true → HasExcited label order
  | [], h => by simp [hasExcitedB] at h
  | e :: rest, h => by
      by_cases he : 1 ≤ label e
      · exact Or.inl he
      · have hr : hasExcitedB label rest = true := by
          simpa [hasExcitedB, he] using h
        exact Or.inr (hasExcitedB_true label rest hr)

/-- Boolean finite fold of all exact trivalent fusion guards. -/
def verticesAdmissibleB : List TrivalentVertex → EdgeLabelling → Bool
  | [], _ => true
  | v :: rest, label =>
      if fusionOK (label v.1) (label v.2.1) (label v.2.2) = true then
        verticesAdmissibleB rest label
      else false

def graphPhysicalB (edges : List Nat) (vertices : List TrivalentVertex)
    (label : EdgeLabelling) : Bool :=
  hasExcitedB label edges && verticesAdmissibleB vertices label

abbrev GraphPhysical (edges : List Nat) (vertices : List TrivalentVertex)
    (label : EdgeLabelling) : Prop :=
  graphPhysicalB edges vertices label = true

private theorem graphPhysical_hasExcited {edges : List Nat}
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (h : GraphPhysical edges vertices label) : HasExcited label edges := by
  unfold GraphPhysical graphPhysicalB at h
  cases he : hasExcitedB label edges with
  | false => simp [he] at h
  | true => exact hasExcitedB_true label edges he

/-- Exact coordinate projector onto gauge-admissible nonvacuum spin networks
of a fixed finite trivalent graph. -/
def graphGaugeVacuumProject (edges : List Nat)
    (vertices : List TrivalentVertex) (f : GraphPacket) : GraphPacket :=
  fun label => if GraphPhysical edges vertices label then f label else 0

theorem graphGaugeVacuumProject_idempotent (edges : List Nat)
    (vertices : List TrivalentVertex) (f : GraphPacket) (label : EdgeLabelling) :
    graphGaugeVacuumProject edges vertices
        (graphGaugeVacuumProject edges vertices f) label ≈
      graphGaugeVacuumProject edges vertices f label := by
  by_cases h : GraphPhysical edges vertices label
  · unfold graphGaugeVacuumProject
    rw [if_pos h, if_pos h]
    exact Q'.eqv_refl _
  · unfold graphGaugeVacuumProject
    rw [if_neg h, if_neg h]
    exact Q'.eqv_refl 0

def graphEigen (order : List Nat) (label : EdgeLabelling) : Q' :=
  eliminateLinks (fun e => eigA coupling (label e)) order

def graphTransfer (order : List Nat) (f : GraphPacket) : GraphPacket :=
  fun label => graphEigen order label * f label

theorem graphEigen_order_independent (label : EdgeLabelling)
    {A B : List Nat} (h : A.Perm B) :
    graphEigen A label ≈ graphEigen B label :=
  eliminateLinks_perm (fun e => eigA coupling (label e)) h

theorem graphTransfer_order_independent (f : GraphPacket)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    graphTransfer A f label ≈ graphTransfer B f label :=
  Q'.mul_eqv_congr_right _ _ _ (graphEigen_order_independent label h)

theorem graphProject_transfer_commutes (edges : List Nat)
    (vertices : List TrivalentVertex) (order : List Nat)
    (f : GraphPacket) (label : EdgeLabelling) :
    graphTransfer order (graphGaugeVacuumProject edges vertices f) label ≈
      graphGaugeVacuumProject edges vertices (graphTransfer order f) label := by
  by_cases h : GraphPhysical edges vertices label
  · unfold graphTransfer graphGaugeVacuumProject
    rw [if_pos h, if_pos h]
    exact Q'.eqv_refl _
  · unfold graphTransfer graphGaugeVacuumProject
    rw [if_neg h, if_neg h]
    exact Q'.mul_zero_eqv _

private theorem graphEigen_nonneg (label : EdgeLabelling) : ∀ order,
    (0 : Q') ≤ graphEigen order label
  | [] => by change (0 : Q') ≤ 1; decide
  | e :: rest => Q'.mul_nonneg _ _
      (eigA_nonneg (w := coupling) (by decide) (label e))
      (graphEigen_nonneg label rest)

private theorem graphEigen_le_one (label : EdgeLabelling) : ∀ order,
    graphEigen order label ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | e :: rest => by
      have hm := Q'.mul_le_mul_of_nonneg
        (eigA_le_one (w := coupling) (by decide) (by decide) (label e))
        (graphEigen_le_one label rest)
        (by decide : (0 : Q') ≤ 1) (graphEigen_nonneg label rest)
      exact Q'.le_trans' _ _ _ hm
        (Q'.le_of_eqv (Q'.one_mul_eqv 1))

private theorem excitedEigen_le_eighth {s : Nat} (hs : 1 ≤ s) :
    eigA coupling s ≤ eighth :=
  Q'.le_trans' _ _ _
    (gapEdge_dominates (by decide) (by decide) hs)
    (Q'.le_of_eqv (by decide : eigA coupling 1 ≈ eighth))

/-- One excited edge is enough: all other link eigenvalues are contractions,
so every nonvacuum finite graph channel lies below the same gap edge. -/
private theorem graphEigen_excited_le_eighth (label : EdgeLabelling) :
    ∀ order, HasExcited label order → graphEigen order label ≤ eighth
  | [], h => False.elim h
  | e :: rest, Or.inl he => by
      have hm := Q'.mul_le_mul_of_nonneg
        (excitedEigen_le_eighth he) (graphEigen_le_one label rest)
        (by decide : (0 : Q') ≤ eighth) (graphEigen_nonneg label rest)
      exact Q'.le_trans' _ _ _ hm
        (Q'.le_of_eqv (Q'.mul_one_eqv eighth))
  | e :: rest, Or.inr hr => by
      have hm := Q'.mul_le_mul_of_nonneg
        (eigA_le_one (w := coupling) (by decide) (by decide) (label e))
        (graphEigen_excited_le_eighth label rest hr)
        (by decide : (0 : Q') ≤ 1) (graphEigen_nonneg label rest)
      exact Q'.le_trans' _ _ _ hm
        (Q'.le_of_eqv (Q'.one_mul_eqv eighth))

private theorem scaled_term_le (a b x : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : (0 : Q') ≤ b) :
    (a * x) * (a * x) ≤ (b * b) * (x * x) := by
  have h1 := Q'.mul_le_mul_of_nonneg_right a b a hab ha
  have h2 := Q'.mul_le_mul_of_nonneg_left a b b hab hb
  have hs : a * a ≤ b * b := Q'.le_trans' _ _ _ h1 h2
  have hm := Q'.mul_le_mul_of_nonneg_right
    (a * a) (b * b) (x * x) hs
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg x)
  have regroup : (a * x) * (a * x) ≈ (a * a) * (x * x) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a x (a * x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv x a x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _
        (Q'.mul_eqv_congr_right _ _ x (Q'.mul_comm_eqv x a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv a x x)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv a a (x * x))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv regroup) hm

private theorem graph_projected_term_uniform (edges : List Nat)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (label : EdgeLabelling) :
    graphTransfer edges (graphGaugeVacuumProject edges vertices f) label *
        graphTransfer edges (graphGaugeVacuumProject edges vertices f) label ≤
      (eighth * eighth) *
        (graphGaugeVacuumProject edges vertices f label *
          graphGaugeVacuumProject edges vertices f label) := by
  by_cases h : GraphPhysical edges vertices label
  · unfold graphTransfer graphGaugeVacuumProject
    rw [if_pos h]
    exact scaled_term_le _ _ _ (graphEigen_nonneg label edges)
      (graphEigen_excited_le_eighth label edges
        (graphPhysical_hasExcited h)) (by decide)
  · unfold graphTransfer graphGaugeVacuumProject
    rw [if_neg h]
    have hl : (graphEigen edges label * 0) *
        (graphEigen edges label * 0) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (q_mul_congr (Q'.mul_zero_eqv _) (Q'.mul_zero_eqv _))
        (Q'.zero_mul_eqv 0)
    have hr : (eighth * eighth) * (0 * 0) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0))
        (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
      (Q'.le_of_eqv (Q'.eqv_symm hr))

def graphNorm (f : GraphPacket) : List EdgeLabelling → Q'
  | [] => 0
  | label :: support => f label * f label + graphNorm f support

/-- **Uniform contraction for every fixed finite trivalent graph.**  The
finite support is arbitrary and the factor is independent of graph size. -/
theorem finite_trivalent_graph_global_contraction (edges : List Nat)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (support : List EdgeLabelling) :
    graphNorm (graphTransfer edges
      (graphGaugeVacuumProject edges vertices f)) support ≤
      (eighth * eighth) *
        graphNorm (graphGaugeVacuumProject edges vertices f) support := by
  induction support with
  | nil =>
      unfold graphNorm
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | cons label rest ih =>
      unfold graphNorm
      have hs := Q'.add_le_add
        (graph_projected_term_uniform edges vertices f label) ih
      exact Q'.le_trans' _ _ _ hs
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.mul_add_eqv (eighth * eighth)
            (graphGaugeVacuumProject edges vertices f label *
              graphGaugeVacuumProject edges vertices f label)
            (graphNorm (graphGaugeVacuumProject edges vertices f) rest))))

private theorem graphNorm_eqv_congr {f g : GraphPacket}
    (h : ∀ label, f label ≈ g label) : ∀ support,
    graphNorm f support ≈ graphNorm g support
  | [] => Q'.eqv_refl 0
  | label :: rest => by
      unfold graphNorm
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (q_mul_congr (h label) (h label)))
        (Q'.add_eqv_congr_left _ _ _ (graphNorm_eqv_congr h rest))

theorem finite_graph_transferred_norm_order_independent
    (edges : List Nat) (vertices : List TrivalentVertex) (f : GraphPacket)
    (support : List EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    graphNorm (graphTransfer A
      (graphGaugeVacuumProject edges vertices f)) support ≈
    graphNorm (graphTransfer B
      (graphGaugeVacuumProject edges vertices f)) support :=
  graphNorm_eqv_congr
    (fun label => graphTransfer_order_independent
      (graphGaugeVacuumProject edges vertices f) label h)
    support

/-! ## The first four-vertex instance: the tetrahedral graph -/

def tetraEdges : List Nat := [0, 1, 2, 3, 4, 5]

/-- Incidences of the tetrahedron's four trivalent vertices. -/
def tetraVertices : List TrivalentVertex :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]

def tetraVacuumLabel : EdgeLabelling := fun _ => 0
def tetraSpinOneLabel : EdgeLabelling := fun e => if e < 6 then 2 else 0

theorem tetra_vacuum_removed :
    ¬ GraphPhysical tetraEdges tetraVertices tetraVacuumLabel := by decide

theorem tetra_spin_one_physical :
    GraphPhysical tetraEdges tetraVertices tetraSpinOneLabel := by decide

theorem tetra_projector_nontrivial (f : GraphPacket) :
    graphGaugeVacuumProject tetraEdges tetraVertices f tetraSpinOneLabel ≈
      f tetraSpinOneLabel := by
  unfold graphGaugeVacuumProject
  rw [if_pos tetra_spin_one_physical]
  exact Q'.eqv_refl _

theorem tetra_global_vacuum_contraction (f : GraphPacket)
    (support : List EdgeLabelling) :
    graphNorm (graphTransfer tetraEdges
      (graphGaugeVacuumProject tetraEdges tetraVertices f)) support ≤
      (eighth * eighth) *
        graphNorm (graphGaugeVacuumProject tetraEdges tetraVertices f) support :=
  finite_trivalent_graph_global_contraction tetraEdges tetraVertices f support

end YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.constant_fundamental_pentagon_fails
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.graphGaugeVacuumProject_idempotent
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.graphProject_transfer_commutes
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.finite_trivalent_graph_global_contraction
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.finite_graph_transferred_norm_order_independent
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.tetra_spin_one_physical
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.tetra_projector_nontrivial
#print axioms YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.tetra_global_vacuum_contraction
