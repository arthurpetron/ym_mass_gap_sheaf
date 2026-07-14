/-
# Transfer obstruction for naive identity refinement

The interacting identity refinement preserves the complete time-zero state
norm, but it inserts one extra copied-edge Wilson eigenvalue at positive
time.  Here a closed fundamental-label example proves that this factor is
genuinely nontrivial at the exact coupling `w = 1/2`: the refined and old
graph eigenvalues are not equivalent.  Consequently a graph-directed
continuum construction cannot use the bare subdivision map as a transfer
intertwiner; it must also renormalize local time/coupling.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- A single old edge carrying the fundamental doubled-spin label. -/
def obstructionLabel : EdgeLabelling :=
  setEdgeLabel zeroEdgeLabelling 0 1

theorem obstructionLabel_old : obstructionLabel 0 = 1 := by
  rfl

/-- The closed coupling eigenvalue at doubled spin one is exactly `1/8`. -/
theorem couplingFundamentalEigen_exact :
    eigA SU2PeterWeylWilsonBlock.coupling 1 ≈
      Q'.mkPos 1 8 (by decide) := by
  decide

/-- Squaring the fundamental eigenvalue changes it. -/
theorem couplingFundamentalEigen_square_ne :
    ¬ ((eigA SU2PeterWeylWilsonBlock.coupling 1 *
          eigA SU2PeterWeylWilsonBlock.coupling 1) ≈
        eigA SU2PeterWeylWilsonBlock.coupling 1) := by
  decide

theorem obstruction_old_graphEigen :
    graphEigen [0] obstructionLabel ≈
      eigA SU2PeterWeylWilsonBlock.coupling 1 := by
  unfold graphEigen obstructionLabel zeroEdgeLabelling setEdgeLabel
    eliminateLinks
  exact Q'.mul_one_eqv _

/-- **Machine-checked fence.**  Bare trivalent identity subdivision is not a
positive-time transfer intertwiner, already on the one-edge fundamental
label.  This refutes a naive graph-colimit route while leaving the exact
time-zero cylinder identity intact. -/
theorem naive_identity_refinement_graphEigen_ne :
    ¬ (graphEigen (identityRefinedEdges 1 2 [0])
          (identityRefinedLabel 0 1 2 obstructionLabel) ≈
        graphEigen [0] obstructionLabel) := by
  have href := graphEigen_identity_refinement
    0 1 2 [0] obstructionLabel (by simp) (by simp) (by decide)
  rw [obstructionLabel_old] at href
  have hold := obstruction_old_graphEigen
  have hrefExact :
      graphEigen (identityRefinedEdges 1 2 [0])
          (identityRefinedLabel 0 1 2 obstructionLabel) ≈
        eigA SU2PeterWeylWilsonBlock.coupling 1 *
          eigA SU2PeterWeylWilsonBlock.coupling 1 :=
    Q'.eqv_trans _ _ _ href
      (q_mul_congr (Q'.eqv_refl _) hold)
  intro hsame
  apply couplingFundamentalEigen_square_ne
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrefExact)
    (Q'.eqv_trans _ _ _ hsame hold)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction.couplingFundamentalEigen_exact
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction.couplingFundamentalEigen_square_ne
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction.obstruction_old_graphEigen
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementObstruction.naive_identity_refinement_graphEigen_ne
