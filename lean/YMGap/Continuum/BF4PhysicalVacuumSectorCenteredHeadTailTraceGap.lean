/-
# Centered head--tail trace compiler for the physical BF4 vacuum sector

The component-centered boundary Gram is the correct positive form in which
to glue an embedded old head to a genuinely new tail.  The new-tail diagonal
trace theorem supplies the tail estimate, while scaled positivity absorbs the
entire mixed block.  For a coefficient of zero physical mean, the centered
boundary Gram is exactly the original same-object reflected quadratic form.

Consequently a centered head estimate with rate `q` and a scalar exact-tail
trace bound with rate `tau` imply the physical full-form estimate at rate
`q + tau`.  This module is a compiler: it supplies neither the uniform head
estimate nor the uniform trace bound.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveFormHeadTailGluing
open YMGap.Continuum.FiniteWeightedGramGNSData
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The centered Gram is the physical form on the vacuum complement -/

/-- For a coefficient of zero stationary mean, the actual component-centered
boundary Gram is exactly the same-object reflected matrix quadratic. -/
theorem centralPhysicalFiniteVacuumSectorCenteredGram_self_eqv_matrix_of_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {coefficient : Nat → Q'}
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw cutoff half
    D.B coefficient coefficient ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
  dsimp only
  have henergy :
      (centralPhysicalFiniteVacuumSectorCenteredGramGNSData
          w hw cutoff half).B coefficient coefficient ≈
        centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
          w hw cutoff half coefficient := by
    unfold centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      finiteWeightedGramGNSData weightedGramBilinear
      centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
      weightedGramSOS
    apply listQSum_congr_on
    intro boundary _hboundary
    have htransform :=
      centralPhysicalFiniteVacuumSector_centeredBoundaryTransform_eqv_raw
        hcenter boundary
    exact Q'.mul_eqv_congr_left
      (centralPhysicalFiniteVacuumSectorGramWeight
        w hw cutoff half boundary) _ _
      (Q'.eqv_trans _
        (centralPhysicalFiniteVacuumSectorBoundaryTransform
            w hw cutoff half coefficient boundary *
          centralPhysicalFiniteVacuumSectorCenteredBoundaryTransform
            w hw cutoff half coefficient boundary) _
        (Q'.mul_eqv_congr_right _ _ _ htransform)
        (Q'.mul_eqv_congr_left _ _ _ htransform))
  exact Q'.eqv_trans _ _ _ henergy
    (Q'.eqv_symm
      (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_boundaryTransformEnergy
        w hw cutoff half coefficient))

/-! ## 2. Centered head plus exact tail trace -/

/-- A centered embedded-head estimate and an exact new-tail trace estimate
contract to the complete centered form at the additive rate `q + tau`. -/
theorem centralPhysicalFiniteVacuumSectorCenteredGram_le_of_head_trace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (q tau : Q')
    (hq0 : (0 : Q') ≤ q) (htau0 : (0 : Q') ≤ tau)
    (hhead :
      let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
        w hw later half
      let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
        w hw base later half coefficient
      D.B head head ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half head)
    (htrace :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half ≤ tau) :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    D.B coefficient coefficient ≤
      (q + tau) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half coefficient := by
  dsimp only at hhead ⊢
  let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
    w hw later half
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    w hw base later half coefficient
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
    w hw base later half coefficient
  let headBudget := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw later half head
  let tailBudget := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw later half tail
  have htail : D.B tail tail ≤ tau * tailBudget := by
    exact
      centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_of_traceBound
        w hw base later half coefficient tau htrace
  have hheadBudget : (0 : Q') ≤ headBudget :=
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
      w hw later half head
  have htailBudget : (0 : Q') ≤ tailBudget :=
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
      w hw later half tail
  have hglued :
      D.B (D.add head tail) (D.add head tail) ≤
        (q + tau) * (headBudget + tailBudget) :=
    GNSData.add_self_le_of_head_tail_nonnegative
      D head tail q tau headBudget tailBudget
      hq0 htau0 hheadBudget htailBudget hhead htail
  have hreassemble : D.veq (D.add head tail) coefficient := by
    intro index
    exact embeddedHead_add_newTail_eqv
      w hw base later half coefficient index
  have hform :
      D.B coefficient coefficient ≤
        (q + tau) * (headBudget + tailBudget) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (D.B_diag_congr hreassemble)) hglued
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorDiagonal_eqv_head_add_tail
      w hw base later half coefficient
  exact Q'.le_trans' _ _ _ hform
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (q + tau) _ _
        (Q'.eqv_symm hdiagonal)))

/-! ## 3. Same-object strict form compiler -/

/-- On the physical vacuum complement, the centered head estimate and exact
tail trace estimate imply the same-object reflected form bound. -/
theorem centralPhysicalFiniteVacuumSectorMatrix_le_of_centeredHead_trace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (q tau : Q')
    (hq0 : (0 : Q') ≤ q) (htau0 : (0 : Q') ≤ tau)
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw later half coefficient ≈ 0)
    (hhead :
      let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
        w hw later half
      let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
        w hw base later half coefficient
      D.B head head ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half head)
    (htrace :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half ≤ tau) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw later half coefficient ≤
      (q + tau) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half coefficient := by
  have hcentered :=
    centralPhysicalFiniteVacuumSectorCenteredGram_le_of_head_trace
      w hw base later half coefficient q tau hq0 htau0 hhead htrace
  have hphysical :=
    centralPhysicalFiniteVacuumSectorCenteredGram_self_eqv_matrix_of_meanZero
      hcenter
  dsimp only at hphysical
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hphysical) hcentered

/-- If the additive rate is strictly below one, the same compiler records
both the physical form inequality and its strictness. -/
theorem centralPhysicalFiniteVacuumSectorStrictMatrixGap_of_centeredHead_trace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (q tau : Q')
    (hq0 : (0 : Q') ≤ q) (htau0 : (0 : Q') ≤ tau)
    (hrate : q + tau < (1 : Q'))
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw later half coefficient ≈ 0)
    (hhead :
      let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
        w hw later half
      let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
        w hw base later half coefficient
      D.B head head ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half head)
    (htrace :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half ≤ tau) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw later half coefficient ≤
        (q + tau) *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw later half coefficient ∧
      q + tau < (1 : Q') :=
  ⟨centralPhysicalFiniteVacuumSectorMatrix_le_of_centeredHead_trace
      w hw base later half coefficient q tau hq0 htau0
      hcenter hhead htrace,
    hrate⟩

/-- The probabilistic tail frontier in its directly consumable form: a
centered embedded-head estimate plus a bound on the new-state self-return
trace gives the same physical strict matrix gap.  The favorable conditioned
stationary subtraction is discharged internally by the exact trace identity. -/
theorem centralPhysicalFiniteVacuumSectorStrictMatrixGap_of_centeredHead_selfReturnTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (q tau : Q')
    (hq0 : (0 : Q') ≤ q) (htau0 : (0 : Q') ≤ tau)
    (hrate : q + tau < (1 : Q'))
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw later half coefficient ≈ 0)
    (hhead :
      let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
        w hw later half
      let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
        w hw base later half coefficient
      D.B head head ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half head)
    (hselfReturn :
      centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
        w hw base later half ≤ tau) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw later half coefficient ≤
        (q + tau) *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw later half coefficient ∧
      q + tau < (1 : Q') := by
  apply centralPhysicalFiniteVacuumSectorStrictMatrixGap_of_centeredHead_trace
    w hw base later half coefficient q tau hq0 htau0 hrate
    hcenter hhead
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorExactNewTailTraceRate_le_selfReturnTrace
      w hw base later half)
    hselfReturn

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap.centralPhysicalFiniteVacuumSectorCenteredGram_self_eqv_matrix_of_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap.centralPhysicalFiniteVacuumSectorCenteredGram_le_of_head_trace
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap.centralPhysicalFiniteVacuumSectorMatrix_le_of_centeredHead_trace
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap.centralPhysicalFiniteVacuumSectorStrictMatrixGap_of_centeredHead_trace
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap.centralPhysicalFiniteVacuumSectorStrictMatrixGap_of_centeredHead_selfReturnTrace
