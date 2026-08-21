/-
# Centered graph-norm bridge to the cutoff-removed BF4 transfer

The fixed-nome finite-cutoff sixteenth now gives an operator-norm gap on each
finite physical GNS completion.  The cutoff-removed completion and its
conditional transfer are separate objects.  This file constructs the
canonical exactly centered finite approximants of every cutoff-removed
representative and proves, without an input, that every such approximant lies
in its finite vacuum complement.

The remaining transport problem is then exactly two graph-norm convergence
laws: convergence of the centered finite norms to the cutoff-removed norm,
and convergence of their transferred norms to the norm of the already
constructed cutoff-removed transfer.  These laws are packaged as Type-level
data.  Together with the fixed-nome sixteenth they construct the previously
isolated strict-contraction certificate on the actual completed vacuum
complement, with literal rate `1/16`.

Neither the fixed-nome sixteenth nor the graph-norm convergence record is
inhabited here.  In particular, finite-cutoff strictness is not silently
identified with same-object cutoff-limit strictness.

## Axiom gate

Only exact finite centering, quotient induction, constructive-real limit
order, and the proved finite completed operator gap are used.  There is no
classical choice, noncomputable declaration, custom axiom, or unproved
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
import YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical exactly centered finite-stage approximants -/

/-- The finite physical GNS datum at representation cutoff `cutoff`, with the
nome and finite half-extent held fixed. -/
abbrev CentralPhysicalFixedNomeStageGNSData
    (w : Q') (hw : (0 : Q') <= w) (half cutoff : Nat) : GNSData :=
  (centralPhysicalSmulGNS w hw cutoff half).toGNSData

/-- The constant finite-GNS Cauchy representative of the exactly centered
`cutoff`-th term of a cutoff-removed Cauchy representative. -/
def centralPhysicalCutoffCenteredStageCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) :
    CauchyGNS
      (CentralPhysicalFixedNomeStageGNSData
        w (Q'.le_of_lt hw0) half cutoff) :=
  let D := CentralPhysicalFixedNomeStageGNSData
    w (Q'.le_of_lt hw0) half cutoff
  constCauchy D
    (centralPhysicalCenteredObservable
      w (Q'.le_of_lt hw0) cutoff half (X.seq cutoff).value)

/-- The corresponding point of the genuine finite-cutoff physical GNS
completion. -/
def centralPhysicalCutoffCenteredStagePoint
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) :
    CentralPhysicalGNSCompletion
      w (Q'.le_of_lt hw0) cutoff half :=
  Quotient.mk
    (cauchySetoid
      (CentralPhysicalFixedNomeStageGNSData
        w (Q'.le_of_lt hw0) half cutoff))
    (centralPhysicalCutoffCenteredStageCauchy
      hw0 hw1 half X cutoff)

/-- Exact finite centering puts every canonical stage approximant in the
literal vacuum complement of its own finite-cutoff GNS completion. -/
theorem centralPhysicalCutoffCenteredStagePoint_vacuumOrthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) :
    CentralPhysicalCompletedVacuumOrthogonal
      w (Q'.le_of_lt hw0) cutoff half
      (centralPhysicalCutoffCenteredStagePoint
        hw0 hw1 half X cutoff) := by
  let hw := Q'.le_of_lt hw0
  let D := CentralPhysicalFixedNomeStageGNSData w hw half cutoff
  let centered := centralPhysicalCenteredObservable
    w hw cutoff half (X.seq cutoff).value
  have hmean :
      centralPhysicalStationaryMean w hw cutoff half centered ≈ 0 :=
    centralPhysicalCenteredObservable_meanZero
      w hw cutoff half (X.seq cutoff).value
  have hpair : D.B centered centralPhysicalVacuumCarrier ≈ 0 := by
    rw [centralPhysicalSmulGNS_B_eq]
    exact Q'.eqv_trans _ _ _
      (centralPhysicalWeightedInner_vacuum_right
        w hw cutoff half centered) hmean
  unfold CentralPhysicalCompletedVacuumOrthogonal
  change D.cinnerCompl
      (embedQuot D (D.qmk centered))
      (embedQuot D (D.qmk centralPhysicalVacuumCarrier)) = CReal.RCzero
  rw [D.cinnerCompl_embed]
  exact Quotient.sound (CReal.ofQ'_equiv_of_eqv hpair)

/-! ## 2. The two finite graph-norm streams -/

/-- A literal constructive-real representative of the centered finite-stage
squared norm. -/
def centralPhysicalCutoffCenteredStageNorm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) : CReal :=
  let D := CentralPhysicalFixedNomeStageGNSData
    w (Q'.le_of_lt hw0) half cutoff
  let centered := centralPhysicalCutoffCenteredStageCauchy
    hw0 hw1 half X cutoff
  D.cinnerRep centered centered

/-- A literal constructive-real representative of the squared norm after the
genuine finite-cutoff completed Markov transfer. -/
def centralPhysicalCutoffCenteredStageTransferredNorm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) : CReal :=
  let D := CentralPhysicalFixedNomeStageGNSData
    w (Q'.le_of_lt hw0) half cutoff
  let centered := centralPhysicalCutoffCenteredStageCauchy
    hw0 hw1 half X cutoff
  let transferred := (centralPhysicalMarkovSymbol
    w (Q'.le_of_lt hw0) cutoff half).cDiagCauchy centered
  D.cinnerRep transferred transferred

/-- The fixed-nome finite completed operator gap, specialized to the canonical
centered representative, is an inequality between its two literal graph-norm
streams. -/
theorem centralPhysicalCutoffCenteredStage_operator_norm_gap_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (cutoff : Nat) :
    CReal.leEv
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X cutoff)
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X cutoff)) := by
  have hgap := fixedNome_completed_vacuum_operator_norm_gap_sixteenth
    certificate cutoff
    (centralPhysicalCutoffCenteredStagePoint hw0 hw1 half X cutoff)
    (centralPhysicalCutoffCenteredStagePoint_vacuumOrthogonal
      hw0 hw1 half X cutoff)
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X cutoff))
    (CReal.RCscale
      (physicalCutoffSixteenth * physicalCutoffSixteenth)
      (Quotient.mk CReal.crealSetoid
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X cutoff))) at hgap
  rw [CReal.RCscale_mk, CReal.RCle_mk] at hgap
  exact hgap

/-! ## 3. Exact graph-norm convergence residual and compiler -/

/-- The two convergence laws still needed to transport the uniform finite
operator gap to the already constructed cutoff-removed transfer.

The approximants themselves and their exact finite vacuum orthogonality are
not fields: they were constructed above.  Convergence is required only for
representatives whose cutoff-removed class is vacuum-orthogonal, exactly the
sector on which strict contraction is asserted. -/
structure CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) : Type where
  norm_converges : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy),
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X) ->
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageNorm hw0 hw1 half X)
      (physicalCauchyPairingLimit hw0 hw1 half X X)
  transferredNorm_converges : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy),
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X) ->
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        (centralPhysicalLinearMarkovMapCauchy M X))

namespace CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence

/-- The finite uniform sixteenth survives the two explicit centered
graph-norm limits at representative level. -/
theorem representative_operator_norm_gap_sixteenth
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    (graph : CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence
      hw0 hw1 half M)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        (centralPhysicalLinearMarkovMapCauchy M X))
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (physicalCauchyPairingLimit hw0 hw1 half X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (graph.transferredNorm_converges X horthogonal)
    (CReal.convergesTo_constMul
      (physicalCutoffSixteenth * physicalCutoffSixteenth)
      (graph.norm_converges X horthogonal))
  intro cutoff
  exact centralPhysicalCutoffCenteredStage_operator_norm_gap_sixteenth
    hw0 hw1 half certificate X cutoff

/-- The fixed-nome finite sixteenth plus exactly the two centered graph-norm
convergences inhabit strict contraction of the actual cutoff-removed transfer
on its actual completed vacuum complement. -/
def toStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    {pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M}
    (graph : CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence
      hw0 hw1 half M)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M pairingInvariant where
  rate := physicalCutoffSixteenth
  rate_nonnegative := physicalCutoffSixteenth_nonnegative
  rate_lt_one := physicalCutoffSixteenth_lt_one
  contraction := by
    intro vector
    rcases vector with ⟨point, horthogonal⟩
    revert horthogonal
    refine Quotient.inductionOn point ?_
    intro X horthogonal
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (centralPhysicalLinearMarkovMapCauchy M X)
          (centralPhysicalLinearMarkovMapCauchy M X)))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half X X)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact graph.representative_operator_norm_gap_sixteenth
      certificate X horthogonal

end CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence

/-! ## Axiom audit -/

#print axioms centralPhysicalCutoffCenteredStagePoint_vacuumOrthogonal
#print axioms centralPhysicalCutoffCenteredStage_operator_norm_gap_sixteenth
#print axioms CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence
#print axioms CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence.representative_operator_norm_gap_sixteenth
#print axioms CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence.toStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
