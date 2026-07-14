/-
# Non-vacuity of the finite spin-network spectral envelope

The generic finite-network envelope is instantiated by the globally wired
pure-`chi_2` theta mode.  Its three edge labels are all `2`, its exact weight
is the interacting two-vertex theta Wilson Gram, and the mode has an explicit
excited edge.  The resulting envelope correlators are proved to be the same
time-zero and time-one states as the previously constructed theta operator.

This is a normalization and non-vacuity audit.  It does not enlarge the theta
graph to a four-dimensional plaquette complex.
-/

import YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
import YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

namespace YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta

set_option maxHeartbeats 1000000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## The concrete one-mode theta family -/

def thetaEnvelopeOrder : List Nat := [0, 1, 2]

def thetaEnvelopeLabels : Nat → Nat → Nat := fun _ _ => 2

def thetaEnvelopeWeight : Nat → Q' := fun _ =>
  thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks

theorem thetaEnvelopeWeight_nonneg :
    ∀ i, (0 : Q') ≤ thetaEnvelopeWeight i := by
  intro i
  exact thetaSpinOneWeight_nonneg i

/-- The weight is genuinely nonzero, so this is not an empty spectral model. -/
theorem thetaEnvelopeWeight_pos :
    (0 : Q') < thetaEnvelopeWeight 0 := by
  unfold thetaEnvelopeWeight thetaWiredWilsonGram thetaWiredWilsonTerm
    thetaTwoVertexAmplitude thetaNonvacuum thetaTensorAmplitude thetaEdgePacket
    thetaFusedEdge pureQuadraticThetaLinks pureQuadraticIrrep
    YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket
    thetaPacketEigen YMGap.Continuum.BondMovingStep.fsum
    YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetEigen
    YMGap.Continuum.SpectralLocalizationCrux.eigA
    YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling
    YMGap.Continuum.SU2TrivalentThetaRecoupling.trivalentMultiplicity
    YMGap.Continuum.BondMovingStep.fusionInd
    YMGap.Continuum.BondMovingStep.fusionOK
  decide

theorem thetaEnvelopeExcitedSupport :
    ExcitedSupport thetaEnvelopeOrder thetaEnvelopeLabels 1 := by
  intro i hi
  refine ⟨0, ?_, ?_⟩
  · decide
  · unfold thetaEnvelopeLabels
    decide

/-- The generic product eigenvalue is the same three-edge eigenvalue used by
the dedicated theta construction. -/
theorem thetaEnvelope_networkEigen_exact :
    networkEigen thetaEnvelopeOrder (thetaEnvelopeLabels 0) ≈
      thetaSpinOneTransferEigen := by
  unfold networkEigen thetaEnvelopeOrder thetaEnvelopeLabels
    YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.eliminateLinks
    thetaSpinOneTransferEigen
    YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetEigen
    YMGap.Continuum.SpectralLocalizationCrux.eigA
    YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling
  decide

def thetaEnvelopeModel : SpectralModel :=
  finiteNetworkFamilyModel thetaEnvelopeOrder thetaEnvelopeLabels
    thetaEnvelopeWeight 1 thetaEnvelopeWeight_nonneg

def thetaEnvelopeLocatedGap : LocatedSpectralGap thetaEnvelopeModel :=
  finiteNetworkFamilyLocatedGap thetaEnvelopeOrder thetaEnvelopeLabels
    thetaEnvelopeWeight 1 thetaEnvelopeWeight_nonneg
    thetaEnvelopeExcitedSupport

theorem thetaEnvelope_gapMargin_exact :
    thetaEnvelopeLocatedGap.gapMargin ≈ Q'.mkPos 63 64 (by decide) :=
  finiteNetworkFamily_gapMargin_exact thetaEnvelopeOrder thetaEnvelopeLabels
    thetaEnvelopeWeight 1 thetaEnvelopeWeight_nonneg
    thetaEnvelopeExcitedSupport

/-! ## Same interacting state at times zero and one -/

theorem thetaEnvelope_corr_zero_is_wired_state :
    corr thetaEnvelopeModel 0 ≈
      thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks := by
  refine Q'.eqv_trans _ _ _
    (finiteNetworkFamily_corr_zero_eq_norm thetaEnvelopeOrder
      thetaEnvelopeLabels thetaEnvelopeWeight 1 thetaEnvelopeWeight_nonneg) ?_
  unfold finiteNetworkFamilyNorm thetaEnvelopeWeight
    YMGap.Continuum.BondMovingStep.fsum
  exact QPoly.q_zero_add_eqv _

private theorem thetaEnvelopeTransferredNorm_expanded :
    finiteNetworkFamilyTransferredNorm thetaEnvelopeOrder thetaEnvelopeLabels
        thetaEnvelopeWeight 1 ≈
      thetaEnvelopeWeight 0 *
        (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen) := by
  unfold finiteNetworkFamilyTransferredNorm
    YMGap.Continuum.BondMovingStep.fsum
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact q_mul_congr (Q'.eqv_refl _)
    (q_mul_congr thetaEnvelope_networkEigen_exact
      thetaEnvelope_networkEigen_exact)

private theorem thetaSpinOne_corr_one_expanded :
    corr thetaSpinOneSpectralModel 1 ≈
      thetaEnvelopeWeight 0 *
        (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen) := by
  unfold corr thetaSpinOneSpectralModel thetaSpinOneWeight
    thetaSpinOneSquaredEigen thetaEnvelopeWeight
  change ((0 : Q') +
      thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks *
        (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen) ^ 1) ≈
    thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks *
      (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen)
  rw [Q'.pow_succ, Q'.pow_zero]
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_one_eqv
      (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen))

/-- The generic envelope uses exactly the SAME interacting theta state and
transfer normalization as the dedicated wired construction. -/
theorem thetaEnvelope_corr_one_is_transferred_wired_state :
    corr thetaEnvelopeModel 1 ≈
      thetaWiredWilsonGram (transferThetaLinks pureQuadraticThetaLinks)
        (transferThetaLinks pureQuadraticThetaLinks) := by
  refine Q'.eqv_trans _
    (finiteNetworkFamilyTransferredNorm thetaEnvelopeOrder
      thetaEnvelopeLabels thetaEnvelopeWeight 1) _
    (finiteNetworkFamily_corr_one_eq_transferred_norm thetaEnvelopeOrder
      thetaEnvelopeLabels thetaEnvelopeWeight 1 thetaEnvelopeWeight_nonneg) ?_
  refine Q'.eqv_trans _
    (thetaEnvelopeWeight 0 *
      (thetaSpinOneTransferEigen * thetaSpinOneTransferEigen)) _
    thetaEnvelopeTransferredNorm_expanded ?_
  refine Q'.eqv_trans _ (corr thetaSpinOneSpectralModel 1) _
    (Q'.eqv_symm thetaSpinOne_corr_one_expanded) ?_
  exact thetaSpinOne_corr_one_is_transferred_wired_state

end YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta

#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelopeWeight_pos
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelopeExcitedSupport
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelope_networkEigen_exact
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelopeLocatedGap
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelope_gapMargin_exact
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelope_corr_zero_is_wired_state
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelopeTheta.thetaEnvelope_corr_one_is_transferred_wired_state
