/-
M4j -- reduce the continuum reconstruction spectral-channel handoff to one
Wilson-character two-point identification.

The projective OS handoff already identifies the continuum correlator with the
Schwinger functional of a fixed connected insertion.  The Wilson/OS4 pin
already identifies the reconstruction model with the finite excited-character
model.  Therefore the remaining spectral-channel assertion is just the
equality of the connected OS two-point function with that character-model
correlator.

For a nonempty character cutoff this module also proves, rather than assumes,
positivity of the spectral correlator at time zero.  No continuum measure,
OS reconstruction, or character two-point identity is constructed here.
-/

import YMGap.Continuum.ProjectiveOSCorrelationHandoff
import YMGap.Continuum.WilsonLinkedOSReconstruction

namespace YMGap.Continuum.WilsonSpectralChannelHandoff

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonLinkedOSReconstruction
open YMGap.Continuum.WilsonSpectralBridge

/-! ## Non-vacuity of a nonempty excited-character model -/

/-- A nonempty excited-character model has a strictly positive time-zero
correlator.  The first character weight is `dimQ 1 > 0`; every later weight is
nonnegative. -/
theorem excitedCharModel_corr_zero_pos
    (w : Q') (hw0 : (0 : Q') <= w) (N : Nat) :
    (0 : Q') < corr (excitedCharModel w hw0 (N + 1)) 0 := by
  let S := excitedCharModel w hw0 (N + 1)
  let f : QSeq := fun i => S.w i * (S.lam i) ^ 0
  have hf0 : (0 : Q') < finSum f 1 := by
    change (0 : Q') < (0 : Q') + (dimQ 1 * (qpow w (c4 1)) ^ 0)
    rw [Q'.zero_add', Q'.pow_zero]
    have hdim : (0 : Q') < dimQ 1 := by
      show (0 : Q') < Q'.ofNat (1 + 1)
      exact Q'.ofNat_succ_pos 1
    exact Q'.mul_pos hdim (by decide)
  have hmono : finSum f 1 <= finSum f (N + 1) :=
    finSum_monotone_of_nonneg f
      (fun i => Q'.mul_nonneg (S.w i) ((S.lam i) ^ 0)
        (S.w_nonneg i) (Q'.pow_nonneg (S.lam i) (S.lam_nonneg i) 0))
      1 (N + 1) (Nat.succ_le_succ (Nat.zero_le N))
  exact Q'.pos_of_lt_of_le hf0 hmono

/-! ## The single remaining character-channel pin -/

/-- The connected OS two-point function is the correlator of the nonempty
finite excited-character model already pinned to OS4.

This is strictly smaller than a free
`ReconstructionSpectralChannelHandoff`: the OS/continuum side is fixed by `B`,
the spectral model is fixed by `characterOS4`, and time-zero non-vacuity is
proved from the first character weight. -/
structure WilsonCharacterSpectralChannelPin
    {Sep : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff Sep H D.measureLinked sampling)
    {w time : Q'} {htime : (0 : Q') <= time} {N : Nat}
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q'))
    (characterOS4 :
      WilsonLinkedOSGNSData.WilsonCharacterOS4Pin D.measureLinked
        D.timeTranslation htime (N + 1) hw0 hw1) : Type 2 where
  /-- The selected connected OS insertion has exactly the finite character
  spectral correlator at every integer Euclidean time. -/
  osConnectedCorr_eq_character : forall n : Nat,
    CReal.Equiv
      (CReal.ofQ' (H.os_axioms.E.E
        (B.osConnectedTwoPoint.connectedInsertion
          B.osConnectedTwoPoint.gapInsertion n)))
      (CReal.ofQ' (corr
        (D.timeTranslation.normalizedCharacterGapData
          (N := N + 1) hw0 hw1).model n))

namespace WilsonCharacterSpectralChannelPin

/-- The OS4 model pin and the connected character-correlator identity construct
the standard continuum reconstruction spectral-channel handoff. -/
def toReconstructionSpectralChannelHandoff
    {Sep : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff Sep H D.measureLinked sampling}
    {w time : Q'} {htime : (0 : Q') <= time} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {characterOS4 :
      WilsonLinkedOSGNSData.WilsonCharacterOS4Pin D.measureLinked
        D.timeTranslation htime (N + 1) hw0 hw1}
    (S : WilsonCharacterSpectralChannelPin D B hw0 hw1 characterOS4) :
    ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
      B D.reconstruction where
  spectralCorr_eq := by
    intro n
    have hmodel : D.reconstruction.spec =
        (D.timeTranslation.normalizedCharacterGapData
          (N := N + 1) hw0 hw1).model :=
      D.selectedModel_eq_reconstructionSpec.symm.trans characterOS4.modelPinned
    refine CReal.Equiv.trans (CReal.Equiv.symm (B.gapFunctional_eq n)) ?_
    refine CReal.Equiv.trans (S.osConnectedCorr_eq_character n) ?_
    rw [hmodel]
    exact CReal.Equiv.refl _
  spectralCorrZero_pos := by
    rw [D.selectedModel_eq_reconstructionSpec.symm.trans
      characterOS4.modelPinned]
    exact excitedCharModel_corr_zero_pos w hw0 N

end WilsonCharacterSpectralChannelPin

end YMGap.Continuum.WilsonSpectralChannelHandoff

#print axioms YMGap.Continuum.WilsonSpectralChannelHandoff.excitedCharModel_corr_zero_pos
#print axioms YMGap.Continuum.WilsonSpectralChannelHandoff.WilsonCharacterSpectralChannelPin.toReconstructionSpectralChannelHandoff
