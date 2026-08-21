/-
# Selected Wilson vacuum and dense mean convergence

The finite centering correction is controlled by the finite stationary mean.
To identify its continuum limit one must first identify the abstract vacuum
stored by the selected transfer operator with the dense constant observable.

This module records exactly that missing pin.  Once the selected vacuum is the
dense unit and time translation preserves that unit, vacuum orthogonality says
that the dense Wilson pairing with the unit converges to zero.  The statement
is proved along every explicitly cofinal sampler, both before and after one
time step.  No finite/continuum mean comparison or continuum construction is
asserted here.
-/

import YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
import YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
import YMGap.Continuum.WilsonIteratedNormDecayHandoff

namespace YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- The physically intended dense vacuum pin: the selected completed vacuum is
the embedded constant observable, and the observable shift preserves that
constant modulo the Wilson carrier equivalence. -/
structure WilsonDenseUnitVacuumPin
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  vacuumPinned :
    D.timeTranslation.op.vacuum =
      embedV D.wilson.toGNSData H.os_axioms.A.one
  tau_one : D.wilson.toGNSData.veq
    (D.timeTranslation.tau H.os_axioms.A.one) H.os_axioms.A.one

namespace WilsonDenseUnitVacuumPin

/-- Dense intertwining turns the unit pin into stationarity of the selected
completed vacuum. -/
def toStationarity
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (V : WilsonDenseUnitVacuumPin D) : WilsonVacuumStationarityPin D where
  stationary := by
    rw [V.vacuumPinned,
      D.timeTranslation.dense_intertwines H.os_axioms.A.one]
    exact embedV_eq_of_veq D.wilson.toGNSData V.tau_one

end WilsonDenseUnitVacuumPin

/-- The Wilson observable whose expectation is the dense pairing with the
constant unit.  No unital star-algebra simplification is assumed. -/
def continuumVacuumPairingObservable
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (a : D.wilson.toGNSData.V) : H.os_axioms.A.carrier :=
  H.os_axioms.A.mul (H.os_axioms.A.star a) H.os_axioms.A.one

/-- The rational Wilson pairing of a cofinally sampled dense representative
with the unit, embedded as a constructive real. -/
def continuumDenseVacuumPairingSequence
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat) (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale => CReal.ofQ'
    (D.wilson.toGNSData.B
      (X.seq (sampleIndex scale)) H.os_axioms.A.one)

/-- Vacuum orthogonality plus the dense-unit vacuum pin makes the sampled
Wilson pairing with the unit converge to zero. -/
theorem continuumDenseVacuumPairingSequence_converges_zero
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (V : WilsonDenseUnitVacuumPin D)
    (sampleIndex cofinalRate : Nat -> Nat)
    (hcofinal : forall threshold scale : Nat,
      cofinalRate threshold <= scale -> threshold <= sampleIndex scale)
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (continuumDenseVacuumPairingSequence D sampleIndex X)
      CReal.czero := by
  let unitRep := constCauchy D.wilson.toGNSData H.os_axioms.A.one
  have hpair : CReal.ConvergesTo
      (fun n => CReal.ofQ'
        (D.wilson.toGNSData.cInnerSeq X unitRep n))
      (D.wilson.toGNSData.cinnerRep X unitRep) :=
    CReal.convergesTo_ofQ'CauchySeq
      (D.wilson.toGNSData.cInnerSeq X unitRep)
      (D.wilson.toGNSData.cInnerQCauchy X unitRep)
  have hreindexed : CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (D.wilson.toGNSData.cInnerSeq X unitRep (sampleIndex scale)))
      (D.wilson.toGNSData.cinnerRep X unitRep) :=
    convergesTo_cofinalReindex hpair sampleIndex cofinalRate hcofinal
  have hsequence : CReal.ConvergesTo
      (continuumDenseVacuumPairingSequence D sampleIndex X)
      (D.wilson.toGNSData.cinnerRep X unitRep) := by
    simpa only [continuumDenseVacuumPairingSequence, unitRep,
      GNSData.cInnerSeq, constCauchy] using hreindexed
  have hquotient :
      Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X unitRep) =
        Quotient.mk CReal.crealSetoid CReal.czero := by
    have hv := horthogonal
    change D.wilson.toGNSData.cinnerCompl
        (selectedWilsonPoint D X) D.timeTranslation.op.vacuum =
      CReal.RCzero at hv
    rw [V.vacuumPinned] at hv
    change Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep X unitRep) =
      Quotient.mk CReal.crealSetoid CReal.czero at hv
    exact hv
  exact CReal.convergesTo_limit_congr hsequence (Quotient.exact hquotient)

/-- The representative selected by the linear time-translation lift is the
completed transfer of the original representative. -/
theorem selectedWilsonPoint_TCauchy
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (X : SelectedWilsonCauchy D) :
    selectedWilsonPoint D (L.linear.linearOperator.TCauchy X) =
      D.timeTranslation.op.T (selectedWilsonPoint D X) := by
  rw [<- L.linear.operatorPinned]
  exact (L.linear.linearOperator.T_ofCauchy X).symm

/-- The pointwise translated dense pairing with the unit also converges to
zero.  Stationarity makes the vacuum complement invariant; the pointwise lift
then identifies its sampled representative with `tau (X_n)`. -/
theorem continuumTranslatedDenseVacuumPairingSequence_converges_zero
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (V : WilsonDenseUnitVacuumPin D)
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (sampleIndex cofinalRate : Nat -> Nat)
    (hcofinal : forall threshold scale : Nat,
      cofinalRate threshold <= scale -> threshold <= sampleIndex scale)
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (D.wilson.toGNSData.B
          (D.timeTranslation.tau (X.seq (sampleIndex scale)))
          H.os_axioms.A.one))
      CReal.czero := by
  let TX := L.linear.linearOperator.TCauchy X
  have hTXOrthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D TX) := by
    rw [selectedWilsonPoint_TCauchy L X]
    exact V.toStationarity.transfer_preservesVacPerp horthogonal
  have hTX := continuumDenseVacuumPairingSequence_converges_zero V
    sampleIndex cofinalRate hcofinal TX hTXOrthogonal
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := continuumDenseVacuumPairingSequence D sampleIndex TX)
  · intro scale
    exact CReal.ofQ'_equiv_of_eqv
      (D.wilson.toGNSData.B_congr_left H.os_axioms.A.one
        (L.pointwise X (sampleIndex scale)))
  · exact hTX

end YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence

#print axioms YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence.WilsonDenseUnitVacuumPin.toStationarity
#print axioms YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence.continuumDenseVacuumPairingSequence_converges_zero
#print axioms YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence.selectedWilsonPoint_TCauchy
#print axioms YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence.continuumTranslatedDenseVacuumPairingSequence_converges_zero
