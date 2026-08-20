/-
M4o -- iterate the minimal Wilson operator-norm gap.

The one-step bound on the selected vacuum complement does not iterate from the
current `TransferOperator` fields alone: that interface does not say that the
chosen vacuum is fixed.  This module names exactly the missing stationarity
datum `T Omega = Omega`.  Self-adjointness then proves invariance of
`Omega^perp`, and the direct one-step norm pin iterates to

  ||T^n x||^2 <= (sep^2)^n ||x||^2.

No continuum datum, stationarity pin, or direct norm pin is constructed here.
-/

import YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

namespace YMGap.Continuum.WilsonIteratedNormDecayHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- The selected transfer fixes its own vacuum.  This is the smallest extra
datum needed to make the selected vacuum complement invariant. -/
structure WilsonVacuumStationarityPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  stationary :
    D.timeTranslation.op.T D.timeTranslation.op.vacuum =
      D.timeTranslation.op.vacuum

/-- A dense-observable sufficient interface for vacuum stationarity.  It pins
the completed vacuum to the embedded additive zero and asks the observable
time shift to preserve zero modulo the GNS carrier equivalence. -/
structure WilsonDenseVacuumPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  vacuumPinned :
    D.timeTranslation.op.vacuum =
      embedV D.wilson.toGNSData D.wilson.toGNSData.zero
  tau_zero : D.wilson.toGNSData.veq
    (D.timeTranslation.tau D.wilson.toGNSData.zero)
    D.wilson.toGNSData.zero

namespace WilsonDenseVacuumPin

/-- Dense intertwining converts the two concrete zero pins into `T Omega =
Omega`. -/
def toStationarity
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (V : WilsonDenseVacuumPin D) : WilsonVacuumStationarityPin D where
  stationary := by
    rw [V.vacuumPinned,
      D.timeTranslation.dense_intertwines D.wilson.toGNSData.zero]
    exact embedV_eq_of_veq D.wilson.toGNSData V.tau_zero

end WilsonDenseVacuumPin

namespace WilsonVacuumStationarityPin

/-- Self-adjointness and `T Omega = Omega` make `Omega^perp` invariant under
one transfer step. -/
theorem transfer_preservesVacPerp
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (S : WilsonVacuumStationarityPin D)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : D.selectedSpectralData.vacPerp x) :
    D.selectedSpectralData.vacPerp (D.timeTranslation.op.T x) := by
  change D.wilson.toGNSData.gnsComplete.hilbert.cinner
      (D.timeTranslation.op.T x) D.timeTranslation.op.vacuum = RCzero
  rw [D.timeTranslation.op.selfAdjoint x D.timeTranslation.op.vacuum,
    S.stationary]
  exact hx

/-- Every transfer iterate preserves the selected vacuum complement. -/
theorem Tpow_preservesVacPerp
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (S : WilsonVacuumStationarityPin D)
    (n : Nat)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : D.selectedSpectralData.vacPerp x) :
    D.selectedSpectralData.vacPerp
      (Tpow D.timeTranslation.op n x) := by
  induction n with
  | zero => exact hx
  | succ k ih => exact S.transfer_preservesVacPerp ih

end WilsonVacuumStationarityPin

/-- The minimal endpoint plus the vacuum stationarity needed for repeated
Euclidean propagation. -/
structure WilsonIteratedBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  boundedGap : WilsonMinimalBoundedMassGap D
  stationarity : WilsonVacuumStationarityPin D

namespace WilsonIteratedBoundedMassGap

/-- The direct one-step gap iterates on the invariant vacuum complement. -/
theorem iteratedNormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonIteratedBoundedMassGap D)
    (n : Nat)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : D.selectedSpectralData.vacPerp x) :
    RCle
      (D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow D.timeTranslation.op n x)
        (Tpow D.timeTranslation.op n x))
      (RCscale
        ((D.selectedSpectralData.gap.sep *
            D.selectedSpectralData.gap.sep) ^ n)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x)) := by
  induction n with
  | zero =>
      rw [Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | succ k ih =>
      have hstep := G.boundedGap.operatorGap.normGap
        (G.stationarity.Tpow_preservesVacPerp k hx)
      refine RCle_trans hstep ?_
      have hsepSqNonneg : (0 : Q') <=
          D.selectedSpectralData.gap.sep *
            D.selectedSpectralData.gap.sep :=
        Q'.mul_nonneg _ _ D.selectedSpectralData.gap.sep_nonneg
          D.selectedSpectralData.gap.sep_nonneg
      have hscaled := RCscale_mono hsepSqNonneg ih
      refine RCle_trans hscaled ?_
      rw [RCscale_RCscale]
      exact RCle_refl _

/-- The iterated endpoint retains the same positive exact physical rate. -/
theorem rate_posEv
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonIteratedBoundedMassGap D) :
    PosEv G.boundedGap.rate :=
  G.boundedGap.rate_posEv

end WilsonIteratedBoundedMassGap

end YMGap.Continuum.WilsonIteratedNormDecayHandoff

#print axioms YMGap.Continuum.WilsonIteratedNormDecayHandoff.WilsonVacuumStationarityPin.transfer_preservesVacPerp
#print axioms YMGap.Continuum.WilsonIteratedNormDecayHandoff.WilsonVacuumStationarityPin.Tpow_preservesVacPerp
#print axioms YMGap.Continuum.WilsonIteratedNormDecayHandoff.WilsonDenseVacuumPin.toStationarity
#print axioms YMGap.Continuum.WilsonIteratedNormDecayHandoff.WilsonIteratedBoundedMassGap.iteratedNormGap
#print axioms YMGap.Continuum.WilsonIteratedNormDecayHandoff.WilsonIteratedBoundedMassGap.rate_posEv
