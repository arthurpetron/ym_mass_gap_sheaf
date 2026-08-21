/-
# Type-level modulus for the selected Wilson vacuum complement

Vacuum orthogonality is an equality in the quotient of constructive reals.
It proves qualitative convergence of dense vacuum pairings to zero, but its
existential `Equiv` witness cannot construct a `Nat`-valued rate without
choice.  The diagonal compiler needs that rate as data.

This module packages precisely the missing constructive witness.  It also
transports the modulus through one selected time step using vacuum stationarity
and the pointwise representative lift.  No modulus is fabricated from the
proposition-level quotient equality.
-/

import YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence

namespace YMGap.Continuum.BF4PhysicalVacuumPairingModulus

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- A dense-unit vacuum pin strengthened by a constructive representative-level
rate for the statement that vacuum-orthogonal classes pair with the unit by an
amount tending to zero. -/
structure WilsonDenseUnitVacuumPairingModulus
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  vacuumPin : WilsonDenseUnitVacuumPin D
  pairingRate : SelectedWilsonCauchy D -> Q' -> Nat
  pairingSmall : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall (epsilon : Q'), (0 : Q') < epsilon ->
        forall n : Nat, pairingRate X epsilon <= n ->
          -epsilon <= D.wilson.toGNSData.B
              (X.seq n) H.os_axioms.A.one /\
            D.wilson.toGNSData.B
              (X.seq n) H.os_axioms.A.one <= epsilon

namespace WilsonDenseUnitVacuumPairingModulus

variable
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (V : WilsonDenseUnitVacuumPairingModulus D)

/-- Running-maximum regularization of the pairing rate along the canonical
positive rational precision ladder. -/
def regularPairingRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  CReal.Gmax
    (fun precision => V.pairingRate X (Q'.invSucc precision))
    (CReal.lv epsilon)

/-- The regularized pairing rate is antitone in its positive tolerance. -/
theorem regularPairingRate_antitone
    (X : SelectedWilsonCauchy D)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    V.regularPairingRate X epsilon <= V.regularPairingRate X delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

/-- The regularized rate retains the original two-sided pairing estimate. -/
theorem regularPairingSmall
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : V.regularPairingRate X epsilon <= n) :
    -epsilon <= D.wilson.toGNSData.B
        (X.seq n) H.os_axioms.A.one /\
      D.wilson.toGNSData.B
        (X.seq n) H.os_axioms.A.one <= epsilon := by
  let delta : Q' := Q'.invSucc (CReal.lv epsilon)
  have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
  have hrawRate : V.pairingRate X delta <=
      V.regularPairingRate X epsilon :=
    CReal.Gmax_ge
      (fun precision => V.pairingRate X (Q'.invSucc precision))
      (CReal.lv epsilon)
  have hraw := V.pairingSmall X horthogonal delta hdelta n
    (Nat.le_trans hrawRate hn)
  have hdeltaepsilon : delta <= epsilon :=
    CReal.invSucc_lv_le hepsilon
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.neg_le_neg hdeltaepsilon) hraw.1,
      Q'.le_trans' _ _ _ hraw.2 hdeltaepsilon⟩

/-- The explicit rate required for the representative selected by one time
step. -/
def transferredPairingRate
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (X : SelectedWilsonCauchy D) (epsilon : Q') : Nat :=
  V.pairingRate (L.linear.linearOperator.TCauchy X) epsilon

/-- Antitone-regularized rate for the transferred representative. -/
def regularTransferredPairingRate
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (X : SelectedWilsonCauchy D) (epsilon : Q') : Nat :=
  V.regularPairingRate (L.linear.linearOperator.TCauchy X) epsilon

/-- The same Type-level vacuum-pairing estimate after one time step.  The
selected vacuum is stationary, so the transferred class is again in the
vacuum complement; pointwise intertwining then replaces the lifted sequence by
the observable translate. -/
theorem transferredPairingSmall
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : V.transferredPairingRate L X epsilon <= n) :
    -epsilon <= D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one /\
      D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one <= epsilon := by
  let TX := L.linear.linearOperator.TCauchy X
  have hTXOrthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D TX) := by
    rw [BF4PhysicalSelectedVacuumMeanConvergence.selectedWilsonPoint_TCauchy
      L X]
    exact V.vacuumPin.toStationarity.transfer_preservesVacPerp horthogonal
  have hsmall := V.pairingSmall TX hTXOrthogonal epsilon hepsilon n hn
  have heq : (D.wilson.toGNSData.B
      (TX.seq n) H.os_axioms.A.one).eqv
      (D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one) :=
    D.wilson.toGNSData.B_congr_left H.os_axioms.A.one
      (L.pointwise X n)
  exact
    ⟨le_of_le_eqv hsmall.1 heq,
      le_of_eqv_le (Q'.eqv_symm heq) hsmall.2⟩

/-- The regularized transferred rate retains the pointwise translated pairing
estimate. -/
theorem regularTransferredPairingSmall
    (L : WilsonPointwiseLinearTimeTranslationPin D.timeTranslation)
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat)
    (hn : V.regularTransferredPairingRate L X epsilon <= n) :
    -epsilon <= D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one /\
      D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one <= epsilon := by
  let TX := L.linear.linearOperator.TCauchy X
  have hTXOrthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D TX) := by
    rw [BF4PhysicalSelectedVacuumMeanConvergence.selectedWilsonPoint_TCauchy
      L X]
    exact V.vacuumPin.toStationarity.transfer_preservesVacPerp horthogonal
  have hsmall := V.regularPairingSmall TX hTXOrthogonal
    epsilon hepsilon n hn
  have heq : (D.wilson.toGNSData.B
      (TX.seq n) H.os_axioms.A.one).eqv
      (D.wilson.toGNSData.B
        (D.timeTranslation.tau (X.seq n)) H.os_axioms.A.one) :=
    D.wilson.toGNSData.B_congr_left H.os_axioms.A.one
      (L.pointwise X n)
  exact
    ⟨le_of_le_eqv hsmall.1 heq,
      le_of_eqv_le (Q'.eqv_symm heq) hsmall.2⟩

/-- The Wilson form pairing with the dense unit is the selected OS expectation
of the explicit vacuum-pairing observable. -/
theorem pairing_eq_continuumVacuumPairingExpectation
    (a : D.wilson.toGNSData.V) :
    D.wilson.toGNSData.B a H.os_axioms.A.one =
      H.os_axioms.E.E (continuumVacuumPairingObservable D a) := by
  change D.wilson.E
      (H.os_axioms.A.mul (H.os_axioms.A.star a) H.os_axioms.A.one) = _
  rw [D.expectationPinned]
  rfl

end WilsonDenseUnitVacuumPairingModulus

end YMGap.Continuum.BF4PhysicalVacuumPairingModulus

#print axioms YMGap.Continuum.BF4PhysicalVacuumPairingModulus.WilsonDenseUnitVacuumPairingModulus.transferredPairingSmall
#print axioms YMGap.Continuum.BF4PhysicalVacuumPairingModulus.WilsonDenseUnitVacuumPairingModulus.regularPairingSmall
#print axioms YMGap.Continuum.BF4PhysicalVacuumPairingModulus.WilsonDenseUnitVacuumPairingModulus.regularTransferredPairingSmall
#print axioms YMGap.Continuum.BF4PhysicalVacuumPairingModulus.WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
