/-
# A nonzero excitation of the ORIGINAL thermodynamic OS completion

The SAME centered translated plaquette covariance has the positive floor
s/16 at every finite volume after cutoff removal. Its already-constructed
thermodynamic limit retains that floor. The actual centered embedded probe
therefore inhabits the existing unit complement with a positive completed
squared norm, carrying explicit representative and volume Cauchy moduli.

The existing fixed-space theorem then proves this state is not fixed by
any positive integer time, and in particular the two-step transfer is not
the identity. This is SU(2), nome 1/1024, fixed spacing, on the current
plaquette-generated OS completion. Full observable realization/completeness,
continuum scaling, continuous-time generator/spectral identification and
continuum QFT/all-group Clay obligations remain open.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor
import YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (probe)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests (bulkProbe_enlarge)
open YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor (normalizedFloor normalizedFloor_positive connectedCovariance_floor)
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit

theorem covarianceSequence_floor (volume : Nat) :
    leEv (ofQ' normalizedFloor) (covarianceSequence probe probe volume) := by
  have h := connectedCovariance_floor (0+volume)
  rw [bulkProbe_enlarge volume] at h
  exact h

/-- The same thermodynamic covariance, not a new limit or measure. -/
def normRepresentative : CReal := covarianceLimit probe probe

def normCauchy : QCauchy normRepresentative.approx := covarianceLimitCauchy probe probe

def volumeModulus : Q' → Nat := covarianceVolumeModulus probe probe

theorem norm_volume_error (epsilon : Q') (he : (0 : Q') < epsilon)
    (volume : Nat) (hv : volumeModulus epsilon ≤ volume) :
    leEv (CReal.abs (CReal.sub normRepresentative (covarianceSequence probe probe volume))) (ofQ' epsilon) :=
  covariance_error_le probe probe epsilon he volume hv

theorem norm_floor : leEv (ofQ' normalizedFloor) normRepresentative :=
  leEv_of_convergesTo_le (convergesTo_const _) (covariance_converges probe probe) covarianceSequence_floor

/-- Actual centered embedded observable in the EXISTING thermodynamic carrier. -/
def state : UnitComplement := centeredState (embedPresentation ⟨0,probe⟩)

theorem norm_pin : completedInner state.val state.val = Quotient.mk crealSetoid normRepresentative :=
  centered_inner_sameBase probe probe

theorem state_norm_floor : RCle (Quotient.mk crealSetoid (ofQ' normalizedFloor)) (completedInner state.val state.val) := by
  rw [norm_pin]
  exact norm_floor

theorem state_orthogonal : completedInner state.val completedUnit = RCzero := state.property

theorem state_ne_zero : state.val ≠ completedZero := by
  intro hz
  have h := state_norm_floor
  rw [hz, completedInner_zero_left] at h
  have hle : normalizedFloor ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q')) (Q'.pos_of_lt_of_le normalizedFloor_positive hle)

/-- Nontrivial ORIGINAL discrete time, at every positive integer lag. -/
theorem state_not_time_fixed (n : Nat) (hn : 0<n) : completedTime n state.val ≠ state.val := by
  intro hx
  have hz := fixed_center_zero n hn state.val hx
  rw [(center_fixed_iff state.val).mpr state.property] at hz
  exact state_ne_zero hz

theorem twoStep_not_identity : twoStepTransfer state.val ≠ state.val :=
  state_not_time_fixed 2 (by decide)

/-- Concrete witness and its norm/moduli are available as Type-level data. -/
def excitationCertificate :
    Σ' x : UnitComplement, Σ' r : CReal, QCauchy r.approx ×'
      (completedInner x.val x.val = Quotient.mk crealSetoid r) ×'
      leEv (ofQ' normalizedFloor) r :=
  ⟨state, normRepresentative, normCauchy, norm_pin, norm_floor⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.covarianceSequence_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.normRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.normCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.norm_volume_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.state_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.state_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.state_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.state_not_time_fixed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.twoStep_not_identity
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation.excitationCertificate
