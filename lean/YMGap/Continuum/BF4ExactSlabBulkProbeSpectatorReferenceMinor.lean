/-
# Positive full-spectator reference minor and homogeneous normalization

The reference determinant is -s*Zsp^2, its square is s^2*Zsp^4, and the
two-test reference budget is s*Zsp^3, where s=(2*w^3)^4/32768. Hence the
exact division-free balance is Dref=(s*Zsp)*Rref. No denominator-plus-one
floor loses the background scaling.

The scalar reference energy is also pinned to the ORIGINAL retained test
energy: reference energies do not contain the removed lower collar. The
original interacting AMPLITUDES still do. Their collar perturbation and
the SAME full partition comparison remain open before a thermodynamic
positive excitation can be claimed.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference

namespace YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference (bulkProbe)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests (localChoice scalarTest)
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes (backgroundMass background_positive)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (channelWeightPower)
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor (determinant_congr channelWeightPower_positive)
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests (referenceEnergy)
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound (determinant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem minor_model (s z : Q') : -(s*z*z) * -(s*z*z) ≈ (s*s)*((z*z)*(z*z)) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))) (by decide)
    (fun | 0 => s | _ => z)

private theorem budget_model (e z : Q') : (2 : Q')*(z*(0*0)+(e*z)*(z*z)) ≈ (2*e)*(z*z*z) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.const 2) (.add (.mul (.var 1) (.mul (.const 0) (.const 0)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 1)))))
    (.mul (.mul (.const 2) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (by decide)
    (fun | 0 => e | _ => z)

private theorem balance_model (s z : Q') : (s*s)*((z*z)*(z*z)) ≈ (s*z)*(s*(z*z*z)) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (by decide)
    (fun | 0 => s | _ => z)

theorem original_scalar_energy_pin {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat) :
    referenceEnergy hw K hK half (localChoice half (some (false,false))) (scalarTest w K half) ≈
      energyScale w * backgroundMass w K half :=
  Q'.eqv_trans _ _ _ (BF4ExactSlabBulkProbeInteractingAmplitudes.scalarEnergy_pin hw K hK half)
    (scalar_energy_pin hw K half)

theorem twice_energyScale (w : Q') : (2 : Q') * energyScale w ≈ signal w :=
  Q'.eqv_trans _ _ _
    (RingNormaliser.poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
      (fun | 0 => channelWeightPower w 4 | _ => Q'.invSucc 65535))
    (Q'.mul_eqv_congr_left _ _ _ (by decide : (2 : Q') * Q'.invSucc 65535 ≈ Q'.invSucc 32767))

def referenceDeterminant (w : Q') (K half : Nat) : Q' := determinant
  (unitAmplitudeReference w K half (lower (bulkProbe half)))
  (scalarAmplitudeReference w K half (lower (bulkProbe half)))
  (unitAmplitudeReference w K half polyOne) (scalarAmplitudeReference w K half polyOne)

def referenceMinor (w : Q') (K half : Nat) : Q' := referenceDeterminant w K half * referenceDeterminant w K half

/-- The identical homogeneous two-test budget formula, evaluated on the
collar-removed amplitudes and the exact original reference energies. -/
def referenceBudget (w : Q') (K half : Nat) : Q' := 2 *
  (unitEnergyReference w K half * (scalarAmplitudeReference w K half polyOne * scalarAmplitudeReference w K half polyOne) +
    scalarEnergyReference w K half * (unitAmplitudeReference w K half polyOne * unitAmplitudeReference w K half polyOne))

variable {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)

include hw

theorem referenceDeterminant_pin : referenceDeterminant w K half ≈ -(signal w * backgroundMass w K half * backgroundMass w K half) :=
  Q'.eqv_trans _ _ _ (determinant_congr (unit_probe_zero hw K half) (scalar_probe_pin hw K half)
    (unit_unit_pin hw K half) (scalar_unit_zero hw K half))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (by decide : (0 : Q')*0 ≈ 0) (Q'.eqv_refl _))
      (QPoly.q_zero_add_eqv _))

theorem referenceMinor_pin : referenceMinor w K half ≈
    (signal w * signal w) * ((backgroundMass w K half * backgroundMass w K half) *
      (backgroundMass w K half * backgroundMass w K half)) :=
  Q'.eqv_trans _ _ _ (qmul (referenceDeterminant_pin hw K half) (referenceDeterminant_pin hw K half))
    (minor_model _ _)

theorem referenceBudget_pin : referenceBudget w K half ≈
    signal w * (backgroundMass w K half * backgroundMass w K half * backgroundMass w K half) := by
  have h := Q'.mul_eqv_congr_left (2 : Q') _ _
    (Q'.add_eqv_congr'
      (qmul (unit_energy_pin hw K half) (qmul (scalar_unit_zero hw K half) (scalar_unit_zero hw K half)))
      (qmul (scalar_energy_pin hw K half) (qmul (unit_unit_pin hw K half) (unit_unit_pin hw K half))))
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (budget_model _ _)
    (qmul (twice_energyScale w) (Q'.eqv_refl _)))

/-- Exact homogeneous balance, without division or an artificial +1. -/
theorem reference_homogeneous_balance : referenceMinor w K half ≈
    (signal w * backgroundMass w K half) * referenceBudget w K half :=
  Q'.eqv_trans _ _ _ (referenceMinor_pin hw K half)
    (Q'.eqv_trans _ _ _
      (balance_model _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (referenceBudget_pin hw K half))))

omit hw in
theorem signal_positive {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < signal w :=
  Q'.mul_pos (channelWeightPower_positive hw 4) (Q'.invSucc_pos 32767)

omit hw in
theorem referenceMinor_positive {w : Q'} (hw : (0 : Q') < w) (K half : Nat)
    (hZ : (0 : Q') < backgroundMass w K half) : (0 : Q') < referenceMinor w K half :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (signal_positive hw) (signal_positive hw))
      (Q'.mul_pos (Q'.mul_pos hZ hZ) (Q'.mul_pos hZ hZ)))
    (Q'.ge_of_eqv (referenceMinor_pin (Q'.le_of_lt hw) K half))

omit hw in
theorem existingNome_referenceMinor_positive (K half : Nat) :
    (0 : Q') < referenceMinor BF4ExactSlabPlaquetteSmallNomeCertificate.nome K half :=
  referenceMinor_positive BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos K half
    (BF4ExactSlabBulkProbeInteractingAmplitudes.existingNome_background_positive K half)

end YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.original_scalar_energy_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.twice_energyScale
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.referenceDeterminant_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.referenceMinor_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.referenceBudget_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.reference_homogeneous_balance
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.signal_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.referenceMinor_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReferenceMinor.existingNome_referenceMinor_positive
