/-
# What the EXISTING completed scalar test actually measures

The original interacting identity survives the SAME volume family and
Cauchy completion: completedTest is the original inner product with the
already-present fundamental plaquette state, scaled by 1/128. The representing
state is explicitly constructed by rational scalar multiplication, without a
Hilbert representation theorem or representative selection.

This resolves this test's meaning. It does not add separating information
beyond the original plaquette pairing, prove a time preimage/range estimate,
or close a physical Hamiltonian or continuum/Clay obligation.
-/

import YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity
import YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest
import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests

namespace YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (probe)
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference (bulkProbe)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests (bulkProbe_enlarge)
open YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity
open YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest (meanLimit meanLimit_converges)
open YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest
open YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm (form)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression (shiftedExpression)
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage (characterFraction)

private abbrev probeP : Presentation := ⟨0,probe⟩

private theorem probe_lower_atBase (volume : Nat) :
    lower (atBase probeP volume (Nat.zero_le _)) = lower (bulkProbe volume) := by
  rw [lower_atBase]
  have hb := congrArg (@lower (0+volume)) (bulkProbe_enlarge volume)
  have hs : polynomial probeP volume = shiftedExpression volume probe := by
    change shiftedExpression (volume-0) probe = shiftedExpression volume probe
    rw [Nat.sub_zero]
  exact hs.trans ((lower_enlarge volume probe).symm.trans
    (hb.symm.trans (congrArg (fun n : Nat => lower (bulkProbe n)) (Nat.zero_add volume))))

/-- The same finite-volume test and common-base original OS pairing. -/
theorem testAt_eq_plaquette (p : Presentation) (volume : Nat) (hp : p.base ≤ volume) :
    Equiv (testAt p volume hp)
      (CReal.mul (ofQ' characterFraction) (formAt p probeP volume hp (Nat.zero_le _))) := by
  unfold formAt form
  rw [probe_lower_atBase]
  exact scalar_expectation_eq_plaquette nome nome_pos nome_lt_one volume (atBase p volume hp)

/-- Both sides use the existing volume limits and their explicit moduli. -/
theorem meanLimit_eq_presented_pairing (p : Presentation) :
    Equiv (meanLimit p.expression) (CReal.mul (ofQ' characterFraction) (presentedForm p probeP)) :=
  Equiv_of_limit_of_equal
    (fun margin => (testAt_sequence_pin p margin).symm.trans
      (testAt_eq_plaquette p (p.base+margin) (Nat.le_add_right _ _)))
    (meanLimit_converges p.expression)
    (convergesTo_const_mul (ofQ' characterFraction)
      (presentedForm_converges_at p probeP p.base (Nat.le_refl _) (Nat.zero_le _)))

/-- Supplied original Cauchy representatives, with no choice of one. -/
theorem representativeTest_eq_pairing (X : seminorm.Cauchy) :
    Equiv (representativeTest X)
      (CReal.mul (ofQ' characterFraction) (representativeInner X (seminorm.constant probeP))) :=
  Equiv_of_limit_of_equal (fun n => meanLimit_eq_presented_pairing (X.seq n))
    (testSequence_converges X)
    (convergesTo_const_mul (ofQ' characterFraction) (pairSequence_converges X (seminorm.constant probeP)))

/-- Equality of the EXISTING functional and EXISTING completed pairing. -/
theorem completedTest_eq_pairing (x : Completion) :
    completedTest x = RCmul (Quotient.mk crealSetoid (ofQ' characterFraction))
      (completedInner x (embedPresentation ⟨0,probe⟩)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (representativeTest_eq_pairing X)

/-- Explicit original state representing this one scalar functional. -/
def representingState : Completion := completedSmul characterFraction (embedPresentation ⟨0,probe⟩)

theorem completedTest_represented (x : Completion) :
    completedTest x = completedInner x representingState :=
  (completedTest_eq_pairing x).trans (completedInner_smul_right characterFraction x (embedPresentation ⟨0,probe⟩)).symm

end YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.testAt_eq_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.meanLimit_eq_presented_pairing
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.representativeTest_eq_pairing
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.completedTest_eq_pairing
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.representingState
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarPlaquettePairing.completedTest_represented
