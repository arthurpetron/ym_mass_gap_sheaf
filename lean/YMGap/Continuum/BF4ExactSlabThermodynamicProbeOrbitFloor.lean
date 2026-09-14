/-
# Explicit positive margins along the ORIGINAL probe orbit

Nonzero is strengthened to a computed rational floor at every positive
integer time. Write m_n=||T_n x||^2, P for the existing positive observable
prefactor, and rho=w^36/16. Cauchy--Schwarz and contraction give

  m_n^2 <= m_(2n)*m_0 <= P*m_(2n),   m_(2n) <= m_(n+1) for n>=1.

Thus r_0=rho, r_(k+1)=r_k^2/P is positive and r_k<=m_(k+1).
The deliberately conservative floors depend on time; they are NOT uniform
as time tends to infinity. The SAME moments already have explicit Cauchy
moduli. No real reciprocal, choice, spectral theorem, new analytic premise,
or alteration of the original nome/action/completion is used.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation (Presentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate (positivePrefactor positivePrefactor_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit (orbit)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse (translated_norm_floor)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (probe)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (leEv_cancel_mul_right_posEv)

theorem moment_antitone (p : Presentation) (s t : Nat) (hst : s<=t) :
    leEv (moment p t) (moment p s) := by
  have h := completedTime_contraction (t-s) (completedTime s (center (embedPresentation p)))
  rw [completedTime_comp,show s+(t-s)=t from Nat.add_sub_of_le hst,moment_pin,moment_pin] at h
  exact h

/-- Pure order algebra: the positive rational margin remains returned data. -/
theorem square_floor_step (P r : Q') (hP : (0 : Q')<P) (hr : (0 : Q')<r)
    (a b c : CReal) (ha : leEv czero a) (hb : leEv czero b)
    (hlower : leEv (ofQ' r) a) (hsquare : leEv (CReal.mul a a) (CReal.mul b c))
    (hceiling : leEv c (ofQ' P)) :
    leEv (ofQ' (Q'.divPos (r*r) P hP)) b := by
  have hrr : leEv (ofQ' (r*r)) (CReal.mul a a) :=
    leEv_trans (leEv_of_equiv (ofQ'_mul r r))
      (leEv_trans (leEv_smul_nonneg (Q'.le_of_lt hr) hlower)
        (leEv_trans (leEv_of_equiv (cmul_comm _ _)) (leEv_mul_nonneg_left ha hlower)))
  apply leEv_cancel_mul_right_posEv (F:=ofQ' P) ⟨P,hP,leEv_refl _⟩
  have he : Equiv (CReal.mul (ofQ' (Q'.divPos (r*r) P hP)) (ofQ' P)) (ofQ' (r*r)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.divPos_mul_eqv (r*r) P hP)
  exact leEv_trans (leEv_of_equiv he)
    (leEv_trans hrr (leEv_trans hsquare (leEv_mul_nonneg_left hb hceiling)))

def probePresentation : Presentation := ⟨0,probe⟩

def normCeiling : Q' := positivePrefactor probe probe

theorem normCeiling_positive : (0 : Q')<normCeiling := positivePrefactor_pos probe probe

theorem initial_moment_ceiling : leEv (moment probePresentation 0) (ofQ' normCeiling) :=
  leEv_trans (moment_envelope probePresentation 0)
    (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv normCeiling)))

theorem first_moment_floor : leEv (ofQ' responseFloor) (moment probePresentation 1) := by
  have h := translated_norm_floor
  change RCle (Quotient.mk crealSetoid (ofQ' responseFloor))
    (completedInner (completedTime 1 (center (embedPresentation probePresentation)))
      (completedTime 1 (center (embedPresentation probePresentation)))) at h
  rw [moment_pin] at h
  exact h

/-- Index k bounds the squared norm at actual discrete time k+1. -/
def positiveTimeFloor : Nat → Q'
  | 0 => responseFloor
  | k+1 => Q'.divPos (positiveTimeFloor k*positiveTimeFloor k) normCeiling normCeiling_positive

theorem positiveTimeFloor_positive : ∀ k, (0 : Q')<positiveTimeFloor k
  | 0 => responseFloor_positive
  | k+1 => Q'.divPos_pos _ _ _ (Q'.mul_pos (positiveTimeFloor_positive k) (positiveTimeFloor_positive k))

theorem positiveTimeFloor_bound : ∀ k, leEv (ofQ' (positiveTimeFloor k)) (moment probePresentation (k+1))
  | 0 => first_moment_floor
  | k+1 => leEv_trans
      (square_floor_step normCeiling (positiveTimeFloor k) normCeiling_positive (positiveTimeFloor_positive k)
        _ _ _ (moment_nonnegative probePresentation (k+1))
        (moment_nonnegative probePresentation (k+1+(k+1))) (positiveTimeFloor_bound k)
        (moment_dyadic probePresentation (k+1)) initial_moment_ceiling)
      (moment_antitone probePresentation (k+1+1) (k+1+(k+1)) (by omega))

theorem orbit_norm_floor (k : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (positiveTimeFloor k)))
      (completedInner (orbit (k+1)).val (orbit (k+1)).val) := by
  change RCle (Quotient.mk crealSetoid (ofQ' (positiveTimeFloor k)))
    (completedInner (completedTime (k+1) (center (embedPresentation probePresentation)))
      (completedTime (k+1) (center (embedPresentation probePresentation))))
  rw [moment_pin]
  exact positiveTimeFloor_bound k

theorem even_autocorrelation_floor (k : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (positiveTimeFloor k)))
      (completedInner state.val (completedTime (k+1+(k+1)) state.val)) := by
  rw [← completedTime_moments]
  exact orbit_norm_floor k

/-- Actual state, same moment representative, explicit Cauchy modulus and
strict rational floor; no witness is extracted from mere nonzeroness. -/
def orbitCertificate (k : Nat) :
    Σ' r : Q', Σ' m : CReal, ((0 : Q')<r) ×' QCauchy m.approx ×'
      (completedInner (orbit (k+1)).val (orbit (k+1)).val=Quotient.mk crealSetoid m) ×'
      leEv (ofQ' r) m :=
  ⟨positiveTimeFloor k,moment probePresentation (k+1),positiveTimeFloor_positive k,
    momentCauchy probePresentation (k+1),moment_pin probePresentation (k+1),positiveTimeFloor_bound k⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.moment_antitone
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.square_floor_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.probePresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.normCeiling_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.initial_moment_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.first_moment_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.positiveTimeFloor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.positiveTimeFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.positiveTimeFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.orbit_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.even_autocorrelation_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor.orbitCertificate
