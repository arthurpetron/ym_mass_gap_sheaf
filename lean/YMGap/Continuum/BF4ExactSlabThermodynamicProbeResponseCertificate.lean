/-
# A finite, sound and complete certificate for the ORIGINAL excited response

The only new test is a finite rational inequality. It uses the actual
finite-slab covariance approximant and the already-proved volume and inner
representative moduli. Each contributes tolerance delta, so a sample s
encloses the ORIGINAL thermodynamic response in [s-2*delta,s+2*delta].

An accepted certificate gives a strictly positive lower response, excluding
annihilation of the concrete excitation. Conversely, a supplied positive
response floor rho constructs an accepted certificate with delta=rho/8
and retained floor rho/2. This is a constructive reduction in BOTH directions,
not a new analytic assumption and not a claim that a certificate was found.

No certificate for the physical probe is instantiated here. The full
positive-time root, observable realization, continuous-time generator,
continuum limit and Clay theorem remain open. Nome and spacing are fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)

private theorem rational_order {a b : Q'} (h : leEv (ofQ' a) (ofQ' b)) : a ≤ b := by
  apply Q'.le_of_forall_pos_add
  intro epsilon he
  obtain ⟨N,hN⟩ := h epsilon he
  exact hN N (Nat.le_refl N)

private theorem subtract_allowance {a b d : Q'} (h : a+d ≤ b) : a ≤ b + -d := by
  apply le_of_add_le_add_right (c := d)
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => b | _ => d)))

/-- Two independently controlled errors, without selecting a limit representative. -/
theorem two_error_interval {x y : CReal} (cy : QCauchy y.approx)
    (delta : Q') (hd : (0 : Q') < delta)
    (hxy : leEv (CReal.abs (CReal.sub x y)) (ofQ' delta))
    (index : Nat) (hi : cy.M delta ≤ index) :
    leEv (ofQ' (y.approx index + -(delta+delta))) x ∧
      leEv x (ofQ' (y.approx index + (delta+delta))) := by
  have bounds (epsilon : Q') (he : (0 : Q') < epsilon) :
      ∃ N, ∀ n, N ≤ n →
        y.approx index + -(delta+delta) ≤ x.approx n + epsilon ∧
        x.approx n ≤ (y.approx index + (delta+delta)) + epsilon := by
    obtain ⟨N,hN⟩ := hxy epsilon he
    refine ⟨max N (cy.M delta), fun n hn => ?_⟩
    have hab : Q'.abs (x.approx n + -y.approx n) ≤ delta+epsilon :=
      hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hreg := cy.bound delta hd index n hi (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hyx := ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm (y.approx n) (x.approx n))) hab)
    have hsl := Q'.le_trans' _ _ _ hreg.1 (Q'.add_le_add_right _ _ delta hyx)
    have hsu := Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le hab)
      (Q'.add_le_add_right _ _ (delta+epsilon) hreg.2)
    constructor
    · exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-(delta+delta)) hsl)
        (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
          (.add (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 1))
            (.neg (.add (.var 1) (.var 1))))
          (.add (.var 0) (.var 2)) (by decide)
          (fun | 0 => x.approx n | 1 => delta | _ => epsilon)))
    · exact Q'.le_trans' _ _ _ hsu (Q'.le_of_eqv
        (RingNormaliser.poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
          (.add (.add (.var 0) (.add (.var 1) (.var 1))) (.var 2)) (by decide)
          (fun | 0 => y.approx index | 1 => delta | _ => epsilon)))
  constructor
  · intro epsilon he
    obtain ⟨N,hN⟩ := bounds epsilon he
    exact ⟨N, fun n hn => (hN n hn).1⟩
  · intro epsilon he
    obtain ⟨N,hN⟩ := bounds epsilon he
    exact ⟨N, fun n hn => (hN n hn).2⟩

/-- Finite rational data from the ORIGINAL covariance, including its SAME
action reciprocal. The index drives the existing nested cutoff schedules. -/
def sample (margin index : Nat) : Q' := (finiteResponse margin).approx index

theorem sample_interval (delta : Q') (hd : (0 : Q') < delta)
    (margin index : Nat) (hm : volumeModulus delta ≤ margin)
    (hi : representativeModulus margin delta ≤ index) :
    leEv (ofQ' (sample margin index + -(delta+delta))) responseRepresentative ∧
      leEv responseRepresentative (ofQ' (sample margin index + (delta+delta))) :=
  two_error_interval (finiteResponseCauchy margin) delta hd
    (response_volume_error delta hd margin hm) index hi

/-- Every condition is decidable on the supplied rational/natural data. -/
def check (delta : Q') (margin index : Nat) (floor : Q') : Bool :=
  decide ((0 : Q') < delta ∧ volumeModulus delta ≤ margin ∧
    representativeModulus margin delta ≤ index ∧ (0 : Q') < floor ∧
    floor + (delta+delta) ≤ sample margin index)

/-- A finite certificate format, not an additional frontier enumeration.
No inhabitant for the physical probe is asserted by this module. -/
structure Certificate where
  tolerance : Q'
  margin : Nat
  index : Nat
  floor : Q'
  accepted : check tolerance margin index floor = true

theorem Certificate.floor_positive (c : Certificate) : (0 : Q') < c.floor :=
  (of_decide_eq_true c.accepted).2.2.2.1

theorem Certificate.response_floor (c : Certificate) :
    leEv (ofQ' c.floor) responseRepresentative := by
  have h := of_decide_eq_true c.accepted
  have hfloor : c.floor ≤ sample c.margin c.index + -(c.tolerance+c.tolerance) :=
    subtract_allowance h.2.2.2.2
  have hlow : leEv (ofQ' c.floor)
      (ofQ' (sample c.margin c.index + -(c.tolerance+c.tolerance))) :=
    leEv_ofQ'_of_approx_ge (fun _ => hfloor)
  exact leEv_trans hlow
    (sample_interval c.tolerance h.1 c.margin c.index h.2.1 h.2.2.1).1

theorem Certificate.operator_floor (c : Certificate) :
    RCle (Quotient.mk crealSetoid (ofQ' c.floor)) response := by
  rw [response_pin]
  exact c.response_floor

theorem Certificate.response_ne_zero (c : Certificate) : response ≠ RCzero := by
  intro hz
  have h := c.operator_floor
  rw [hz] at h
  have hle : c.floor ≤ (0 : Q') := rational_order h
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le c.floor_positive hle)

theorem Certificate.translatedState_ne_zero (c : Certificate) :
    translatedState.val ≠ completedZero := fun h => c.response_ne_zero (response_zero_iff.mpr h)

theorem Certificate.twoStep_ne_zero (c : Certificate) :
    twoStepTransfer state.val ≠ completedZero :=
  fun h => c.response_ne_zero (response_zero_iff_twoStep_zero.mpr h)

def witnessTolerance (rho : Q') : Q' := Q'.invSucc 7 * rho

theorem witnessTolerance_positive {rho : Q'} (hr : (0 : Q') < rho) :
    (0 : Q') < witnessTolerance rho := Q'.mul_pos (Q'.invSucc_pos 7) hr

/-- Four error allowances plus the retained half-floor sum to the given floor. -/
theorem witness_budget (rho : Q') :
    Q'.eqv ((HalfPow.half*rho + (witnessTolerance rho+witnessTolerance rho)) +
      (witnessTolerance rho+witnessTolerance rho)) rho := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 2))
      (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
    (.mul (.add (.var 0) (.mul (.const 4) (.var 1))) (.var 2)) (by decide)
    (fun | 0 => HalfPow.half | 1 => Q'.invSucc 7 | _ => rho)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (HalfPow.half+4*Q'.invSucc 7) (1 : Q') rho (by decide))
    (Q'.one_mul_eqv rho))

/-- Completeness with supplied quantitative positivity: no unbounded search,
choice, equality test on reals, or assumed successful finite computation. -/
def certificateOfFloor (rho : Q') (hr : (0 : Q') < rho)
    (hresponse : leEv (ofQ' rho) responseRepresentative) : Certificate := by
  let delta := witnessTolerance rho
  have hd : (0 : Q') < delta := witnessTolerance_positive hr
  let margin := volumeModulus delta
  let index := representativeModulus margin delta
  have hs := (sample_interval delta hd margin index (Nat.le_refl _) (Nat.le_refl _)).2
  have hup : rho ≤ sample margin index + (delta+delta) := rational_order (leEv_trans hresponse hs)
  have hguard : HalfPow.half*rho + (delta+delta) ≤ sample margin index := by
    apply le_of_add_le_add_right (c := delta+delta)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (witness_budget rho)) hup
  refine ⟨delta,margin,index,HalfPow.half*rho,?_⟩
  exact decide_eq_true ⟨hd,Nat.le_refl _,Nat.le_refl _,ExpNeg.half_mul_pos rho hr,hguard⟩

theorem certificateOfFloor_floor (rho : Q') (hr : (0 : Q') < rho)
    (hresponse : leEv (ofQ' rho) responseRepresentative) :
    (certificateOfFloor rho hr hresponse).floor = HalfPow.half*rho := rfl

/-- The open response field is quantitatively equivalent to a finite accepted
certificate. Neither side is inhabited here. Witnesses remain Type-level data. -/
def positiveResponseWitness (c : Certificate) :
    Σ' rho : Q', ((0 : Q') < rho) ×' leEv (ofQ' rho) responseRepresentative :=
  ⟨c.floor,c.floor_positive,c.response_floor⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.two_error_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.sample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.sample_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.check
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.floor_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.response_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.operator_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.response_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.translatedState_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.Certificate.twoStep_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.witnessTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.witnessTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.witness_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.certificateOfFloor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.certificateOfFloor_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate.positiveResponseWitness
