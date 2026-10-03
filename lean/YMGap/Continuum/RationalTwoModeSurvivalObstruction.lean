/-
# Positive two-mode moments do not supply selected-excitation retention

At horizon s=n+1 the slow rate is q=1-1/(2s), the fast rate is 1/2,
and the positive slow overlap is alpha=(half^s)^4. The literal two-mode
moments, normalized by their positive total weight, have C0=1 and
s*(1-q)=half. Nevertheless C(2s)<=2*half^s*C(s), so every fixed positive
macroscopic retention coefficient fails at a computed eventual cutoff.

These are explicit scalar positive-mode data, not an original BF4 state,
action, terminal source, or continuum/Yang--Mills counterexample. They
disprove the proposed implication from rate compatibility, unit norm and
existence of a slow mode alone; a quantitative selected-source overlap is
still needed. No spectral theorem or choice is used.
-/

import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.HalfPow
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.RationalTwoModeSurvivalObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def horizon (n : Nat) : Nat := n+1

def fastHorizon (n : Nat) : Q' := half^(horizon n)

def slowOverlap (n : Nat) : Q' :=
  (fastHorizon n*fastHorizon n)*(fastHorizon n*fastHorizon n)

def slowRate (n : Nat) : Q' := 1-half*Q'.invSucc n

private theorem power_positive (q : Q') (hq : (0 : Q') < q) :
    ∀ j : Nat, (0 : Q') < q^j
  | 0 => by change (0 : Q') < (1 : Q'); decide
  | j+1 => Q'.mul_pos hq (power_positive q hq j)

private theorem power_le_one (q : Q') (hq : (0 : Q') ≤ q) (hq1 : q ≤ 1) :
    ∀ j : Nat, q^j ≤ 1
  | 0 => Q'.le_refl' _
  | j+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ q (power_le_one q hq hq1 j) hq)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q)) hq1)

private theorem pow_add (q : Q') (a : Nat) : ∀ b : Nat,
    q^(a+b) ≈ q^a*q^b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv _)
  | b+1 => by
      rw [show a+(b+1)=a+b+1 by omega, Q'.pow_succ, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ (pow_add q a b))
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => q | 1 => q^a | _ => q^b))

/-- Both mode weights are positive; the selected slow overlap is literal
alpha, not a uniform lower bound on it. -/
theorem slowOverlap_positive (n : Nat) : (0 : Q') < slowOverlap n := by
  have hv := power_positive half (by decide) (horizon n)
  exact Q'.mul_pos (Q'.mul_pos hv hv) (Q'.mul_pos hv hv)

private theorem inv_le_one (n : Nat) : Q'.invSucc n ≤ (1 : Q') := by
  change (Q'.invSucc n).num*(1 : Int) ≤ (1 : Int)*((Q'.invSucc n).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den]
  simp only [Int.one_mul, Int.mul_one]
  omega

/-- The explicitly constructed slow and fast rates lie in (0,1]. -/
theorem slowRate_bounds (n : Nat) : half ≤ slowRate n ∧ slowRate n ≤ 1 := by
  have hloss : half*Q'.invSucc n ≤ half := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ half (inv_le_one n) half_nonneg)
    (Q'.le_of_eqv (Q'.mul_one_eqv half))
  have hlo := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hloss)
  have hhi := Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (Q'.mul_nonneg _ _ half_nonneg (Q'.invSucc_nonneg n)))
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : half ≈ 1-half)) hlo,
    Q'.le_trans' _ _ _ hhi (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))⟩

/-- Neither mode is stationary at any finite horizon. -/
theorem slowRate_lt_one (n : Nat) : slowRate n < (1 : Q') := by
  have hloss : (0 : Q') < half*Q'.invSucc n :=
    Q'.mul_pos (by decide : (0 : Q') < half) (Q'.invSucc_pos n)
  simpa only [slowRate, PositiveContractionResidual.rate] using
    (PositiveContractionResidual.rate_lt_one hloss)

/-- Exact compatibility at the chosen physical-sized horizon, independent
of the exponentially tiny selected slow overlap. -/
theorem horizon_rate_loss (n : Nat) :
    Q'.ofNat (horizon n)*(1-slowRate n) ≈ half := by
  have hcancel := Q'.ofNat_succ_mul_invSucc n
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.const 1)
      (.neg (.add (.const 1) (.neg (.mul (.var 1) (.var 2)))))))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => Q'.ofNat (n+1) | 1 => half | _ => Q'.invSucc n)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ hcancel)
    (Q'.mul_one_eqv half)

private theorem total_positive (n : Nat) : (0 : Q') < 1+slowOverlap n :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 _ (Q'.le_of_lt (slowOverlap_positive n)))

def normalization (n : Nat) : Q' := Q'.recipPos (1+slowOverlap n) (total_positive n)

/-- A literal sum of two positive scalar mode responses. -/
def response (n j : Nat) : Q' :=
  normalization n*(slowOverlap n*(slowRate n)^j+half^j)

theorem response_zero (n : Nat) : response n 0 ≈ 1 := by
  have hrec := Q'.mul_recipPos_eqv (1+slowOverlap n) (total_positive n)
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.mul (.var 1) (.const 1)) (.const 1)))
    (.mul (.add (.const 1) (.var 1)) (.var 0))
    (by decide) (fun | 0 => normalization n | _ => slowOverlap n)) hrec

/-- Literal positive fast-mode floor, with the actual normalization retained. -/
theorem response_fast_floor (n j : Nat) :
    normalization n*half^j ≤ response n j := by
  have hq0 := Q'.le_trans' _ _ _ half_nonneg (slowRate_bounds n).1
  have ha0 := Q'.le_of_lt (slowOverlap_positive n)
  have hraw : half^j ≤ slowOverlap n*(slowRate n)^j+half^j :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ ha0 (Q'.pow_nonneg _ hq0 j)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.mul_le_mul_of_nonneg_left _ _ (normalization n) hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ (total_positive n)))

/-- Cancellation below uses only this computed pointwise positive floor,
never a scale-uniform lower bound on the response. -/
theorem response_positive (n j : Nat) : (0 : Q') < response n j :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (Q'.recipPos_pos _ (total_positive n))
    (power_positive half (by decide) j)) (response_fast_floor n j)

/-- The SAME normalized selected excitation loses its macroscopic ratio
despite the slow mode and the exact half rate budget. -/
theorem response_doubling_upper (n : Nat) :
    response n (2*horizon n) ≤ 2*fastHorizon n*response n (horizon n) := by
  let v := fastHorizon n
  let a := slowOverlap n
  let r := normalization n
  have hv0 : (0 : Q') ≤ v := Q'.pow_nonneg half half_nonneg _
  have hv1 : v ≤ 1 := power_le_one half half_nonneg (by decide) _
  have hvv0 := Q'.mul_nonneg _ _ hv0 hv0
  have hvv1 : v*v ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ v hv1 hv0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hv1)
  have ha : a ≤ v*v := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (v*v) hvv1 hvv0)
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hq0 := Q'.le_trans' _ _ _ half_nonneg (slowRate_bounds n).1
  have hslow : a*(slowRate n)^(2*horizon n) ≤ a := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ a
      (power_le_one _ hq0 (slowRate_bounds n).2 _) (Q'.le_of_lt (slowOverlap_positive n)))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hfast : half^(2*horizon n) ≈ v*v := by
    rw [show 2*horizon n=horizon n+horizon n by omega]
    exact pow_add half (horizon n) (horizon n)
  have hraw : a*(slowRate n)^(2*horizon n)+half^(2*horizon n) ≤ 2*(v*v) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_trans' _ _ _ hslow ha) (Q'.le_of_eqv hfast))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.mul (.const 2) (.mul (.var 0) (.var 0))) (by decide) (fun _ => v)))
  have hfloor : v ≤ a*(slowRate n)^(horizon n)+v :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg v _ (Q'.mul_nonneg _ _
      (Q'.le_of_lt (slowOverlap_positive n)) (Q'.pow_nonneg _ hq0 _)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hnorm := Q'.mul_le_mul_of_nonneg_left _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ (total_positive n)))
  have hright := Q'.mul_le_mul_of_nonneg_left _ _ (2*v*r) hfloor
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hv0)
      (Q'.le_of_lt (Q'.recipPos_pos _ (total_positive n))))
  have hbridge : r*(2*(v*v)) ≈ (2*v*r)*v :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 2) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.mul (.const 2) (.var 1)) (.var 0)) (.var 1))
      (by decide) (fun | 0 => r | _ => v)
  have hend : (2*v*r)*(a*(slowRate n)^(horizon n)+v) ≈
      2*v*response n (horizon n) := Q'.mul_assoc_eqv (2*v) r _
  exact Q'.le_trans' _ _ _ hnorm
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hbridge)
      (Q'.le_trans' _ _ _ hright (Q'.le_of_eqv hend)))

/-- Explicit eventual failure threshold for each proposed positive floor. -/
def failureCutoff (kappa : Q') : Nat := geometricCutoff half 2 (half*kappa)

private theorem half_lt (x : Q') (hx : (0 : Q') < x) : half*x < x := by
  have hn := Q'.num_pos_of_pos hx
  have hd : (0 : Int) < (x.den : Int) := Int.ofNat_lt.mpr x.den_pos
  have hp := Int.mul_pos hn hd
  change (half*x).num*(x.den : Int) < x.num*((half*x).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  change (1*x.num)*(x.den : Int) < x.num*(2*(x.den : Int))
  simp only [Int.one_mul, ← Int.mul_assoc]
  rw [Int.mul_comm x.num 2, Int.mul_assoc]
  omega

/-- No positive macroscopic retention coefficient survives these explicit
normalized two-mode data. This is not a statement about a BF4 family. -/
theorem eventual_macro_floor_false (kappa : Q') (hkappa : (0 : Q') < kappa)
    (n : Nat) (hn : failureCutoff kappa ≤ horizon n) :
    ¬ kappa*response n (horizon n) ≤ response n (2*horizon n) := by
  have hgeo := geometric_bound half_nonneg (by decide : half < (1 : Q'))
    (by decide : (0 : Q') ≤ 2) (Q'.mul_pos (by decide) hkappa) (horizon n) hn
  have hcoefficient : 2*fastHorizon n ≤ half*kappa := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv 2 (fastHorizon n))) hgeo
  have hsmall := Q'.mul_le_mul_of_nonneg_right _ _ (response n (horizon n))
    hcoefficient (Q'.le_of_lt (response_positive n (horizon n)))
  have hupper := Q'.le_trans' _ _ _ (response_doubling_upper n) hsmall
  have he : (half*kappa)*response n (horizon n) ≈ half*(kappa*response n (horizon n)) :=
    Q'.mul_assoc_eqv _ _ _
  intro hfloor
  have hbad := Q'.le_trans' _ _ _ hfloor (Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv he))
  exact (Int.not_lt.mpr hbad)
    (half_lt _ (Q'.mul_pos hkappa (response_positive n (horizon n))))

end YMGap.Continuum.RationalTwoModeSurvivalObstruction

#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.horizon
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.fastHorizon
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.slowOverlap
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.slowRate
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.slowOverlap_positive
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.slowRate_bounds
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.slowRate_lt_one
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.horizon_rate_loss
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.normalization
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.response
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.response_zero
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.response_fast_floor
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.response_positive
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.response_doubling_upper
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.failureCutoff
#print axioms YMGap.Continuum.RationalTwoModeSurvivalObstruction.eventual_macro_floor_false
