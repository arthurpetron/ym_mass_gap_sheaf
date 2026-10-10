/-
# A finite scalar test separating area control from earliest-point survival

This is an exact finite two-mode rational test, not a Yang--Mills instance,
not an original-action estimate, and not a continuum counterexample.  The
positive moment law below has two modes with eigenvalues strictly below one.
At the constants used by the backward-area consumer (C=6, hence the old
window threshold theta=1/11), the finite area input holds while earliest-point
survival fails. The separate finite H1 inequality also holds. These are tests
at one scalar datum; they assert no uniformly weaker implication,
original-action estimate, or continuum counterexample.

The second, separately scoped test below establishes the converse separation
at one finite endpoint: the endpoint H1 inequality holds while the C=6
backward-area premise fails. It does not assert an unbounded/cofinal family
or realize either test on the original completed Yang--Mills carrier.

The separately scoped `PolynomialUV` family below is parametric: an exact
unit late floor and even a linear UV ceiling do not give a uniform endpoint
H1 coefficient for general positive scalar moments. It asserts no physical
realization of that scalar family.
-/

import YMGap.Constructive.Geometric
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy

namespace YMGap.Continuum.BackwardResponseAreaStrictness

set_option autoImplicit false

open YMGap.Constructive

/-- Slow and fast eigenvalues for the finite rational test. -/
def q : Q' := Q'.mkPos 63 64 (by decide)
def a : Q' := Q'.mkPos 1 2 (by decide)
def amplitude : Q' := 1048576

theorem q_bounds : (0 : Q') < q ∧ q < 1 := by decide
theorem a_bounds : (0 : Q') < a ∧ a < 1 := by decide
theorem one_sub_q_bounds : (0 : Q') < 1-q ∧ 1-q < 1 := by decide
theorem amplitude_positive : (0 : Q') < amplitude := by decide

/-- The unnormalized two-mode scalar response. -/
def response (k : Nat) : Q' := q^k + amplitude*a^k

/-- Positive two-mode moment law: the weights are 1 and 1048576, and the
corresponding eigenvalues are q and a. -/
def moment (k l : Nat) : Q' :=
  q^k*(1-q)^l + amplitude*a^(k+l)

/-- Every moment is nonnegative by the positive-weight decomposition. -/
theorem moment_nonnegative (k l : Nat) : (0 : Q') ≤ moment k l := by
  unfold moment
  apply Q'.zero_le_add
  · exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg q (by decide) k)
      (Q'.pow_nonneg (1-q) (by decide) l)
  · exact Q'.mul_nonneg _ _ (by decide)
      (Q'.pow_nonneg a (by decide) (k+l))

/-- The exact finite area window R(16)+...+R(31) is below
6*16*R(32), the area premise with C=6 and S=32. -/
def areaWindow : Q' :=
  response 16 + response 17 + response 18 + response 19 +
    response 20 + response 21 + response 22 + response 23 +
    response 24 + response 25 + response 26 + response 27 +
    response 28 + response 29 + response 30 + response 31

theorem finite_area_input : areaWindow ≤ 6*16*response 32 := by decide

/-- The old earliest-point floor fails at theta=1/11 for p=16. -/
theorem earliest_point_survival_fails :
    (Q'.mkPos 1 11 (by decide) : Q')*response 16 > response 33 := by decide

/-- The finite H1 bound with c0=20 holds at S=32. -/
theorem finite_H1 : 32*(response 32-response 33) ≤ 20*response 32 := by decide

/-- Positivity of a pure fast mode alone does not give this side-scaled H1.
This is a scalar screen, not an original-action obstruction. -/
theorem pure_fast_H1_fails : 20*a^64 < 64*(a^64-a^65) := by
  have hpos := ClusteringImpliesGap.pow_pos a_bounds.1 64
  have hlt := ClusteringImpliesGap.mul_lt_mul_of_pos_right hpos
    (by decide : (20 : Q') < 32)
  have heq : Q'.eqv (64*(a^64-a*a^64)) (32*a^64) := by
    exact Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.const 64) (.add (.var 0) (.neg (.mul (.var 1) (.var 0)))))
        (.mul (.add (.const 64) (.neg (.mul (.const 64) (.var 1)))) (.var 0))
        (by decide) (fun | 0 => a^64 | _ => a))
      (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (64 + -(64*a)) 32))
  exact ClusteringImpliesGap.lt_of_lt_of_le hlt (Q'.ge_of_eqv heq)

/-! ## A finite endpoint-H1 example outside the backward-area premise -/

namespace EndpointVsArea

/-- The second test keeps the fast rate at one half, but changes the slow
rate and positive fast weight. These are scalar moments, not BF4 responses. -/
def q : Q' := Q'.mkPos 127 128 (by decide)
def a : Q' := Q'.mkPos 1 2 (by decide)
def amplitude : Q' := 4194304

theorem q_bounds : (0 : Q') < q ∧ q < 1 := by decide
theorem a_bounds : (0 : Q') < a ∧ a < 1 := by decide
theorem amplitude_positive : (0 : Q') < amplitude := by decide

def response (k : Nat) : Q' := q^k + amplitude*a^k
def moment (k l : Nat) : Q' :=
  q^k*(1-q)^l + amplitude*a^(k+l)

/-- Both modal weights and both defect eigenvalues are nonnegative. -/
theorem moment_nonnegative (k l : Nat) : (0 : Q') ≤ moment k l := by
  unfold moment
  apply Q'.zero_le_add
  · exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg q (by decide) k)
      (Q'.pow_nonneg (1-q) (by decide) l)
  · exact Q'.mul_nonneg _ _ (by decide)
      (Q'.pow_nonneg a (by decide) (k+l))

/-- Literal backward area at p=16, n=16, endpoint s=32. -/
def areaWindow : Q' :=
  response 16 + response 17 + response 18 + response 19 +
    response 20 + response 21 + response 22 + response 23 +
    response 24 + response 25 + response 26 + response 27 +
    response 28 + response 29 + response 30 + response 31

/-- The endpoint H1 estimate has coefficient one, despite the large
early fast-mode contribution to the backward window. -/
theorem finite_endpoint_H1 :
    32*(response 32-response 33) ≤ response 32 := by decide

/-- The SAME positive moment law violates the C=6 backward-area ceiling. -/
theorem finite_area_ceiling_fails :
    6*16*response 32 < areaWindow := by decide

theorem endpoint_without_area :
    32*(response 32-response 33) ≤ response 32 ∧
      6*16*response 32 < areaWindow :=
  ⟨finite_endpoint_H1, finite_area_ceiling_fails⟩

end EndpointVsArea

/-! ## A parametric linear-UV countermodel for endpoint H1

This separate scalar family has an EXACT unit late response and a linear
time-zero ceiling, but its endpoint-scaled loss has no uniform coefficient.
All moments come from one positive contraction mode. This disproves only
the inference from these scalar premises; it is not a BF4 source, original
action, physical scaling family, or counterexample to Yang--Mills survival.
-/

namespace PolynomialUV

open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def k (n : Nat) : Nat := n+1
def block (n : Nat) : Nat := 2^(k n)
def index (n : Nat) : Nat := block n-1
def rate (n : Nat) : Q' := RationalTwoModeSurvivalObstruction.slowRate (index n)
def endpoint (n : Nat) : Nat := k n * block n

private theorem block_pos (n : Nat) : 0 < block n := Nat.pow_pos (by decide)

private theorem block_horizon (n : Nat) :
    RationalTwoModeSurvivalObstruction.horizon (index n) = block n :=
  Nat.sub_add_cancel (block_pos n)

/-- Each datum is a genuine strictly positive, strictly subunit pure mode. -/
theorem rate_bounds (n : Nat) : (0 : Q') < rate n ∧ rate n < 1 :=
  ⟨Q'.pos_of_lt_of_le (by decide : (0 : Q') < half)
      (RationalTwoModeSurvivalObstruction.slowRate_bounds (index n)).1,
    RationalTwoModeSurvivalObstruction.slowRate_lt_one (index n)⟩

attribute [local irreducible] rate

private theorem power_add (q : Q') (a : Nat) : ∀ b : Nat,
    q^(a+b) ≈ q^a*q^b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv _)
  | b+1 => by
      rw [show a+(b+1)=a+b+1 by omega, Q'.pow_succ, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ (power_add q a b))
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => q | 1 => q^a | _ => q^b))

private theorem ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  change ((a*b : Nat) : Int)*1 = ((a : Int)*(b : Int))*1
  rw [Int.natCast_mul]

private theorem ofNat_mono {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simpa only [Int.mul_one] using Int.ofNat_le.mpr h

private theorem half_power_normalizes (j : Nat) :
    half^j * Q'.ofNat (2^j) ≈ 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [Q'.pow_succ, Nat.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (half*half^j) _ _ (ofNat_mul (2^j) 2))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.const 2)))
            (.mul (.mul (.var 0) (.const 2)) (.mul (.var 1) (.var 2)))
            (by decide) (fun | 0 => half | 1 => half^j | _ => Q'.ofNat (2^j)))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ (half^j*Q'.ofNat (2^j))
              (by decide : half*2 ≈ 1))
            (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ih)))

private theorem repeated_block_floor (q : Q') (hq : (0 : Q') ≤ q)
    (m : Nat) (hm : half ≤ q^m) (j : Nat) : half^j ≤ q^(j*m) := by
  induction j with
  | zero => simpa only [Nat.zero_mul, Q'.pow_zero] using Q'.le_refl' (1 : Q')
  | succ j ih =>
      rw [Nat.succ_mul, Q'.pow_succ]
      have h1 := Q'.mul_le_mul_of_nonneg_left _ _ half ih half_nonneg
      have h2 := Q'.mul_le_mul_of_nonneg_right _ _ (q^(j*m)) hm
        (Q'.pow_nonneg q hq (j*m))
      have he : q^m*q^(j*m) ≈ q^(j*m+m) :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.eqv_symm (power_add q (j*m) m))
      exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv he))

/-- The previously proved one-block floor iterates over k actual blocks. -/
theorem endpoint_power_floor (n : Nat) : half^(k n) ≤ (rate n)^(endpoint n) := by
  have h : half ≤ (rate n)^(block n) := by
    unfold rate
    simpa only [block_horizon n] using
      RationalMacroRetentionWithoutInitialEnergy.slow_horizon_floor (index n)
  exact repeated_block_floor (rate n) (Q'.le_of_lt (rate_bounds n).1) (block n) h (k n)

private theorem endpoint_power_positive (n : Nat) :
    (0 : Q') < (rate n)^(endpoint n) :=
  ClusteringImpliesGap.pow_pos (rate_bounds n).1 (endpoint n)

/-- The reciprocal is constructed from the computed positive late power. -/
def amplitude (n : Nat) : Q' :=
  Q'.recipPos ((rate n)^(endpoint n)) (endpoint_power_positive n)

def response (n t : Nat) : Q' := amplitude n * (rate n)^t

/-- Positive pure-mode moments; all defect orders are retained. -/
def moment (n t l : Nat) : Q' := response n t * (1-rate n)^l

attribute [local irreducible] amplitude response moment

theorem amplitude_positive (n : Nat) : (0 : Q') < amplitude n := by
  unfold amplitude
  exact Q'.recipPos_pos _ (endpoint_power_positive n)

/-- No exponential UV prefactor is needed: A is at most 2^k. -/
theorem amplitude_le_block (n : Nat) : amplitude n ≤ Q'.ofNat (block n) := by
  have hc : (rate n)^(endpoint n)*amplitude n ≈ 1 := by
    unfold amplitude
    exact Q'.mul_recipPos_eqv _ (endpoint_power_positive n)
  have hlow : (1 : Q') ≤ (rate n)^(endpoint n)*Q'.ofNat (block n) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (half_power_normalizes (k n)))
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat (block n))
        (endpoint_power_floor n) (Q'.ofNat_nonneg _))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hc) hlow) (endpoint_power_positive n)

theorem endpoint_positive (n : Nat) : 0 < endpoint n :=
  Nat.mul_pos (Nat.succ_pos n) (block_pos n)

/-- The time-zero response has a LINEAR ceiling in the actual endpoint. -/
theorem response_zero_le_endpoint (n : Nat) : response n 0 ≤ Q'.ofNat (endpoint n) := by
  have hm : block n ≤ endpoint n := by
    have h := Nat.mul_le_mul_right (block n) (Nat.succ_pos n)
    simpa only [Nat.one_mul, k, endpoint] using h
  have hz : response n 0 ≈ amplitude n := by
    unfold response
    exact Q'.mul_one_eqv _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz)
    (Q'.le_trans' _ _ _ (amplitude_le_block n) (ofNat_mono hm))

/-- The late lower floor is exactly one, with its own normalization retained. -/
theorem response_endpoint (n : Nat) : response n (endpoint n) ≈ 1 := by
  unfold response amplitude
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv _ (endpoint_power_positive n))

theorem response_positive (n t : Nat) : (0 : Q') < response n t := by
  unfold response
  exact Q'.mul_pos (amplitude_positive n) (ClusteringImpliesGap.pow_pos (rate_bounds n).1 t)

/-- Every moment is nonnegative, at every time and defect order. -/
theorem moment_nonnegative (n t l : Nat) : (0 : Q') ≤ moment n t l := by
  have hd : (0 : Q') ≤ 1-rate n :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ 1-1))
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt (rate_bounds n).2)))
  unfold moment
  exact Q'.mul_nonneg _ _ (Q'.le_of_lt (response_positive n t))
    (Q'.pow_nonneg _ hd l)

theorem moment_response (n t : Nat) : moment n t 0 ≈ response n t := by
  unfold moment
  exact Q'.mul_one_eqv _

/-- Exact binomial splitting, rather than an assumed positive-moment law. -/
theorem moment_split (n t l : Nat) :
    moment n (t+1) l + moment n t (l+1) ≈ moment n t l := by
  unfold moment response
  rw [Q'.pow_succ, Q'.pow_succ]
  exact poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 0) (.var 2))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 3))))
    (.mul (.mul (.var 0) (.var 2)) (.var 3)) (by decide)
    (fun | 0 => amplitude n | 1 => rate n | 2 => (rate n)^t | _ => (1-rate n)^l)

private theorem endpoint_rate_loss (n : Nat) :
    Q'.ofNat (endpoint n)*(1-rate n) ≈ Q'.ofNat (k n)*half := by
  have h : Q'.ofNat (block n)*(1-rate n) ≈ half := by
    unfold rate
    simpa only [block_horizon n] using
      RationalTwoModeSurvivalObstruction.horizon_rate_loss (index n)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (1-rate n) (ofNat_mul (k n) (block n)))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left (Q'.ofNat (k n)) _ _ h))

/-- Exact growing endpoint loss: s(R(s)-R(s+1))=k/2. -/
theorem scaled_loss_pin (n : Nat) :
    Q'.ofNat (endpoint n)*(response n (endpoint n)-response n (endpoint n+1)) ≈
      Q'.ofNat (k n)*half := by
  have hstep : response n (endpoint n)-response n (endpoint n+1) ≈
      response n (endpoint n)*(1-rate n) := by
    unfold response
    rw [Q'.pow_succ]
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.mul (.var 2) (.var 1)))))
      (.mul (.mul (.var 0) (.var 1)) (.add (.const 1) (.neg (.var 2))))
      (by decide) (fun | 0 => amplitude n | 1 => (rate n)^(endpoint n) | _ => rate n)
  have hunit : response n (endpoint n)*(1-rate n) ≈ 1-rate n :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (1-rate n) (response_endpoint n))
      (Q'.one_mul_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (endpoint n)) _ _ (Q'.eqv_trans _ _ _ hstep hunit))
    (endpoint_rate_loss n)

/-- This explicit index defeats every proposed natural endpoint coefficient. -/
theorem endpoint_bound_fails (C : Nat) :
    Q'.ofNat C * response (2*C+1) (endpoint (2*C+1)) <
      Q'.ofNat (endpoint (2*C+1)) *
        (response (2*C+1) (endpoint (2*C+1)) -
          response (2*C+1) (endpoint (2*C+1)+1)) := by
  have hstrict : Q'.ofNat C < Q'.ofNat (k (2*C+1))*half := by
    change (C : Int)*2 < (((2*C+1+1 : Nat) : Int)*1)*1
    simp only [Int.natCast_add, Int.natCast_mul, Int.mul_one]
    omega
  have hleft : Q'.ofNat C * response (2*C+1) (endpoint (2*C+1)) ≈ Q'.ofNat C :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (response_endpoint (2*C+1))) (Q'.mul_one_eqv _)
  exact Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft)
    (ClusteringImpliesGap.lt_of_lt_of_le hstrict (Q'.ge_of_eqv (scaled_loss_pin (2*C+1))))

/-- A computed failing datum, retaining the index and all scalar premises.
There is no BF4 realization or physical source asserted by this witness. -/
def failingDatum (C : Nat) :
    Σ' n : Nat,
      0 < endpoint n ∧ ((0 : Q') < rate n ∧ rate n < 1) ∧
      ((0 : Q') < amplitude n) ∧ response n 0 ≤ Q'.ofNat (endpoint n) ∧
      response n (endpoint n) ≈ 1 ∧
      (∀ t l, (0 : Q') ≤ moment n t l) ∧
      (∀ t l, moment n (t+1) l + moment n t (l+1) ≈ moment n t l) ∧
      Q'.ofNat C * response n (endpoint n) <
        Q'.ofNat (endpoint n)*(response n (endpoint n)-response n (endpoint n+1)) :=
  ⟨2*C+1, endpoint_positive _, rate_bounds _, amplitude_positive _,
    response_zero_le_endpoint _, response_endpoint _, moment_nonnegative _,
    moment_split _, endpoint_bound_fails C⟩

end PolynomialUV

end YMGap.Continuum.BackwardResponseAreaStrictness

#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.moment_nonnegative
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.finite_area_input
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.earliest_point_survival_fails
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.finite_H1
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.pure_fast_H1_fails
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.EndpointVsArea.moment_nonnegative
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.EndpointVsArea.finite_endpoint_H1
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.EndpointVsArea.finite_area_ceiling_fails
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.EndpointVsArea.endpoint_without_area
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.rate_bounds
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.endpoint_power_floor
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.amplitude
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.response
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.moment
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.amplitude_positive
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.amplitude_le_block
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.endpoint_positive
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.response_zero_le_endpoint
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.response_endpoint
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.response_positive
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.moment_nonnegative
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.moment_response
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.moment_split
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.scaled_loss_pin
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.endpoint_bound_fails
#print axioms YMGap.Continuum.BackwardResponseAreaStrictness.PolynomialUV.failingDatum
