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
-/

import YMGap.Constructive.Geometric
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.RingNormaliser

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
