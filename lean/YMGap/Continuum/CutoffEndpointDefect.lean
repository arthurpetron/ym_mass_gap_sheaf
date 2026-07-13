/-
Exact finite-cutoff endpoint audit for the `p=2` refined Edgeworth route.

At `w=1`, every `(1-w)^2` retune correction vanishes and `retEig2=1`,
independently of its coefficient.  The actual finite character sum at pilot
cutoff `N=3`, however, gives `vacNorm(1)=2/3`; hence both the original and
refined spectral defects are exactly `1/3`.

This proves that a uniform fixed-cutoff bound of the advertised pure shape

  normEigShift2 <= Cq * (1-w)^2

cannot hold on the closed interval `0 <= w <= 1`.  In particular, the current
`RefinedBulkRemainderQuadratic` and `RefinedFactorization` carriers are
uninhabited at `N=3,p=2,w=1`.  The corrected local-CLT statement must expose a
finite-cutoff tail (which vanishes only as `N -> infinity`) or quantify a
coupled moving cutoff `N(w) -> infinity`; adjusting the second-order retune
coefficient cannot repair the boundary term.

All values are derived by kernel reduction of the exact finite SU(2)
character sums.  No numerical estimate, classical axiom, or frontier carrier
is used or inhabited.
-/

import YMGap.Continuum.RefinedQuadraticClose

namespace YMGap.Continuum.CutoffEndpointDefect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RefinedQuadraticClose

local infix:50 " ≈ " => Q'.eqv

def q13 : Q' := Q'.mkPos 1 3 (by decide)
def q23 : Q' := Q'.mkPos 2 3 (by decide)

/-- Every natural power of the rational endpoint `1` is equivalent to `1`. -/
theorem qpow_endpoint_one : ∀ n : Nat, (qpow (1 : Q') n) ≈ (1 : Q')
  | 0 => Q'.eqv_refl 1
  | n + 1 =>
      Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (qpow (1 : Q') n))
        (qpow_endpoint_one n)

/-- The second-order correction is identically one at `w=1`, for every
coefficient `a`; the margin it multiplies has vanished. -/
theorem corrFactor_endpoint (a : Q') :
    corrFactor a (1 : Q') ≈ (1 : Q') := by
  unfold corrFactor
  have hs : ((1 : Q') - (1 : Q')) ≈ (0 : Q') := Q'.add_neg_self_eqv 1
  have hsq : (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q'))) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ ((1 : Q') - (1 : Q')) hs) ?_
    exact Q'.zero_mul_eqv _
  have ha0 : (a * (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q')))) ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ hsq) (Q'.mul_zero_eqv a)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ ha0)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))

/-- At the endpoint the refined retuned eigenvalue is `1`, independently
of the correction coefficient. -/
theorem retEig2_endpoint (p : Nat) (hp : 0 < p) (a : Q') (s : Nat) :
    retEig2 p hp a (1 : Q') s ≈ (1 : Q') := by
  unfold retEig2 renormW2 renormWFix renormTauFix
  have hs : ((1 : Q') - (1 : Q')) ≈ (0 : Q') := Q'.add_neg_self_eqv 1
  have htau : (((1 : Q') - (1 : Q')) * Q'.mkPos 1 p hp) ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.mkPos 1 p hp) hs)
      (Q'.zero_mul_eqv _)
  have hwfix : ((1 : Q') + -(((1 : Q') - (1 : Q')) * Q'.mkPos 1 p hp)) ≈
      (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ htau)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))
  have hbase :
      (((1 : Q') + -(((1 : Q') - (1 : Q')) * Q'.mkPos 1 p hp)) *
        corrFactor a (1 : Q')) ≈ (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (corrFactor a (1 : Q')) hwfix) ?_
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (corrFactor_endpoint a)
  exact Q'.eqv_trans _ _ _ (qpow_eqv_congr_base hbase (c4 s))
    (qpow_endpoint_one (c4 s))

private theorem absQ_eqv_abs_local (x : Q') : (absQ x) ≈ (Q'.abs x) := by
  unfold absQ Q'.abs
  by_cases hx : (0 : Int) ≤ x.num
  · rw [if_pos hx]
    have hx' : (0 : Q') ≤ x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_pos hx']
    exact Q'.eqv_refl x
  · rw [if_neg hx]
    have hx' : ¬ (0 : Q') ≤ x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_neg hx']
    exact Q'.eqv_refl (-x)

private theorem absQ_eqv_congr_local {x y : Q'} (h : x ≈ y) :
    absQ x ≈ absQ y :=
  Q'.eqv_trans _ _ _ (absQ_eqv_abs_local x)
    (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr h)
      (Q'.eqv_symm (absQ_eqv_abs_local y)))

/-- At fixed cutoff `N = 3`, the vacuum-normalized fundamental fused
eigenvalue has the exact endpoint value `2/3`, not `1`. -/
theorem vacNorm_endpoint_N3 :
    (vacNorm 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) 1) ≈ q23 := by
  decide

/-- Consequently the actual, unrefined `p=2` spectral defect at the
finite-cutoff endpoint is exactly `1/3`. -/
theorem endpoint_defect_N3 :
    (normEigShift 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) 1) ≈ q13 := by
  decide

theorem refined_endpoint_defect_N3 :
    (normEigShift2 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) (refineCoeff 2 (by decide)) 1) ≈ q13 := by
  decide

/-- The exact refined endpoint defect is `1/3` for *every* correction
coefficient, not merely the formal `7/24`: a Casimir-shaped correction
proportional to `(1-w)^2` cannot remove a finite-cutoff boundary error. -/
theorem refined_endpoint_defect_N3_anyCoeff (a : Q') :
    (normEigShift2 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
      (by decide : (1 : Q') ≤ (1 : Q')) a 1) ≈ q13 := by
  unfold normEigShift2
  have harg :
      (vacNorm 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
          (by decide : (1 : Q') ≤ (1 : Q')) 1 + -(retEig2 2 (by decide) a 1 1)) ≈
        (vacNorm 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
          (by decide : (1 : Q') ≤ (1 : Q')) 1 + -(1 : Q')) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (retEig2_endpoint 2 (by decide) a 1))
  exact Q'.eqv_trans _ _ _ (absQ_eqv_congr_local harg) (by decide)

/-- No scalar constant can make the fixed-cutoff refined defect quadratic
at the closed endpoint: the right side is zero while the exact defect is
`1/3`. -/
theorem no_quadratic_endpoint_N3 (a C : Q') :
    ¬ (normEigShift2 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
        (by decide : (1 : Q') ≤ (1 : Q')) a 1
      ≤ C * (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q')))) := by
  intro h
  have hsub : ((1 : Q') - (1 : Q')) ≈ (0 : Q') :=
    Q'.add_neg_self_eqv (1 : Q')
  have hsq :
      (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q'))) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ ((1 : Q') - (1 : Q')) hsub) ?_
    exact Q'.zero_mul_eqv ((1 : Q') - (1 : Q'))
  have hz :
      (C * (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q')))) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left C _ _ hsq) ?_
    exact Q'.mul_zero_eqv C
  have hle0 :
      normEigShift2 3 2 (by decide) (by decide : (0 : Q') ≤ (1 : Q'))
          (by decide : (1 : Q') ≤ (1 : Q')) a 1
        ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv hz)
  have h13le0 : q13 ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (refined_endpoint_defect_N3_anyCoeff a)) hle0
  exact (by decide : ¬ (q13 ≤ (0 : Q'))) h13le0

/-- The existing uniform quadratic carrier is therefore uninhabited at
fixed cutoff `N=3`, `p=2`, `w=1` and the intended coefficient `7/24`.
Any valid Edgeworth theorem must carry a cutoff-tail term (or impose a
coupled `N(w) → ∞` regime); a pure `Cq(1-w)^2` bound cannot hold on the
closed interval at fixed `N`. -/
theorem refinedBulkRemainderQuadratic_endpoint_N3_uninhabited :
    RefinedBulkRemainderQuadratic 3 2 (by decide)
      (by decide : (0 : Q') ≤ (1 : Q')) (by decide : (1 : Q') ≤ (1 : Q'))
      (refineCoeff 2 (by decide)) → False := by
  intro rq
  exact no_quadratic_endpoint_N3 (refineCoeff 2 (by decide)) rq.Cq (rq.quad 1)

/-- The stronger multiplicative `RefinedFactorization` carrier is likewise
impossible at this fixed-cutoff endpoint, since it would construct the
refuted pure quadratic bound. -/
theorem refinedFactorization_endpoint_N3_uninhabited :
    RefinedFactorization 3 2 (by decide)
      (by decide : (0 : Q') ≤ (1 : Q')) (by decide : (1 : Q') ≤ (1 : Q'))
      (refineCoeff 2 (by decide)) → False := by
  intro fac
  exact refinedBulkRemainderQuadratic_endpoint_N3_uninhabited
    (refinedBulkRemainderQuadratic_of_factorization 3 2 (by decide)
      (by decide : (0 : Q') ≤ (1 : Q')) (by decide : (1 : Q') ≤ (1 : Q'))
      (refineCoeff 2 (by decide)) fac)

end YMGap.Continuum.CutoffEndpointDefect

#print axioms YMGap.Continuum.CutoffEndpointDefect.refined_endpoint_defect_N3
#print axioms YMGap.Continuum.CutoffEndpointDefect.qpow_endpoint_one
#print axioms YMGap.Continuum.CutoffEndpointDefect.corrFactor_endpoint
#print axioms YMGap.Continuum.CutoffEndpointDefect.retEig2_endpoint
#print axioms YMGap.Continuum.CutoffEndpointDefect.refined_endpoint_defect_N3_anyCoeff
#print axioms YMGap.Continuum.CutoffEndpointDefect.vacNorm_endpoint_N3
#print axioms YMGap.Continuum.CutoffEndpointDefect.endpoint_defect_N3
#print axioms YMGap.Continuum.CutoffEndpointDefect.no_quadratic_endpoint_N3
#print axioms YMGap.Continuum.CutoffEndpointDefect.refinedBulkRemainderQuadratic_endpoint_N3_uninhabited
#print axioms YMGap.Continuum.CutoffEndpointDefect.refinedFactorization_endpoint_N3_uninhabited
