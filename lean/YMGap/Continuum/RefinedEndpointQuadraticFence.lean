/-
`RefinedEndpointQuadraticFence` — the refined retune does not make the
fixed-cutoff endpoint-tail variation second order.

At cutoff `N=1`, the finite-character eigenvalue has the exact quotient
`2w^3/(1+4w^6)` and lies in `[2/5,1/2]` on the endpoint neighborhood
`3/4 <= w <= 1`.  A closed rational instance then refutes the deliberately
generous quadratic coefficient `C=10^6` at `w=1-10^-7` by full kernel
computation.

The exact counterexample proves that the second-order correction
`7/24*(1-w)^2` does not by itself make the fixed-cutoff endpoint-subtracted
defect quadratic with that constant.  The module does not infer a lower bound
for the moving-cutoff physical defect.

Consequently an endpoint Taylor route paired with an AF margin of harmonic
order cannot yield a summable defect.  The final theorem reuses the proved
harmonic divergence engine for this exact linear lower scale.  This is a
fence around that route, not a lower bound on the moving-cutoff physical
defect.
-/

import YMGap.Continuum.EndpointCutoffTwoParameter

namespace YMGap.Continuum.RefinedEndpointQuadraticFence

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.EpsilonSummability
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private def q14 : Q' := Q'.mkPos 1 4 (by decide)
private def q12 : Q' := Q'.mkPos 1 2 (by decide)
private def q25 : Q' := Q'.mkPos 2 5 (by decide)
private def q34 : Q' := Q'.mkPos 3 4 (by decide)

private def prodFenceLHS : RingNormaliser.PolyExpr :=
  .mul (.add (.mul (.const 2) (.var 0)) (.neg (.const 1)))
    (.add (.const 2) (.neg (.var 0)))

private def prodFenceRHS : RingNormaliser.PolyExpr :=
  .add (.mul (.const 5) (.var 0))
    (.neg (.mul (.const 2) (.add (.const 1) (.mul (.var 0) (.var 0)))))

private theorem prodFence_normal :
    RingNormaliser.normalize prodFenceLHS = RingNormaliser.normalize prodFenceRHS := by decide

private theorem prodFence_identity (x : Q') :
    (Q'.ofNat 2 * x - 1) * (Q'.ofNat 2 - x) ≈
      Q'.ofNat 5 * x - Q'.ofNat 2 * ((1 : Q') + x * x) := by
  have h := RingNormaliser.poly_identity_of_normal_eq prodFenceLHS prodFenceRHS
    prodFence_normal (fun _ => x)
  simpa [RingNormaliser.eval, prodFenceLHS, prodFenceRHS] using h

/-- Closed form of the cutoff-one adjacent correlation. -/
theorem adjCorr_one (w : Q') :
    adjCorr w 1 ≈ Q'.ofNat 2 * qpow w 3 := by
  unfold adjCorr
  change (0 : Q') + coeffW w 0 * coeffW w 1 ≈ _
  rw [coeffW_zero]
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact Q'.one_mul_eqv _

/-- Closed form of the cutoff-one diagonal norm. -/
theorem coordNormSq_one (w : Q') :
    coordNormSq w 1 ≈
      (1 : Q') + (Q'.ofNat 2 * qpow w 3) * (Q'.ofNat 2 * qpow w 3) := by
  unfold coordNormSq
  change ((0 : Q') + coeffW w 0 * coeffW w 0) +
    coeffW w 1 * coeffW w 1 ≈ _
  rw [coeffW_zero]
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact Q'.one_mul_eqv 1

/-- At cutoff one the fundamental vacuum-normalized eigenvalue is at most
`1/2`; cross multiplication reduces to the square `(2w^3-1)^2 >= 0`. -/
theorem vacNorm_one_le_half {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    vacNorm 1 2 (by decide) hw0 hw1 1 ≤ q12 := by
  have hv := vacNorm_fundamental_eq_ratio hw0 hw1 1
  have hD := coordNormSq_ge_one hw0 1
  let x := Q'.ofNat 2 * qpow w 3
  have hx0 : (0 : Q') ≤ x :=
    Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw0 3)
  have hcross : x ≤ q12 * ((1 : Q') + x * x) := by
    have ham : x * (1 : Q') + x * (1 : Q') ≤
        x * x + (1 : Q') * (1 : Q') := amgm_two x 1
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ q12 ham (by decide)
    have hL : q12 * (x * (1 : Q') + x * (1 : Q')) ≈ x := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left q12 _ _
          (Q'.add_eqv_congr' (Q'.mul_one_eqv x) (Q'.mul_one_eqv x))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv q12 x x) ?_
      have hh : q12 + q12 ≈ (1 : Q') := by decide
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv q12 q12 x)) ?_
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x hh)
        (Q'.one_mul_eqv x)
    have hR : q12 * (x * x + (1 : Q') * (1 : Q')) ≈
        q12 * ((1 : Q') + x * x) := by
      refine Q'.mul_eqv_congr_left q12 _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (x * x) _ _ (Q'.one_mul_eqv 1)) ?_
      exact Q'.add_comm_eqv (x * x) 1
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hR))
  have hratio :
      Q'.divPos (adjCorr w 1) (coordNormSq w 1)
          (FusedRatioCorridor.pos_of_one_le hD) ≤ q12 := by
    refine Q'.divPos_le_of_le_mul _ _ _ ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (adjCorr_one w))
      (Q'.le_trans' _ _ _ hcross
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left q12 _ _
          (Q'.eqv_symm (coordNormSq_one w)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hv) hratio

/-- On `w >= 3/4`, the cutoff-one eigenvalue is at least its endpoint value
`2/5`. -/
theorem q25_le_vacNorm_one {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwlo : q34 ≤ w) :
    q25 ≤ vacNorm 1 2 (by decide) hw0 hw1 1 := by
  have hv := vacNorm_fundamental_eq_ratio hw0 hw1 1
  have hD := coordNormSq_ge_one hw0 1
  let x := Q'.ofNat 2 * qpow w 3
  have hx0 : (0 : Q') ≤ x :=
    Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw0 3)
  have hxlo : q12 ≤ x := by
    have hp : qpow q34 3 ≤ qpow w 3 := qpow_mono (by decide) hwlo 3
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hp (by decide)
    exact Q'.le_trans' _ _ _ (by decide : q12 ≤ Q'.ofNat 2 * qpow q34 3) hs
  have hxhi : x ≤ Q'.ofNat 2 := by
    have hp : qpow w 3 ≤ (1 : Q') := qpow_le_one hw0 hw1 3
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hp (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat 2)))
  have hleft : (0 : Q') ≤ Q'.ofNat 2 * x - (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hxlo (by decide)
    have h1 : (1 : Q') ≤ Q'.ofNat 2 * x :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (by decide : Q'.ofNat 2 * q12 ≈ (1 : Q'))) h
    exact Q'.sub_nonneg_of_le h1
  have hright : (0 : Q') ≤ Q'.ofNat 2 - x := Q'.sub_nonneg_of_le hxhi
  have hprod : (0 : Q') ≤
      (Q'.ofNat 2 * x - 1) * (Q'.ofNat 2 - x) :=
    Q'.mul_nonneg _ _ hleft hright
  have hraw : Q'.ofNat 2 * ((1 : Q') + x * x) ≤ Q'.ofNat 5 * x := by
    have he : (Q'.ofNat 2 * x - 1) * (Q'.ofNat 2 - x) ≈
        Q'.ofNat 5 * x - Q'.ofNat 2 * ((1 : Q') + x * x) := by
      exact prodFence_identity x
    have hdiff : (0 : Q') ≤
        Q'.ofNat 5 * x - Q'.ofNat 2 * ((1 : Q') + x * x) :=
      Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv he)
    exact Q'.le_of_sub_nonneg hdiff
  have hcross : q25 * ((1 : Q') + x * x) ≤ x := by
    let fifth := Q'.mkPos 1 5 (by decide)
    have hs := Q'.mul_le_mul_of_nonneg_right _ _ fifth hraw (by decide)
    have hL : (Q'.ofNat 2 * ((1 : Q') + x * x)) * fifth ≈
        q25 * ((1 : Q') + x * x) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (Q'.ofNat 2) ((1 : Q') + x * x) fifth) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_comm_eqv ((1 : Q') + x * x) fifth)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) fifth
          ((1 : Q') + x * x))) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (by decide : Q'.ofNat 2 * fifth ≈ q25)
    have hR : (Q'.ofNat 5 * x) * fifth ≈ x := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (Q'.ofNat 5) x fifth) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 5) _ _
          (Q'.mul_comm_eqv x fifth)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 5) fifth x)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x
          (by decide : Q'.ofNat 5 * fifth ≈ (1 : Q'))) ?_
      exact Q'.one_mul_eqv x
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hR))
  have hratio : q25 ≤
      Q'.divPos (adjCorr w 1) (coordNormSq w 1)
        (FusedRatioCorridor.pos_of_one_le hD) := by
    refine Q'.le_divPos_of_mul_le _ _ _ ?_
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left q25 _ _ (coordNormSq_one w)))
      (Q'.le_trans' _ _ _ hcross (Q'.le_of_eqv (Q'.eqv_symm (adjCorr_one w))))
  exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv (Q'.eqv_symm hv))

/-! ## Closed machine fence for the quadratic endpoint candidate -/

/-- A weight ten-millionth away from the endpoint. -/
def fenceW : Q' := Q'.mkPos 9999999 10000000 (by decide)

/-- A deliberately generous proposed quadratic coefficient. -/
def fenceC : Q' := Q'.ofNat 1000000

/-- **Exact refutation of the refined quadratic endpoint-tail candidate.**
Even the coefficient one million does not bound the endpoint-subtracted
refined defect by `C(1-w)^2` at cutoff one.  All quantities are closed exact
rationals; `decide` checks the full finite character quotient and refined
retune in the kernel. -/
theorem refined_endpoint_quadratic_million_refuted :
    ¬ (absQ
        (normEigShift2 1 2 (by decide)
            (by decide : (0 : Q') ≤ fenceW)
            (by decide : fenceW ≤ (1 : Q'))
            (refineCoeff 2 (by decide)) 1 - endpointTail 1)
      ≤ fenceC * (((1 : Q') - fenceW) * ((1 : Q') - fenceW))) := by
  decide

/-- Therefore the proposed coefficient cannot hold uniformly on `[0,1]` at
even the first nonzero finite cutoff. -/
theorem no_uniform_refined_endpoint_quadratic_million :
    ¬ (∀ (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')),
      absQ
          (normEigShift2 1 2 (by decide) hw0 hw1
              (refineCoeff 2 (by decide)) 1 - endpointTail 1)
        ≤ fenceC * (((1 : Q') - w) * ((1 : Q') - w))) := by
  intro h
  exact refined_endpoint_quadratic_million_refuted
    (h fenceW (by decide) (by decide))

/-- The linear scale exposed by the endpoint fence is harmonic along every
AF reciprocal-rate schedule, hence has unbounded partial sums.  This is the
schedule diagnostic: an actual moving-cutoff proof must produce cancellation
beyond endpoint Taylor continuity. -/
theorem endpoint_linear_scale_partial_unbounded
    (afr : AFRateModulus) (R : Q') :
    ∃ M : Nat, R < fsum (fun k => harmTerm afr.B afr.B_pos k) M := by
  refine harmonicLower_partial_unbounded afr (1 : Q') (by decide)
    (fun k => harmTerm afr.B afr.B_pos k) ?_ R
  intro k
  exact Q'.le_of_eqv (Q'.one_mul_eqv (harmTerm afr.B afr.B_pos k))

end YMGap.Continuum.RefinedEndpointQuadraticFence

#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.adjCorr_one
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.coordNormSq_one
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.vacNorm_one_le_half
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.q25_le_vacNorm_one
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.refined_endpoint_quadratic_million_refuted
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.no_uniform_refined_endpoint_quadratic_million
#print axioms YMGap.Continuum.RefinedEndpointQuadraticFence.endpoint_linear_scale_partial_unbounded
