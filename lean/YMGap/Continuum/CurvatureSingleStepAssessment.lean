/-
# Scope of the free-curvature identities and the SZZ scalar bound

Scope correction, 2026-09-27: the earlier commentary overstated what these
declarations prove. Their statements and proofs are unchanged.

The checked core consists of the free Casimir anchor, the exact rational
counterterm/residual factorization, and sample values of the scalar
szzCurvature(beta)=1-48*beta. It does not calculate the actual interacting
Hessian or establish its sign, prove a general no-go theorem for curvature
methods, or identify a renormalon obstruction.

In Shen--Zhu--Zhu, arXiv:2204.12737, Assumption 1.1, Lemma 4.1 and (4.7),
K_S is a LOWER BOUND on Ric-Hess S. For SU(2), d=4 and nonnegative beta,
that displayed coefficient is 1-48*beta. When it is negative, this bound
does not certify positive curvature; negativity of the bound does NOT
imply negativity of the actual curvature or failure of a sharper argument.
The primary paper concerns Wilson-action Langevin dynamics. No equality
with the current full-action conditional sweep is proved in this module.

There is no theorem here asserting that every useful curvature estimate
is analytic in g^2, that it must be polynomial, or that all multiscale or
renormalized curvature methods are excluded by dimensional transmutation.
Those older prose claims are withdrawn, not promoted to hypotheses.

The historical theorem name curvature_route_verdict is retained for API
compatibility. Its conclusion is only the displayed conjunction of the
free anchor, rational factorization and one negative scalar sample.
Neither SingleStepDefectBound nor UniformCurvatureBound is inhabited or
refuted here. The same-theory physical and continuum Clay target remains
open. See audits/AUDIT-CURVATURE-LOWER-BOUND-SCOPE-2026-09-27.md.

Axiom gate: only the already recorded propext / Quot.sound dependencies;
no declaration statement, proof body or canonical field is changed.
-/

import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Continuum.HeatKernelCurvature
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.CurvatureSingleStepAssessment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.HeatKernelCurvature

/-- Existing free diagonal/Casimir facts; no interacting curvature claim. -/
theorem free_curvature_anchor_bundled :
    (0 : Q') < casimirGap
    ∧ DiagCD freeDiag casimirGap
    ∧ (c4 1 = 3 ∧ (Q'.ofNat 4 * casimirGap).eqv (Q'.ofNat (c4 1))) :=
  ⟨casimirGap_pos, free_DiagCD, c4_one_eq_four_casimirGap⟩

/-- Exact rational factorization of the model residual. -/
theorem bondMovingDeltaRen_one_factor (N : Nat) (w : Q') :
    (bondMovingDeltaRen N 1 w).eqv
      (dimQ 1 * ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))) := by
  -- δ_ren(N,1,w) = ofNat 1 · (dimQ 1 · bracket),  bracket = C₄(1)(1−w) − (1 − w^{C₄(1)}).
  show (Q'.ofNat 1 * (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))).eqv _
  -- strip the ofNat 1 factor
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 _ (by decide))
      (Q'.one_mul_eqv _)) ?_
  -- inner bracket ≃ (1−w)²·(2+w)  by renDefect_factor (c4 1 = 3 definitionally)
  exact Q'.mul_eqv_congr_left (dimQ 1) _ _ (renDefect_factor w)

/-- The displayed factorization and Casimir identity, not a no-go theorem. -/
theorem curvature_lands_on_marginal_not_residual (w : Q') :
    ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))
    ∧ (Q'.ofNat 4 * casimirGap).eqv (Q'.ofNat (c4 1)) :=
  ⟨renDefect_factor w, c4_one_eq_four_casimirGap.2⟩

/-- Nonnegativity and vanishing of the model residual at w=1. -/
theorem residual_second_order_at_free_end (N p : Nat) :
    bondMovingDeltaRen N p 1 ≤ 0 ∧ (0 : Q') ≤ bondMovingDeltaRen N p 1 :=
  ⟨SingleStepDefectReduction.freeEnd_defect_scaleExact N p,
    SingleStepDefectReduction.freeEnd_defect_nonneg N p⟩

/-- Scalar specialization of the cited lower-bound coefficient for beta>=0.
No actual curvature tensor is defined by this abbreviation. -/
def szzCurvature (beta : Q') : Q' := (1 : Q') - Q'.ofNat 48 * beta

/-- The scalar coefficient vanishes at beta=1/48. -/
theorem szz_curvature_zero_at_threshold :
    (szzCurvature (Q'.mkPos 1 48 (by decide))).eqv 0 := by decide

/-- Historical name: proves ONLY szzCurvature(1)<0, not actual curvature negativity. -/
theorem szz_interacting_curvature_goes_negative :
    szzCurvature 1 < 0 := by decide

/-- Positive sample of the scalar coefficient at beta=1/100. -/
theorem szz_curvature_pos_strong_coupling :
    (0 : Q') < szzCurvature (Q'.mkPos 1 100 (by decide)) := by decide

/-- Historical name: bundles the free anchor, factorization and negative
scalar sample. It refutes no interacting or continuum frontier bundle. -/
theorem curvature_route_verdict :
    ((0 : Q') < casimirGap ∧ DiagCD freeDiag casimirGap)
    ∧ (∀ w : Q', (bondMovingDeltaRen 1 1 w).eqv
        (dimQ 1 * ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))))
    ∧ szzCurvature 1 < 0 :=
  ⟨⟨casimirGap_pos, free_DiagCD⟩,
    fun w => bondMovingDeltaRen_one_factor 1 w,
    szz_interacting_curvature_goes_negative⟩

end YMGap.Continuum.CurvatureSingleStepAssessment

#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.free_curvature_anchor_bundled
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.bondMovingDeltaRen_one_factor
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.curvature_lands_on_marginal_not_residual
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.residual_second_order_at_free_end
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_curvature_zero_at_threshold
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_interacting_curvature_goes_negative
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_curvature_pos_strong_coupling
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.curvature_route_verdict
