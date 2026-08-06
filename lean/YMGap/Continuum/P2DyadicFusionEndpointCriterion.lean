/-
Track 11.7-fusion / R2w -- endpoint criterion for the dyadic monotonicity tail.

The raw tail left by `P2DyadicFusionMonotonicityAudit` compares two large
finite fusion quotients.  The fundamental quotient already has a proved
finite-character continuity theorem around the exact endpoint rate

    endpointRate N = 2*N/(2*N+3).

This file applies a generic two-Lipschitz square argument.  It is enough that
the closed endpoint-rate separation pays the coarse continuity error and
twice the fine continuity error.  The remaining tail is therefore an
explicit scalar inequality over `endpointRate`, `vacLip`, and the dyadic
margin, with no fusion convolution or quotient comparison.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionMonotonicityAudit
import YMGap.Continuum.EndpointCutoffTwoParameter

namespace YMGap.Continuum.P2DyadicFusionEndpointCriterion

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2DyadicFusionMonotonicityAudit
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- The raw mode-one eigenvalue, stripped of all control proof fields. -/
def rawDyadicModeOne (k : Nat) : Q' :=
  p2VacNorm (Ncut k) (dyadicWeight_nonneg k) (dyadicWeight_le_one k) 1

/-- Explicit finite-character endpoint-continuity error. -/
def dyadicEndpointError (k : Nat) : Q' :=
  vacLip (Ncut k) * dyadicMargin k

theorem rawDyadicModeOne_range (k : Nat) :
    ((0 : Q') <= rawDyadicModeOne k) /\
      (rawDyadicModeOne k <= (1 : Q')) := by
  have h0 := p2VacNorm_nonneg (Ncut k)
    (dyadicWeight_nonneg k) (dyadicWeight_le_one k) 1
  have hret := p2VacNorm_one_le_retuned (Ncut k)
    (dyadicWeight_nonneg k) (dyadicWeight_le_one k)
  have hret1 :
      qpow (p2RetunedWeight (dyadicWeight k)) (c4 1) <= (1 : Q') :=
    qpow_le_one
      (p2RetunedWeight_nonneg (dyadicWeight_nonneg k))
      (p2RetunedWeight_le_one (dyadicWeight_le_one k)) (c4 1)
  exact ⟨h0, Q'.le_trans' _ _ _ hret hret1⟩

/-- The existing finite-character continuity theorem on the exact dyadic
schedule. -/
theorem rawDyadicModeOne_endpoint_error (k : Nat) :
    absQ (rawDyadicModeOne k + -(endpointRate (Ncut k))) <=
      dyadicEndpointError k := by
  have h := vacNorm_fundamental_endpoint_continuity
    (dyadicWeight_nonneg k) (dyadicWeight_le_one k) (Ncut k)
  have hmargin :
      vacLip (Ncut k) * ((1 : Q') - dyadicWeight k) ≈
        dyadicEndpointError k :=
    Q'.mul_eqv_congr_left (vacLip (Ncut k)) _ _
      (one_sub_dyadicWeight_eqv_margin k)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hmargin)

/-- The strict-fold square is semantically the ordinary product square. -/
theorem qpow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  show ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

/-- Generic endpoint-error compiler.  The reference square separation pays
one coarse error and twice the fine error. -/
theorem coarse_le_fine_square_of_reference_budget
    {coarse fine refCoarse refFine coarseError fineError : Q'}
    (hfine0 : (0 : Q') <= fine) (hfine1 : fine <= (1 : Q'))
    (hrefFine0 : (0 : Q') <= refFine)
    (hrefFine1 : refFine <= (1 : Q'))
    (hcoarseError : absQ (coarse + -refCoarse) <= coarseError)
    (hfineError : absQ (fine + -refFine) <= fineError)
    (hbudget :
      refCoarse + (coarseError + Q'.ofNat 2 * fineError) <=
        refFine * refFine) :
    coarse <= fine * fine := by
  have hcoarse : coarse + -refCoarse <= coarseError :=
    Q'.le_trans' _ _ _ (le_absQ (coarse + -refCoarse)) hcoarseError
  have hfineError' : absQ (refFine + -fine) <= fineError :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (absQ_sub_comm_eqv fine refFine)) hfineError
  have hfineSquare :
      refFine * refFine + -(fine * fine) <= Q'.ofNat 2 * fineError :=
    square_sub_square_le_two_abs hrefFine0 hrefFine1 hfine0 hfine1
      hfineError'
  have hgap : coarse + -(fine * fine) <=
      (refCoarse + -(refFine * refFine)) +
        (coarseError + Q'.ofNat 2 * fineError) :=
    gap_le_reference_gap_add_errors hcoarse hfineSquare
  have hbudgetSub :
      (refCoarse + (coarseError + Q'.ofNat 2 * fineError)) +
          -(refFine * refFine) <= (0 : Q') := by
    have h := Q'.add_le_add_right _ _ (-(refFine * refFine)) hbudget
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_neg_self_eqv (refFine * refFine)))
  have hregroup :
      (refCoarse + -(refFine * refFine)) +
          (coarseError + Q'.ofNat 2 * fineError) ≈
        (refCoarse + (coarseError + Q'.ofNat 2 * fineError)) +
          -(refFine * refFine) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv refCoarse (-(refFine * refFine))
        (coarseError + Q'.ofNat 2 * fineError)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left refCoarse _ _
        (Q'.add_comm_eqv (-(refFine * refFine))
          (coarseError + Q'.ofNat 2 * fineError))) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv refCoarse
        (coarseError + Q'.ofNat 2 * fineError) (-(refFine * refFine)))
  have hsub : coarse + -(fine * fine) <= (0 : Q') :=
    Q'.le_trans' _ _ _ hgap
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hbudgetSub)
  have hadd := Q'.add_le_add_right _ _ (fine * fine) hsub
  have hlhs :
      (coarse + -(fine * fine)) + fine * fine ≈ coarse := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv (coarse + -(fine * fine)) (fine * fine)) ?_
    exact Q'.eqv_symm (Q'.add_sub_cancel_eqv coarse (fine * fine))
  have hrhs : (0 : Q') + fine * fine ≈ fine * fine := by
    rw [Q'.zero_add']
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hlhs)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hrhs))

/-- The endpoint rates themselves lie in `[0,1]`. -/
theorem endpointRate_range (N : Nat) :
    ((0 : Q') <= endpointRate N) /\ (endpointRate N <= (1 : Q')) := by
  constructor
  · unfold endpointRate
    exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
      (Q'.le_of_lt (Q'.recipPos_pos _ (endpointDen_pos N)))
  · have hnum : Q'.ofNat (2 * N) <= Q'.ofNat (2 * N + 3) :=
      Q'.ofNat_le_ofNat (by omega)
    apply Q'.divPos_le_of_le_mul _ _ (endpointDen_pos N)
    exact Q'.le_trans' _ _ _ hnum
      (Q'.ge_of_eqv (Q'.one_mul_eqv (Q'.ofNat (2 * N + 3))))

/-- Scalar proof-about-computation tail.  Unlike the original fusion
inequality, this contains only explicit endpoint fractions and finite
character Lipschitz constants. -/
structure DyadicP2EndpointMonotonicityTail : Type where
  budget : forall k, 2 <= k ->
    endpointRate (Ncut k) +
        (dyadicEndpointError k + Q'.ofNat 2 * dyadicEndpointError (k + 1)) <=
      endpointRate (Ncut (k + 1)) * endpointRate (Ncut (k + 1))

/-- The scalar endpoint budget discharges the raw fusion-quotient tail. -/
def DyadicP2EndpointMonotonicityTail.toModeOneTailMonotonicity
    (E : DyadicP2EndpointMonotonicityTail) :
    DyadicP2ModeOneTailMonotonicity where
  tail := fun k hk => by
    have hfine := rawDyadicModeOne_range (k + 1)
    have hrefFine := endpointRate_range (Ncut (k + 1))
    have hsquare := coarse_le_fine_square_of_reference_budget
      hfine.1 hfine.2 hrefFine.1 hrefFine.2
      (rawDyadicModeOne_endpoint_error k)
      (rawDyadicModeOne_endpoint_error (k + 1)) (E.budget k hk)
    exact Q'.le_trans' _ _ _ hsquare
      (Q'.ge_of_eqv (qpow_two_eqv (rawDyadicModeOne (k + 1))))

/-- Hence the endpoint-only scalar tail reaches the complete physical
monotonicity input, including the two exact head cells and cutoff cap. -/
def DyadicP2EndpointMonotonicityTail.toPhysicalMonotoneInput
    (E : DyadicP2EndpointMonotonicityTail)
    {D : P2DyadicFusionGapEnvelope.DyadicP2CoeffTailData}
    {R : P2DyadicFusionGapBudget.DyadicP2RefinedCutoffData D}
    {B : BlockingStepFrontier.BlockingStep
      (P2RetunedBlockingDictionary.fusionSeparator D.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne)}
    (hCq : R.Cq <= P2DyadicFusionHalfFloor.cutoffCoeffCap) :
    P2DyadicFusionHalfFloor.DyadicP2PhysicalMonotoneInput D R B :=
  E.toModeOneTailMonotonicity.toPhysicalMonotoneInput hCq

end YMGap.Continuum.P2DyadicFusionEndpointCriterion

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicFusionEndpointCriterion.rawDyadicModeOne_endpoint_error
#print axioms YMGap.Continuum.P2DyadicFusionEndpointCriterion.coarse_le_fine_square_of_reference_budget
#print axioms YMGap.Continuum.P2DyadicFusionEndpointCriterion.endpointRate_range
#print axioms YMGap.Continuum.P2DyadicFusionEndpointCriterion.DyadicP2EndpointMonotonicityTail.toModeOneTailMonotonicity
#print axioms YMGap.Continuum.P2DyadicFusionEndpointCriterion.DyadicP2EndpointMonotonicityTail.toPhysicalMonotoneInput
