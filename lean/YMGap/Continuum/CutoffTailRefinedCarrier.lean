/-
`CutoffTailRefinedCarrier` replaces the endpoint-inconsistent pure quadratic
`RefinedFactorization` interface by the honest finite-cutoff statement.

At cutoff `N`, the refined local-CLT error is allowed the exactly derived
endpoint tail `3/(2N+3)`.  The only analytic datum retained is therefore

  normEigShift2 <= Cq * (1-w)^2 + endpointTail N.

The p=2 range facts are theorems, not fields.  This file transports the bound
to the actual fused Peter--Weyl margin, proves that the corrected carrier is
inhabited at the endpoint for every cutoff, and lands the cutoff part on the
existing exact inverse-square window modulus at `Ncut(k)`.
-/

import YMGap.Continuum.FusedRefinedSpectralBridge
import YMGap.Continuum.EndpointCutoffTailClose
import YMGap.Continuum.NetDriftInvSqBudget

namespace YMGap.Continuum.CutoffTailRefinedCarrier

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.CutoffEndpointDefect
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedRefinedSpectralBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Honest one-field finite-cutoff carrier -/

/-- The corrected local-CLT carrier.  `Cq` is an explicit parameter and the
sole field is the analytic estimate.  The finite-cutoff endpoint tail is not
assumed: it is the derived rational `endpointTail N`. -/
structure CutoffTailRefinedBound (N : Nat) {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (Cq : Q') (s : Nat) : Type where
  quadratic_add_tail :
    normEigShift2 N 2 (by decide) hw0 hw1 (refineCoeff 2 (by decide)) s <=
      Cq * (((1 : Q') - w) * ((1 : Q') - w)) + endpointTail N

/-- The refined base range needed by transport is derived uniformly; it is
deliberately absent from `CutoffTailRefinedBound`. -/
theorem corrected_carrier_range {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (s : Nat) :
    ((0 : Q') <= retEig2 2 (by decide) (refineCoeff 2 (by decide)) w s) /\
      (retEig2 2 (by decide) (refineCoeff 2 (by decide)) w s <= (1 : Q')) :=
  retEig2_refineCoeff_p2_mem hw0 hw1 s

/-! ## 2. Sharp local triangle and transport -/

/-- Replacing `(1-w)^2` by any supplied upper square `r^2` costs no extra
constant; the derived cutoff tail is carried unchanged. -/
theorem defect_le_scaled_quadratic_add_tail
    (N : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {Cq r : Q'} (hCq : (0 : Q') <= Cq)
    (hr : (1 : Q') - w <= r) (s : Nat)
    (b : CutoffTailRefinedBound N hw0 hw1 Cq s) :
    normEigShift2 N 2 (by decide) hw0 hw1 (refineCoeff 2 (by decide)) s <=
      Cq * (r * r) + endpointTail N := by
  have hd0 : (0 : Q') <= (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hsq : ((1 : Q') - w) * ((1 : Q') - w) <= r * r :=
    BondMovingQuadratic.sq_le_sq hd0 hr
  have hmul :
      Cq * (((1 : Q') - w) * ((1 : Q') - w)) <= Cq * (r * r) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq hCq
  exact Q'.le_trans' _ _ _ b.quadratic_add_tail
    (Q'.add_le_add_right _ _ (endpointTail N) hmul)

/-- **Sharp cutoff-tail transport to the actual fused margin.**  A supplied
quadratic remainder and the derived finite-cutoff tail erode the refined
margin additively, with coefficient one on each term. -/
theorem fused_margin_after_quadratic_add_cutoff_tail
    (N k : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {Cq r : Q'} (hCq : (0 : Q') <= Cq)
    (hr : (1 : Q') - w <= r)
    (b : CutoffTailRefinedBound N hw0 hw1 Cq (k + 1)) :
    ((1 : Q') - retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1)) -
        (Cq * (r * r) + endpointTail N) <=
      (1 : Q') - lamPW w N (k + 1) := by
  have hshift := defect_le_scaled_quadratic_add_tail N hw0 hw1 hCq hr (k + 1) b
  have hneg : -(Cq * (r * r) + endpointTail N) <=
      -(normEigShift2 N 2 (by decide) hw0 hw1
        (refineCoeff 2 (by decide)) (k + 1)) :=
    Q'.neg_le_neg hshift
  have hbudget :
      ((1 : Q') - retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1)) -
          (Cq * (r * r) + endpointTail N) <=
        ((1 : Q') - retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1)) -
          normEigShift2 N 2 (by decide) hw0 hw1
            (refineCoeff 2 (by decide)) (k + 1) :=
    Q'.add_le_add_left _ _ _ hneg
  exact Q'.le_trans' _ _ _ hbudget
    (fused_margin_after_refined_erosion hw0 hw1 N k (refineCoeff 2 (by decide)))

/-! ## 3. Endpoint consistency and non-vacuity -/

private theorem absQ_eqv_abs_local (x : Q') : absQ x ≈ Q'.abs x := by
  unfold absQ Q'.abs
  by_cases hx : (0 : Int) <= x.num
  · rw [if_pos hx]
    have hx' : (0 : Q') <= x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_pos hx']
    exact Q'.eqv_refl _
  · rw [if_neg hx]
    have hx' : ¬ (0 : Q') <= x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_neg hx']
    exact Q'.eqv_refl _

private theorem absQ_eqv_congr_local {x y : Q'} (h : x ≈ y) : absQ x ≈ absQ y :=
  Q'.eqv_trans _ _ _ (absQ_eqv_abs_local x)
    (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr h)
      (Q'.eqv_symm (absQ_eqv_abs_local y)))

/-- At `w=1`, the refined defect in the fundamental channel is exactly the
derived cutoff tail, for every `N`; this is the endpoint term missing from the
old pure-quadratic statement. -/
theorem normEigShift2_endpoint_formula (N : Nat) :
    normEigShift2 N 2 (by decide) (by decide : (0 : Q') <= (1 : Q'))
        (by decide : (1 : Q') <= (1 : Q')) (refineCoeff 2 (by decide)) 1 ≈
      endpointTail N := by
  unfold normEigShift2
  have hret2 := retEig2_endpoint 2 (by decide) (refineCoeff 2 (by decide)) 1
  have hret := retEig2_endpoint 2 (by decide) 0 1
  have hret0 : retEig 2 (by decide) (1 : Q') 1 ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (retEig2_param_zero 2 (by decide) 1 1)) hret
  have hargs :
      vacNorm N 2 (by decide) (by decide : (0 : Q') <= (1 : Q'))
          (by decide : (1 : Q') <= (1 : Q')) 1 +
          -(retEig2 2 (by decide) (refineCoeff 2 (by decide)) 1 1) ≈
        vacNorm N 2 (by decide) (by decide : (0 : Q') <= (1 : Q'))
          (by decide : (1 : Q') <= (1 : Q')) 1 +
          -(retEig 2 (by decide) (1 : Q') 1) := by
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ hret2 (Q'.eqv_symm hret0)))
  exact Q'.eqv_trans _ _ _ (absQ_eqv_congr_local hargs)
    (EndpointCutoffTailClose.normEigShift_endpoint_formula N)

/-- The corrected carrier is constructively inhabited at the endpoint with
`Cq=0`, for every finite cutoff, in the fundamental channel. -/
def endpoint_inhabitant (N : Nat) :
    CutoffTailRefinedBound N (by decide : (0 : Q') <= (1 : Q'))
      (by decide : (1 : Q') <= (1 : Q')) (0 : Q') 1 where
  quadratic_add_tail := by
    have he := normEigShift2_endpoint_formula N
    have hzero :
        (0 : Q') * (((1 : Q') - (1 : Q')) * ((1 : Q') - (1 : Q'))) + endpointTail N ≈
          endpointTail N := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _)) ?_
      exact QPoly.q_zero_add_eqv _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.ge_of_eqv hzero)

/-! ## 4. Moving-cutoff exact tail and window modulus -/

/-- The derived endpoint tail lands exactly on the pre-existing moving-cutoff
envelope; no comparison constant is lost. -/
theorem endpointTail_Ncut (k : Nat) : endpointTail (Ncut k) ≈ tailCut k := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (EndpointCutoffTailClose.normEigShift_endpoint_formula (Ncut k)))
    (EndpointCutoffTailClose.normEigShift_endpoint_Ncut k)

/-- The exact derived endpoint-tail sequence has the already proved window
modulus `3 * pot 2 N`. -/
theorem endpointTail_Ncut_window_modulus (N M : Nat) :
    tailSum (fun k => endpointTail (Ncut k)) N M <=
      Q'.ofNat 3 * pot 2 (by decide) N := by
  have hterm : forall k, endpointTail (Ncut k) <= tailCut k :=
    fun k => Q'.le_of_eqv (endpointTail_Ncut k)
  exact Q'.le_trans' _ _ _
    (tailSum_le_of_termwise hterm N M)
    (tailCut_window_modulus N M)

/-- Window transport for the full honest defect budget.  The analytic part
only has to provide the standard inverse-square majorant `Aq`; the exact
finite-cutoff tail contributes the derived constant `3`. -/
theorem quadratic_add_endpointTail_window_modulus
    (quad : Nat -> Q') (Aq : Q') (hAq : (0 : Q') <= Aq)
    (hquad : forall k, quad k <= Aq * invSqTerm 2 (by decide) k)
    (N M : Nat) :
    tailSum (fun k => quad k + endpointTail (Ncut k)) N M <=
      Aq * pot 2 (by decide) N + Q'.ofNat 3 * pot 2 (by decide) N := by
  have hadd :
      tailSum (fun k => quad k + endpointTail (Ncut k)) N M ≈
        tailSum quad N M + tailSum (fun k => endpointTail (Ncut k)) N M := by
    induction M with
    | zero =>
        rw [tailSum_zero, tailSum_zero, tailSum_zero]
        exact Q'.eqv_symm (QPoly.q_add_zero_eqv 0)
    | succ M ih =>
        rw [tailSum_succ, tailSum_succ, tailSum_succ]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ ih) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hq : tailSum quad N M <= Aq * pot 2 (by decide) N :=
    summableBound_of_invSq 2 (by decide) Aq hAq quad hquad N M
  have ht := endpointTail_Ncut_window_modulus N M
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hadd)
    (BulkModeCrux.qadd_le_add hq ht)

/-- The actual refined defect along the coupled cutoff schedule. -/
def movingRefinedDefect (w : Nat -> Q')
    (hw0 : forall k, (0 : Q') <= w k) (hw1 : forall k, w k <= (1 : Q'))
    (s : Nat -> Nat) (k : Nat) : Q' :=
  normEigShift2 (Ncut k) 2 (by decide) (hw0 k) (hw1 k)
    (refineCoeff 2 (by decide)) (s k)

/-- The one-field corrected carrier, together with a supplied inverse-square
quadratic majorant, gives a window estimate for the *actual* finite character-
sum defects.  The analytic contribution is `Aq`; the cutoff contribution is
the exact derived `3`, not a fitted constant. -/
theorem movingRefinedDefect_window_modulus
    (w : Nat -> Q')
    (hw0 : forall k, (0 : Q') <= w k) (hw1 : forall k, w k <= (1 : Q'))
    (s : Nat -> Nat) (r : Nat -> Q') (Cq Aq : Q')
    (hCq : (0 : Q') <= Cq) (hAq : (0 : Q') <= Aq)
    (hr : forall k, (1 : Q') - w k <= r k)
    (b : forall k, CutoffTailRefinedBound (Ncut k) (hw0 k) (hw1 k) Cq (s k))
    (hquad : forall k, Cq * (r k * r k) <= Aq * invSqTerm 2 (by decide) k)
    (N M : Nat) :
    tailSum (movingRefinedDefect w hw0 hw1 s) N M <=
      Aq * pot 2 (by decide) N + Q'.ofNat 3 * pot 2 (by decide) N := by
  let quad : Nat -> Q' := fun k => Cq * (r k * r k)
  have hterm : forall k,
      movingRefinedDefect w hw0 hw1 s k <= quad k + endpointTail (Ncut k) := by
    intro k
    exact defect_le_scaled_quadratic_add_tail (Ncut k) (hw0 k) (hw1 k)
      hCq (hr k) (s k) (b k)
  have hsum :
      tailSum (movingRefinedDefect w hw0 hw1 s) N M <=
        tailSum (fun k => quad k + endpointTail (Ncut k)) N M :=
    tailSum_le_of_termwise hterm N M
  exact Q'.le_trans' _ _ _ hsum
    (quadratic_add_endpointTail_window_modulus quad Aq hAq hquad N M)

end YMGap.Continuum.CutoffTailRefinedCarrier

#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.corrected_carrier_range
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.defect_le_scaled_quadratic_add_tail
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.fused_margin_after_quadratic_add_cutoff_tail
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.normEigShift2_endpoint_formula
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.endpoint_inhabitant
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.endpointTail_Ncut
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.endpointTail_Ncut_window_modulus
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.quadratic_add_endpointTail_window_modulus
#print axioms YMGap.Continuum.CutoffTailRefinedCarrier.movingRefinedDefect_window_modulus
