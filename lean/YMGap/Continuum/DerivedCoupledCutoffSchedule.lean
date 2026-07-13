/-
`DerivedCoupledCutoffSchedule` — a fully derived moving-cutoff schedule on
which the actual refined fundamental defect has a summable envelope.

This is deliberately not the physical AF schedule.  It couples the already
proved quadratic cutoff `Ncut(k)` to a weight margin chosen from the exact
finite-character Lipschitz coefficient itself:

  u_k = (1/2)^k / (vacLip(Ncut k) + 5/2),   w_k = 1-u_k.

The refined correction changes the unrefined fundamental defect by at most
`u_k`.  Therefore the exact two-parameter theorem gives

  normEigShift2(Ncut k,w_k,1) <= endpointTail(Ncut k) + (1/2)^k.

Both terms are summable.  This proves a genuine coupled `(N,w)` existence
route with no Edgeworth carrier, while honestly showing why it does not close
the AF trajectory: the derived margin is much smaller than harmonic order.
-/

import YMGap.Continuum.RefinedEndpointQuadraticFence
import YMGap.Continuum.AllWindowCorrDirichlet

namespace YMGap.Continuum.DerivedCoupledCutoffSchedule

set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.AllWindowCorrDirichlet

local infix:50 " ≈ " => Q'.eqv

private def q52 : Q' := EndpointCutoffTwoParameter.q32 + (1 : Q')

private theorem add_scaled_margin (A q u m : Q') (hum : u ≈ m) :
    (A + q) * u + u ≈ (A + (q + 1)) * m := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hum) hum) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (RingNormaliser.q_add_mul A (q + 1) m) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A * m) _ _ (RingNormaliser.q_add_mul q 1 m)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A * m) _ _
      (Q'.add_eqv_congr_left (q * m) _ _ (Q'.one_mul_eqv m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (A * m) (q * m) m)) ?_
  exact Q'.add_eqv_congr_right _ _ m
    (Q'.eqv_symm (RingNormaliser.q_add_mul A q m))

/-- The p=2 refined coefficient is nonnegative. -/
theorem refineCoeff_two_nonneg : (0 : Q') ≤ refineCoeff 2 (by decide) :=
  Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ Q'.mkPos 7 24 (by decide))
    (Q'.le_of_eqv (Q'.eqv_symm (refineCoeff_p2 (by decide))))

/-- On `[0,1]`, the p=2 correction factor stays in `[0,1]`. -/
theorem corrFactor_two_bounds {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ corrFactor (refineCoeff 2 (by decide)) w ∧
      corrFactor (refineCoeff 2 (by decide)) w ≤ (1 : Q') := by
  let u := (1 : Q') - w
  let a := refineCoeff 2 (by decide)
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le hw1
  have hu1 : u ≤ (1 : Q') := by
    have hn := Q'.neg_le_neg hw0
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
  have huu : u * u ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg hu1 hu1 (by decide) hu0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have ha0 : (0 : Q') ≤ a := refineCoeff_two_nonneg
  have ha1 : a ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (refineCoeff_p2 (by decide))) (by decide)
  have hau : a * (u * u) ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg ha1 huu
      (by decide) (Q'.mul_nonneg _ _ hu0 hu0)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hcorr0 : (0 : Q') ≤ (1 : Q') - a * (u * u) := Q'.sub_nonneg_of_le hau
  have hcorr1 : (1 : Q') - a * (u * u) ≤ (1 : Q') :=
    oneSub_le_one (Q'.mul_nonneg _ _ ha0 (Q'.mul_nonneg _ _ hu0 hu0))
  exact ⟨hcorr0, hcorr1⟩

/-- The refined-vs-unrefined fundamental retune displacement is at most the
margin `1-w`. -/
theorem refined_retune_displacement_le_margin {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    absQ (retEig 2 (by decide) w 1 +
      -(retEig2 2 (by decide) (refineCoeff 2 (by decide)) w 1)) ≤
        (1 : Q') - w := by
  let u := (1 : Q') - w
  let a := refineCoeff 2 (by decide)
  let r := renormWFix 2 (by decide) w
  let c := corrFactor a w
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le hw1
  have hu1 : u ≤ (1 : Q') := by
    have hn := Q'.neg_le_neg hw0
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
  have hcc := corrFactor_two_bounds hw0 hw1
  have hr0 : (0 : Q') ≤ r := renormWFix_nonneg hw0 2 (by decide)
  have hr1 : r ≤ (1 : Q') := renormWFix_le_one hw1 2 (by decide)
  have hret0 : (0 : Q') ≤ retEig 2 (by decide) w 1 := qpow_nonneg r hr0 (c4 1)
  have hret1 : retEig 2 (by decide) w 1 ≤ (1 : Q') := qpow_le_one hr0 hr1 (c4 1)
  have hshape := corr_casimir_shape (a := a) (w := w) 1 hcc.1 hcc.2
  have hfac := retEig2_factor 2 (by decide) a w 1
  have hdiff : retEig 2 (by decide) w 1 + -(retEig2 2 (by decide) a w 1) ≈
      retEig 2 (by decide) w 1 * ((1 : Q') - qpow c (c4 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hfac)) ?_
    show retEig 2 (by decide) w 1 +
        -(retEig 2 (by decide) w 1 * qpow c (c4 1)) ≈ _
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (retEig 2 (by decide) w 1) 1 (-(qpow c (c4 1)))) ?_
    exact Q'.add_eqv_congr' (Q'.mul_one_eqv _)
      (Q'.mul_neg_eqv _ _)
  have hdiff0 : (0 : Q') ≤
      retEig 2 (by decide) w 1 * ((1 : Q') - qpow c (c4 1)) :=
    Q'.mul_nonneg _ _ hret0 (Q'.sub_nonneg_of_le (qpow_le_one hcc.1 hcc.2 _))
  have habs : absQ (retEig 2 (by decide) w 1 +
      -(retEig2 2 (by decide) a w 1)) ≈
      retEig 2 (by decide) w 1 * ((1 : Q') - qpow c (c4 1)) := by
    refine Q'.eqv_trans _ _ _ (absQ_eqv_congr hdiff) ?_
    unfold absQ
    rw [if_pos ((Q'.zero_le_iff_num_nonneg _).mp hdiff0)]
    exact Q'.eqv_refl _
  have hmul : retEig 2 (by decide) w 1 * ((1 : Q') - qpow c (c4 1)) ≤
      (1 : Q') * (Q'.ofNat (c4 1) * (a * (u * u))) :=
    Q'.mul_le_mul_of_nonneg hret1 hshape
      (by decide) (Q'.sub_nonneg_of_le (qpow_le_one hcc.1 hcc.2 _))
  have huu : u * u ≤ u := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ u hu1 hu0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv u))
  have hcoef : Q'.ofNat (c4 1) * a ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat (c4 1)) _ _
        (refineCoeff_p2 (by decide)))) (by decide)
  have hfinal : Q'.ofNat (c4 1) * (a * (u * u)) ≤ u := by
    have he : Q'.ofNat (c4 1) * (a * (u * u)) ≈
        (Q'.ofNat (c4 1) * a) * (u * u) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg hcoef huu
        (by decide) (Q'.mul_nonneg _ _ hu0 hu0))
      (Q'.le_of_eqv (Q'.one_mul_eqv u))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hfinal))

/-- The actual refined defect is at most the unrefined defect plus one margin. -/
theorem normEigShift2_le_normEigShift_add_margin {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    normEigShift2 N 2 (by decide) hw0 hw1 (refineCoeff 2 (by decide)) 1 ≤
      normEigShift N 2 (by decide) hw0 hw1 1 + ((1 : Q') - w) := by
  let v := vacNorm N 2 (by decide) hw0 hw1 1
  let r := retEig 2 (by decide) w 1
  let r2 := retEig2 2 (by decide) (refineCoeff 2 (by decide)) w 1
  have harg : v + (-r2) ≈ (v + (-r)) + (r + (-r2)) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv v (-r) (r + (-r2))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left v _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-r) r (-r2)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left v _ _
        (Q'.add_eqv_congr_right _ _ (-r2) (Q'.neg_add_self_eqv r))) ?_
    exact Q'.add_eqv_congr_left v _ _ (QPoly.q_zero_add_eqv (-r2))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (absQ_eqv_congr harg)) ?_
  refine Q'.le_trans' _ _ _ (absQ_add_le (v + (-r)) (r + (-r2))) ?_
  exact Q'.add_le_add (Q'.le_refl' _)
    (refined_retune_displacement_le_margin hw0 hw1)

/-! ## The derived schedule -/

def coupledCoeff (k : Nat) : Q' := vacLip (Ncut k) + q52

theorem coupledCoeff_eqv (k : Nat) :
    coupledCoeff k ≈
      vacLip (Ncut k) + (EndpointCutoffTwoParameter.q32 + (1 : Q')) := by
  exact Q'.eqv_refl _

theorem coupledCoeff_pos (k : Nat) : (0 : Q') < coupledCoeff k := by
  have hv := vacLip_nonneg (Ncut k)
  have hq : q52 ≤ coupledCoeff k := by
    unfold coupledCoeff
    have h := Q'.add_le_self_of_nonneg q52 (vacLip (Ncut k)) hv
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_comm_eqv q52 (vacLip (Ncut k))))
  exact ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < q52) hq

def coupledMargin (k : Nat) : Q' :=
  Q'.divPos (HalfPow.half ^ k) (coupledCoeff k) (coupledCoeff_pos k)

def coupledW (k : Nat) : Q' := (1 : Q') - coupledMargin k

theorem coupledMargin_nonneg (k : Nat) : (0 : Q') ≤ coupledMargin k :=
  Q'.mul_nonneg _ _ (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg k)
    (Q'.le_of_lt (Q'.recipPos_pos _ (coupledCoeff_pos k)))

theorem coupledCoeff_ge_one (k : Nat) : (1 : Q') ≤ coupledCoeff k := by
  have hq : q52 ≤ coupledCoeff k := by
    unfold coupledCoeff
    have h := Q'.add_le_self_of_nonneg q52 (vacLip (Ncut k)) (vacLip_nonneg _)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_comm_eqv q52 (vacLip (Ncut k))))
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ q52) hq

theorem coupledMargin_le_one (k : Nat) : coupledMargin k ≤ (1 : Q') := by
  refine Q'.divPos_le_of_le_mul _ _ (coupledCoeff_pos k) ?_
  have hp : HalfPow.half ^ k ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc k)
      (YMGap.Constructive.CReal.invSucc_le_one k)
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_trans' _ _ _ (coupledCoeff_ge_one k)
      (Q'.ge_of_eqv (Q'.one_mul_eqv (coupledCoeff k))))

theorem coupledW_nonneg (k : Nat) : (0 : Q') ≤ coupledW k :=
  Q'.sub_nonneg_of_le (coupledMargin_le_one k)

theorem coupledW_le_one (k : Nat) : coupledW k ≤ (1 : Q') :=
  oneSub_le_one (coupledMargin_nonneg k)

theorem one_sub_coupledW (k : Nat) :
    (1 : Q') - coupledW k ≈ coupledMargin k := by
  unfold coupledW
  have h : (-((1 : Q') + -(coupledMargin k))) ≈
      (-1 : Q') + coupledMargin k := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(coupledMargin k))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) (coupledMargin k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv 1)) ?_
  exact QPoly.q_zero_add_eqv _

theorem coupledCoeff_mul_margin (k : Nat) :
    coupledCoeff k * coupledMargin k ≈ HalfPow.half ^ k := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  exact Q'.divPos_mul_eqv _ _ (coupledCoeff_pos k)

/-! ## Exact fence: the raw retune correlation has no endpoint-linear cancellation -/

/-- At the first quadratic cutoff `Ncut(0)=4`, even a coefficient of one
million cannot bound the endpoint-subtracted retune correlation residual by
`C(1-w)^2` at `w=1-10^-7`.  Since the refined correction itself starts at
second order, this directly machine-refutes first-order cancellation of the
raw `corrResidual` along the quadratic cutoff route. -/
theorem corrResidual_Ncut0_quadratic_cancellation_refuted :
    ¬ (absQ
        (corrResidual RefinedEndpointQuadraticFence.fenceW (Ncut 0) -
          corrResidual (1 : Q') (Ncut 0)) ≤
      RefinedEndpointQuadraticFence.fenceC *
        (((1 : Q') - RefinedEndpointQuadraticFence.fenceW) *
          ((1 : Q') - RefinedEndpointQuadraticFence.fenceW))) := by
  decide

/-- **Actual refined coupled defect bound.** -/
theorem refined_defect_coupled_le (k : Nat) :
    normEigShift2 (Ncut k) 2 (by decide)
        (coupledW_nonneg k) (coupledW_le_one k)
        (refineCoeff 2 (by decide)) 1 ≤
      endpointTail (Ncut k) + HalfPow.half ^ k := by
  have href := normEigShift2_le_normEigShift_add_margin
    (coupledW_nonneg k) (coupledW_le_one k) (Ncut k)
  have hun := normEigShift_fundamental_two_parameter
    (coupledW_nonneg k) (coupledW_le_one k) (Ncut k)
  have hmargin := one_sub_coupledW k
  have hstep :
      normEigShift (Ncut k) 2 (by decide) (coupledW_nonneg k) (coupledW_le_one k) 1 +
          ((1 : Q') - coupledW k) ≤
        endpointTail (Ncut k) + coupledCoeff k * coupledMargin k := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ ((1 : Q') - coupledW k) hun) ?_
    have hcoef := add_scaled_margin (vacLip (Ncut k))
      EndpointCutoffTwoParameter.q32 ((1 : Q') - coupledW k)
      (coupledMargin k) hmargin
    have hcoef' :
        (vacLip (Ncut k) + EndpointCutoffTwoParameter.q32) *
              ((1 : Q') - coupledW k) + ((1 : Q') - coupledW k) ≈
          coupledCoeff k * coupledMargin k :=
      Q'.eqv_trans _ _ _ hcoef
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (coupledCoeff_eqv k)))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (endpointTail (Ncut k))
        ((vacLip (Ncut k) + EndpointCutoffTwoParameter.q32) *
          ((1 : Q') - coupledW k)) ((1 : Q') - coupledW k))
      (Q'.add_eqv_congr_left (endpointTail (Ncut k))
        ((vacLip (Ncut k) + EndpointCutoffTwoParameter.q32) *
          ((1 : Q') - coupledW k) + ((1 : Q') - coupledW k))
        (coupledCoeff k * coupledMargin k) hcoef'))
  exact Q'.le_trans' _ _ _ href
    (Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left (endpointTail (Ncut k))
          (coupledCoeff k * coupledMargin k) (HalfPow.half ^ k)
          (coupledCoeff_mul_margin k))))

end YMGap.Continuum.DerivedCoupledCutoffSchedule

#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.refined_retune_displacement_le_margin
#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.normEigShift2_le_normEigShift_add_margin
#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.coupledW_nonneg
#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.coupledCoeff_mul_margin
#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.corrResidual_Ncut0_quadratic_cancellation_refuted
#print axioms YMGap.Continuum.DerivedCoupledCutoffSchedule.refined_defect_coupled_le
