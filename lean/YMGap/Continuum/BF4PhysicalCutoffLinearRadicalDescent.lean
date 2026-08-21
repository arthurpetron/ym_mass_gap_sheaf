/-
# CReal Cauchy--Schwarz and radical descent for the physical cutoff limit

`BF4PhysicalCutoffLinearGNSForm` constructs the additive finite rational span
of genuine physical unit observables and a positive `CReal`-valued limiting
form.  This module proves the two analytic laws needed before that form can be
fed to the choice-free squared-seminorm completion.

At each approximation index the limiting form is the literal finite physical
GNS form.  Its already-proved sharp rational Cauchy--Schwarz inequality
therefore passes approximation by approximation to the limiting form.  If one
diagonal limiting form is zero, local boundedness of the other diagonal and a
division-free product tolerance force every cross form to zero.  This is the
required radical-descent law; no square root or choice is used.

The result remains at fixed nome and fixed finite half-extent.  It constructs
neither the quotient/completion nor a cutoff-independent transfer operator.

## Axiom gate

The declarations below use only constructive rational estimates, finite GNS
Cauchy--Schwarz, and Bishop-real moduli.  There is no classical choice,
noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm

namespace YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Sharp Cauchy--Schwarz survives every approximation -/

theorem innerLimit_self_approx_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalLinearObservable) :
    (0 : Q') <=
      (innerLimit hw0 hw1 half observable observable).approx cutoff := by
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  exact Q'.le_trans' _ _ _
    (D.self_nonneg observable.value)
    (Q'.ge_of_eqv
      (innerLimit_approx_eqv_stage
        hw0 hw1 half cutoff observable observable))

/-- The sharp rational Cauchy--Schwarz inequality at approximation `K` of the
limiting physical form. -/
theorem innerLimit_approx_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half left right).approx cutoff *
        (innerLimit hw0 hw1 half left right).approx cutoff <=
      (innerLimit hw0 hw1 half left left).approx cutoff *
        (innerLimit hw0 hw1 half right right).approx cutoff := by
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have hcross := innerLimit_approx_eqv_stage
    hw0 hw1 half cutoff left right
  have hleft := innerLimit_approx_eqv_stage
    hw0 hw1 half cutoff left left
  have hright := innerLimit_approx_eqv_stage
    hw0 hw1 half cutoff right right
  have hlhs :
      (innerLimit hw0 hw1 half left right).approx cutoff *
          (innerLimit hw0 hw1 half left right).approx cutoff ≈
        D.B left.value right.value * D.B left.value right.value :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hcross)
      (Q'.mul_eqv_congr_left _ _ _ hcross)
  have hrhs :
      D.B left.value left.value * D.B right.value right.value ≈
        (innerLimit hw0 hw1 half left left).approx cutoff *
          (innerLimit hw0 hw1 half right right).approx cutoff :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hleft))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hright))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlhs)
    (Q'.le_trans' _ _ _
      (D.cauchy_schwarz left.value right.value)
      (Q'.le_of_eqv hrhs))

private theorem leEv_of_approx_le {left right : CReal}
    (h : forall cutoff, left.approx cutoff <= right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨0, fun cutoff _ =>
    Q'.le_trans' _ _ _ (h cutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

/-- Cauchy--Schwarz in the transitive eventual order on constructive reals. -/
theorem innerLimit_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.leEv
      (CReal.mul
        (innerLimit hw0 hw1 half left right)
        (innerLimit hw0 hw1 half left right))
      (CReal.mul
        (innerLimit hw0 hw1 half left left)
        (innerLimit hw0 hw1 half right right)) :=
  leEv_of_approx_le (fun cutoff =>
    innerLimit_approx_cauchy_schwarz
      hw0 hw1 half cutoff left right)

/-! ## 2. The limiting radical kills every cross form -/

/-- If a finite-linear physical observable has zero limiting norm, then its
limiting pairing with every finite-linear physical observable is zero. -/
theorem innerLimit_equiv_czero_of_self_equiv_czero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable)
    (hnull : CReal.Equiv
      (innerLimit hw0 hw1 half left left) CReal.czero) :
    CReal.Equiv
      (innerLimit hw0 hw1 half left right) CReal.czero := by
  intro epsilon hepsilon
  let rightSelf := innerLimit hw0 hw1 half right right
  obtain ⟨Nbound, bound, hbound, hrightBound⟩ :=
    CReal.localBound rightSelf
  have hepsilonSq : (0 : Q') < epsilon * epsilon :=
    Q'.mul_pos hepsilon hepsilon
  obtain ⟨delta, hdelta, hbudget⟩ :=
    CReal.exists_mul_le hbound hepsilonSq
  obtain ⟨Nnull, hnullAt⟩ := hnull delta hdelta
  refine ⟨max Nbound Nnull, fun cutoff hcutoff => ?_⟩
  have hcutoffBound : Nbound <= cutoff :=
    Nat.le_trans (Nat.le_max_left _ _) hcutoff
  have hcutoffNull : Nnull <= cutoff :=
    Nat.le_trans (Nat.le_max_right _ _) hcutoff
  have hleftUpper :
      (innerLimit hw0 hw1 half left left).approx cutoff <= delta := by
    exact Q'.le_trans' _ _ _ (hnullAt cutoff hcutoffNull).1
      (Q'.le_of_eqv (QPoly.q_zero_add_eqv delta))
  have hrightUpper : rightSelf.approx cutoff <= bound :=
    (hrightBound cutoff hcutoffBound).2
  have hrightNonnegative : (0 : Q') <= rightSelf.approx cutoff :=
    innerLimit_self_approx_nonnegative
      hw0 hw1 half cutoff right
  have hproduct :
      (innerLimit hw0 hw1 half left left).approx cutoff *
          rightSelf.approx cutoff <=
        delta * bound :=
    Q'.mul_le_mul_of_nonneg hleftUpper hrightUpper
      (Q'.le_of_lt hdelta) hrightNonnegative
  have hdeltaBound : delta * bound <= epsilon * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv delta bound)) hbudget
  have hsquare :
      (innerLimit hw0 hw1 half left right).approx cutoff *
          (innerLimit hw0 hw1 half left right).approx cutoff <=
        epsilon * epsilon :=
    Q'.le_trans' _ _ _
      (innerLimit_approx_cauchy_schwarz
        hw0 hw1 half cutoff left right)
      (Q'.le_trans' _ _ _ hproduct hdeltaBound)
  have habs :
      Q'.abs ((innerLimit hw0 hw1 half left right).approx cutoff) <=
        epsilon :=
    Q'.abs_le_of_sq_le_sq hepsilon hsquare
  have hzeroSub :
      ((innerLimit hw0 hw1 half left right).approx cutoff + (-(0 : Q'))) ≈
        (innerLimit hw0 hw1 half left right).approx cutoff := by
    rw [show (-(0 : Q')) = 0 from rfl, Q'.add_zero']
    exact Q'.eqv_refl _
  have habsSub :
      Q'.abs
          ((innerLimit hw0 hw1 half left right).approx cutoff + (-(0 : Q'))) <=
        epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hzeroSub)) habs
  exact Q'.two_sided_of_abs_sub_le habsSub

/-! ## 3. Bundled limiting pre-Hilbert datum -/

/-- A CReal GNS form together with sharp Cauchy--Schwarz and the radical law
needed by the squared-seminorm quotient. -/
structure CRealPreHilbertData extends CRealGNSFormData where
  cauchy_schwarz : forall left right,
    CReal.leEv
      (CReal.mul (toCRealGNSFormData.B left right)
        (toCRealGNSFormData.B left right))
      (CReal.mul (toCRealGNSFormData.B left left)
        (toCRealGNSFormData.B right right))
  radical_descends : forall left right,
    CReal.Equiv (toCRealGNSFormData.B left left) CReal.czero ->
      CReal.Equiv (toCRealGNSFormData.B left right) CReal.czero

/-- The actual fixed-nome finite-linear physical pre-Hilbert datum. -/
def centralPhysicalCutoffLinearPreHilbert
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CRealPreHilbertData where
  toCRealGNSFormData := centralPhysicalCutoffLinearGNSForm hw0 hw1 half
  cauchy_schwarz := innerLimit_cauchy_schwarz hw0 hw1 half
  radical_descends :=
    innerLimit_equiv_czero_of_self_equiv_czero hw0 hw1 half

/-! ## Axiom audit -/

#print axioms innerLimit_approx_cauchy_schwarz
#print axioms innerLimit_cauchy_schwarz
#print axioms innerLimit_equiv_czero_of_self_equiv_czero
#print axioms CRealPreHilbertData
#print axioms centralPhysicalCutoffLinearPreHilbert

end YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent
