/-
# Generic pairing completion adapter for the physical cutoff carrier

The physical cutoff pairing already supplies every quantitative field of the
generic `PairingData` interface.  This module packages those results and
identifies the resulting generic representative and completed pairings with
the pre-existing physical constructions. Vanishing against every actual dense
observable then forces a completed vector to be zero. No new analytic
estimate or coordinate-pairing formula is assumed.
-/

import YMGap.Continuum.CRealSeminormPairingPosdef
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner

namespace YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormPairingCompletion

local infix:50 " ≈ " => Q'.eqv

private def innerLimitQCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    QCauchy (innerLimit hw0 hw1 half left right).approx where
  M := (innerLimitInnerRegularity hw0 hw1 half left right).rate
  bound := (innerLimitInnerRegularity hw0 hw1 half left right).regular

private theorem innerLimit_diagonal_anchor_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (value anchor : CentralPhysicalLinearObservable) :
    leEv (innerLimit hw0 hw1 half value value)
      (add
        (add
          (physicalLinearDistSq hw0 hw1 half value anchor)
          (physicalLinearDistSq hw0 hw1 half value anchor))
        (add
          (innerLimit hw0 hw1 half anchor anchor)
          (innerLimit hw0 hw1 half anchor anchor))) := by
  have hvalue := innerLimit_self_equiv_distSq_zero
    hw0 hw1 half value
  have hanchor := innerLimit_self_equiv_distSq_zero
    hw0 hw1 half anchor
  have htriangle := physicalLinearDistSq_triangle
    hw0 hw1 half value anchor .zero
  apply leEv_trans (leEv_of_equiv hvalue)
  apply leEv_trans htriangle
  exact leEv_of_equiv
    (add_congr_right
      ((add_congr_left hanchor.symm).trans
        (add_congr_right hanchor.symm)))

private theorem pairingTolerance_budget_local
    (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') :
    let u := pairingTolerance B hB epsilon
    (u + u) * (B + 1) ≤
      (HalfPow.half * epsilon) * (HalfPow.half * epsilon) := by
  let r := HalfPow.half * epsilon
  have hden : (0 : Q') < B + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg 1 B hB)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hmul : smallTolerance B hB r * (B + 1) ≈
      HalfPow.half * (r * r) :=
    Q'.divPos_mul_eqv _ _ hden
  have htwo :
      (smallTolerance B hB r + smallTolerance B hB r) * (B + 1) ≈
        r * r := by
    refine Q'.eqv_trans _
      (smallTolerance B hB r * (B + 1) +
        smallTolerance B hB r * (B + 1)) _
      (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.eqv_trans _
      (HalfPow.half * (r * r) + HalfPow.half * (r * r)) _
      (Q'.add_eqv_congr' hmul hmul)
      (ExpNeg.two_halves (r * r))
  exact Q'.le_of_eqv htwo

private theorem innerLimit_pairing_close
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (x x' y y' : CentralPhysicalLinearObservable)
    (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (physicalLinearDistSq hw0 hw1 half x x')
      (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (physicalLinearDistSq hw0 hw1 half y y')
      (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (innerLimit hw0 hw1 half y y) (ofQ' B))
    (hx'norm : leEv (innerLimit hw0 hw1 half x' x') (ofQ' B)) :
    leRat (sub (innerLimit hw0 hw1 half x y)
      (innerLimit hw0 hw1 half x' y')) epsilon ∧
    leRat (sub (innerLimit hw0 hw1 half x' y')
      (innerLimit hw0 hw1 half x y)) epsilon := by
  let u := pairingTolerance B hB epsilon
  let r := HalfPow.half * epsilon
  have hu : (0 : Q') < u := pairingTolerance_pos B hB hepsilon
  have hr : (0 : Q') < r := ExpNeg.half_mul_pos epsilon hepsilon
  have hbudget := pairingTolerance_budget_local B hB epsilon
  have htermX := innerLimit_twoSided_leRat hw0 hw1 half
    (CentralPhysicalLinearObservable.sub x x') y u B r hu hr hx hynorm hbudget
  have htermY := innerLimit_twoSided_leRat hw0 hw1 half
    (CentralPhysicalLinearObservable.sub y y') x' u B r hu hr hy hx'norm hbudget
  have hsplit := innerLimit_diff_split hw0 hw1 half x x' y y'
  have hforward := leRat_of_equiv hsplit
    (leRat_mono (leRat_add htermX.1 htermY.1)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))
  have hreverse : Equiv
      (sub (innerLimit hw0 hw1 half x' y')
        (innerLimit hw0 hw1 half x y))
      (add
        (neg (innerLimit hw0 hw1 half
          (CentralPhysicalLinearObservable.sub x x') y))
        (neg (innerLimit hw0 hw1 half
          (CentralPhysicalLinearObservable.sub y y') x'))) :=
    (Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((neg_congr hsplit).trans
        (Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _)))
  exact ⟨hforward, leRat_of_equiv hreverse
    (leRat_mono (leRat_add htermX.2 htermY.2)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- The actual physical limiting pairing packaged for the generic
choice-free pairing completion. -/
def physicalPairingData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    PairingData (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half) where
  pairing := innerLimit hw0 hw1 half
  pairingCauchy := innerLimitQCauchy hw0 hw1 half
  diagonal_anchor_bound := innerLimit_diagonal_anchor_bound hw0 hw1 half
  pairing_close := innerLimit_pairing_close hw0 hw1 half

/-- The generic representative scalar is the already-constructed physical
pairing limit, because both are limits of the same dense sequence. -/
theorem representativeInner_equiv_physicalCauchyPairingLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Equiv
      (representativeInner (physicalPairingData hw0 hw1 half) X Y)
      (physicalCauchyPairingLimit hw0 hw1 half X Y) := by
  apply representativeInner_unique
    (physicalPairingData hw0 hw1 half) X Y
  exact physicalCauchyPairingSeq_converges hw0 hw1 half X Y

/-- The generic completed pairing is definitionally on the same completion
and equals the existing physical completed inner form. -/
theorem completedInner_eq_centralPhysicalCutoffCompletedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedInner (physicalPairingData hw0 hw1 half) x y =
      centralPhysicalCutoffCompletedInner hw0 hw1 half x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound
    (representativeInner_equiv_physicalCauchyPairingLimit
      hw0 hw1 half X Y)

/-- Dense tests separate zero in the existing physical completion. This uses
actual completed pairings, not merely pointwise coordinates; the formula
relating those pairings to persistent coordinates remains a separate task. -/
theorem completed_eq_zero_of_dense_pairings_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half)
    (hdense : ∀ p : CentralPhysicalLinearObservable,
      centralPhysicalCutoffCompletedInner hw0 hw1 half x
        ((centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).embedRep p) =
      RCzero) :
    x = (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).embedRep .zero := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let P := physicalPairingData hw0 hw1 half
  apply (completedInner_posdef P .zero
    (fun p => (innerLimit_self_equiv_distSq_zero hw0 hw1 half p).symm)
    (Equiv.refl _) x).mp
  revert hdense
  refine Quotient.inductionOn x ?_
  intro X hdense
  apply Quotient.sound
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => representativeInner P X (D.constant (X.seq n)))
    (bSeq := fun _ => czero)
  · intro n
    exact Quotient.exact
      ((completedInner_eq_centralPhysicalCutoffCompletedInner hw0 hw1 half
        (Quotient.mk D.completionSetoid X) (D.embedRep (X.seq n))).trans
          (hdense (X.seq n)))
  · exact representativeInner_right_stage_converges P X X
  · exact convergesTo_const czero

end YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter.physicalPairingData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter.representativeInner_equiv_physicalCauchyPairingLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter.completedInner_eq_centralPhysicalCutoffCompletedInner
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter.completed_eq_zero_of_dense_pairings_zero
