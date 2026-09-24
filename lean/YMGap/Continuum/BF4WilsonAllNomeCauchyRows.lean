/-
# Explicit represented limits on the SAME all-nome Wilson carrier

The actual completed squared distance now supplies every input of the generic
diagonal construction. Both inner and outer moduli are data; convergence is
measured in the actual norm of the actual difference. No representative of an
arbitrary quotient-valued sequence is selected. The discrete time map preserves
these rows and their moduli, and commutes with the computed limit.
The actual vacuum complement is closed under these represented limits:
Cauchy--Schwarz bounds the squared vacuum pairing by the distance to any
orthogonal row point, which tends to zero with the supplied modulus.

This proves represented completeness at fixed nome and width. It does not
identify different widths, extend scalar multiplication to all constructive
reals, or supply continuous physical time, QFT axioms or a continuum limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.CRealSeminormCauchyRows

namespace YMGap.Continuum.BF4WilsonAllNomeCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub completedNeg)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedTime_sub completedInner_add_right completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1

/-- A dense Wilson expression AND its actual completed-distance certificate,
computed from the supplied representative's own modulus. -/
def denseApproximation (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' x : IntrinsicExpression width,
      RCle (completedDist hw0 hw1 (embed hw0 hw1 x) (Quotient.mk (D).completionSetoid X))
        (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  CRealSeminormCompletedApproximation.approximationData P X epsilon he

/-- The existing row type, instantiated with the PROVED actual distance data.
The Cauchy condition is in completed norm, not an extra pointwise comparison. -/
abbrev RepresentedCauchy := CRealSeminormCauchyRows.CauchyRows P

def rowPoint (R : RepresentedCauchy hw0 hw1 (width := width)) (n : Nat) : V :=
  CRealSeminormCauchyRows.rowPoint P R n

def limit (R : RepresentedCauchy hw0 hw1 (width := width)) : V :=
  CRealSeminormCauchyRows.rowLimit P R

def limitRate (R : RepresentedCauchy hw0 hw1 (width := width)) (epsilon : Q') : Nat :=
  R.modulus (quarter (quarter epsilon))

/-- Convergence in the actual SAME-carrier squared distance, with explicit
outer rate epsilon/16. The rows already contain their inner moduli. -/
theorem limit_bound (R : RepresentedCauchy hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : limitRate hw0 hw1 R epsilon ≤ n) :
    RCle (completedDist hw0 hw1 (rowPoint hw0 hw1 R n) (limit hw0 hw1 R))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  CRealSeminormCauchyRows.rowLimit_bound P R epsilon he n hn

theorem limit_unique (R : RepresentedCauchy hw0 hw1 (width := width))
    (L : V) (rate : Q' → Nat)
    (h : ∀ epsilon, (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
      RCle (completedDist hw0 hw1 (rowPoint hw0 hw1 R n) L)
        (Quotient.mk crealSetoid (ofQ' epsilon))) : limit hw0 hw1 R = L :=
  CRealSeminormCauchyRows.rowLimit_eq_of_bound P R L rate h

theorem limit_independent (R S : RepresentedCauchy hw0 hw1 (width := width))
    (h : ∀ n, rowPoint hw0 hw1 R n = rowPoint hw0 hw1 S n) :
    limit hw0 hw1 R = limit hw0 hw1 S :=
  CRealSeminormCauchyRows.rowLimit_independent P R S h

/-- Constant rows from an original Cauchy stream recover its original class. -/
theorem limit_original (X : (D).Cauchy) :
    limit hw0 hw1 (CRealSeminormCauchyRows.presentationRows P X) =
      Quotient.mk (D).completionSetoid X :=
  CRealSeminormCauchyRows.rowLimit_presentationRows P X

/-- Actual completed time contracts the actual distance between any states. -/
theorem completedDist_time (n : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 (T n x) (T n y)) (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← completedTime_sub]
  exact completedInner_time_contraction hw0 hw1 n (completedSub hw0 hw1 x y)

/-- Both the row representatives and their inner/outer moduli are retained by
the actual nonexpansive temporal map. -/
def timeRows (time : Nat) (R : RepresentedCauchy hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => (timeNonexpansive hw0 hw1 time).mapCauchy (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist hw0 hw1
      (T time (rowPoint hw0 hw1 R m)) (T time (rowPoint hw0 hw1 R n))) _
    exact RCle_trans (completedDist_time hw0 hw1 time _ _) (R.isCauchy epsilon he m n hm hn)

theorem timeRows_modulus (time : Nat) (R : RepresentedCauchy hw0 hw1 (width := width)) :
    (timeRows hw0 hw1 time R).modulus = R.modulus := rfl

theorem timeRows_rowPoint (time : Nat) (R : RepresentedCauchy hw0 hw1 (width := width))
    (n : Nat) : rowPoint hw0 hw1 (timeRows hw0 hw1 time R) n = T time (rowPoint hw0 hw1 R n) := rfl

/-- The computed diagonal is compatible with actual time, not merely with an
unrelated candidate limit. Its inner sampling indices are unchanged. -/
theorem limit_timeRows (time : Nat) (R : RepresentedCauchy hw0 hw1 (width := width)) :
    limit hw0 hw1 (timeRows hw0 hw1 time R) = T time (limit hw0 hw1 R) := rfl

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_one_mul (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' 1)) a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (A.approx n)))

private theorem rc_zero_of_small_square (a : RC)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (RCmul a a) (Quotient.mk crealSetoid (ofQ' epsilon))) : a = RCzero := by
  revert h
  refine Quotient.inductionOn a ?_
  intro A h
  apply Quotient.sound
  intro epsilon he
  let delta := HalfPow.half * (epsilon * epsilon)
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos _ (Q'.mul_pos he he)
  obtain ⟨N, hN⟩ := h delta hd delta hd
  refine ⟨N, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon * epsilon :=
    Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves _))
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- Orthogonality is closed under the computed limit on this SAME carrier.
The proof uses its actual sharp CS and row-distance bound, not a new centering
map or a scalar extension. -/
theorem limit_orthogonal (R : RepresentedCauchy hw0 hw1 (width := width))
    (h : ∀ n, completedInner hw0 hw1 (unitState hw0 hw1 width)
      (rowPoint hw0 hw1 R n) = RCzero) :
    completedInner hw0 hw1 (unitState hw0 hw1 width) (limit hw0 hw1 R) = RCzero := by
  apply rc_zero_of_small_square
  intro epsilon he
  let n := limitRate hw0 hw1 R epsilon
  have hdiff : completedInner hw0 hw1 (unitState hw0 hw1 width)
      (completedSub hw0 hw1 (limit hw0 hw1 R) (rowPoint hw0 hw1 R n)) =
      completedInner hw0 hw1 (unitState hw0 hw1 width) (limit hw0 hw1 R) := by
    unfold completedSub completedNeg
    rw [completedInner_add_right, completedInner_smul_right, h n,
      RCscale_RCzero, rc_add_zero]
  have hCS := completedInner_cauchySchwarz hw0 hw1 (unitState hw0 hw1 width)
    (completedSub hw0 hw1 (limit hw0 hw1 R) (rowPoint hw0 hw1 R n))
  rw [hdiff, unitState_norm_one, rc_one_mul] at hCS
  apply RCle_trans hCS
  change RCle (completedDist hw0 hw1 (limit hw0 hw1 R) (rowPoint hw0 hw1 R n)) _
  rw [completedDist_symm]
  exact limit_bound hw0 hw1 R epsilon he n (Nat.le_refl _)

/-- An actual state in the pre-existing vacuum-complement subtype, with the
same computed limit as its underlying vector. -/
def orthogonalLimit (R : RepresentedCauchy hw0 hw1 (width := width))
    (h : ∀ n, completedInner hw0 hw1 (unitState hw0 hw1 width)
      (rowPoint hw0 hw1 R n) = RCzero) : VacuumComplement hw0 hw1 (width := width) :=
  ⟨limit hw0 hw1 R, limit_orthogonal hw0 hw1 R h⟩

#print axioms denseApproximation
#print axioms RepresentedCauchy
#print axioms rowPoint
#print axioms limit
#print axioms limitRate
#print axioms limit_bound
#print axioms limit_unique
#print axioms limit_independent
#print axioms limit_original
#print axioms completedDist_time
#print axioms timeRows
#print axioms timeRows_modulus
#print axioms timeRows_rowPoint
#print axioms limit_timeRows
#print axioms limit_orthogonal
#print axioms orthogonalLimit

end YMGap.Continuum.BF4WilsonAllNomeCauchyRows
