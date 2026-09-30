/-
# All fixed-depth nested root limits on the ORIGINAL Wilson carrier

Every finite row is a polynomial in the original D=I-T. Coefficient
monotonicity and the explicit nested mass modulus give represented limits
at every natural depth, with no choice of quotient representatives and no
new intermediate carrier. The compatible square laws and strong continuity
are separate obligations; these limits are not yet a dyadic semigroup.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootIteration
import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.ComplementRootNestedMass

namespace YMGap.Continuum.BF4WilsonAllNomeNestedRootIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra (action_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeRootIteration (polynomialCauchy polynomialCauchy_pin)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.ComplementRootComposition

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Class" => Quotient.mk (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
  (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

def approximant (k n : Nat) (x : V) : V := action hw0 hw1 (nested k n) x

/-- Only the exact positive polynomial difference is estimated. -/
theorem ordered_distance_bound (k m n : Nat) (hmn : m ≤ n) (x : V) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 k n x) (approximant hw0 hw1 k m x))
      (RCscale (ComplementRootNestedMass.residual k m * ComplementRootNestedMass.residual k m)
        (B x x)) := by
  have hd := nested_difference_nonnegative k hmn
  have h := action_distance_bound hw0 hw1 (nested k n) (nested k m) hd x
  have h0 := mass_nonnegative (psub (nested k n) (nested k m)) hd
  have hm : eval (psub (nested k n) (nested k m)) 1 ≤ ComplementRootNestedMass.residual k m :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_psub _ _ _))
      (Q'.add_le_add_right _ _ (-(ComplementRootNestedMass.mass k m))
        (ComplementRootNestedMass.mass_le_one k n))
  exact RCle_trans h (RCscale_scalar_mono
    (Q'.mul_le_mul_of_nonneg hm hm (ComplementRootNestedMass.residual_nonnegative k m) h0)
    (completedInner_nonnegative hw0 hw1 x))

private theorem cap_tail_small (cap epsilon : Q') (hc : (0 : Q') ≤ cap)
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : max cap.num.toNat epsilon.den ≤ n) :
    (Q'.invSucc n * Q'.invSucc n) * cap ≤ epsilon := by
  have hcap : cap * Q'.invSucc n ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_left _ _) hn)) hc)
      (ExpNeg.mul_invSucc_toNat_le_one cap hc)
  have heq : Q'.eqv ((Q'.invSucc n * Q'.invSucc n)*cap)
      ((cap * Q'.invSucc n)*Q'.invSucc n) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.mul (.var 1) (.var 0)) (.var 0)) (by decide)
      (fun | 0 => Q'.invSucc n | _ => cap)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcap (Q'.invSucc_nonneg n))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le epsilon he))))

/-- Absolute precision uses the supplied original representative's norm cap. -/
def iterationModulus (k : Nat) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  ComplementRootNestedMass.residualModulus k
    (Q'.invSucc (max (normCeiling PD X).num.toNat epsilon.den))

private theorem distance_small (k : Nat) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hmn : m ≤ n) (hm : iterationModulus hw0 hw1 k X epsilon ≤ m) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 k n (Class X))
      (approximant hw0 hw1 k m (Class X))) (Rq epsilon) := by
  let c := normCeiling PD X
  let j := max c.num.toNat epsilon.den
  have hc : (0 : Q') ≤ c := normCeiling_nonnegative PD X
  have hr := ComplementRootNestedMass.residual_small k (Q'.invSucc j)
    (Q'.invSucc_pos j) m hm
  have hr0 := ComplementRootNestedMass.residual_nonnegative k m
  have h := RCle_trans (ordered_distance_bound hw0 hw1 k m n hmn (Class X))
    (RCscale_mono (Q'.mul_nonneg _ _ hr0 hr0) (completedInner_diagonal_le_normCeiling PD X))
  have hscale (a b : Q') : RCscale a (Rq b) = Rq (a*b) :=
    Quotient.sound (CRealAlg.ofQ'_mul a b).symm
  rw [hscale] at h
  apply RCle_trans h
  apply leEv_le_ofQ'_of_approx_le
  intro i
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ c
      (Q'.mul_le_mul_of_nonneg hr hr (Q'.invSucc_nonneg j) hr0) hc)
    (cap_tail_small c epsilon hc he j (Nat.le_refl j))

def iterationRows (k : Nat) (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => polynomialCauchy hw0 hw1 (nested k n) 0 X
  modulus := iterationModulus hw0 hw1 k X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist hw0 hw1
      (Class (polynomialCauchy hw0 hw1 (nested k m) 0 X))
      (Class (polynomialCauchy hw0 hw1 (nested k n) 0 X))) _
    rw [polynomialCauchy_pin, polynomialCauchy_pin]
    change RCle (completedDist hw0 hw1 (approximant hw0 hw1 k m (Class X))
      (approximant hw0 hw1 k n (Class X))) _
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact distance_small hw0 hw1 k X epsilon he m n hmn hm
    · exact distance_small hw0 hw1 k X epsilon he n m hnm hn

theorem iterationRows_point (k : Nat) (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (iterationRows hw0 hw1 k X) n = approximant hw0 hw1 k n (Class X) :=
  polynomialCauchy_pin hw0 hw1 (nested k n) 0 X

/-- Actual original-carrier limits at every fixed depth; square compatibility
is deliberately not asserted by this definition. -/
def nestedLimit (k : Nat) : V → V :=
  Quotient.lift (fun X => limit hw0 hw1 (iterationRows hw0 hw1 k X)) (fun X Y h => by
    apply limit_independent hw0 hw1
    intro n
    rw [iterationRows_point, iterationRows_point, Quotient.sound h])

def convergenceModulus (k : Nat) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  limitRate hw0 hw1 (iterationRows hw0 hw1 k X) epsilon

theorem nestedLimit_approximation (k : Nat) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : convergenceModulus hw0 hw1 k X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 k n (Class X))
      (nestedLimit hw0 hw1 k (Class X))) (Rq epsilon) := by
  change RCle (completedDist hw0 hw1 (approximant hw0 hw1 k n (Class X))
    (limit hw0 hw1 (iterationRows hw0 hw1 k X))) _
  rw [← iterationRows_point]
  exact limit_bound hw0 hw1 (iterationRows hw0 hw1 k X) epsilon he n hn

def nestedLimitCertificate (k : Nat) (X : (D).Cauchy) :
    Σ' y : V, Σ' modulus : Q' → Nat,
      (y = nestedLimit hw0 hw1 k (Class X)) ×'
      (∀ epsilon, (0 : Q') < epsilon → ∀ n, modulus epsilon ≤ n →
        RCle (completedDist hw0 hw1 (approximant hw0 hw1 k n (Class X)) y) (Rq epsilon)) :=
  ⟨nestedLimit hw0 hw1 k (Class X), convergenceModulus hw0 hw1 k X, rfl,
    nestedLimit_approximation hw0 hw1 k X⟩

theorem nestedLimit_symmetric (k : Nat) (x y : V) :
    B (nestedLimit hw0 hw1 k x) y = B x (nestedLimit hw0 hw1 k y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1 (iterationRows hw0 hw1 k X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (iterationRows hw0 hw1 k Y) (fun n => by
      rw [iterationRows_point, constantRows_point, constantRows_point, iterationRows_point]
      exact action_symmetric hw0 hw1 (nested k n) (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  exact h

/-- Each limiting complement form stays below the ORIGINAL norm form. -/
theorem nestedLimit_form_le (k : Nat) (x : V) :
    RCle (B x (nestedLimit hw0 hw1 k x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let S := iterationRows hw0 hw1 k X
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).2
  change RCle (B (limit hw0 hw1 (constantRows hw0 hw1 X))
    (limit hw0 hw1 (iterationRows hw0 hw1 k X)))
    (RCadd (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) n)
      (rowPoint hw0 hw1 (iterationRows hw0 hw1 k X) n)) (Rq epsilon)) at h
  rw [constantRows_point, iterationRows_point, limit_constantRows] at h
  have hp := actionFrom_defect_pair_bound hw0 hw1 (nested k n)
    (nested_coeffNonnegative k n) (Class X) 0 0
  change RCle (B (approximant hw0 hw1 k n (Class X)) (Class X)) _ at hp
  rw [completedInner_symm hw0 hw1 (approximant hw0 hw1 k n (Class X)) (Class X)] at hp
  have hle := RCle_trans hp (RCscale_scalar_mono
    (ComplementRootNestedMass.mass_le_one k n) (completedInner_nonnegative hw0 hw1 (Class X)))
  rw [RCscale_one] at hle
  exact RCle_trans h (RCadd_le_add hle (RCle_refl _))

#print axioms ordered_distance_bound
#print axioms iterationRows
#print axioms nestedLimit
#print axioms nestedLimit_approximation
#print axioms nestedLimitCertificate
#print axioms nestedLimit_symmetric
#print axioms nestedLimit_form_le

end YMGap.Continuum.BF4WilsonAllNomeNestedRootIteration
