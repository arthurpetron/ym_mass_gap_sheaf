/-
# Rational operations on the SAME Wilson spatial-union completion

Common-base coherence transports the original dense form algebra. Positivity
and the parallelogram identity give the addition distance bound; bilinearity
gives the exact scalar-square distance law. These proved estimates supply the
existing explicit-modulus completion maps, acting on the existing union
Cauchy quotient. No support bound for a whole stream is imposed.

Completed bilinearity and linear laws are consumers, not hypotheses here.
Real scalar extension, full Hilbert completeness, observable coverage and
canonical OS/QFT or continuum realization are not asserted.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionPosdef
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4WilsonSpatialUnionLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (pairing_symm pairing_nonnegative)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (pairing_zero_left)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (intrinsicForm_sum_left intrinsicForm_smul_left intrinsicForm_difference_left)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "d" => distSq hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq intrinsicForm
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

theorem pairing_add_left (x y z : Stage) :
    Equiv (P (sumStage x y) z) (add (P x z) (P y z)) := by
  let N := max (max x.base y.base) z.base
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have h := pairing_at_base hw0 hw1 hsmall hd hs (sumStage x y) z N
    (Nat.max_le.mpr ⟨hx, hy⟩) hz
  rw [atBase_sum x y hx hy] at h
  exact h.trans ((intrinsicForm_sum_left hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy) (atBase z hz)).trans
      (Equiv_add (pairing_at_base hw0 hw1 hsmall hd hs x z N hx hz)
        (pairing_at_base hw0 hw1 hsmall hd hs y z N hy hz)).symm)

theorem pairing_add_right (x y z : Stage) :
    Equiv (P x (sumStage y z)) (add (P x y) (P x z)) :=
  (pairing_symm hw0 hw1 hsmall hd hs x (sumStage y z)).trans
    ((pairing_add_left hw0 hw1 hsmall hd hs y z x).trans
      (Equiv_add (pairing_symm hw0 hw1 hsmall hd hs y x)
        (pairing_symm hw0 hw1 hsmall hd hs z x)))

theorem pairing_smul_left (c : Q') (x y : Stage) :
    Equiv (P (smulStage c x) y) (mul (ofQ' c) (P x y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have h := pairing_at_base hw0 hw1 hsmall hd hs (smulStage c x) y N hx hy
  simp only [atBase_smul] at h
  exact h.trans ((intrinsicForm_smul_left hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) c (atBase x hx) (atBase y hy)).trans
      (Pivot2.mul_congr_right (pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy)).symm)

theorem pairing_smul_right (c : Q') (x y : Stage) :
    Equiv (P x (smulStage c y)) (mul (ofQ' c) (P x y)) :=
  (pairing_symm hw0 hw1 hsmall hd hs x (smulStage c y)).trans
    ((pairing_smul_left hw0 hw1 hsmall hd hs c y x).trans
      (Pivot2.mul_congr_right (pairing_symm hw0 hw1 hsmall hd hs y x)))

theorem pairing_zero_right (x : Stage) : Equiv (P x zeroStage) czero :=
  (pairing_symm hw0 hw1 hsmall hd hs x zeroStage).trans
    (pairing_zero_left hw0 hw1 hsmall hd hs x)

theorem pairing_difference_left (x y z : Stage) :
    Equiv (P (difference x y) z) (sub (P x z) (P y z)) := by
  let N := max (max x.base y.base) z.base
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have h := pairing_at_base hw0 hw1 hsmall hd hs (difference x y) z N
    (Nat.max_le.mpr ⟨hx, hy⟩) hz
  rw [atBase_difference x y hx hy] at h
  exact h.trans ((intrinsicForm_difference_left hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy) (atBase z hz)).trans
      (Equiv_add (pairing_at_base hw0 hw1 hsmall hd hs x z N hx hz)
        (neg_congr (pairing_at_base hw0 hw1 hsmall hd hs y z N hy hz))).symm)

theorem pairing_difference_right (x y z : Stage) :
    Equiv (P x (difference y z)) (sub (P x y) (P x z)) :=
  (pairing_symm hw0 hw1 hsmall hd hs x (difference y z)).trans
    ((pairing_difference_left hw0 hw1 hsmall hd hs y z x).trans
      (Equiv_add (pairing_symm hw0 hw1 hsmall hd hs y x)
        (neg_congr (pairing_symm hw0 hw1 hsmall hd hs z x))))

theorem difference_eq_sum_smul (x y : Stage) :
    difference x y = sumStage x (smulStage (-1) y) := rfl

/-- The original union distance is the original form of its literal difference. -/
theorem distance_difference (x y : Stage) :
    Equiv (d x y) (P (difference x y) (difference x y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hp : Equiv (P (difference x y) (difference x y))
      (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy)) := by
    unfold BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq
    simpa only [atBase_difference x y hx hy] using
      pairing_at_base hw0 hw1 hsmall hd hs (difference x y) (difference x y) N
        (Nat.max_le.mpr ⟨hx, hy⟩) (Nat.max_le.mpr ⟨hx, hy⟩)
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans hp.symm

private theorem norm_congr (x y : Stage) (h : ∀ z, Equiv (P x z) (P y z)) :
    Equiv (P x x) (P y y) :=
  (h x).trans ((pairing_symm hw0 hw1 hsmall hd hs y x).trans (h y))

/-- Parallelogram positivity for the actual original union form. -/
theorem pairing_sum_bound (x y : Stage) :
    leEv (P (sumStage x y) (sumStage x y))
      (add (add (P x x) (P x x)) (add (P y y) (P y y))) := by
  have hsum := (pairing_add_left hw0 hw1 hsmall hd hs x y (sumStage x y)).trans
    (Equiv_add (pairing_add_right hw0 hw1 hsmall hd hs x x y)
      (pairing_add_right hw0 hw1 hsmall hd hs y x y))
  have hdiff := (pairing_difference_left hw0 hw1 hsmall hd hs x y (difference x y)).trans
    (Equiv_add (pairing_difference_right hw0 hw1 hsmall hd hs x x y)
      (neg_congr (pairing_difference_right hw0 hw1 hsmall hd hs y x y)))
  have hpar : Equiv
      (add (P (sumStage x y) (sumStage x y)) (P (difference x y) (difference x y)))
      (add (add (P x x) (P x x)) (add (P y y) (P y y))) := by
    refine (Equiv_add hsum hdiff).trans ?_
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3))))))
      (.add (.add (.var 0) (.var 0)) (.add (.var 3) (.var 3))) (by decide)
      (fun | 0 => (P x x).approx n | 1 => (P x y).approx n
           | 2 => (P y x).approx n | _ => (P y y).approx n)
  have hz : Equiv (add (P (sumStage x y) (sumStage x y)) czero)
      (P (sumStage x y) (sumStage x y)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv hz.symm)
    (leEv_trans (leEv_add (leEv_refl _)
      (pairing_nonnegative hw0 hw1 hsmall hd hs (difference x y))) (leEv_of_equiv hpar))

private theorem difference_add_pair (x x' y y' z : Stage) :
    Equiv (P (difference (sumStage x y) (sumStage x' y')) z)
      (P (sumStage (difference x x') (difference y y')) z) := by
  have hl := (pairing_difference_left hw0 hw1 hsmall hd hs (sumStage x y) (sumStage x' y') z).trans
    (Equiv_add (pairing_add_left hw0 hw1 hsmall hd hs x y z)
      (neg_congr (pairing_add_left hw0 hw1 hsmall hd hs x' y' z)))
  have hr := (pairing_add_left hw0 hw1 hsmall hd hs (difference x x') (difference y y') z).trans
    (Equiv_add (pairing_difference_left hw0 hw1 hsmall hd hs x x' z)
      (pairing_difference_left hw0 hw1 hsmall hd hs y y' z))
  refine hl.trans (Equiv.trans ?_ hr.symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (by decide)
    (fun | 0 => (P x z).approx n | 1 => (P x' z).approx n
         | 2 => (P y z).approx n | _ => (P y' z).approx n)

theorem distSq_add (x x' y y' : Stage) :
    leEv (d (sumStage x y) (sumStage x' y'))
      (add (add (d x x') (d x x')) (add (d y y') (d y y'))) := by
  have hpin := (distance_difference hw0 hw1 hsmall hd hs (sumStage x y) (sumStage x' y')).trans
    (norm_congr hw0 hw1 hsmall hd hs _ _ (difference_add_pair hw0 hw1 hsmall hd hs x x' y y'))
  have hx := distance_difference hw0 hw1 hsmall hd hs x x'
  have hy := distance_difference hw0 hw1 hsmall hd hs y y'
  exact leEv_trans (leEv_of_equiv hpin)
    (leEv_trans (pairing_sum_bound hw0 hw1 hsmall hd hs (difference x x') (difference y y'))
      (leEv_of_equiv (Equiv_add (Equiv_add hx hx) (Equiv_add hy hy)).symm))

private theorem difference_smul_pair (c : Q') (x y z : Stage) :
    Equiv (P (difference (smulStage c x) (smulStage c y)) z)
      (P (smulStage c (difference x y)) z) := by
  have hl := (pairing_difference_left hw0 hw1 hsmall hd hs (smulStage c x) (smulStage c y) z).trans
    (Equiv_add (pairing_smul_left hw0 hw1 hsmall hd hs c x z)
      (neg_congr (pairing_smul_left hw0 hw1 hsmall hd hs c y z)))
  have hr := (pairing_smul_left hw0 hw1 hsmall hd hs c (difference x y) z).trans
    (Pivot2.mul_congr_right (pairing_difference_left hw0 hw1 hsmall hd hs x y z))
  refine hl.trans (Equiv.trans ?_ hr.symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
    (fun | 0 => c | 1 => (P x z).approx n | _ => (P y z).approx n)

theorem distSq_smul (c : Q') (x y : Stage) :
    Equiv (d (smulStage c x) (smulStage c y)) (mul (ofQ' (c*c)) (d x y)) := by
  let z := difference x y
  have hpin := (distance_difference hw0 hw1 hsmall hd hs (smulStage c x) (smulStage c y)).trans
    (norm_congr hw0 hw1 hsmall hd hs _ _ (difference_smul_pair hw0 hw1 hsmall hd hs c x y))
  have hscale := (pairing_smul_left hw0 hw1 hsmall hd hs c z (smulStage c z)).trans
    (Pivot2.mul_congr_right (pairing_smul_right hw0 hw1 hsmall hd hs c z z))
  have halg : Equiv (mul (ofQ' c) (mul (ofQ' c) (P z z))) (mul (ofQ' (c*c)) (P z z)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv c c ((P z z).approx n)))
  exact hpin.trans (hscale.trans (halg.trans
    (Pivot2.mul_congr_right (distance_difference hw0 hw1 hsmall hd hs x y).symm)))

def addition : (D).BinaryQuadraticLipschitz where
  toFun := sumStage
  contraction := distSq_add hw0 hw1 hsmall hd hs

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smulStage c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (c*c)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    exact leEv_trans (leEv_of_equiv (distSq_smul hw0 hw1 hsmall hd hs c x y))
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def addCauchy (X Y : (D).Cauchy) : (D).Cauchy := (addition hw0 hw1 hsmall hd hs).mapCauchy X Y
def smulCauchy (c : Q') (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 hsmall hd hs c).mapCauchy X

theorem addCauchy_seq (X Y : (D).Cauchy) (n : Nat) :
    (addCauchy hw0 hw1 hsmall hd hs X Y).seq n = sumStage (X.seq n) (Y.seq n) := rfl
theorem smulCauchy_seq (c : Q') (X : (D).Cauchy) (n : Nat) :
    (smulCauchy hw0 hw1 hsmall hd hs c X).seq n = smulStage c (X.seq n) := rfl

theorem addCauchy_modulus (X Y : (D).Cauchy) (epsilon : Q') :
    (addCauchy hw0 hw1 hsmall hd hs X Y).modulus epsilon =
      max (X.modulus (HalfPow.half*(HalfPow.half*epsilon)))
        (Y.modulus (HalfPow.half*(HalfPow.half*epsilon))) := rfl
theorem smulCauchy_modulus (c : Q') (X : (D).Cauchy) (epsilon : Q') :
    (smulCauchy hw0 hw1 hsmall hd hs c X).modulus epsilon = X.modulus (scalarTolerance c epsilon) := rfl

def completedAdd : V → V → V := (addition hw0 hw1 hsmall hd hs).completionMap
def completedSmul (c : Q') : V → V := (scalarContinuous hw0 hw1 hsmall hd hs c).completionMap
def completedNeg : V → V := completedSmul hw0 hw1 hsmall hd hs (-1)

theorem completedAdd_mk (X Y : (D).Cauchy) :
    completedAdd hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)
      (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (addCauchy hw0 hw1 hsmall hd hs X Y) := rfl
theorem completedSmul_mk (c : Q') (X : (D).Cauchy) :
    completedSmul hw0 hw1 hsmall hd hs c (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (smulCauchy hw0 hw1 hsmall hd hs c X) := rfl
theorem completedAdd_embedStage (x y : Stage) :
    completedAdd hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) = embedStage hw0 hw1 hsmall hd hs (sumStage x y) := rfl
theorem completedSmul_embedStage (c : Q') (x : Stage) :
    completedSmul hw0 hw1 hsmall hd hs c (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (smulStage c x) := rfl

#print axioms pairing_add_left
#print axioms pairing_add_right
#print axioms pairing_smul_left
#print axioms pairing_smul_right
#print axioms pairing_zero_right
#print axioms pairing_difference_left
#print axioms pairing_difference_right
#print axioms difference_eq_sum_smul
#print axioms distance_difference
#print axioms pairing_sum_bound
#print axioms distSq_add
#print axioms distSq_smul
#print axioms addition
#print axioms scalarContinuous
#print axioms addCauchy
#print axioms smulCauchy
#print axioms addCauchy_seq
#print axioms smulCauchy_seq
#print axioms addCauchy_modulus
#print axioms smulCauchy_modulus
#print axioms completedAdd
#print axioms completedSmul
#print axioms completedNeg
#print axioms completedAdd_mk
#print axioms completedSmul_mk
#print axioms completedAdd_embedStage
#print axioms completedSmul_embedStage

end YMGap.Continuum.BF4WilsonSpatialUnionLinear
