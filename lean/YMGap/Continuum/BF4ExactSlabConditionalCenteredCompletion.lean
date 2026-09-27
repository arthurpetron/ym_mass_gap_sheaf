/-
# Explicit centered approximations on the original full-action completion

Apply the existing finite mean subtraction to every term of a supplied
Cauchy representative. Orthogonal projection contracts squared distances,
so its original Cauchy modulus is unchanged. Completed orthogonality to
the actual constant (of squared norm Z, not one) implies that the centered
representative has the SAME class, with a recovered Type-level null modulus.
No square root, normalized replacement form, or representative choice.

This prepares the dense-to-completed centered consumer. No analytic lower
coercivity, neighboring influence, physical gap or continuum result follows.
-/

import YMGap.Continuum.BF4ExactSlabConditionalCovariance
import YMGap.Continuum.GNSNullModulusRecovery

namespace YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSNullModulusRecovery
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

local infix:50 " ≈ " => Q'.eqv

private theorem pair_sub_left (D : GNSData) (a b c : D.V) :
    D.B (D.sub a b) c ≈ D.B a c + -(D.B b c) :=
  Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg b) c)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_left b c))

private theorem pair_sub_right (D : GNSData) (a b c : D.V) :
    D.B a (D.sub b c) ≈ D.B a b + -(D.B a c) :=
  Q'.eqv_trans _ _ _ (D.B_add_right a b (D.neg c))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_right a c))

private theorem pair_sub_sub (D : GNSData) (a b c d : D.V) :
    D.B (D.sub a b) (D.sub c d) ≈
      (D.B a c + -(D.B a d)) + -(D.B b c + -(D.B b d)) :=
  Q'.eqv_trans _ _ _ (pair_sub_left D a b (D.sub c d))
    (Q'.add_eqv_congr' (pair_sub_right D a c d)
      (Q'.neg_eqv_congr _ _ (pair_sub_right D b c d)))

private theorem norm_le_of_self_pair (D : GNSData) (a b : D.V)
    (h : D.B a a ≈ D.B a b) : D.B a a ≤ D.B b b := by
  have hx : D.B b a ≈ D.B a a :=
    Q'.eqv_trans _ _ _ (D.B_symm b a) (Q'.eqv_symm h)
  have he : D.B (D.sub b a) (D.sub b a) ≈ D.B b b + -(D.B a a) :=
    Q'.eqv_trans _ _ _ (D.B_sub_diag_expand b a)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hx))
        (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hx) (Q'.eqv_refl _)))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.var 1))) (.add (.neg (.var 1)) (.var 1)))
          (.add (.var 0) (.neg (.var 1))) (by decide)
          (fun | 0 => D.B b b | _ => D.B a a)))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (D.self_nonneg (D.sub b a)) (Q'.le_of_eqv he))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "U" => unit hw0 hw1 extent stage
local notation "r" => inversePartition hw0 hw1 extent stage
local notation "C" p => centered hw0 hw1 extent stage p

private theorem inversePartition_pos : (0 : Q') < r := by
  unfold inversePartition reciprocalTerm
  exact PositiveRationalCauchyReciprocal.term_pos _ _ _ _

/-- Dense centering contracts distances in the UNNORMALIZED original form. -/
theorem centered_distSq_le (p q : (F).V) :
    (F).distSqQ (C p) (C q) ≤ (F).distSqQ p q := by
  apply norm_le_of_self_pair
  exact Q'.eqv_trans _ _ _ (pair_sub_sub F (C p) (C q) (C p) (C q))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (centered_pair_right hw0 hw1 extent stage p p)
          (Q'.neg_eqv_congr _ _ (centered_pair_right hw0 hw1 extent stage p q)))
        (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr'
          (centered_pair_right hw0 hw1 extent stage q p)
          (Q'.neg_eqv_congr _ _ (centered_pair_right hw0 hw1 extent stage q q)))))
      (Q'.eqv_symm (pair_sub_sub F (C p) (C q) p q)))

/-- Actual centered polynomials, with the original supplied Cauchy rate. -/
def centeredCauchy (X : CauchyGNS F) : CauchyGNS F where
  seq n := C (X.seq n)
  modulus := X.modulus
  isCauchy := fun e he p q hp hq => Q'.le_trans' _ _ _
    (centered_distSq_le hw0 hw1 extent stage (X.seq p) (X.seq q))
    (X.isCauchy e he p q hp hq)

theorem centeredCauchy_modulus (X : CauchyGNS F) :
    (centeredCauchy hw0 hw1 extent stage X).modulus = X.modulus := rfl

theorem centeredCauchy_term_centered (X : CauchyGNS F) (n : Nat) :
    (F).B ((centeredCauchy hw0 hw1 extent stage X).seq n) U ≈ 0 :=
  centered_unit hw0 hw1 extent stage (X.seq n)

/-- The correct normalization is the reciprocal partition, not a unit norm. -/
theorem self_center_distance (p : (F).V) :
    (F).distSqQ p (C p) ≈ r * ((F).B p U * (F).B p U) := by
  have hm : mean hw0 hw1 extent stage p ≈ r*(F).B p U :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (pair_unit hw0 hw1 extent stage p)))
      (Q'.mul_comm_eqv _ _)
  have hcp : (F).B (C p) p ≈ (F).B p p + -((r*(F).B p U)*(F).B p U) :=
    Q'.eqv_trans _ _ _ ((F).B_add_left p ((F).smul (-(mean hw0 hw1 extent stage p)) U) p)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ ((F).B_smul_left _ U p)
          (Q'.eqv_trans _ _ _
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_eqv_congr _ _ hm))
              (Q'.mul_eqv_congr_left _ _ _ ((F).B_symm U p))) (Q'.neg_mul_eqv _ _))))
  have hpc := Q'.eqv_trans _ _ _ ((F).B_symm p (C p)) hcp
  have hcc := Q'.eqv_trans _ _ _ (centered_pair_right hw0 hw1 extent stage p p) hcp
  exact Q'.eqv_trans _ _ _ ((F).B_sub_diag_expand p (C p))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hpc))
      (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hpc) hcc))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 2))))))
          (.add (.neg (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 2)))))
            (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 2))))))
        (.mul (.var 1) (.mul (.var 2) (.var 2))) (by decide)
        (fun | 0 => (F).B p p | 1 => r | _ => (F).B p U)))

private theorem eventual_square_bound (s : Nat → Q')
    (h : CReal.ConvergesTo (fun n => CReal.ofQ' (s n)) CReal.czero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    ∃ N : Nat, ∀ n, N ≤ n → s n * s n ≤ epsilon := by
  let d := Q'.min' epsilon 1
  have hd : (0 : Q') < d := by
    unfold d Q'.min'
    split
    · exact he
    · decide
  obtain ⟨N, hN⟩ := h d hd
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨A, hA⟩ := hN n hn
  have hb := hA A (Nat.le_refl A)
  change s n ≤ 0+d ∧ 0 ≤ s n+d at hb
  have ha : Q'.abs (s n) ≤ d := Q'.abs_le_of_bounds
    (Q'.neg_le_of_zero_le_add hb.2) (by simpa only [Q'.zero_add'] using hb.1)
  have hs := Q'.mul_le_mul_of_nonneg ha ha (Q'.le_of_lt hd) (Q'.abs_nonneg (s n))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (s n)))
    (Q'.le_trans' _ _ _ hs
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ d (Q'.min_le_right (p := epsilon) (q := 1))
          (Q'.le_of_lt hd))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv d)) Q'.min_le_left)))

private theorem centered_null (X : CauchyGNS F)
    (horth : (F).cinnerCompl (Quotient.mk (cauchySetoid F) X) (embedV F U) = CReal.RCzero) :
    CauchyNull F X (centeredCauchy hw0 hw1 extent stage X) := by
  have hmean : CReal.ConvergesTo
      (fun n => CReal.ofQ' ((F).B (X.seq n) U)) CReal.czero :=
    CReal.convergesTo_limit_congr (CReal.convergesTo_ofQ'CauchySeq _
      ((F).cInnerQCauchy X (constCauchy F U))) (Quotient.exact horth)
  intro e he
  let t := e * ExpUBInstance.oneOver1p r
  have ht : (0 : Q') < t := Q'.mul_pos he (oneOver1p_pos _)
  obtain ⟨N, hN⟩ := eventual_square_bound _ hmean t ht
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (self_center_distance hw0 hw1 extent stage (X.seq n)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ r (hN n hn)
      (Q'.le_of_lt (inversePartition_pos hw0 hw1 extent stage)))
      (key_bound r e (Q'.le_of_lt (inversePartition_pos hw0 hw1 extent stage)) (Q'.le_of_lt he)))

/-- Completed orthogonality suffices; no termwise mean-zero input is required. -/
def centeredNullModulus (X : CauchyGNS F)
    (horth : (F).cinnerCompl (Quotient.mk (cauchySetoid F) X) (embedV F U) = CReal.RCzero) :
    CauchyNullModulus F X (centeredCauchy hw0 hw1 extent stage X) :=
  recoverNullModulus (centered_null hw0 hw1 extent stage X horth)

theorem centeredNullModulus_modulus (X : CauchyGNS F)
    (horth : (F).cinnerCompl (Quotient.mk (cauchySetoid F) X) (embedV F U) = CReal.RCzero)
    (e : Q') : (centeredNullModulus hw0 hw1 extent stage X horth).modulus e =
      X.modulus (nullTolerance e) := Nat.max_self _

theorem centeredCauchy_same_class (X : CauchyGNS F)
    (horth : (F).cinnerCompl (Quotient.mk (cauchySetoid F) X) (embedV F U) = CReal.RCzero) :
    Quotient.mk (cauchySetoid F) (centeredCauchy hw0 hw1 extent stage X) =
      Quotient.mk (cauchySetoid F) X :=
  (Quotient.sound (centeredNullModulus hw0 hw1 extent stage X horth).toCauchyNull).symm

#print axioms centered_distSq_le
#print axioms centeredCauchy
#print axioms centeredCauchy_modulus
#print axioms centeredCauchy_term_centered
#print axioms self_center_distance
#print axioms centeredNullModulus
#print axioms centeredNullModulus_modulus
#print axioms centeredCauchy_same_class

end YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
