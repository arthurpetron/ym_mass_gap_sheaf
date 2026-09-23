/-
# Unit-vacuum projection algebra for a generic GNS carrier

This module records the finite algebra of subtracting the component along a
unit vector.  It uses only the bilinear form laws of `GNSData`; in particular,
it does not assume any distributivity law for the carrier scalar action.
-/

import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.GNSUnitVacuumProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             first
             | ac_rfl
             | (simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]; omega)))

/-- Subtract the component of `a` along `vacuum`. -/
def center (D : GNSData) (vacuum a : D.V) : D.V :=
  D.sub a (D.smul (D.B a vacuum) vacuum)

/-- Pairing two centered vectors subtracts the product of their vacuum
coefficients.  The proof expands the form and requires no carrier-level
scalar distributivity. -/
theorem center_pairing_eqv
    (D : GNSData) (vacuum : D.V)
    (hunit : D.B vacuum vacuum ≈ 1) (a b : D.V) :
    D.B (center D vacuum a) (center D vacuum b) ≈
      D.B a b + -(D.B a vacuum * D.B b vacuum) := by
  let ma := D.B a vacuum
  let mb := D.B b vacuum
  have hab : D.B a (D.smul mb vacuum) ≈ mb * ma := by
    exact D.B_smul_right mb a vacuum
  have hba : D.B (D.smul ma vacuum) b ≈ ma * mb := by
    exact Q'.eqv_trans _ _ _ (D.B_smul_left ma vacuum b)
      (Q'.mul_eqv_congr_left ma _ _ (D.B_symm vacuum b))
  have hvv : D.B (D.smul ma vacuum) (D.smul mb vacuum) ≈ ma * mb := by
    refine Q'.eqv_trans _ (ma * (mb * D.B vacuum vacuum)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (D.B_smul_left ma vacuum (D.smul mb vacuum))
        (Q'.mul_eqv_congr_left ma _ _ (D.B_smul_right mb vacuum vacuum))
    refine Q'.eqv_trans _ (ma * (mb * 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left ma _ _
        (Q'.mul_eqv_congr_left mb _ _ hunit)
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ma _ _ (Q'.mul_one_eqv mb))
      (Q'.eqv_refl _)
  unfold center
  refine Q'.eqv_trans _
    ((D.B a b + -(D.B a (D.smul mb vacuum))) +
      ((-(D.B (D.smul ma vacuum) b)) +
        D.B (D.smul ma vacuum) (D.smul mb vacuum))) _ ?_ ?_
  · unfold GNSData.sub
    refine Q'.eqv_trans _ _ _
      (D.B_add_left a (D.neg (D.smul ma vacuum))
        (D.add b (D.neg (D.smul mb vacuum)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (D.B_add_right a b (D.neg (D.smul mb vacuum)))
        (D.B_add_right (D.neg (D.smul ma vacuum)) b
          (D.neg (D.smul mb vacuum)))) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_right a _))
      (Q'.add_eqv_congr'
        (D.B_neg_left _ b)
        (Q'.eqv_trans _ _ _ (D.B_neg_left _ (D.neg _))
          (Q'.eqv_trans _ _ _
            (Q'.neg_eqv_congr _ _ (D.B_neg_right _ _))
            (Q'.neg_neg_eqv _))))
  · refine Q'.eqv_trans _
      (((D.B a b) + (-(mb * ma))) + ((-(ma * mb)) + (ma * mb))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hab))
        (Q'.add_eqv_congr'
          (Q'.neg_eqv_congr _ _ hba)
          hvv)
    change
      ((D.B a b + -(mb * ma)) + (-(ma * mb) + ma * mb)) ≈
        D.B a b + -(ma * mb)
    q_ring

/-- Pairing a vector with its centered projection subtracts its squared
vacuum coefficient. -/
theorem pair_center_self_eqv
    (D : GNSData) (vacuum : D.V)
    (a : D.V) :
    D.B a (center D vacuum a) ≈
      D.B a a + -(D.B a vacuum * D.B a vacuum) := by
  let ma := D.B a vacuum
  unfold center GNSData.sub
  refine Q'.eqv_trans _ _ _
    (D.B_add_right a a (D.neg (D.smul ma vacuum))) ?_
  refine Q'.eqv_trans _
    (D.B a a + -(ma * ma)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (D.B_neg_right a (D.smul ma vacuum))
        (Q'.neg_eqv_congr _ _
          (D.B_smul_right ma a vacuum)))
  change D.B a a + -(ma * ma) ≈ D.B a a + -(ma * ma)
  exact Q'.eqv_refl _

/-- Centering subtracts exactly the squared vacuum coefficient from the
diagonal form. -/
theorem center_diag_eqv
    (D : GNSData) (vacuum : D.V)
    (hunit : D.B vacuum vacuum ≈ 1) (a : D.V) :
    D.B (center D vacuum a) (center D vacuum a) ≈
      D.B a a + -(D.B a vacuum * D.B a vacuum) :=
  center_pairing_eqv D vacuum hunit a a

/-- Orthogonal projection onto the complement of a unit vector is
nonexpansive in squared GNS distance. -/
theorem center_distSq_le
    (D : GNSData) (vacuum : D.V)
    (hunit : D.B vacuum vacuum ≈ 1) (a b : D.V) :
    D.distSqQ (center D vacuum a) (center D vacuum b) ≤ D.distSqQ a b := by
  let ma := D.B a vacuum
  let mb := D.B b vacuum
  have hdist : D.distSqQ (center D vacuum a) (center D vacuum b) ≈
      D.distSqQ a b + -((ma + -mb) * (ma + -mb)) := by
    refine Q'.eqv_trans _
      (((D.B (center D vacuum a) (center D vacuum a)) +
          (-(D.B (center D vacuum a) (center D vacuum b)))) +
        ((-(D.B (center D vacuum a) (center D vacuum b))) +
          D.B (center D vacuum b) (center D vacuum b))) _
      (D.B_sub_diag_expand _ _) ?_
    have haa := center_pairing_eqv D vacuum hunit a a
    have hab := center_pairing_eqv D vacuum hunit a b
    have hbb := center_pairing_eqv D vacuum hunit b b
    refine Q'.eqv_trans _
      (((D.B a a + -(ma * ma)) + (-(D.B a b + -(ma * mb)))) +
        ((-(D.B a b + -(ma * mb))) + (D.B b b + -(mb * mb)))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr' haa (Q'.neg_eqv_congr _ _ hab))
        (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hab) hbb)
    unfold GNSData.distSqQ
    refine Q'.eqv_trans _
      ((((D.B a a) + (-(D.B a b))) +
          ((-(D.B a b)) + (D.B b b))) +
        -((ma + -mb) * (ma + -mb))) _ ?_ ?_
    · q_ring
    exact Q'.add_eqv_congr' (Q'.eqv_symm (D.B_sub_diag_expand a b))
      (Q'.eqv_refl _)
  have hsquare : (0 : Q') ≤ (ma + -mb) * (ma + -mb) :=
    SumOfSquares.q_mul_self_nonneg (ma + -mb)
  have hneg : -((ma + -mb) * (ma + -mb)) ≤ (0 : Q') := by
    exact Q'.le_trans' _ (-(0 : Q')) 0 (Q'.neg_le_neg hsquare)
      (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
  have hupper : D.distSqQ a b + -((ma + -mb) * (ma + -mb)) ≤
      D.distSqQ a b := by
    have h := Q'.add_le_add_left (D.distSqQ a b) _ _ hneg
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv (D.distSqQ a b)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) hupper

/-- The squared distance from a vector to its centered projection is exactly
the square of its vacuum coefficient. -/
theorem self_center_distSq_eqv
    (D : GNSData) (vacuum : D.V)
    (hunit : D.B vacuum vacuum ≈ 1) (a : D.V) :
    D.distSqQ a (center D vacuum a) ≈
      D.B a vacuum * D.B a vacuum := by
  let ma := D.B a vacuum
  unfold GNSData.distSqQ
  refine Q'.eqv_trans _
    (((D.B a a) + (-(D.B a (center D vacuum a)))) +
      ((-(D.B a (center D vacuum a))) +
        D.B (center D vacuum a) (center D vacuum a))) _
    (D.B_sub_diag_expand _ _) ?_
  have hac := pair_center_self_eqv D vacuum a
  have hcc := center_diag_eqv D vacuum hunit a
  refine Q'.eqv_trans _
    (((D.B a a) + (-(D.B a a + -(ma * ma)))) +
      ((-(D.B a a + -(ma * ma))) +
        (D.B a a + -(ma * ma)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hac))
      (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hac) hcc)
  change
    D.B a a + -(D.B a a + -(ma * ma)) +
        (-(D.B a a + -(ma * ma)) + (D.B a a + -(ma * ma))) ≈
      ma * ma
  q_ring

#print axioms center
#print axioms center_pairing_eqv
#print axioms pair_center_self_eqv
#print axioms center_diag_eqv
#print axioms center_distSq_le
#print axioms self_center_distSq_eqv

end YMGap.Continuum.GNSUnitVacuumProjection
