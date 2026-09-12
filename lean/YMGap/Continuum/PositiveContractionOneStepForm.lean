/-
# A positive contraction contracts its own one-step form

For a symmetric positive contraction P, put B_P(a,b) = B(a,Pb).
This positive form is generally different from B, and need not be equivalent
to it. Nevertheless P is contractive for B_P as well. The elementary identity

  P - P^3 = (I-P)P(I-P) + 2 P(I-P)P

proves this without a spectral theorem, square root, inverse, or strict gap.
The same rational symbol therefore acts on the completion of B_P. This is a
generic algebraic theorem; a physical application must identify B_P with its
actual reflected joint law. No cross-cutoff compatibility is inferred.
-/

import YMGap.Continuum.LinearTransferOperator

namespace YMGap.Continuum.PositiveContractionOneStepForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-- The one-step form retains exactly the original carrier operations. -/
def oneStepGNSData (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.B a (P a)) : GNSData :=
  { D with
    B := fun a b => D.B a (P b)
    B_congr_left := fun b h => D.B_congr_left (P b) h
    B_add_left := fun a b c => D.B_add_left a b (P c)
    B_smul_left := fun s a b => D.B_smul_left s a (P b)
    B_symm := fun a b => Q'.eqv_trans _ _ _ (hsa a b) (D.B_symm (P a) b)
    self_nonneg := hpos }

private theorem sub_diagonal (D : GNSData) (a b : D.V) :
    D.B (D.sub a b) (D.sub a b) ≈
      (D.B a a + -(D.B a b)) + (-(D.B b a) + D.B b b) := by
  refine Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg b) (D.sub a b)) ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _ _ _ (D.B_add_right a a (D.neg b))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_right a b))
  · refine Q'.eqv_trans _ _ _ (D.B_neg_left b (D.sub a b)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (D.B_add_right b a (D.neg b))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv _ _) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (D.B_neg_right b b)) (Q'.neg_neg_eqv _))

private theorem neg_num (a : Q') : (-a).num = -a.num := rfl

private theorem three_moment_identity (a b c : Q') :
    (((a + -b) + (-b + c)) + ((b + -c) + (b + -c))) ≈ a + -c := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- The cubic contraction follows from two nonnegative quadratic forms. -/
theorem oneStep_contraction (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.B a (P a))
    (hupper : ∀ a, D.B a (P a) ≤ D.B a a) (a : D.V) :
    D.B (P a) (P (P a)) ≤ D.B a (P a) := by
  let E := oneStepGNSData D P hsa hpos
  have he : E.B (E.sub a (P a)) (E.sub a (P a)) ≈
      (D.B a (P a) + -(D.B (P a) (P a))) +
        (-(D.B (P a) (P a)) + D.B (P a) (P (P a))) := by
    refine Q'.eqv_trans _ _ _ (sub_diagonal E a (P a)) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (hsa a (P a))))
      (Q'.eqv_refl _)
  have hfirst := Q'.le_trans' _ _ _ (E.self_nonneg (E.sub a (P a))) (Q'.le_of_eqv he)
  have hsecond := Q'.sub_nonneg_of_le (hupper (P a))
  have hsum := Q'.zero_le_add _ _ hfirst (Q'.zero_le_add _ _ hsecond hsecond)
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (three_moment_identity _ _ _))

/-- Rational subtraction laws are unchanged by the new form. -/
def oneStepSmulGNSData (D : SmulGNSData) (P : D.toGNSData.V → D.toGNSData.V)
    (hsa : ∀ a b, D.toGNSData.B a (P b) ≈ D.toGNSData.B (P a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (P a)) : SmulGNSData where
  toGNSData := oneStepGNSData D.toGNSData P hsa hpos
  smul_sub := D.smul_sub

/-- The SAME action is a contraction on the one-step form completion. -/
def oneStepSymbol (D : SmulGNSData) (S : DiagonalTransferSymbol D)
    (hsub : ∀ a b, D.toGNSData.veq (S.Dv (D.toGNSData.sub a b))
      (D.toGNSData.sub (S.Dv a) (S.Dv b)))
    (hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a))
    (hupper : ∀ a, D.toGNSData.B a (S.Dv a) ≤ D.toGNSData.B a a) :
    DiagonalTransferSymbol (oneStepSmulGNSData D S.Dv hsa hpos) where
  Dv := S.Dv
  Dv_congr := S.Dv_congr
  Dv_add := S.Dv_add
  Dv_smul := S.Dv_smul
  distSqQ_Dv := by
    intro a b
    let E := oneStepGNSData D.toGNSData S.Dv hsa hpos
    have he := E.B_diag_congr (D.toGNSData.veq_symm (hsub a b))
    exact le_of_eqv_le he
      (oneStep_contraction D.toGNSData S.Dv hsa hpos hupper (D.toGNSData.sub a b))

end YMGap.Continuum.PositiveContractionOneStepForm

#print axioms YMGap.Continuum.PositiveContractionOneStepForm.oneStepGNSData
#print axioms YMGap.Continuum.PositiveContractionOneStepForm.oneStep_contraction
#print axioms YMGap.Continuum.PositiveContractionOneStepForm.oneStepSmulGNSData
#print axioms YMGap.Continuum.PositiveContractionOneStepForm.oneStepSymbol
