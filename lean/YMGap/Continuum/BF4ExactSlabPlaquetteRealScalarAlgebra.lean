/-
# Modulus-bearing scalar arithmetic and the ORIGINAL completed action laws

Scalar sums and products carry computed QCauchy data, not an additional
convergence assumption. The completed action respects this arithmetic by
the original plaquette coefficient identities. These are laws for scalars
with supplied moduli; no modulus for an arbitrary legacy RC is selected.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar

def scalarAddCauchy (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) :
    QCauchy (CReal.add s t).approx :=
  let h := InnerRegularity.add (show InnerRegularity s from ⟨cs.M, cs.bound⟩)
    (show InnerRegularity t from ⟨ct.M, ct.bound⟩)
  ⟨h.rate, h.regular⟩

def scalarNegCauchy (s : CReal) (cs : QCauchy s.approx) : QCauchy (CReal.neg s).approx :=
  let h := InnerRegularity.neg (show InnerRegularity s from ⟨cs.M, cs.bound⟩)
  ⟨h.rate, h.regular⟩

def productCeiling (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) : Q' :=
  Q'.max' (scalarCeiling s cs) (scalarCeiling t ct)

theorem productCeiling_pos (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) :
    (0 : Q') < productCeiling s t cs ct := by
  have hs : (0 : Q') < scalarCeiling s cs :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.pos_of_lt_of_le hs (Q'.le_max'_left _ _)

/-- Multiplication uses tail ceilings computed from the two input moduli. -/
def scalarMulCauchy (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) :
    QCauchy (CReal.mul s t).approx where
  M epsilon := max (max (cs.M 1) (ct.M 1))
    (max (cs.M (BoundedRationalCauchyProduct.tolerance (productCeiling s t cs ct) (productCeiling_pos s t cs ct) epsilon))
      (ct.M (BoundedRationalCauchyProduct.tolerance (productCeiling s t cs ct) (productCeiling_pos s t cs ct) epsilon)))
  bound := by
    intro epsilon he p q hp hq
    let B := productCeiling s t cs ct
    let hB := productCeiling_pos s t cs ct
    let delta := BoundedRationalCauchyProduct.tolerance B hB epsilon
    have hd := BoundedRationalCauchyProduct.tolerance_pos B hB he
    have stageS (i : Nat) (hi : max (max (cs.M 1) (ct.M 1)) (max (cs.M delta) (ct.M delta)) ≤ i) :
        cs.M delta ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hi
    have stageT (i : Nat) (hi : max (max (cs.M 1) (ct.M 1)) (max (cs.M delta) (ct.M delta)) ≤ i) :
        ct.M delta ≤ i := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hi
    have step (i j : Nat)
        (hi : max (max (cs.M 1) (ct.M 1)) (max (cs.M delta) (ct.M delta)) ≤ i)
        (hj : max (max (cs.M 1) (ct.M 1)) (max (cs.M delta) (ct.M delta)) ≤ j) :
        s.approx i * t.approx i ≤ s.approx j * t.approx j + epsilon := by
      have hsi : Q'.abs (s.approx i) ≤ B :=
        Q'.le_trans' _ _ _ (scalar_approx_le_ceiling s cs i
          (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hi)) (Q'.le_max'_left _ _)
      have htj : Q'.abs (t.approx j) ≤ B :=
        Q'.le_trans' _ _ _ (scalar_approx_le_ceiling t ct j
          (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hj)) (Q'.le_max'_right _ _)
      exact Q'.le_trans' _ _ _
        (BoundedRationalCauchyProduct.product_close _ _ _ _ B delta (Q'.le_of_lt hB) (Q'.le_of_lt hd) hsi htj
          (cs.bound delta hd i j (stageS i hi) (stageS j hj)) (ct.bound delta hd i j (stageT i hi) (stageT j hj)))
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (BoundedRationalCauchyProduct.tolerance_budget B hB epsilon)))
    exact ⟨step p q hp hq, step q p hq hp⟩

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

theorem completedRealSmul_addScalar (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 (CReal.add s t) (scalarAddCauchy s t cs ct) x =
      completedAdd w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) (completedRealSmul w hw0 hw1 t ct x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨(RatPolyCoeffEqv.add_smul_same (s.approx n) (t.approx n) (lower (X.seq n))).symm,
     (RatPolyCoeffEqv.add_smul_same (s.approx n) (t.approx n) (upper (X.seq n))).symm⟩)

theorem completedRealSmul_mul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 s cs (completedRealSmul w hw0 hw1 t ct x) =
      completedRealSmul w hw0 hw1 (CReal.mul s t) (scalarMulCauchy s t cs ct) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.smul_assoc (s.approx n) (t.approx n) (lower (X.seq n)),
     RatPolyCoeffEqv.smul_assoc (s.approx n) (t.approx n) (upper (X.seq n))⟩)

theorem completedRealSmul_neg (s : CReal) (cs : QCauchy s.approx) (x : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 s cs (completedNeg w hw0 hw1 x) =
      completedNeg w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) := by
  have hleft := completedRealSmul_mul w hw0 hw1 s (ofQ' (-1)) cs (rationalCauchy (-1)) x
  have hright := completedRealSmul_mul w hw0 hw1 (ofQ' (-1)) s (rationalCauchy (-1)) cs x
  rw [completedRealSmul_ofQ'] at hleft hright
  exact hleft.trans ((completedRealSmul_congr w hw0 hw1 _ _ _ _ (CRealAlg.cmul_comm s (ofQ' (-1))) x).trans hright.symm)

theorem completedRealSmul_sub (s : CReal) (cs : QCauchy s.approx) (x y : Completion w hw0 hw1 half) :
    completedRealSmul w hw0 hw1 s cs (completedSub w hw0 hw1 x y) =
      completedSub w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) (completedRealSmul w hw0 hw1 s cs y) := by
  unfold completedSub
  rw [completedRealSmul_add, completedRealSmul_neg]

theorem completedInner_realSmul_diagonal (s : CReal) (cs : QCauchy s.approx) (x : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) (completedRealSmul w hw0 hw1 s cs x) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (completedInner w hw0 hw1 x x)) := by
  rw [completedInner_realSmul_left, completedInner_realSmul_right]

theorem completedDist_realSmul (s : CReal) (cs : QCauchy s.approx) (x y : Completion w hw0 hw1 half) :
    completedDist w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) (completedRealSmul w hw0 hw1 s cs y) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (completedDist w hw0 hw1 x y)) := by
  unfold completedDist
  rw [← completedRealSmul_sub, completedInner_realSmul_diagonal]

end YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.scalarAddCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.scalarNegCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.productCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.productCeiling_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.scalarMulCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedRealSmul_addScalar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedRealSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedRealSmul_neg
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedRealSmul_sub
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedInner_realSmul_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra.completedDist_realSmul
