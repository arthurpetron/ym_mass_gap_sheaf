/-
# Computed mixed rational-row Gram contractions

This leaf uses the EXISTING finiteProductGaussian, finiteLinearRow and
finiteRowDerivative. It computes the literal finite rational Gram sum and
derives the mixed derivative contraction, row-pair second moment and paired
square fourth moment, for every N (including zero) and every rational row.
The derivative contraction allows EVERY RatPoly as its multiplying insertion.
No Gaussian/moment/pullback law, Gram identity or product rule is assumed.

The finite evaluator integrates coordinates below N and evaluates variables
outside N at ONE. It does not preserve tail coefficients. In particular, the
padded constant monomials in row derivatives are handled under this SAME
evaluation, not falsely equated with polyConst in arbitrary coefficient probes.

Consumer: the literal correlated-row radial quartic/quadratic covariance in
the adaptive-score audit, Rational-row covariance section. The general sixth
moment and radial finite sums, actual transverse mode coefficients and their
CReal moduli, and ORIGINAL compact-Haar/section/source/OLD-center comparisons
remain separate obligations. No original-law pin, interacting uniform bound,
covariance bundle or physical gap is introduced. Root serializes compilation.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein

local infix:50 " ≈ " => Q'.eqv

/-- Literal computed Gram sum; no nondegeneracy or orthogonality premise. -/
def finiteRowGram (N : Nat) (b d : Nat → Q') : Q' :=
  qListSum ((List.range N).map fun i => b i * d i)

private theorem sum_congr (f g : Nat → Q') (h : ∀ i, f i ≈ g i) :
    ∀ ids : List Nat, qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [] => Q'.eqv_refl _
  | i :: ids => Q'.add_eqv_congr' (h i) (sum_congr f g h ids)

/-- Symmetry of the computed SAME rational Gram sum. -/
theorem finiteRowGram_symm (N : Nat) (b d : Nat → Q') :
    finiteRowGram N b d ≈ finiteRowGram N d b :=
  sum_congr _ _ (fun i => Q'.mul_comm_eqv (b i) (d i)) (List.range N)

private def derivativeOn (d : Nat → Q') (p : RatPoly) : List Nat → RatPoly
  | [] => polyZero
  | i :: ids => polyAdd (polySmul (d i) (ratDerivative i p)) (derivativeOn d p ids)

private theorem derivativeOn_pin (N : Nat) (d : Nat → Q') (p : RatPoly) :
    finiteRowDerivative N d p = derivativeOn d p (List.range N) := by
  unfold finiteRowDerivative
  generalize List.range N = ids
  induction ids with
  | nil => rfl
  | cons i ids ih =>
      exact congrArg (fun q => polyAdd (polySmul (d i) (ratDerivative i p)) q) ih

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (a : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul a p) ≈ a * finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) a p

private theorem gaussian_smul_mul (N : Nat) (a : Q') (q p : RatPoly) :
    finiteProductGaussian N (polyMul (polySmul a q) p) ≈
      a * finiteProductGaussian N (polyMul q p) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.polyMul_smul_left a q p))
    (gaussian_smul N a (polyMul q p))

private theorem derivativeOn_linearRow (N : Nat) (d b : Nat → Q') (p : RatPoly) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i<N) →
      finiteProductGaussian N (polyMul (derivativeOn d (finiteLinearRow N b) ids) p) ≈
        qListSum (ids.map fun i => d i * b i) * finiteProductGaussian N p
  | [], _ => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | i :: ids, hids => by
      have hfirst := Q'.eqv_trans _ _ _
        (gaussian_smul_mul N (d i) (ratDerivative i (finiteLinearRow N b)) p)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (finiteLinearRow_coordinate_derivative N i (hids i List.mem_cons_self) b p))
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
      change finiteProductGaussian N
        (polyMul (polyAdd (polySmul (d i) (ratDerivative i (finiteLinearRow N b)))
          (derivativeOn d (finiteLinearRow N b) ids)) p) ≈ _
      rw [polyMul_add_left_exact]
      simp only [List.map_cons, qListSum]
      exact Q'.eqv_trans _ _ _ (gaussian_add N _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hfirst
            (derivativeOn_linearRow N d b p ids
              (fun j hj => hids j (List.mem_cons_of_mem i hj))))
          (Q'.eqv_symm (q_add_mul _ _ _)))

/-- Computed mixed derivative contraction on actual rows and EVERY insertion.
The Gram order is (direction row, differentiated row). -/
theorem finiteRowDerivative_mixed_contraction (N : Nat) (d b : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul (finiteRowDerivative N d (finiteLinearRow N b)) p) ≈
      finiteRowGram N d b * finiteProductGaussian N p := by
  rw [derivativeOn_pin]
  exact derivativeOn_linearRow N d b p (List.range N)
    (fun _ hi => List.mem_range.mp hi)

private theorem monoMul_nil_right (m : List Nat) : monoMul m [] = m := by
  cases m <;> rfl

private theorem polyMul_one_right : ∀ p : RatPoly, RatPolyCoeffEqv (polyMul p polyOne) p
  | [] => RatPolyCoeffEqv.refl _
  | term :: p => by
      intro weight
      rcases term with ⟨m,a⟩
      change (a * 1) * weight (monoMul m []) + ratWeightedSum weight (polyMul p polyOne) ≈
        a * weight m + ratWeightedSum weight p
      rw [monoMul_nil_right]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv a))
        (polyMul_one_right p weight)

private theorem gaussianMono_nil (N : Nat) : finiteGaussianMono N [] = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change gaussianMoment1 ([].getD N 0) * finiteGaussianMono N [] = 1
      rw [List.getD_nil, ih]
      rfl

private theorem gaussian_one (N : Nat) : finiteProductGaussian N polyOne ≈ 1 := by
  change 1 * finiteGaussianMono N [] + 0 ≈ 1
  rw [gaussianMono_nil]
  decide

/-- Actual mixed second moment of the existing rational linear rows. -/
theorem finiteProductGaussian_row_pair (N : Nat) (b d : Nat → Q') :
    finiteProductGaussian N (polyMul (finiteLinearRow N b) (finiteLinearRow N d)) ≈
      finiteRowGram N b d := by
  have hderivative : finiteProductGaussian N (finiteRowDerivative N b (finiteLinearRow N d)) ≈
      finiteRowGram N b d :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (finiteProductGaussian_coeffEqv N
        (polyMul_one_right (finiteRowDerivative N b (finiteLinearRow N d)))))
      (Q'.eqv_trans _ _ _ (finiteRowDerivative_mixed_contraction N b d polyOne)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (gaussian_one N))
          (Q'.mul_one_eqv _)))
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_linearRow_stein N b (finiteLinearRow N d)) hderivative

private theorem swap_first_two (p q r : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyMul q r)) (polyMul q (polyMul p r)) :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_assoc p q r))
    (RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm p q).mul_right r)
      (RatPolyCoeffEqv.mul_assoc q p r))

private theorem row_square_derivative_contraction (N : Nat) (b d : Nat → Q') :
    finiteProductGaussian N
      (polyMul (finiteLinearRow N b)
        (finiteRowDerivative N b (polyMul (finiteLinearRow N d) (finiteLinearRow N d)))) ≈
      finiteRowGram N b d * finiteProductGaussian N
          (polyMul (finiteLinearRow N b) (finiteLinearRow N d)) +
        finiteRowGram N b d * finiteProductGaussian N
          (polyMul (finiteLinearRow N b) (finiteLinearRow N d)) := by
  let B := finiteLinearRow N b
  let D := finiteLinearRow N d
  let C := finiteRowDerivative N b D
  have hleft : RatPolyCoeffEqv (polyMul B (polyMul C D)) (polyMul C (polyMul B D)) :=
    swap_first_two B C D
  have hright : RatPolyCoeffEqv (polyMul B (polyMul D C)) (polyMul C (polyMul B D)) :=
    RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm D C).mul_left B) hleft
  have hderivative := (finiteRowDerivative_mul N b D D).mul_left B
  have hsplit := RatPolyCoeffEqv.trans hderivative
    (RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_add_right B (polyMul C D) (polyMul D C))
      (RatPolyCoeffEqv.add hleft hright))
  exact Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N hsplit)
    (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
      (Q'.add_eqv_congr'
        (finiteRowDerivative_mixed_contraction N b d (polyMul B D))
        (finiteRowDerivative_mixed_contraction N b d (polyMul B D))))

private theorem fourth_scalar (a c g : Q') :
    a * c + (g * g + g * g) ≈ a * c + 2 * (g * g) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.mul (.const 2) (.mul (.var 2) (.var 2))))
    (by decide) (fun | 0 => a | 1 => c | _ => g)

/-- Actual paired-square fourth moment, with the computed finite Gram sum.
Every finite dimension and every rational row are included, without division,
nonzero variance, independence or orthogonal-change-of-basis hypotheses. -/
theorem finiteProductGaussian_row_square_pair (N : Nat) (b d : Nat → Q') :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N b))
        (polyMul (finiteLinearRow N d) (finiteLinearRow N d))) ≈
      finiteRowNorm2 N b * finiteRowNorm2 N d +
        2 * (finiteRowGram N b d * finiteRowGram N b d) := by
  let B := finiteLinearRow N b
  let D := finiteLinearRow N d
  have hfirst : finiteProductGaussian N
      (polyMul (finiteRowDerivative N b B) (polyMul D D)) ≈
      finiteRowNorm2 N b * finiteRowNorm2 N d :=
    Q'.eqv_trans _ _ _ (finiteRowDerivative_mixed_contraction N b b (polyMul D D))
      (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N d d))
  have hsecond : finiteProductGaussian N
      (polyMul B (finiteRowDerivative N b (polyMul D D))) ≈
      finiteRowGram N b d * finiteRowGram N b d +
        finiteRowGram N b d * finiteRowGram N b d :=
    Q'.eqv_trans _ _ _ (row_square_derivative_contraction N b d)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N b d))
        (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N b d)))
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_assoc B B (polyMul D D)))
    (Q'.eqv_trans _ _ _ (finiteProductGaussian_linearRow_stein N b (polyMul B (polyMul D D)))
      (Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N (finiteRowDerivative_mul N b B (polyMul D D)))
        (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst hsecond)
            (fourth_scalar (finiteRowNorm2 N b) (finiteRowNorm2 N d) (finiteRowGram N b d))))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram.finiteRowGram_symm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram.finiteRowDerivative_mixed_contraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram.finiteProductGaussian_row_pair
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram.finiteProductGaussian_row_square_pair
