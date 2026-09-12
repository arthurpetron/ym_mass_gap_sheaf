/-
# A constructed cofinal cutoff-uniform strict form gap on the actual BF4 sector

The actual anchored-head estimate and raw-tail absorption give
N(f) <= (1+3*C(w))*E(f), with E=2*(N-P), at every K>=K0(w).
This module computes q(w)=(1+6*C(w))/(2+6*C(w)), proves 0<q(w)<1,
and bounds the ORIGINAL physical matrix quadratic of EVERY centered
coefficient by q(w) times its ORIGINAL stationary squared norm.

This is a strict form gap for the code's conditional kernel on its finite
vacuum component, uniform in representation cutoff after an explicit onset.
It is not yet a theorem about the completed reflected carrier or geometric
Euclidean time. The coefficient-independent rate depends explicitly on w.
Scope: SU(2), extent one, 0<w<=1/2. No coupling-uniform, volume/spacing,
continuum QFT, or Clay mass-gap claim is made.
-/

import YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound

namespace YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Exact finite-data numerator: all nome dependence is explicit. -/
def gapNumerator (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  1 + 6 * headEnergyConstant w hw

theorem gapNumerator_pos (w : Q') (hw : (0 : Q') ≤ w) : (0 : Q') < gapNumerator w hw :=
  Q'.add_pos (by decide) (Q'.mul_pos (by decide) (headEnergyConstant_pos w hw))

def gapDenominator (w : Q') (hw : (0 : Q') ≤ w) : Q' := 1 + gapNumerator w hw

theorem gapDenominator_pos (w : Q') (hw : (0 : Q') ≤ w) : (0 : Q') < gapDenominator w hw :=
  Q'.add_pos (by decide) (gapNumerator_pos w hw)

/-- One computable rational rate for all coefficients and all later cutoffs.
This definition does not contain the varying representation cutoff K. -/
def cutoffUniformRate (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (gapNumerator w hw) (gapDenominator w hw) (gapDenominator_pos w hw)

theorem cutoffUniformRate_pos (w : Q') (hw : (0 : Q') ≤ w) : (0 : Q') < cutoffUniformRate w hw :=
  Q'.divPos_pos _ _ _ (gapNumerator_pos w hw)

private theorem lt_one_add (a : Q') : a < 1 + a := by
  show a.num * (((1 : Q') + a).den : Int) < ((1 : Q') + a).num * (a.den : Int)
  rw [Q'.add_den_cast, Q'.add_num_cast]
  change a.num * (1 * (a.den : Int)) < (1 * (a.den : Int) + a.num * 1) * (a.den : Int)
  simp only [Int.one_mul, Int.mul_one, Int.add_mul]
  have hs := Int.mul_pos (show (0 : Int) < (a.den : Int) from by exact_mod_cast a.den_pos)
    (show (0 : Int) < (a.den : Int) from by exact_mod_cast a.den_pos)
  omega

theorem cutoffUniformRate_lt_one (w : Q') (hw : (0 : Q') ≤ w) : cutoffUniformRate w hw < (1 : Q') := by
  let p := gapNumerator w hw
  let q := gapDenominator w hw
  let hq := gapDenominator_pos w hw
  have h := Q'.mul_lt_mul_of_pos_left (Q'.recipPos_pos q hq) (lt_one_add p)
  have hr : Q'.recipPos q hq * q ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv q hq)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv p (Q'.recipPos q hq))) h)
    (Q'.le_of_eqv hr)

private theorem gap_polynomial (C N P : Q') :
    (1 + 3 * C) * ((N + N) + -(P + P)) + -N ≈
      (1 + 6 * C) * N + -((1 + (1 + 6 * C)) * P) := by
  let c := PolyExpr.var 0
  let n := PolyExpr.var 1
  let p := PolyExpr.var 2
  let a : PolyExpr := .add (.const 1) (.mul (.const 3) c)
  let b : PolyExpr := .add (.const 1) (.mul (.const 6) c)
  let left : PolyExpr := .add (.mul a (.add (.add n n) (.neg (.add p p)))) (.neg n)
  let right : PolyExpr := .add (.mul b n) (.neg (.mul (.add (.const 1) b) p))
  let valuation := fun i => if i = 0 then C else if i = 1 then N else P
  have h := poly_identity_of_normal_eq left right (by decide) valuation
  simpa [left, right, a, b, c, n, p, valuation, RingNormaliser.eval] using h

private theorem division_regroup (p N q : Q') (hq : (0 : Q') < q) :
    Q'.divPos (p * N) q hq ≈ Q'.divPos p q hq * N := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ (p * (N * Q'.recipPos q hq)) _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (p * (Q'.recipPos q hq * N)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- The actual physical quadratic has a strict, common cofinal-cutoff rate
on EVERY stationary-mean-zero coefficient. No analytic premise remains. -/
theorem matrix_le_cutoffUniformRate {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (K : Nat) (hK : headBoundStart w ≤ K) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) K 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) K 0 f ≤
      cutoffUniformRate w (Q'.le_of_lt hw0) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) K 0 f := by
  let hw' := Q'.le_of_lt hw0
  let N := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' K 0 f
  let P := centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw' K 0 f
  let num := gapNumerator w hw'
  let den := gapDenominator w hw'
  have henergy := centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit w hw' K 0 f
  have hn := centered_norm_le_coercivity_mul_energy hw0 hw K hK f hcenter
  have hbound : N ≤ coercivityConstant w hw' * ((N + N) + -(P + P)) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ henergy))
  have hscaled : den * P ≤ num * N := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbound)
      (Q'.le_of_eqv (gap_polynomial (headEnergyConstant w hw') N P))
  have hdiv := Q'.le_divPos_of_mul_le (num * N) den (gapDenominator_pos w hw')
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv P den)) hscaled)
  exact Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv (division_regroup num N den _))

/-- Reflection positivity makes the same strict upper bound absolute. -/
theorem abs_matrix_le_cutoffUniformRate {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (K : Nat) (hK : headBoundStart w ≤ K) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) K 0 f ≈ 0) :
    Q'.abs (centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) K 0 f) ≤
      cutoffUniformRate w (Q'.le_of_lt hw0) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) K 0 f := by
  unfold Q'.abs
  rw [if_pos (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative w (Q'.le_of_lt hw0) K 0 f)]
  exact matrix_le_cutoffUniformRate hw0 hw K hK f hcenter

end YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap

#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.gapNumerator
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.gapNumerator_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.gapDenominator
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.gapDenominator_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.cutoffUniformRate
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.cutoffUniformRate_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.cutoffUniformRate_lt_one
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.matrix_le_cutoffUniformRate
#print axioms YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap.abs_matrix_le_cutoffUniformRate
