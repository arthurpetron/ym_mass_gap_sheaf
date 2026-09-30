/-
# Common-mass quadratic response cancellation

A positive partition cap forces the shared mass parameter to be positive.
The detector lower bound and quadratic-cost upper bound then cancel that
common mass exactly, retaining the displayed rational response constant.
This module is scalar algebra only; it carries no analytic estimate.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Soundness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalCommonQuadraticResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem cancelCommonMassLeft (ell Q : Q') (hQ : (0 : Q') < Q) :
    (((ell*Q)*(ell*Q))*Q'.recipPos Q hQ) ≈ ((ell*ell)*Q) := by
  have hQR : ((ell*Q)*Q'.recipPos Q hQ).eqv ell := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ell Q (Q'.recipPos Q hQ)) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ell _ _ (Q'.mul_recipPos_eqv Q hQ))
      (Q'.mul_one_eqv ell)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (ell*Q) (ell*Q) (Q'.recipPos Q hQ)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ell*Q) ((ell*Q)*Q'.recipPos Q hQ) ell hQR) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (ell*Q) ell) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv ell ell Q)

private theorem cancelCommonMassRight (N C Q : Q') (hQ : (0 : Q') < Q) :
    (N*(C*Q))*Q'.recipPos Q hQ ≈ N*C := by
  have hQR : ((C*Q)*Q'.recipPos Q hQ).eqv C := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv C Q (Q'.recipPos Q hQ)) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left C _ _ (Q'.mul_recipPos_eqv Q hQ))
      (Q'.mul_one_eqv C)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv N (C*Q) (Q'.recipPos Q hQ)) ?_
  exact Q'.mul_eqv_congr_left N ((C*Q)*Q'.recipPos Q hQ) C hQR

/-- If `0 < p`, `0 < q`, and `p*q' ≤ p'*q`, then the corresponding
positive-denominator quotients are ordered. -/
private theorem divPos_le_divPos_of_cross
    (p q p' q' : Q') (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p*q' ≤ p'*q) :
    Q'.divPos p q hq ≤ Q'.divPos p' q' hq' := by
  refine Q'.divPos_le_of_le_mul p q hq ?_
  have hr : (0 : Q') ≤ Q'.recipPos q' hq' :=
    Q'.le_of_lt (Q'.recipPos_pos q' hq')
  have hstep : (p*q')*Q'.recipPos q' hq' ≤ (p'*q)*Q'.recipPos q' hq' :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hr
  have hleft : ((p*q')*Q'.recipPos q' hq').eqv p := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p q' (Q'.recipPos q' hq')) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _ (Q'.mul_recipPos_eqv q' hq'))
      (Q'.mul_one_eqv p)
  have hright : ((p'*q)*Q'.recipPos q' hq').eqv (Q'.divPos p' q' hq' * q) := by
    unfold Q'.divPos
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p' q (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p' _ _ (Q'.mul_comm_eqv q (Q'.recipPos q' hq'))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv p' (Q'.recipPos q' hq') q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hright))

/-- Common-mass quadratic response bound. From `ell*Q ≤ D`, the cap
`Z ≤ U²*Q`, and `D² ≤ N*(C*Q)`, conclude `ell²*Z ≤ C*U²*N`.
No estimate or positivity premise beyond the displayed rational hypotheses is
used. -/
theorem common_quadratic_response_lower
    (ell U C Z Q D N : Q')
    (hell : (0 : Q') < ell) (hU : (0 : Q') < U)
    (hC : (0 : Q') < C) (hZ : (0 : Q') < Z)
    (hQ : (0 : Q') ≤ Q) (hD : ell*Q ≤ D)
    (hpartition : Z ≤ (U*U)*Q)
    (hcost : D*D ≤ N*(C*Q)) :
    (ell*ell)*Z ≤ (C*(U*U))*N := by
  have hU2 : (0 : Q') < U*U := Q'.mul_pos hU hU
  have hU2num : 0 < (U*U).num := Q'.num_pos_of_pos hU2
  have hproductPos : (0 : Q') < (U*U)*Q :=
    Q'.pos_of_lt_of_le hZ hpartition
  have hproductNum : 0 < ((U*U)*Q).num :=
    Q'.num_pos_of_pos hproductPos
  have hQnumNonneg : (0 : Int) ≤ Q.num :=
    (Q'.zero_le_iff_num_nonneg Q).mp hQ
  have hQnumPos : (0 : Int) < Q.num := by
    have hzeroOrPos : Q.num = 0 ∨ (0 : Int) < Q.num := by omega
    rcases hzeroOrPos with hzero | hpos
    · rw [show ((U*U)*Q).num = (U*U).num * Q.num from rfl] at hproductNum
      simp [hzero] at hproductNum
    · exact hpos
  have hQpos : (0 : Q') < Q := by
    show (0 : Int) * (Q.den : Int) < Q.num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    exact hQnumPos
  have hmassPos : (0 : Q') < ell*Q := Q'.mul_pos hell hQpos
  have hDpos : (0 : Q') < D := Q'.pos_of_lt_of_le hmassPos hD
  have hell2Pos : (0 : Q') < ell*ell := Q'.mul_pos hell hell
  have hell2Nonneg : (0 : Q') ≤ ell*ell := Q'.le_of_lt hell2Pos
  have hU2Nonneg : (0 : Q') ≤ U*U := Q'.le_of_lt hU2
  have hQNonneg : (0 : Q') ≤ Q := hQ
  have hmassSq : (ell*Q)*(ell*Q) ≤ D*D :=
    Q'.mul_le_mul_of_nonneg hD hD (Q'.le_of_lt hDpos) (Q'.le_of_lt hmassPos)
  have hmassCost : (ell*Q)*(ell*Q) ≤ N*(C*Q) :=
    Q'.le_trans' _ _ _ hmassSq hcost
  have hrecipNonneg : (0 : Q') ≤ Q'.recipPos Q hQpos :=
    Q'.le_of_lt (Q'.recipPos_pos Q hQpos)
  have hcancelledRaw :
      ((ell*Q)*(ell*Q))*Q'.recipPos Q hQpos ≤
        (N*(C*Q))*Q'.recipPos Q hQpos :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmassCost hrecipNonneg
  have hlinear : (ell*ell)*Q ≤ N*C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancelCommonMassLeft ell Q hQpos))
      (Q'.le_trans' _ _ _ hcancelledRaw
        (Q'.le_of_eqv (cancelCommonMassRight N C Q hQpos)))
  have hscaleCap : (ell*ell)*Z ≤ (ell*ell)*((U*U)*Q) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpartition hell2Nonneg
  have hscaleLinear : ((ell*ell)*Q)*(U*U) ≤ (N*C)*(U*U) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hlinear hU2Nonneg
  have hmiddle : ((ell*ell)*((U*U)*Q)).eqv (((ell*ell)*Q)*(U*U)) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => ell | 1 => U | _ => Q)
  have hright : ((N*C)*(U*U)).eqv ((C*(U*U))*N) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 1) (.mul (.var 2) (.var 2))) (.var 0))
      (by decide) (fun | 0 => N | 1 => C | _ => U)
  exact Q'.le_trans' _ _ _ hscaleCap
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
      (Q'.le_trans' _ _ _ hscaleLinear (Q'.le_of_eqv hright)))

/-- Ratio form of the common-mass response estimate. -/
theorem common_quadratic_response_ratio
    (ell U C Z Q D N : Q')
    (hell : (0 : Q') < ell) (hU : (0 : Q') < U)
    (hC : (0 : Q') < C) (hZ : (0 : Q') < Z)
    (hQ : (0 : Q') ≤ Q) (hD : ell*Q ≤ D)
    (hpartition : Z ≤ (U*U)*Q)
    (hcost : D*D ≤ N*(C*Q)) :
    Q'.divPos (ell*ell) (C*(U*U)) (Q'.mul_pos hC (Q'.mul_pos hU hU)) ≤
      Q'.divPos N Z hZ := by
  have hlower := common_quadratic_response_lower
    ell U C Z Q D N hell hU hC hZ hQ hD hpartition hcost
  have hcross : (ell*ell)*Z ≤ N*(C*(U*U)) :=
    Q'.le_trans' _ _ _ hlower
      (Q'.le_of_eqv (Q'.mul_comm_eqv (C*(U*U)) N))
  exact divPos_le_divPos_of_cross _ _ _ _
    (Q'.mul_pos hC (Q'.mul_pos hU hU)) hZ hcross

#print axioms common_quadratic_response_lower
#print axioms common_quadratic_response_ratio

end YMGap.Continuum.RationalCommonQuadraticResponse
