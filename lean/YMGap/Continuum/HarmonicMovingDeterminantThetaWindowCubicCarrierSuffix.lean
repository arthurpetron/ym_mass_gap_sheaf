/-
Terminal-suffix structure of the cubic theta carrier cells.

The predecessor proves normalized monotonicity of the actual root carrier.
Here it is first lifted through signs and squares, then converted into the
cell statement needed by the cumulative Abel argument: once a mode cell is
strictly negative on the nonnegative-slope branch, the next mode cell is also
strictly negative.  Thus the adverse cells form a terminal suffix after the
unique slope crossing.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierMonotone

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierMonotone
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) <
    (Q'.ofNat n).num * (((0 : Q').den) : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show ((0 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  exact Int.ofNat_lt.mpr hn

private theorem lt_of_mul_lt_mul_left_pos {c a b : Q'}
    (hc : (0 : Q') < c) (h : c * a < c * b) : a < b := by
  have hcnum : (0 : Int) < c.num := Q'.num_pos_of_pos hc
  have hcommon : (0 : Int) < c.num * (c.den : Int) :=
    Int.mul_pos hcnum (Int.ofNat_lt.mpr (Q'.den_pos c))
  have h' : (c * a).num * ((c * b).den : Int) <
      (c * b).num * ((c * a).den : Int) := h
  rw [show (c * a).num = c.num * a.num from rfl,
      show (c * b).num = c.num * b.num from rfl,
      Q'.mul_den_cast c b, Q'.mul_den_cast c a] at h'
  have e1 :
      (c.num * a.num) * ((c.den : Int) * (b.den : Int)) =
        (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by
    ac_rfl
  have e2 :
      (c.num * b.num) * ((c.den : Int) * (a.den : Int)) =
        (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by
    ac_rfl
  rw [e1, e2] at h'
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  exact Int.lt_of_mul_lt_mul_left h' (Int.le_of_lt hcommon)

private theorem lt_of_sub_neg {a b : Q'}
    (h : a + -b < (0 : Q')) : a < b := by
  have h' : (a + -b).num * (((0 : Q').den) : Int) <
      (0 : Q').num * ((a + -b).den : Int) := h
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  simp only [Q'.add_num_cast, Q'.neg_den,
    show (-b).num = -b.num from rfl,
    show ((0 : Q').den : Int) = 1 from rfl,
    show (0 : Q').num = 0 from rfl,
    Int.mul_one, Int.zero_mul, Int.neg_mul] at h'
  omega

private theorem sub_neg_of_lt {a b : Q'} (h : a < b) :
    a + -b < (0 : Q') := by
  have h' : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  show (a + -b).num * (((0 : Q').den) : Int) <
      (0 : Q').num * ((a + -b).den : Int)
  simp only [Q'.add_num_cast, Q'.neg_den,
    show (-b).num = -b.num from rfl,
    show ((0 : Q').den : Int) = 1 from rfl,
    show (0 : Q').num = 0 from rfl,
    Int.mul_one, Int.zero_mul, Int.neg_mul]
  omega

/-- Once the cubic slope is nonnegative it remains nonnegative at the next
mode. -/
theorem thetaCubicRightCarrier_nonnegative_succ {k n : Nat}
    (hn0 : 1 ≤ n) (hnD : n + 1 ≤ k + 2)
    (hR : (0 : Q') ≤ thetaCubicRightCarrier k n) :
    (0 : Q') ≤ thetaCubicRightCarrier k (n + 1) := by
  have hmono := thetaCubicRightCarrier_normalized_mono hnD
  have hleft : (0 : Q') ≤
      Q'.ofNat (n + 1) * thetaCubicRightCarrier k n :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) hR
  have hprod : (0 : Q') ≤
      Q'.ofNat n * thetaCubicRightCarrier k (n + 1) :=
    Q'.le_trans' _ _ _ hleft hmono
  have hnpos : (0 : Q') < Q'.ofNat n := ofNat_pos_of_pos (by omega)
  have hzero : Q'.ofNat n * (0 : Q') ≤
      Q'.ofNat n * thetaCubicRightCarrier k (n + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _)) hprod
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos hnpos hzero

/-- Squared normalized monotonicity on the nonnegative branch. -/
theorem thetaCubicRightCarrier_normalized_square_mono {k n : Nat}
    (hn0 : 1 ≤ n) (hnD : n + 1 ≤ k + 2)
    (hR : (0 : Q') ≤ thetaCubicRightCarrier k n) :
    (Q'.ofNat (n + 1) * thetaCubicRightCarrier k n) *
        (Q'.ofNat (n + 1) * thetaCubicRightCarrier k n) ≤
      (Q'.ofNat n * thetaCubicRightCarrier k (n + 1)) *
        (Q'.ofNat n * thetaCubicRightCarrier k (n + 1)) := by
  have hmono := thetaCubicRightCarrier_normalized_mono hnD
  have hnext := thetaCubicRightCarrier_nonnegative_succ hn0 hnD hR
  have hleft : (0 : Q') ≤
      Q'.ofNat (n + 1) * thetaCubicRightCarrier k n :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) hR
  have hright : (0 : Q') ≤
      Q'.ofNat n * thetaCubicRightCarrier k (n + 1) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) hnext
  exact Q'.mul_le_mul_of_nonneg hmono hmono hright hleft

private def suffixCellLeftPoly : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.var 2
  .mul (.mul P (.mul n n)) (.mul p p)

private def suffixCellLeftNormalPoly : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.var 2
  .mul (.mul n n) (.mul P (.mul p p))

private def suffixCellMidPoly : RingNormaliser.PolyExpr :=
  let R := RingNormaliser.PolyExpr.var 0
  let p := RingNormaliser.PolyExpr.var 1
  .mul (.mul (.const 4) (.mul R R)) (.mul p p)

private def suffixCellMidNormalPoly : RingNormaliser.PolyExpr :=
  let R := RingNormaliser.PolyExpr.var 0
  let p := RingNormaliser.PolyExpr.var 1
  .mul (.const 4) (.mul (.mul p R) (.mul p R))

private def suffixCellRightPoly : RingNormaliser.PolyExpr :=
  let S := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  .mul (.const 4) (.mul (.mul n S) (.mul n S))

private def suffixCellRightNormalPoly : RingNormaliser.PolyExpr :=
  let S := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  .mul (.mul n n) (.mul (.const 4) (.mul S S))

private theorem suffixCellLeft_normal :
    RingNormaliser.normalize suffixCellLeftPoly =
      RingNormaliser.normalize suffixCellLeftNormalPoly := by decide

private theorem suffixCellMid_normal :
    RingNormaliser.normalize suffixCellMidPoly =
      RingNormaliser.normalize suffixCellMidNormalPoly := by decide

private theorem suffixCellRight_normal :
    RingNormaliser.normalize suffixCellRightPoly =
      RingNormaliser.normalize suffixCellRightNormalPoly := by decide

private theorem suffix_cell_left_regroup (P n p : Q') :
    (P * (n * n)) * (p * p) ≈ (n * n) * (P * (p * p)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    suffixCellLeftPoly suffixCellLeftNormalPoly suffixCellLeft_normal
    (fun | 0 => P | 1 => n | _ => p)
  simpa [suffixCellLeftPoly, suffixCellLeftNormalPoly,
    RingNormaliser.eval] using h

private theorem suffix_cell_mid_regroup (R p : Q') :
    (Q'.ofNat 4 * (R * R)) * (p * p) ≈
      Q'.ofNat 4 * ((p * R) * (p * R)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    suffixCellMidPoly suffixCellMidNormalPoly suffixCellMid_normal
    (fun | 0 => R | _ => p)
  simpa [suffixCellMidPoly, suffixCellMidNormalPoly,
    RingNormaliser.eval] using h

private theorem suffix_cell_right_regroup (S n : Q') :
    Q'.ofNat 4 * ((n * S) * (n * S)) ≈
      (n * n) * (Q'.ofNat 4 * (S * S)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    suffixCellRightPoly suffixCellRightNormalPoly suffixCellRight_normal
    (fun | 0 => S | _ => n)
  simpa [suffixCellRightPoly, suffixCellRightNormalPoly,
    RingNormaliser.eval] using h

private theorem cell_negative_succ_of_normalized_square
    {P n p R S : Q'}
    (hn : (0 : Q') < n) (hp : (0 : Q') < p)
    (hcell : P * (n * n) < Q'.ofNat 4 * (R * R))
    (hsq : (p * R) * (p * R) ≤ (n * S) * (n * S)) :
    P * (p * p) < Q'.ofNat 4 * (S * S) := by
  have hpp : (0 : Q') < p * p := Q'.mul_pos hp hp
  have hscaled := ClusteringImpliesGap.mul_lt_mul_of_pos_right hpp hcell
  have hleftEq := suffix_cell_left_regroup P n p
  have hmidEq := suffix_cell_mid_regroup R p
  have h1 : (n * n) * (P * (p * p)) <
      Q'.ofNat 4 * ((p * R) * (p * R)) :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (Q'.lt_of_le_of_lt (Q'.ge_of_eqv hleftEq) hscaled)
      (Q'.le_of_eqv hmidEq)
  have hfour := Q'.mul_le_mul_of_nonneg_left _ _ _ hsq
    (by decide : (0 : Q') ≤ Q'.ofNat 4)
  have hrightEq := suffix_cell_right_regroup S n
  have h2 : (n * n) * (P * (p * p)) <
      (n * n) * (Q'.ofNat 4 * (S * S)) :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (ClusteringImpliesGap.lt_of_lt_of_le h1 hfour)
      (Q'.le_of_eqv hrightEq)
  exact lt_of_mul_lt_mul_left_pos (Q'.mul_pos hn hn) h2

/-- Cubic central cell indexed directly by its mode. -/
def thetaCubicModeCell (k n : Nat) : Q' :=
  sevenDirichletProfile k * (Q'.ofNat n * Q'.ofNat n) +
    -(Q'.ofNat 4 *
      (thetaCubicRightCarrier k n * thetaCubicRightCarrier k n))

/-- A strictly negative cubic cell on the nonnegative-slope branch forces the
next cell to be strictly negative. -/
theorem thetaCubicModeCell_negative_succ {k n : Nat}
    (hn0 : 1 ≤ n) (hnD : n + 1 ≤ k + 2)
    (hR : (0 : Q') ≤ thetaCubicRightCarrier k n)
    (hcell : thetaCubicModeCell k n < (0 : Q')) :
    thetaCubicModeCell k (n + 1) < (0 : Q') := by
  have hbase :
      sevenDirichletProfile k * (Q'.ofNat n * Q'.ofNat n) <
        Q'.ofNat 4 *
          (thetaCubicRightCarrier k n * thetaCubicRightCarrier k n) := by
    unfold thetaCubicModeCell at hcell
    exact lt_of_sub_neg hcell
  have hsq := thetaCubicRightCarrier_normalized_square_mono
    hn0 hnD hR
  have hnext :
      sevenDirichletProfile k *
          (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) <
        Q'.ofNat 4 *
          (thetaCubicRightCarrier k (n + 1) *
            thetaCubicRightCarrier k (n + 1)) :=
    cell_negative_succ_of_normalized_square
      (ofNat_pos_of_pos (by omega)) (ofNat_pos_of_pos (by omega)) hbase hsq
  unfold thetaCubicModeCell
  exact sub_neg_of_lt hnext

#print axioms thetaCubicRightCarrier_nonnegative_succ
#print axioms thetaCubicRightCarrier_normalized_square_mono
#print axioms thetaCubicModeCell
#print axioms thetaCubicModeCell_negative_succ

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix
