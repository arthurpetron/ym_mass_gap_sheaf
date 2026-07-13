/-
# The rational circle polygon as an exact trapezoid rule

This module isolates the finite geometric identity needed by the remaining
polygon-to-midpoint common-refinement argument.  For the rational quadrant
vertices `(cx j, cy j)`, the oriented cross product of the `j`-th chord is the
doubled trapezoid contribution plus an adjacent boundary difference:

    cross j = (x_j-x_{j+1})(y_j+y_{j+1})
                + x_{j+1}y_{j+1} - x_j y_j.

The boundary products telescope, and both endpoint products vanish.  Hence the
existing rational polygon sum is *exactly* the nonuniform doubled trapezoid sum
under the upper unit semicircle.  This is the algebraic normal form in which a
common rational refinement can compare it with `seqSemi`.

The module also records the now-unconditional value of the polygon sequence:
the branch-safe Machin theorem identifies its already-proved Darboux limit with
`halfPi`, so the polygon sequence converges to `halfPi`.

No classical choice, native decision procedure, approximation input, or new
axiom is used.
-/

import YMGap.Continuum.SemicircleAtanAddition
import YMGap.Continuum.SemicircleBoundClosed
import YMGap.Constructive.SqrtSubadd

namespace YMGap.Continuum.SemicirclePolygonMidpointBridge

open YMGap.Constructive
open YMGap.Continuum.SemicircleRationalPolygon
open YMGap.Continuum.SemicircleAtanDarboux
open YMGap.Continuum.SemicircleAtanAddition
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanFiniteMeshBridge

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm];
             omega))

/-- The vertex boundary product `x_j y_j`. -/
def boundaryProduct (n j : Nat) (hn : 0 < n) : Q' :=
  cx n j hn * cy n j hn

/-- The doubled trapezoid contribution between consecutive rational circle
vertices.  The vertices run from `(1,0)` to `(0,1)`, so `x_j-x_{j+1}` is the
positive horizontal cell width. -/
def trapezoidCell (n j : Nat) (hn : 0 < n) : Q' :=
  (cx n j hn + -(cx n (j+1) hn)) * (cy n j hn + cy n (j+1) hn)

/-- The complete doubled nonuniform trapezoid sum on the rational quadrant
partition. -/
def polygonTrapezoidQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => trapezoidCell n j hn) n

private def crossTrapL : RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 1)))

private def crossTrapR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 0) (.neg (.var 1)))
      (.add (.var 2) (.var 3)))
    (.add (.mul (.var 1) (.var 3))
      (.neg (.mul (.var 0) (.var 2))))

private theorem crossTrap_normal :
    RingNormaliser.normalize crossTrapL =
      RingNormaliser.normalize crossTrapR := by decide

private theorem cross_trapezoid_identity (x0 x1 y0 y1 : Q') :
    (x0 * y1 + -(y0 * x1)).eqv
      ((x0 + -x1) * (y0 + y1) +
        ((x1 * y1) + -(x0 * y0))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    crossTrapL crossTrapR crossTrap_normal
    (fun | 0 => x0 | 1 => x1 | 2 => y0 | _ => y1)
  simpa [crossTrapL, crossTrapR, RingNormaliser.eval] using h

/-- Per chord, the cross product differs from the doubled trapezoid by an
adjacent boundary-product difference. -/
theorem polygonCross_eqv_trapezoid_add_boundary
    (n j : Nat) (hn : 0 < n) :
    (polygonCross n j hn).eqv
      (trapezoidCell n j hn +
        (boundaryProduct n (j+1) hn + -(boundaryProduct n j hn))) := by
  unfold polygonCross trapezoidCell boundaryProduct
  exact cross_trapezoid_identity _ _ _ _

/-- Adjacent differences telescope in the substrate's non-normalized rational
finite sums. -/
theorem finSum_adjacentDiff_telescope (b : Nat → Q') : ∀ n : Nat,
    (RationalTail.finSum (fun j => b (j+1) + -(b j)) n).eqv
      (b n + -(b 0))
  | 0 => Q'.eqv_symm (Q'.add_neg_self_eqv (b 0))
  | n + 1 => by
      refine Q'.eqv_trans _
        ((b n + -(b 0)) + (b (n+1) + -(b n))) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_adjacentDiff_telescope b n)
      · ring_qeqv

/-- The initial circle vertex has zero boundary product. -/
theorem boundaryProduct_zero_eqv (n : Nat) (hn : 0 < n) :
    (boundaryProduct n 0 hn).eqv 0 := by
  unfold boundaryProduct cx cy
  show (Q'.mkPos _ _ _ * Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _ * Q'.mkPos _ _ _).den : Int)
  simp only [Q'.mul_num_cast, Q'.mkPos_num, zero_num_cast, zero_den_cast,
    Int.mul_one, Int.zero_mul, Int.mul_zero]
  omega

/-- The terminal circle vertex also has zero boundary product. -/
theorem boundaryProduct_diag_eqv (n : Nat) (hn : 0 < n) :
    (boundaryProduct n n hn).eqv 0 := by
  unfold boundaryProduct cx cy
  show (Q'.mkPos _ _ _ * Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _ * Q'.mkPos _ _ _).den : Int)
  simp only [Q'.mul_num_cast, Q'.mkPos_num, zero_num_cast, zero_den_cast,
    Int.mul_one, Int.zero_mul, Int.mul_zero]
  omega

/-- The sum of all boundary corrections is exactly zero. -/
theorem boundaryCorrectionSum_eqv_zero (n : Nat) (hn : 0 < n) :
    (RationalTail.finSum
      (fun j => boundaryProduct n (j+1) hn + -(boundaryProduct n j hn)) n).eqv 0 := by
  refine Q'.eqv_trans _ _ _
    (finSum_adjacentDiff_telescope (fun j => boundaryProduct n j hn) n) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (boundaryProduct_diag_eqv n hn)
      (Q'.neg_eqv_congr _ _ (boundaryProduct_zero_eqv n hn))) ?_
  decide

/-- **Exact finite polygon/trapezoid identity.**  The rational polygon sum is
the doubled nonuniform trapezoid rule on its rational `x`-partition. -/
theorem polygonSemiQ_eqv_polygonTrapezoidQ (n : Nat) (hn : 0 < n) :
    (polygonSemiQ n hn).eqv (polygonTrapezoidQ n hn) := by
  unfold polygonSemiQ polygonTrapezoidQ
  refine Q'.eqv_trans _
    (RationalTail.finSum (fun j => polygonCross n j hn) n) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _
      (fun j => Q'.eqv_symm (polygonCross_eqv_crossCell n j hn)) n
  refine Q'.eqv_trans _
    (RationalTail.finSum
      (fun j => trapezoidCell n j hn +
        (boundaryProduct n (j+1) hn + -(boundaryProduct n j hn))) n) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _
      (fun j => polygonCross_eqv_trapezoid_add_boundary n j hn) n
  refine Q'.eqv_trans _
    (RationalTail.finSum (fun j => trapezoidCell n j hn) n +
      RationalTail.finSum
        (fun j => boundaryProduct n (j+1) hn + -(boundaryProduct n j hn)) n) _
    (RationalTail.finSum_add _ _ n) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ 0 (boundaryCorrectionSum_eqv_zero n hn)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## Quantitative mesh of the rational polygon partition -/

/-- Closed positive rational form of the horizontal width of the `j`-th
polygon cell. -/
def xWidthClosed (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos
    (2 * (n : Int) * (n : Int) * (2 * (j : Int) + 1))
    (cden n j * cden n (j+1))
    (Nat.mul_pos (cden_pos hn j) (cden_pos hn (j+1)))

private theorem raw_x_width (n j : Int) :
    (n*n-j*j) * (n*n+(j+1)*(j+1))
      - (n*n-(j+1)*(j+1)) * (n*n+j*j)
      = 2*n*n*(2*j+1) := by
  have hs : (j+1)*(j+1) = j*j + (j+j+1) := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
    omega
  have ht : 2*j+1 = j+j+1 := by omega
  rw [hs, ht]
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]
  have hnj2 : n * (n * (j * 2)) = (n * (n * j)) * 2 := by ac_rfl
  have hn2 : n * (n * 2) = (n * n) * 2 := by ac_rfl
  rw [hnj2, hn2]
  omega

/-- Exact horizontal cell-width formula. -/
theorem cx_sub_next_eqv_xWidthClosed (n j : Nat) (hn : 0 < n) :
    (cx n j hn + -(cx n (j+1) hn)).eqv (xWidthClosed n j hn) := by
  show (cx n j hn + -(cx n (j+1) hn)).num *
      ((xWidthClosed n j hn).den : Int) =
    (xWidthClosed n j hn).num *
      ((cx n j hn + -(cx n (j+1) hn)).den : Int)
  have hnum0 : (cx n j hn).num =
      (n:Int)*(n:Int) - (j:Int)*(j:Int) := by
    unfold cx
    rw [Q'.mkPos_num]
  have hnum1 : (cx n (j+1) hn).num =
      (n:Int)*(n:Int) - ((j+1:Nat):Int)*((j+1:Nat):Int) := by
    unfold cx
    rw [Q'.mkPos_num]
  have hden0 : ((cx n j hn).den : Int) = (cden n j : Int) := by
    unfold cx
    rw [Q'.mkPos_den]
  have hden1 : ((cx n (j+1) hn).den : Int) = (cden n (j+1) : Int) := by
    unfold cx
    rw [Q'.mkPos_den]
  have hsumNum : (cx n j hn + -(cx n (j+1) hn)).num =
      ((n:Int)*(n:Int) - (j:Int)*(j:Int)) * (cden n (j+1) : Int) +
        (-((n:Int)*(n:Int) - ((j+1:Nat):Int)*((j+1:Nat):Int))) *
          (cden n j : Int) := by
    rw [Q'.add_num_cast, neg_num_cast, hnum0, hnum1,
      Q'.neg_den, hden0, hden1]
  have hsumDen : ((cx n j hn + -(cx n (j+1) hn)).den : Int) =
      (cden n j : Int) * (cden n (j+1) : Int) := by
    rw [Q'.add_den_cast, Q'.neg_den, hden0, hden1]
  rw [hsumNum, hsumDen]
  unfold xWidthClosed
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hjcast : (((j+1 : Nat) : Int)) = (j:Int)+1 := by omega
  have hd0 : ((cden n j : Nat) : Int) =
      (n:Int)*(n:Int)+(j:Int)*(j:Int) := by
    unfold cden
    push_cast
    rfl
  have hd1 : ((cden n (j+1) : Nat) : Int) =
      (n:Int)*(n:Int)+((j:Int)+1)*((j:Int)+1) := by
    unfold cden
    push_cast
    rfl
  have hPcast : ((cden n j * cden n (j+1) : Nat) : Int) =
      ((n:Int)*(n:Int)+(j:Int)*(j:Int)) *
        ((n:Int)*(n:Int)+((j:Int)+1)*((j:Int)+1)) := by
    push_cast
    rw [hd0, hd1]
  rw [hd0, hd1, hjcast, hPcast]
  have hraw := raw_x_width (n:Int) (j:Int)
  rw [show (-((n:Int)*(n:Int) - ((j:Int)+1)*((j:Int)+1))) =
      -((n:Int)*(n:Int) - ((j:Int)+1)*((j:Int)+1)) by rfl]
  have hleft :
      ((n:Int)*(n:Int) - (j:Int)*(j:Int)) *
          ((n:Int)*(n:Int)+((j:Int)+1)*((j:Int)+1)) +
        (-((n:Int)*(n:Int) - ((j:Int)+1)*((j:Int)+1))) *
          ((n:Int)*(n:Int)+(j:Int)*(j:Int)) =
        2*(n:Int)*(n:Int)*(2*(j:Int)+1) := by
    simpa only [Int.sub_eq_add_neg, Int.neg_mul] using hraw
  rw [hleft]

/-- Every horizontal polygon cell has width at most `2/n`.  This is the exact
mesh estimate needed by monotone common refinement. -/
theorem xWidthClosed_le_two_over_n
    (n j : Nat) (hn : 0 < n) (hj : j < n) :
    xWidthClosed n j hn ≤ Q'.mkPos 2 n hn := by
  show (xWidthClosed n j hn).num * ((Q'.mkPos 2 n hn).den : Int) ≤
    (Q'.mkPos 2 n hn).num * ((xWidthClosed n j hn).den : Int)
  unfold xWidthClosed
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hjI : (j:Int) + 1 ≤ (n:Int) := by exact_mod_cast hj
  have hfactor0 : (0:Int) ≤ (n:Int) - (j:Int) := by omega
  have hfactor1 : (0:Int) ≤ (n:Int) - ((j:Int)+1) := by omega
  have hprod : (0:Int) ≤
      ((n:Int) - (j:Int)) * ((n:Int) - ((j:Int)+1)) :=
    Int.mul_nonneg hfactor0 hfactor1
  have htwice :
      (n:Int)*(2*(j:Int)+1) =
        (n:Int)*(j:Int) + (n:Int)*(j:Int) + (n:Int) := by
    have hjtwo : 2*(j:Int) = (j:Int)+(j:Int) := by omega
    rw [Int.mul_add, hjtwo, Int.mul_add, Int.mul_one]
  have hdecomp :
      (n:Int)*(n:Int) + ((j:Int)+1)*((j:Int)+1) =
        (n:Int)*(2*(j:Int)+1) +
          ((n:Int)-(j:Int))*((n:Int)-((j:Int)+1)) + ((j:Int)+1) := by
    rw [htwice]
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_add,
      Int.mul_one, Int.one_mul]
    have hjn : (j:Int) * (n:Int) = (n:Int) * (j:Int) := Int.mul_comm _ _
    have hjj1 : ((j:Int)+1) * (j:Int) = (j:Int)*(j:Int)+(j:Int) := by
      rw [Int.add_mul, Int.one_mul]
    rw [hjn, hjj1]
    omega
  have hsecond :
      (n:Int)*(2*(j:Int)+1) ≤
        (n:Int)*(n:Int) + ((j:Int)+1)*((j:Int)+1) := by
    rw [hdecomp]
    have hj1nonneg : (0:Int) ≤ (j:Int)+1 := by omega
    simpa only [Int.add_assoc] using
      (Int.le_add_of_nonneg_right (a := (n:Int)*(2*(j:Int)+1))
        (Int.add_nonneg hprod hj1nonneg))
  have hfirst : (n:Int)*(n:Int) ≤
      (n:Int)*(n:Int)+(j:Int)*(j:Int) := by
    exact Int.le_add_of_nonneg_right (Int.mul_nonneg (Int.natCast_nonneg j) (Int.natCast_nonneg j))
  have hmul := Int.mul_le_mul hfirst hsecond
    (Int.mul_nonneg (Int.natCast_nonneg n)
      (by omega : (0:Int) ≤ 2*(j:Int)+1))
    (Int.add_nonneg
      (Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg n))
      (Int.mul_nonneg (Int.natCast_nonneg j) (Int.natCast_nonneg j)))
  unfold cden
  push_cast
  have hnI : (0:Int) < (n:Int) := by exact_mod_cast hn
  have hscaled := Int.mul_le_mul_of_nonneg_left hmul (by decide : (0:Int) ≤ 2)
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hscaled

/-- Every closed-form horizontal width is strictly positive. -/
theorem xWidthClosed_pos (n j : Nat) (hn : 0 < n) :
    (0 : Q') < xWidthClosed n j hn := by
  show (0 : Int) * ((xWidthClosed n j hn).den : Int) <
    (xWidthClosed n j hn).num * (1 : Int)
  unfold xWidthClosed
  rw [Q'.mkPos_num, Int.zero_mul, Int.mul_one]
  have hnI : (0:Int) < (n:Int) := by exact_mod_cast hn
  have hjI : (0:Int) < 2*(j:Int)+1 := by omega
  exact Int.mul_pos (Int.mul_pos (by omega) hnI) hjI

/-- The rational polygon's `x`-coordinates are strictly decreasing along the
quadrant traversal. -/
theorem cx_next_lt_cx (n j : Nat) (hn : 0 < n) :
    cx n (j+1) hn < cx n j hn := by
  have hwidth : (0 : Q') < cx n j hn + -(cx n (j+1) hn) :=
    Q'.pos_of_lt_of_le (xWidthClosed_pos n j hn)
      (Q'.ge_of_eqv (cx_sub_next_eqv_xWidthClosed n j hn))
  change (0 : Int) * ((cx n j hn + -(cx n (j+1) hn)).den : Int) <
    (cx n j hn + -(cx n (j+1) hn)).num * (1 : Int) at hwidth
  rw [Int.zero_mul, Int.mul_one, Q'.add_num_cast, neg_num_cast,
    Q'.neg_den] at hwidth
  rw [Int.neg_mul] at hwidth
  show (cx n (j+1) hn).num * ((cx n j hn).den : Int) <
    (cx n j hn).num * ((cx n (j+1) hn).den : Int)
  omega

private theorem raw_y_rise (n j : Int) :
    (j+1) * (n*n+j*j) - j * (n*n+(j+1)*(j+1)) =
      n*n - j*(j+1) := by
  have hs : (j+1)*(j+1) = j*j + (j+j+1) := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
    omega
  rw [hs]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul]
  omega

/-- The rational polygon's `y`-coordinates are strictly increasing up to the
terminal quadrant vertex. -/
theorem cy_lt_next (n j : Nat) (hn : 0 < n) (hj : j < n) :
    cy n j hn < cy n (j+1) hn := by
  have hj1 : j+1 ≤ n := hj
  have hj1pos : 0 < j+1 := Nat.succ_pos j
  have hmul1 : j*(j+1) < n*(j+1) :=
    Nat.mul_lt_mul_of_pos_right hj hj1pos
  have hmul2 : n*(j+1) ≤ n*n := Nat.mul_le_mul_left n hj1
  have hcoreN : j*(j+1) < n*n := Nat.lt_of_lt_of_le hmul1 hmul2
  have hcore : (j:Int)*((j:Int)+1) < (n:Int)*(n:Int) := by
    exact_mod_cast hcoreN
  have hraw := raw_y_rise (n:Int) (j:Int)
  have hinner :
      (j:Int) * ((n:Int)*(n:Int)+((j:Int)+1)*((j:Int)+1)) <
        ((j:Int)+1) * ((n:Int)*(n:Int)+(j:Int)*(j:Int)) := by
    omega
  have hscalePos : (0:Int) < 2*(n:Int) := by
    have hnI : (0:Int) < (n:Int) := by exact_mod_cast hn
    omega
  have hscaled := Int.mul_lt_mul_of_pos_left hinner hscalePos
  show (cy n j hn).num * ((cy n (j+1) hn).den : Int) <
    (cy n (j+1) hn).num * ((cy n j hn).den : Int)
  unfold cy cden
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hscaled

/-- Doubled right-endpoint (lower) rectangle on a polygon cell. -/
def polygonLowerCell (n j : Nat) (hn : 0 < n) : Q' :=
  (cx n j hn + -(cx n (j+1) hn)) * (cy n j hn + cy n j hn)

/-- Doubled left-endpoint (upper) rectangle on a polygon cell. -/
def polygonUpperCell (n j : Nat) (hn : 0 < n) : Q' :=
  (cx n j hn + -(cx n (j+1) hn)) *
    (cy n (j+1) hn + cy n (j+1) hn)

/-- Each doubled trapezoid cell lies between its lower and upper monotone
rectangle cells. -/
theorem polygonLower_le_trapezoid_le_upper
    (n j : Nat) (hn : 0 < n) (hj : j < n) :
    polygonLowerCell n j hn ≤ trapezoidCell n j hn ∧
      trapezoidCell n j hn ≤ polygonUpperCell n j hn := by
  have hx : (0 : Q') ≤ cx n j hn + -(cx n (j+1) hn) :=
    Q'.sub_nonneg_of_le (Q'.le_of_lt (cx_next_lt_cx n j hn))
  have hy : cy n j hn ≤ cy n (j+1) hn := Q'.le_of_lt (cy_lt_next n j hn hj)
  constructor
  · unfold polygonLowerCell trapezoidCell
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_left _ _ _ hy) hx
  · unfold trapezoidCell polygonUpperCell
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_right _ _ _ hy) hx

/-- Complete doubled lower Darboux sum on the rational polygon partition. -/
def polygonLowerQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => polygonLowerCell n j hn) n

/-- Complete doubled upper Darboux sum on the rational polygon partition. -/
def polygonUpperQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => polygonUpperCell n j hn) n

/-- The polygon trapezoid sum is bracketed by the endpoint Darboux sums on
the same nonuniform partition. -/
theorem polygonLowerQ_le_trapezoid_le_polygonUpperQ
    (n : Nat) (hn : 0 < n) :
    polygonLowerQ n hn ≤ polygonTrapezoidQ n hn ∧
      polygonTrapezoidQ n hn ≤ polygonUpperQ n hn := by
  constructor
  · exact YMGap.Constructive.finSum_le_lt _ _ n
      (fun j hj => (polygonLower_le_trapezoid_le_upper n j hn hj).1)
  · exact YMGap.Constructive.finSum_le_lt _ _ n
      (fun j hj => (polygonLower_le_trapezoid_le_upper n j hn hj).2)

/-- Vertical rise of one polygon cell. -/
def polygonYRise (n j : Nat) (hn : 0 < n) : Q' :=
  cy n (j+1) hn + -(cy n j hn)

private def upperLowerL : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.add (.var 2) (.var 2))

private def upperLowerR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.var 0) (.add (.var 1) (.var 1)))
    (.mul (.add (.var 0) (.var 0))
      (.add (.var 2) (.neg (.var 1))))

private theorem upperLower_normal :
    RingNormaliser.normalize upperLowerL =
      RingNormaliser.normalize upperLowerR := by decide

private theorem upper_lower_identity (w y0 y1 : Q') :
    (w * (y1 + y1)).eqv
      (w * (y0 + y0) + (w + w) * (y1 + -y0)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    upperLowerL upperLowerR upperLower_normal
    (fun | 0 => w | 1 => y0 | _ => y1)
  simpa [upperLowerL, upperLowerR, RingNormaliser.eval] using h

/-- Exact decomposition of an upper rectangle into the lower rectangle plus
twice the horizontal width times the vertical rise. -/
theorem polygonUpperCell_eqv_lower_add_gap
    (n j : Nat) (hn : 0 < n) :
    (polygonUpperCell n j hn).eqv
      (polygonLowerCell n j hn +
        ((cx n j hn + -(cx n (j+1) hn)) +
          (cx n j hn + -(cx n (j+1) hn))) * polygonYRise n j hn) := by
  unfold polygonUpperCell polygonLowerCell polygonYRise
  exact upper_lower_identity _ _ _

/-- A polygon cell's upper/lower gap is controlled by twice the mesh bound
times its vertical rise. -/
theorem polygonUpperCell_le_lower_add_mesh_rise
    (n j : Nat) (hn : 0 < n) (hj : j < n) :
    polygonUpperCell n j hn ≤
      polygonLowerCell n j hn +
        (Q'.mkPos 2 n hn + Q'.mkPos 2 n hn) * polygonYRise n j hn := by
  let w := cx n j hn + -(cx n (j+1) hn)
  let q := Q'.mkPos 2 n hn
  have hw : w ≤ q :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (cx_sub_next_eqv_xWidthClosed n j hn))
      (xWidthClosed_le_two_over_n n j hn hj)
  have hww : w + w ≤ q + q := Q'.add_le_add hw hw
  have hry : (0 : Q') ≤ polygonYRise n j hn :=
    Q'.sub_nonneg_of_le (Q'.le_of_lt (cy_lt_next n j hn hj))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (polygonUpperCell_eqv_lower_add_gap n j hn)) ?_
  exact Q'.add_le_add_left _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hww hry)

/-- The initial rational circle ordinate is exactly zero. -/
theorem cy_zero_eqv (n : Nat) (hn : 0 < n) :
    (cy n 0 hn).eqv 0 := by
  unfold cy
  show (Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _).den : Int)
  rw [Q'.mkPos_num, zero_den_cast, zero_num_cast, Int.mul_one, Int.zero_mul]
  omega

/-- The terminal rational circle ordinate is exactly one. -/
theorem cy_diag_eqv_one (n : Nat) (hn : 0 < n) :
    (cy n n hn).eqv 1 := by
  unfold cy cden
  show (Q'.mkPos _ _ _).num * (((1 : Q').den : Int)) =
    (1 : Q').num * (((Q'.mkPos _ _ _).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  change (2 * (n:Int) * (n:Int)) * 1 =
    1 * (((n*n + n*n : Nat) : Int))
  push_cast
  simp only [Int.mul_one, Int.one_mul]
  show ((1 + 1 : Int) * (n:Int)) * (n:Int) =
    (n:Int) * (n:Int) + (n:Int) * (n:Int)
  rw [Int.add_mul, Int.one_mul, Int.add_mul]

/-- The polygon's vertical rises telescope to one. -/
theorem polygonYRiseSum_eqv_one (n : Nat) (hn : 0 < n) :
    (RationalTail.finSum (fun j => polygonYRise n j hn) n).eqv 1 := by
  refine Q'.eqv_trans _ _ _
    (finSum_adjacentDiff_telescope (fun j => cy n j hn) n) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (cy_diag_eqv_one n hn)
      (Q'.neg_eqv_congr _ _ (cy_zero_eqv n hn))) ?_
  decide

/-- The full upper/lower Darboux gap on the rational polygon partition is at
most twice its horizontal mesh, i.e. `2/n + 2/n`. -/
theorem polygonUpperQ_le_lower_add_mesh
    (n : Nat) (hn : 0 < n) :
    polygonUpperQ n hn ≤ polygonLowerQ n hn +
      (Q'.mkPos 2 n hn + Q'.mkPos 2 n hn) := by
  let q2 : Q' := Q'.mkPos 2 n hn + Q'.mkPos 2 n hn
  have hterm : ∀ j, j < n →
      polygonUpperCell n j hn ≤
        polygonLowerCell n j hn + q2 * polygonYRise n j hn := by
    intro j hj
    exact polygonUpperCell_le_lower_add_mesh_rise n j hn hj
  have hsum : polygonUpperQ n hn ≤
      RationalTail.finSum
        (fun j => polygonLowerCell n j hn + q2 * polygonYRise n j hn) n :=
    YMGap.Constructive.finSum_le_lt _ _ n hterm
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (RationalTail.finSum_add
      (fun j => polygonLowerCell n j hn)
      (fun j => q2 * polygonYRise n j hn) n)) ?_
  have hgapEqv :
      (RationalTail.finSum (fun j => q2 * polygonYRise n j hn) n).eqv q2 := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (RationalTail.const_mul_finSum
        (fun j => polygonYRise n j hn) q2 n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q2 _ _ (polygonYRiseSum_eqv_one n hn)) ?_
    exact Q'.mul_one_eqv q2
  exact Q'.add_le_add_left _ _ _ (Q'.le_of_eqv hgapEqv)

/-- Consequently the exact rational polygon/trapezoid value lies in a
certified interval of width at most `2/n + 2/n`. -/
theorem polygonTrapezoidQ_darboux_width
    (n : Nat) (hn : 0 < n) :
    polygonLowerQ n hn ≤ polygonTrapezoidQ n hn ∧
      polygonTrapezoidQ n hn ≤ polygonLowerQ n hn +
        (Q'.mkPos 2 n hn + Q'.mkPos 2 n hn) := by
  constructor
  · exact (polygonLowerQ_le_trapezoid_le_polygonUpperQ n hn).1
  · exact Q'.le_trans' _ _ _
      (polygonLowerQ_le_trapezoid_le_polygonUpperQ n hn).2
      (polygonUpperQ_le_lower_add_mesh n hn)

/-- The displayed mesh budget is exactly `4/n`. -/
theorem two_over_n_add_eqv_four_over_n (n : Nat) (hn : 0 < n) :
    (Q'.mkPos 2 n hn + Q'.mkPos 2 n hn).eqv
      (Q'.mkPos 4 n hn) :=
  SemicircleIntegral.mkPos_add_same_den 2 2 n hn

/-- Consumer form: the original rational chord-area polygon sum itself is
bracketed by the lower endpoint sum with exact width `4/n`. -/
theorem polygonSemiQ_darboux_width
    (n : Nat) (hn : 0 < n) :
    polygonLowerQ n hn ≤ polygonSemiQ n hn ∧
      polygonSemiQ n hn ≤ polygonLowerQ n hn + Q'.mkPos 4 n hn := by
  have hpoly := polygonSemiQ_eqv_polygonTrapezoidQ n hn
  have htrap := polygonTrapezoidQ_darboux_width n hn
  constructor
  · exact Q'.le_trans' _ _ _ htrap.1 (Q'.ge_of_eqv hpoly)
  · refine Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpoly) htrap.2) ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.le_of_eqv (two_over_n_add_eqv_four_over_n n hn))

/-- Resolution-indexed lower polygon Darboux sequence. -/
def polygonLowerSeq (N : Nat) : CReal :=
  CReal.ofQ' (polygonLowerQ (N+1) (Nat.succ_pos N))

/-- Resolution-indexed upper polygon Darboux sequence. -/
def polygonUpperSeq (N : Nat) : CReal :=
  CReal.ofQ' (polygonUpperQ (N+1) (Nat.succ_pos N))

/-- Explicit cutoff for `4/(N+1) ≤ q`. -/
theorem four_over_succ_le {q : Q'} (hq : (0 : Q') < q) {N : Nat}
    (hN : 4 * q.den ≤ N + 1) :
    Q'.mkPos 4 (N+1) (Nat.succ_pos N) ≤ q := by
  show (4 : Int) * (q.den : Int) ≤ q.num * ((N+1 : Nat) : Int)
  have hqnum : (1 : Int) ≤ q.num := by
    have hp : (0 : Int) < q.num := Q'.num_pos_of_pos hq
    omega
  have hNI : (4 : Int) * (q.den : Int) ≤ ((N+1 : Nat) : Int) := by
    exact_mod_cast hN
  have hscale : ((N+1 : Nat) : Int) ≤ q.num * ((N+1 : Nat) : Int) := by
    have hn0 : (0 : Int) ≤ ((N+1 : Nat) : Int) := Int.natCast_nonneg _
    have h := Int.mul_le_mul_of_nonneg_right hqnum hn0
    simpa only [Int.one_mul] using h
  exact Int.le_trans hNI hscale

/-- A rational lower sequence squeezed below `polygonSeq` with the explicit
`4/(N+1)` error has the same limit. -/
theorem polygonLowerSeq_converges_of_polygonSeq {L : CReal}
    (hconv : CReal.ConvergesTo polygonSeq L) :
    CReal.ConvergesTo polygonLowerSeq L := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Npoly, hNpoly⟩ := hconv q hq
  let Ntail : Nat := 4 * q.den
  refine ⟨max Npoly Ntail, fun N hN => ?_⟩
  have hPolyN : Npoly ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hTailN : Ntail ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨Napx, hclose⟩ := hNpoly N hPolyN
  refine ⟨Napx, fun k hk => ?_⟩
  have htail : Q'.mkPos 4 (N+1) (Nat.succ_pos N) ≤ q := by
    apply four_over_succ_le hq
    unfold Ntail at hTailN
    omega
  have hbr := polygonSemiQ_darboux_width (N+1) (Nat.succ_pos N)
  obtain ⟨hPolyL, hLPoly⟩ := hclose k hk
  change polygonLowerQ (N+1) (Nat.succ_pos N) ≤ L.approx k + epsilon ∧
    L.approx k ≤ polygonLowerQ (N+1) (Nat.succ_pos N) + epsilon
  have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hqeps : q ≤ epsilon := by
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hq))
        (Q'.le_of_eqv hqq)
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ hbr.1 hPolyL)
      (Q'.add_le_add_left _ _ _ hqeps)
  · have hchain : L.approx k ≤
        (polygonLowerQ (N+1) (Nat.succ_pos N) + q) + q :=
      Q'.le_trans' _ _ _ hLPoly
        (Q'.add_le_add_right _ _ q
          (Q'.le_trans' _ _ _ hbr.2
            (Q'.add_le_add_left _ _ _ htail)))
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (polygonLowerQ (N+1) (Nat.succ_pos N)) q q)
        (Q'.add_eqv_congr_left _ _ _ hqq)))

/-- The upper polygon Darboux sequence has the same limit as `polygonSeq`. -/
theorem polygonUpperSeq_converges_of_polygonSeq {L : CReal}
    (hconv : CReal.ConvergesTo polygonSeq L) :
    CReal.ConvergesTo polygonUpperSeq L := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Npoly, hNpoly⟩ := hconv q hq
  let Ntail : Nat := 4 * q.den
  refine ⟨max Npoly Ntail, fun N hN => ?_⟩
  have hPolyN : Npoly ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hTailN : Ntail ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨Napx, hclose⟩ := hNpoly N hPolyN
  refine ⟨Napx, fun k hk => ?_⟩
  have htail : Q'.mkPos 4 (N+1) (Nat.succ_pos N) ≤ q := by
    apply four_over_succ_le hq
    unfold Ntail at hTailN
    omega
  have hbr := polygonSemiQ_darboux_width (N+1) (Nat.succ_pos N)
  have htrap := polygonLowerQ_le_trapezoid_le_polygonUpperQ
    (N+1) (Nat.succ_pos N)
  have huplo : polygonSemiQ (N+1) (Nat.succ_pos N) ≤
      polygonUpperQ (N+1) (Nat.succ_pos N) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (polygonSemiQ_eqv_polygonTrapezoidQ
        (N+1) (Nat.succ_pos N))) htrap.2
  have huphi : polygonUpperQ (N+1) (Nat.succ_pos N) ≤
      polygonSemiQ (N+1) (Nat.succ_pos N) + Q'.mkPos 4 (N+1) (Nat.succ_pos N) :=
    Q'.le_trans' _ _ _ (polygonUpperQ_le_lower_add_mesh
      (N+1) (Nat.succ_pos N))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ hbr.1)
        (Q'.add_le_add_left _ _ _
          (Q'.le_of_eqv (two_over_n_add_eqv_four_over_n
            (N+1) (Nat.succ_pos N)))))
  obtain ⟨hPolyL, hLPoly⟩ := hclose k hk
  change polygonUpperQ (N+1) (Nat.succ_pos N) ≤ L.approx k + epsilon ∧
    L.approx k ≤ polygonUpperQ (N+1) (Nat.succ_pos N) + epsilon
  have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain : polygonUpperQ (N+1) (Nat.succ_pos N) ≤
        (L.approx k + q) + q :=
      Q'.le_trans' _ _ _ huphi
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ _ hPolyL)
          (Q'.add_le_add_left _ _ _ htail))
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (L.approx k) q q)
        (Q'.add_eqv_congr_left _ _ _ hqq)))
  · have hqeps : q ≤ epsilon := by
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hq))
        (Q'.le_of_eqv hqq)
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ hLPoly
        (Q'.add_le_add_right _ _ _ huplo))
      (Q'.add_le_add_left _ _ _ hqeps)

/-! ## Pointwise common-refinement consumer -/

/-- Sound order between arbitrary constructive reals, expressed through the
regularity-free rational upper-bound predicate. -/
def LimitLe (A B : CReal) : Prop :=
  CReal.leRat (CReal.add A (CReal.neg B)) 0

/-- A constructive real lies between two others in the sound limit order. -/
def LimitBracket (lower value upper : CReal) : Prop :=
  LimitLe lower value ∧ LimitLe value upper

private theorem limitLe_refl (A : CReal) : LimitLe A A := by
  apply CReal.leRat_of_eventually
  refine ⟨0, fun k _ => ?_⟩
  exact Q'.le_of_eqv (Q'.add_neg_self_eqv (A.approx k))

private theorem limitLe_trans {A B C : CReal}
    (hAB : LimitLe A B) (hBC : LimitLe B C) : LimitLe A C := by
  have hsum := CReal.leRat_add hAB hBC
  have hzero : (0 + 0 : Q') ≤ 0 := Q'.le_of_eqv (by decide)
  have hsum0 := CReal.leRat_mono hsum hzero
  apply CReal.leRat_congr (b := CReal.add
    (CReal.add A (CReal.neg B)) (CReal.add B (CReal.neg C)))
  · intro k
    change (A.approx k + -(C.approx k)).eqv
      ((A.approx k + -(B.approx k)) + (B.approx k + -(C.approx k)))
    ring_qeqv
  · exact hsum0

private theorem limitLe_add {A B C D : CReal}
    (hAB : LimitLe A B) (hCD : LimitLe C D) :
    LimitLe (CReal.add A C) (CReal.add B D) := by
  have hsum := CReal.leRat_add hAB hCD
  have hzero : (0 + 0 : Q') ≤ 0 := Q'.le_of_eqv (by decide)
  have hsum0 := CReal.leRat_mono hsum hzero
  apply CReal.leRat_congr (b := CReal.add
    (CReal.add A (CReal.neg B)) (CReal.add C (CReal.neg D)))
  · intro k
    change ((A.approx k + C.approx k) + -(B.approx k + D.approx k)).eqv
      ((A.approx k + -(B.approx k)) + (C.approx k + -(D.approx k)))
    ring_qeqv
  · exact hsum0

private theorem limitLe_scale {A B : CReal} (c : Q')
    (hc : (0 : Q') ≤ c) (hAB : LimitLe A B) :
    LimitLe
      (CReal.mul (CReal.ofQ' c) A)
      (CReal.mul (CReal.ofQ' c) B) := by
  have hscale := CReal.leRat_smul_nonneg hc hAB
  have hzero : c * (0 : Q') ≤ 0 :=
    Q'.le_of_eqv (Q'.mul_zero_eqv c)
  have hscale0 := CReal.leRat_mono hscale hzero
  apply CReal.leRat_congr (b :=
    CReal.mul (CReal.ofQ' c) (CReal.add A (CReal.neg B)))
  · intro k
    change (c * A.approx k + -(c * B.approx k)).eqv
      (c * (A.approx k + -(B.approx k)))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * A.approx k) _ _
        (Q'.eqv_symm (Q'.mul_neg_eqv c (B.approx k))))
      (Q'.eqv_symm (Q'.mul_add_eqv c (A.approx k) (-(B.approx k))))
  · exact hscale0

/-- Pointwise semantic equality of constructive-real approximations. -/
def ApproxEq (A B : CReal) : Prop :=
  ∀ k, (A.approx k).eqv (B.approx k)

private theorem approxEq_refl (A : CReal) : ApproxEq A A :=
  fun k => Q'.eqv_refl (A.approx k)

private theorem approxEq_symm {A B : CReal} (h : ApproxEq A B) :
    ApproxEq B A := fun k => Q'.eqv_symm (h k)

private theorem approxEq_limitLe_left {A A' B : CReal}
    (hAA' : ApproxEq A A') (h : LimitLe A' B) : LimitLe A B := by
  apply CReal.leRat_congr (b := CReal.add A' (CReal.neg B))
  · intro k
    exact Q'.add_eqv_congr_right _ _ _ (hAA' k)
  · exact h

private theorem approxEq_limitLe_right {A B B' : CReal}
    (hBB' : ApproxEq B B') (h : LimitLe A B) : LimitLe A B' := by
  apply CReal.leRat_congr (b := CReal.add A (CReal.neg B))
  · intro k
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (hBB' k)))
  · exact h

private theorem equiv_limitLe_left {A A' B : CReal}
    (hAA' : CReal.Equiv A A') (h : LimitLe A' B) : LimitLe A B := by
  apply CReal.leRat_of_equiv
    (CReal.add_congr_left hAA')
  exact h

private theorem equiv_limitLe_right {A B B' : CReal}
    (hBB' : CReal.Equiv B B') (h : LimitLe A B) : LimitLe A B' := by
  apply CReal.leRat_of_equiv
    (CReal.Equiv.symm (CReal.add_congr_right (CReal.neg_congr hBB')))
  exact h

/-! ### Generic constructive-real Darboux sums -/

open YMGap.Continuum.SemicircleAtanPartitionInsertion

/-- A rectangle for a constructive-real-valued function on rational nodes. -/
def cPartitionRect (f : Q' → CReal) (x y sample : Q') : CReal :=
  CReal.mul (CReal.ofQ' (y + -x)) (f sample)

def cPartitionLeftSum (f : Q' → CReal) : List PartitionCell → CReal
  | [] => CReal.czero
  | c :: cs => CReal.add (cPartitionRect f c.1 c.2 c.1)
      (cPartitionLeftSum f cs)

def cPartitionRightSum (f : Q' → CReal) : List PartitionCell → CReal
  | [] => CReal.czero
  | c :: cs => CReal.add (cPartitionRect f c.1 c.2 c.2)
      (cPartitionRightSum f cs)

private theorem split_rect_approxEq (f : Q' → CReal) (x z y s : Q') :
    ApproxEq
      (CReal.add (cPartitionRect f x z s) (cPartitionRect f z y s))
      (cPartitionRect f x y s) := by
  intro k
  change (((z + -x) * (f s).approx k) +
      ((y + -z) * (f s).approx k)).eqv
    ((y + -x) * (f s).approx k)
  ring_qeqv

/-- One-node refinement decreases a left endpoint sum for an antitone
constructive-real-valued function. -/
theorem cSplit_left_le_coarse (f : Q' → CReal) {x z y : Q'}
    (hxz : x ≤ z) (hzy : z ≤ y)
    (hanti : LimitLe (f z) (f x)) :
    LimitLe
      (CReal.add (cPartitionRect f x z x) (cPartitionRect f z y z))
      (cPartitionRect f x y x) := by
  have hw : (0 : Q') ≤ y + -z := Q'.sub_nonneg_of_le hzy
  have hscaled := limitLe_scale (y + -z) hw hanti
  have hfirst := limitLe_refl (cPartitionRect f x z x)
  have hsum := limitLe_add hfirst hscaled
  exact approxEq_limitLe_right (split_rect_approxEq f x z y x) hsum

/-- Dually, one-node refinement increases a right endpoint sum. -/
theorem cCoarse_right_le_split (f : Q' → CReal) {x z y : Q'}
    (hxz : x ≤ z) (hzy : z ≤ y)
    (hanti : LimitLe (f y) (f z)) :
    LimitLe (cPartitionRect f x y y)
      (CReal.add (cPartitionRect f x z z) (cPartitionRect f z y y)) := by
  have hw : (0 : Q') ≤ z + -x := Q'.sub_nonneg_of_le hxz
  have hscaled := limitLe_scale (z + -x) hw hanti
  have hsecond := limitLe_refl (cPartitionRect f z y y)
  have hsum := limitLe_add hscaled hsecond
  exact approxEq_limitLe_left
    (approxEq_symm (split_rect_approxEq f x z y y)) hsum

/-- On one ordered cell the right rectangle is below the left rectangle. -/
theorem cRight_le_left (f : Q' → CReal) {x y : Q'}
    (hxy : x ≤ y) (hanti : LimitLe (f y) (f x)) :
    LimitLe (cPartitionRect f x y y) (cPartitionRect f x y x) :=
  limitLe_scale (y + -x) (Q'.sub_nonneg_of_le hxy) hanti

private theorem cRefine_cell_left (f : Q' → CReal)
    (pre post : List PartitionCell) {x z y : Q'}
    (hxz : x ≤ z) (hzy : z ≤ y) (hanti : LimitLe (f z) (f x)) :
    LimitLe
      (cPartitionLeftSum f (pre ++ (x,z) :: (z,y) :: post))
      (cPartitionLeftSum f (pre ++ (x,y) :: post)) := by
  induction pre with
  | nil =>
      have hlocal := cSplit_left_le_coarse f hxz hzy hanti
      have hsum := limitLe_add hlocal (limitLe_refl (cPartitionLeftSum f post))
      apply approxEq_limitLe_left (A' := CReal.add
        (CReal.add (cPartitionRect f x z x) (cPartitionRect f z y z))
        (cPartitionLeftSum f post))
      · intro k
        change ((cPartitionRect f x z x).approx k +
          ((cPartitionRect f z y z).approx k + (cPartitionLeftSum f post).approx k)).eqv
          (((cPartitionRect f x z x).approx k +
            (cPartitionRect f z y z).approx k) + (cPartitionLeftSum f post).approx k)
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      · exact hsum
  | cons c pre ih =>
      exact limitLe_add (limitLe_refl (cPartitionRect f c.1 c.2 c.1)) ih

private theorem cRefine_cell_right (f : Q' → CReal)
    (pre post : List PartitionCell) {x z y : Q'}
    (hxz : x ≤ z) (hzy : z ≤ y) (hanti : LimitLe (f y) (f z)) :
    LimitLe
      (cPartitionRightSum f (pre ++ (x,y) :: post))
      (cPartitionRightSum f (pre ++ (x,z) :: (z,y) :: post)) := by
  induction pre with
  | nil =>
      have hlocal := cCoarse_right_le_split f hxz hzy hanti
      have hsum := limitLe_add hlocal (limitLe_refl (cPartitionRightSum f post))
      apply approxEq_limitLe_right (B := CReal.add
        (CReal.add (cPartitionRect f x z z) (cPartitionRect f z y y))
        (cPartitionRightSum f post))
      · intro k
        change (((cPartitionRect f x z z).approx k +
          (cPartitionRect f z y y).approx k) + (cPartitionRightSum f post).approx k).eqv
          ((cPartitionRect f x z z).approx k +
            ((cPartitionRect f z y y).approx k + (cPartitionRightSum f post).approx k))
        exact Q'.add_assoc_eqv _ _ _
      · exact hsum
  | cons c pre ih =>
      exact limitLe_add (limitLe_refl (cPartitionRect f c.1 c.2 c.2)) ih

/-- The existing finite `CellRefines` certificate acts on arbitrary antitone
constructive-real endpoint sums. -/
theorem cCellRefines_left_le (f : Q' → CReal)
    (hanti : ∀ {x y : Q'}, (0 : Q') ≤ x → x ≤ y → LimitLe (f y) (f x))
    {fine coarse : List PartitionCell} (h : CellRefines fine coarse) :
    LimitLe (cPartitionLeftSum f fine) (cPartitionLeftSum f coarse) := by
  induction h with
  | refl cells => exact limitLe_refl _
  | insert pre post x z y hx0 hxz hzy =>
      exact cRefine_cell_left f pre post hxz hzy (hanti hx0 hxz)
  | cons cell h ih =>
      exact limitLe_add (limitLe_refl (cPartitionRect f cell.1 cell.2 cell.1)) ih
  | trans h₁ h₂ ih₁ ih₂ => exact limitLe_trans ih₁ ih₂

theorem cCellRefines_right_le (f : Q' → CReal)
    (hanti : ∀ {x y : Q'}, (0 : Q') ≤ x → x ≤ y → LimitLe (f y) (f x))
    {fine coarse : List PartitionCell} (h : CellRefines fine coarse) :
    LimitLe (cPartitionRightSum f coarse) (cPartitionRightSum f fine) := by
  induction h with
  | refl cells => exact limitLe_refl _
  | insert pre post x z y hx0 hxz hzy =>
      have hz0 := Q'.le_trans' _ _ _ hx0 hxz
      exact cRefine_cell_right f pre post hxz hzy (hanti hz0 hzy)
  | cons cell h ih =>
      exact limitLe_add (limitLe_refl (cPartitionRect f cell.1 cell.2 cell.2)) ih
  | trans h₁ h₂ ih₁ ih₂ => exact limitLe_trans ih₂ ih₁

theorem cValidCells_right_le_left (f : Q' → CReal)
    (hanti : ∀ {x y : Q'}, (0 : Q') ≤ x → x ≤ y → LimitLe (f y) (f x))
    {cells : List PartitionCell} (h : ValidCells cells) :
    LimitLe (cPartitionRightSum f cells) (cPartitionLeftSum f cells) := by
  induction h with
  | nil => exact limitLe_refl _
  | cons x y rest hx0 hxy hrest ih =>
      exact limitLe_add (cRight_le_left f hxy (hanti hx0 hxy)) ih

private theorem cRect_equiv_congr (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {x y s x' y' s' : Q'} (hx : x.eqv x') (hy : y.eqv y')
    (hs : s.eqv s') :
    CReal.Equiv (cPartitionRect f x y s) (cPartitionRect f x' y' s') := by
  have hw : (y + -x).eqv (y' + -x') :=
    Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
  exact CReal.Equiv.trans
    (CReal.mul_congr_left (TrigAdd.equiv_ofQ'_of_eqv hw))
    ((CRealAlg.cmul_comm _ _).trans
      ((CReal.mul_congr_left (hf hs)).trans (CRealAlg.cmul_comm _ _)))

private theorem cPartitionEqv_left (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionLeftSum f cells) (cPartitionLeftSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      exact CReal.Equiv.trans
        (CReal.add_congr_left (cRect_equiv_congr f hf hx hy hx))
        (CReal.add_congr_right ih)

private theorem cPartitionEqv_right (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionRightSum f cells) (cPartitionRightSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      exact CReal.Equiv.trans
        (CReal.add_congr_left (cRect_equiv_congr f hf hx hy hy))
        (CReal.add_congr_right ih)

/-- Semantic common-refinement bracket for any antitone
constructive-real-valued function on nonnegative rational cuts. -/
theorem cCommon_refinement_bracket_of_eqv (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    (hanti : ∀ {x y : Q'}, (0 : Q') ≤ x → x ≤ y → LimitLe (f y) (f x))
    {common₁ common₂ first second : List PartitionCell}
    (hvalid : ValidCells common₂)
    (hfirst : CellRefines common₁ first)
    (hsecond : CellRefines common₂ second)
    (heqv : PartitionEqv common₁ common₂) :
    LimitLe (cPartitionRightSum f first) (cPartitionLeftSum f second) := by
  have h1 := cCellRefines_right_le f hanti hfirst
  have he : LimitLe (cPartitionRightSum f common₁)
      (cPartitionRightSum f common₂) :=
    equiv_limitLe_right (cPartitionEqv_right f hf heqv)
      (limitLe_refl _)
  have hv := cValidCells_right_le_left f hanti hvalid
  have h2 := cCellRefines_left_le f hanti hsecond
  exact limitLe_trans h1 (limitLe_trans he (limitLe_trans hv h2))

/-- **Generic constructive-real common-refinement theorem.**  Any two ordered
rational meshes on the same nonnegative interval have cross-bracketed endpoint
sums for a semantically well-defined antitone constructive-real function. -/
theorem cOrdered_partitions_common_bracket (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    (hanti : ∀ {x y : Q'}, (0 : Q') ≤ x → x ≤ y → LimitLe (f y) (f x))
    {x y : Q'} {first second : List Q'}
    (hfirst : OrderedCuts x y first) (hsecond : OrderedCuts x y second) :
    LimitLe
      (cPartitionRightSum f (cutCells x first y))
      (cPartitionLeftSum f (cutCells x second y)) := by
  have hfirstWithin := hfirst.cutsWithin
  have hsecondWithin := hsecond.cutsWithin
  have hcommonOrdered :=
    mergeCuts_ordered first second hfirstWithin hsecond
  have hrefFirst :=
    mergeCuts_refines_base second first hsecondWithin hfirst
  have hrefSecond :=
    mergeCuts_refines_base first second hfirstWithin hsecond
  have heqv : PartitionEqv
      (cutCells x (mergeCuts second first) y)
      (cutCells x (mergeCuts first second) y) :=
    cutCells_eqv_congr (Q'.eqv_refl x) (Q'.eqv_refl y)
      (mergeCuts_comm_eqv hsecond hfirst)
  exact cCommon_refinement_bracket_of_eqv f hf hanti
    hcommonOrdered.validCells hrefFirst hrefSecond heqv

private theorem le_add_of_sub_le_q {a b q : Q'}
    (h : a + -b ≤ q) : a ≤ b + q := by
  have h' := Q'.add_le_add_right (a + -b) q b h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (Q'.add_comm_eqv q b)))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-! ### The constructive semicircle as an antitone endpoint function -/

/-- The rational radicand `1-x²` on the positive unit quadrant. -/
def quadrantRad (x : Q') : Q' := 1 + -(x * x)

private theorem quadrantRad_pos {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) : (0 : Q') < quadrantRad x := by
  have hxx1 : x * x < (1 : Q') := by
    have hmul : x * x ≤ x * 1 :=
      Q'.mul_le_mul_of_nonneg_left x 1 x (Q'.le_of_lt hx1) hx0
    have hxx : x * x ≤ x :=
      Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv x))
    exact Q'.lt_of_le_of_lt hxx hx1
  exact HKPos.one_sub_pos hxx1

private theorem quadrantRad_le_one (x : Q') : quadrantRad x ≤ (1 : Q') := by
  have hs : (0 : Q') ≤ x * x := SumOfSquares.q_mul_self_nonneg x
  have hn : -(x * x) ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hs
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-(x * x)) 0 hn) ?_
  exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem quadrantRad_sq_le {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) :
    quadrantRad x * quadrantRad x ≤ quadrantRad x := by
  have ha0 : (0 : Q') ≤ quadrantRad x :=
    Q'.le_of_lt (quadrantRad_pos hx0 hx1)
  have hmul : quadrantRad x * quadrantRad x ≤ quadrantRad x * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (quadrantRad_le_one x) ha0
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.mul_one_eqv (quadrantRad x)))

private theorem quadrantRad_eqv_congr {x y : Q'} (hxy : x.eqv y) :
    (quadrantRad x).eqv (quadrantRad y) := by
  unfold quadrantRad
  exact Q'.add_eqv_congr_left 1 _ _
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right x y x hxy)
      (Q'.mul_eqv_congr_left y x y hxy)))

private theorem quadrantRad_antitone {x y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) :
    quadrantRad y ≤ quadrantRad x := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hs : x * x ≤ y * y :=
    Q'.mul_le_mul_of_nonneg hxy hxy hy0 hx0
  unfold quadrantRad
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hs)

/-- A sound constructive-real comparison of positive rational square roots. -/
private theorem sqrtFrom_limitLe_of_le
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv)
    (hLva : Lv * Lv ≤ v) (huv : u ≤ v) :
    LimitLe (CReal.sqrtFrom u Lu hu hLu hLua)
      (CReal.sqrtFrom v Lv hv hLv hLva) := by
  intro epsilon hepsilon
  let c : Q' := HalfPow.half * epsilon
  have hc : (0 : Q') < c := ExpNeg.half_mul_pos epsilon hepsilon
  have hcc : (0 : Q') ≤ c * c := SumOfSquares.q_mul_self_nonneg c
  have huvc : u ≤ v + c * c :=
    Q'.le_trans' _ _ _ huv (Q'.add_le_self_of_nonneg v (c * c) hcc)
  have hs := CReal.sqrtFrom_sub_leRat
    u Lu hu hLu hLua v Lv hv hLv hLva c hc huvc
  obtain ⟨N, hN⟩ := hs c hc
  refine ⟨N, fun n hn => ?_⟩
  have htwo : (c + c).eqv epsilon := ExpNeg.two_halves epsilon
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ htwo
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

private theorem limitLe_antisymm_equiv {A B : CReal}
    (hAB : LimitLe A B) (hBA : LimitLe B A) : CReal.Equiv A B := by
  intro epsilon hepsilon
  obtain ⟨Nab, hNab⟩ := hAB epsilon hepsilon
  obtain ⟨Nba, hNba⟩ := hBA epsilon hepsilon
  refine ⟨max Nab Nba, fun n hn => ?_⟩
  have hnab : Nab ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnba : Nba ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have habSub : A.approx n + -(B.approx n) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hNab n hnab)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  have hbaSub : B.approx n + -(A.approx n) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hNba n hnba)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  exact ⟨le_add_of_sub_le_q habSub, le_add_of_sub_le_q hbaSub⟩

private theorem sqrtFrom_equiv_of_rad_eqv
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv)
    (hLva : Lv * Lv ≤ v) (huv : u.eqv v) :
    CReal.Equiv (CReal.sqrtFrom u Lu hu hLu hLua)
      (CReal.sqrtFrom v Lv hv hLv hLva) :=
  limitLe_antisymm_equiv
    (sqrtFrom_limitLe_of_le u Lu hu hLu hLua v Lv hv hLv hLva
      (Q'.le_of_eqv huv))
    (sqrtFrom_limitLe_of_le v Lv hv hLv hLva u Lu hu hLu hLua
      (Q'.ge_of_eqv huv))

/-- `sqrt(1-x²)` on `[0,1)`, extended by zero outside that interval.  The
radicand itself is a valid positive Heron lower witness because `0<a≤1`
implies `a²≤a`. -/
def quadrantSemi (x : Q') : CReal :=
  if h : (0 : Q') ≤ x ∧ x < (1 : Q') then
    CReal.sqrtFrom (quadrantRad x) (quadrantRad x)
      (quadrantRad_pos h.1 h.2) (quadrantRad_pos h.1 h.2)
      (quadrantRad_sq_le h.1 h.2)
  else CReal.czero

theorem quadrantSemi_eqv_congr {x y : Q'} (hxy : x.eqv y) :
    CReal.Equiv (quadrantSemi x) (quadrantSemi y) := by
  have hpred : ((0 : Q') ≤ x ∧ x < (1 : Q')) ↔
      ((0 : Q') ≤ y ∧ y < (1 : Q')) := by
    constructor
    · intro hx
      exact ⟨Q'.le_trans' _ _ _ hx.1 (Q'.le_of_eqv hxy),
        Q'.lt_of_le_of_lt (Q'.ge_of_eqv hxy) hx.2⟩
    · intro hy
      exact ⟨Q'.le_trans' _ _ _ hy.1 (Q'.ge_of_eqv hxy),
        Q'.lt_of_le_of_lt (Q'.le_of_eqv hxy) hy.2⟩
  by_cases hx : (0 : Q') ≤ x ∧ x < (1 : Q')
  · have hy := hpred.mp hx
    simp only [quadrantSemi, dif_pos hx, dif_pos hy]
    exact sqrtFrom_equiv_of_rad_eqv
      (quadrantRad x) (quadrantRad x)
      (quadrantRad_pos hx.1 hx.2) (quadrantRad_pos hx.1 hx.2)
      (quadrantRad_sq_le hx.1 hx.2)
      (quadrantRad y) (quadrantRad y)
      (quadrantRad_pos hy.1 hy.2) (quadrantRad_pos hy.1 hy.2)
      (quadrantRad_sq_le hy.1 hy.2) (quadrantRad_eqv_congr hxy)
  · have hy : ¬ ((0 : Q') ≤ y ∧ y < (1 : Q')) :=
      fun h => hx (hpred.mpr h)
    simp only [quadrantSemi, dif_neg hx, dif_neg hy]
    exact CReal.Equiv.refl _

private theorem czero_limitLe_sqrtFrom
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u) :
    LimitLe CReal.czero (CReal.sqrtFrom u Lu hu hLu hLua) := by
  apply CReal.leRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  change (0 : Q') + -(CReal.heronSeq u n) ≤ 0
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-(CReal.heronSeq u n))))) ?_
  exact Q'.nonpos_neg_of_nonneg (Q'.le_of_lt (CReal.heronSeq_pos hu n))

/-- The constructive quadrant semicircle is antitone on nonnegative rational
arguments, including the zero extension at and beyond `x=1`. -/
theorem quadrantSemi_antitone {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hxy : x ≤ y) : LimitLe (quadrantSemi y) (quadrantSemi x) := by
  by_cases hy : (0 : Q') ≤ y ∧ y < (1 : Q')
  · have hx : (0 : Q') ≤ x ∧ x < (1 : Q') :=
      ⟨hx0, Q'.lt_of_le_of_lt hxy hy.2⟩
    rw [quadrantSemi, dif_pos hy, quadrantSemi, dif_pos hx]
    exact sqrtFrom_limitLe_of_le
      (quadrantRad y) (quadrantRad y)
      (quadrantRad_pos hy.1 hy.2) (quadrantRad_pos hy.1 hy.2)
      (quadrantRad_sq_le hy.1 hy.2)
      (quadrantRad x) (quadrantRad x)
      (quadrantRad_pos hx.1 hx.2) (quadrantRad_pos hx.1 hx.2)
      (quadrantRad_sq_le hx.1 hx.2) (quadrantRad_antitone hx0 hxy)
  · rw [quadrantSemi, dif_neg hy]
    by_cases hx : (0 : Q') ≤ x ∧ x < (1 : Q')
    · rw [quadrantSemi, dif_pos hx]
      exact czero_limitLe_sqrtFrom
        (quadrantRad x) (quadrantRad x)
        (quadrantRad_pos hx.1 hx.2) (quadrantRad_pos hx.1 hx.2)
        (quadrantRad_sq_le hx.1 hx.2)
    · rw [quadrantSemi, dif_neg hx]
      exact limitLe_refl _

/-- Twice the quadrant height.  Integrating this function on `[0,1]` is the
full upper-semicircle area represented by `seqSemi`. -/
def doubledQuadrantSemi (x : Q') : CReal :=
  CReal.add (quadrantSemi x) (quadrantSemi x)

theorem doubledQuadrantSemi_eqv_congr {x y : Q'} (hxy : x.eqv y) :
    CReal.Equiv (doubledQuadrantSemi x) (doubledQuadrantSemi y) := by
  unfold doubledQuadrantSemi
  exact CReal.Equiv.trans
    (CReal.add_congr_left (quadrantSemi_eqv_congr hxy))
    (CReal.add_congr_right (quadrantSemi_eqv_congr hxy))

theorem doubledQuadrantSemi_antitone {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hxy : x ≤ y) :
    LimitLe (doubledQuadrantSemi y) (doubledQuadrantSemi x) :=
  limitLe_add (quadrantSemi_antitone hx0 hxy)
    (quadrantSemi_antitone hx0 hxy)

/-! ### Explicit polygon and uniform meshes on the canonical interval -/

private theorem cx_nonneg_of_le (n j : Nat) (hn : 0 < n) (hj : j ≤ n) :
    (0 : Q') ≤ cx n j hn := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold cx
  rw [Q'.mkPos_num]
  have hsqN : j * j ≤ n * n := Nat.mul_le_mul hj hj
  have hsqI : (j:Int) * (j:Int) ≤ (n:Int) * (n:Int) := by
    exact_mod_cast hsqN
  omega

private theorem cx_diag_eqv_zero (n : Nat) (hn : 0 < n) :
    (cx n n hn).eqv 0 := by
  unfold cx
  show (Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _).den : Int)
  rw [Q'.mkPos_num, zero_den_cast, zero_num_cast, Int.mul_one, Int.zero_mul]
  omega

private theorem cx_zero_eqv_one (n : Nat) (hn : 0 < n) :
    (cx n 0 hn).eqv 1 := by
  unfold cx cden
  show (Q'.mkPos _ _ _).num * (((1 : Q').den : Int)) =
    (1 : Q').num * (((Q'.mkPos _ _ _).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  change ((n:Int)*(n:Int) - 0*0) * 1 =
    1 * (((n*n + 0*0 : Nat) : Int))
  push_cast
  simp only [Int.zero_mul, Int.mul_zero, Int.sub_zero, Int.mul_one,
    Int.one_mul]
  omega

/-- The polygon `x`-nodes in increasing order, saturated after the terminal
node so the generic mesh constructor has a globally monotone node family. -/
def polygonXNode (N j : Nat) : Q' :=
  let n := N + 1
  cx n (n - min j n) (Nat.succ_pos N)

private theorem polygonXNode_nonneg (N j : Nat) :
    (0 : Q') ≤ polygonXNode N j := by
  unfold polygonXNode
  exact cx_nonneg_of_le (N+1) ((N+1) - min j (N+1))
    (Nat.succ_pos N) (Nat.sub_le _ _)

private theorem polygonXNode_mono (N j : Nat) :
    polygonXNode N j ≤ polygonXNode N (j+1) := by
  change cx (N+1) ((N+1) - min j (N+1)) (Nat.succ_pos N) ≤
    cx (N+1) ((N+1) - min (j+1) (N+1)) (Nat.succ_pos N)
  by_cases hj : j < N + 1
  · have hj1 : j + 1 ≤ N + 1 := hj
    have hminj : min j (N+1) = j := Nat.min_eq_left (Nat.le_of_lt hj)
    have hminj1 : min (j+1) (N+1) = j+1 := Nat.min_eq_left hj1
    rw [hminj, hminj1]
    have hidx : (N + 1 - (j + 1)) + 1 = N + 1 - j := by omega
    rw [← hidx]
    exact Q'.le_of_lt
      (cx_next_lt_cx (N+1) (N+1-(j+1)) (Nat.succ_pos N))
  · have hnj : N + 1 ≤ j := Nat.le_of_not_gt hj
    have hnj1 : N + 1 ≤ j + 1 := Nat.le_trans hnj (Nat.le_succ j)
    rw [Nat.min_eq_right hnj, Nat.min_eq_right hnj1]
    exact Q'.le_refl' _

def polygonMeshCuts (N : Nat) : List Q' :=
  meshCuts (polygonXNode N) 0 N

theorem polygonMeshCuts_ordered (N : Nat) :
    OrderedCuts 0 1 (polygonMeshCuts N) := by
  have h := meshCuts_ordered (polygonXNode N)
    (polygonXNode_nonneg N) (polygonXNode_mono N) N 0
  have hend : meshEndIndex 0 N = N + 1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
  rw [hend] at h
  have hzero : (polygonXNode N 0).eqv 0 := by
    unfold polygonXNode
    simp only [Nat.min_eq_left (Nat.zero_le (N+1)), Nat.sub_zero]
    exact cx_diag_eqv_zero (N+1) (Nat.succ_pos N)
  have hone : (polygonXNode N (N+1)).eqv 1 := by
    unfold polygonXNode
    simp only [Nat.min_self, Nat.sub_self]
    exact cx_zero_eqv_one (N+1) (Nat.succ_pos N)
  exact h.congr_endpoints hzero hone

def unitMeshCuts (N : Nat) : List Q' :=
  uniformMeshCuts 1 1 N (by decide)

theorem unitMeshCuts_ordered (N : Nat) :
    OrderedCuts 0 1 (unitMeshCuts N) := by
  have h := uniformMeshCuts_ordered 1 1 N (by decide)
  have hzero :
      (gridNode 1 1 (N+1) 0 (by decide) (Nat.succ_pos N)).eqv 0 :=
    gridNode_zero_eqv 1 1 (N+1) (by decide) (Nat.succ_pos N)
  have hone :
      (gridNode 1 1 (N+1) (N+1) (by decide) (Nat.succ_pos N)).eqv 1 := by
    refine Q'.eqv_trans _ (rat 1 1 (by decide)) _
      (gridNode_endpoint_eqv 1 1 (N+1) (by decide) (Nat.succ_pos N)) ?_
    unfold rat
    decide
  exact h.congr_endpoints hzero hone

/-- **Exact common-refinement cross-brackets** between every rational polygon
mesh and every uniform quadrant mesh.  No same-index comparison is used. -/
theorem polygon_uniform_partition_cross_brackets (N M : Nat) :
    LimitLe
        (cPartitionRightSum doubledQuadrantSemi
          (cutCells 0 (polygonMeshCuts N) 1))
        (cPartitionLeftSum doubledQuadrantSemi
          (cutCells 0 (unitMeshCuts M) 1))
      ∧
    LimitLe
        (cPartitionRightSum doubledQuadrantSemi
          (cutCells 0 (unitMeshCuts M) 1))
        (cPartitionLeftSum doubledQuadrantSemi
          (cutCells 0 (polygonMeshCuts N) 1)) := by
  constructor
  · exact cOrdered_partitions_common_bracket doubledQuadrantSemi
      doubledQuadrantSemi_eqv_congr
      (fun hx0 hxy => doubledQuadrantSemi_antitone hx0 hxy)
      (polygonMeshCuts_ordered N) (unitMeshCuts_ordered M)
  · exact cOrdered_partitions_common_bracket doubledQuadrantSemi
      doubledQuadrantSemi_eqv_congr
      (fun hx0 hxy => doubledQuadrantSemi_antitone hx0 hxy)
      (unitMeshCuts_ordered M) (polygonMeshCuts_ordered N)

/-- **Constructive squeeze transfer.**  Pointwise sound brackets are enough;
their approximation thresholds may depend on the outer sequence index, so no
choice or uniform inner modulus is required. -/
theorem convergesTo_of_limitBracket
    {lower value upper : Nat → CReal} {L : CReal}
    (hlower : CReal.ConvergesTo lower L)
    (hupper : CReal.ConvergesTo upper L)
    (hbracket : ∀ N, LimitBracket (lower N) (value N) (upper N)) :
    CReal.ConvergesTo value L := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Nlo, hNlo⟩ := hlower q hq
  obtain ⟨Nup, hNup⟩ := hupper q hq
  refine ⟨max Nlo Nup, fun N hN => ?_⟩
  have hloN : Nlo ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hupN : Nup ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨Klo, hKlo⟩ := hNlo N hloN
  obtain ⟨Kup, hKup⟩ := hNup N hupN
  obtain ⟨Klv, hKlv⟩ := (hbracket N).1 q hq
  obtain ⟨Kvu, hKvu⟩ := (hbracket N).2 q hq
  refine ⟨max (max Klo Kup) (max Klv Kvu), fun k hk => ?_⟩
  have hklo : Klo ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
  have hkup : Kup ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  have hklv : Klv ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk
  have hkvu : Kvu ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk
  have hlvSub : (lower N).approx k + -(value N).approx k ≤ q := by
    have h := hKlv k hklv
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' q)))
  have hvuSub : (value N).approx k + -(upper N).approx k ≤ q := by
    have h := hKvu k hkvu
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' q)))
  have hlv : (lower N).approx k ≤ (value N).approx k + q :=
    le_add_of_sub_le_q hlvSub
  have hvu : (value N).approx k ≤ (upper N).approx k + q :=
    le_add_of_sub_le_q hvuSub
  have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain : (value N).approx k ≤ (L.approx k + q) + q :=
      Q'.le_trans' _ _ _ hvu
        (Q'.add_le_add_right _ _ q (hKup k hkup).1)
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (L.approx k) q q)
        (Q'.add_eqv_congr_left _ _ _ hqq)))
  · have hchain : L.approx k ≤ ((value N).approx k + q) + q :=
      Q'.le_trans' _ _ _ (hKlo k hklo).2
        (Q'.add_le_add_right _ _ q hlv)
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((value N).approx k) q q)
        (Q'.add_eqv_congr_left _ _ _ hqq)))

private theorem convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
    (h : CReal.ConvergesTo s L) (hL : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Nstage, hstage⟩ := h q hq
  obtain ⟨Nequiv, hequiv⟩ := hL q hq
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napprox, hclose⟩ := hstage N hN
  refine ⟨max Napprox Nequiv, fun k hk => ?_⟩
  have hkA : Napprox ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkE : Nequiv ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hsL, hLs⟩ := hclose k hkA
  obtain ⟨hLL', hL'L⟩ := hequiv k hkE
  have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  constructor
  · refine Q'.le_trans' _ _ _ hsL ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hLL') ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (L'.approx k) q q)
        (Q'.add_eqv_congr_left (L'.approx k) _ _ hqq))
  · refine Q'.le_trans' _ _ _ hL'L ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hLs) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((s N).approx k) q q)
        (Q'.add_eqv_congr_left ((s N).approx k) _ _ hqq))

/-- **The rational inscribed-polygon sequence converges to `pi/2`.**  Its
unconditional Darboux limit is `atanIntegral`, and the branch-safe four-step
Machin addition theorem identifies that limit with `halfPi`. -/
theorem polygonSeq_converges_halfPi :
    CReal.ConvergesTo polygonSeq Constructive.Pi.halfPi :=
  convergesTo_retarget polygonSeq_converges atanIntegral_eq_halfPi

/-- The lower polygon Darboux sequence converges to `pi/2`, with the explicit
`4/(N+1)` squeeze proved above. -/
theorem polygonLowerSeq_converges_halfPi :
    CReal.ConvergesTo polygonLowerSeq Constructive.Pi.halfPi :=
  polygonLowerSeq_converges_of_polygonSeq polygonSeq_converges_halfPi

/-- The upper polygon Darboux sequence also converges to `pi/2`. -/
theorem polygonUpperSeq_converges_halfPi :
    CReal.ConvergesTo polygonUpperSeq Constructive.Pi.halfPi :=
  polygonUpperSeq_converges_of_polygonSeq polygonSeq_converges_halfPi

/-- **Final pointwise comparison interface.**  To obtain the desired midpoint
limit it now suffices to place each genuine `seqSemi N` between the explicit
lower and upper rational polygon Darboux terms in the sound constructive-real
order.  No uniform approximation-index modulus is demanded: the squeeze
transfer permits each finite common-refinement proof to supply its own eventual
threshold. -/
theorem seqSemi_converges_halfPi_of_polygon_brackets
    (h : ∀ N, LimitBracket (polygonLowerSeq N) (seqSemi N) (polygonUpperSeq N)) :
    CReal.ConvergesTo seqSemi Constructive.Pi.halfPi :=
  convergesTo_of_limitBracket
    polygonLowerSeq_converges_halfPi polygonUpperSeq_converges_halfPi h

end YMGap.Continuum.SemicirclePolygonMidpointBridge

#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonCross_eqv_trapezoid_add_boundary
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.finSum_adjacentDiff_telescope
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.boundaryCorrectionSum_eqv_zero
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonSemiQ_eqv_polygonTrapezoidQ
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.cx_sub_next_eqv_xWidthClosed
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.xWidthClosed_le_two_over_n
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.cy_lt_next
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonUpperQ_le_lower_add_mesh
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonSemiQ_darboux_width
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonLowerSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonUpperSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.convergesTo_of_limitBracket
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.seqSemi_converges_halfPi_of_polygon_brackets
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.cOrdered_partitions_common_bracket
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.quadrantSemi_eqv_congr
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.quadrantSemi_antitone
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygonMeshCuts_ordered
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.unitMeshCuts_ordered
#print axioms YMGap.Continuum.SemicirclePolygonMidpointBridge.polygon_uniform_partition_cross_brackets
