/-
# Adjacent-column differences for the first general Hahn rows

Column elimination for the general shell matrix is driven by the Hahn
forward-difference law.  This module establishes the law uniformly for the
first two nonconstant rows.  The proof is not a finite-label computation:
the natural factorial rows are first bridged to symbolic `Q'` polynomials,
and the two polynomial difference identities are then checked by the
constructive reflective ring normaliser.

The remaining all-order step is a creative-telescoping theorem for the finite
alternating factorial sum `transvectFactorialCoeff`.
-/

import YMGap.Continuum.SU2GeneralShellHahnMatrix
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2GeneralHahnAdjacentDifference

set_option maxRecDepth 24000
set_option maxHeartbeats 1200000

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem ofInt_neg_one : Q'.ofInt (-1) = (-1 : Q') := rfl
private theorem ofInt_two : Q'.ofInt 2 = (2 : Q') := rfl

/-! ## Symbolic rows -/

def qPred (x : Q') : Q' := x + (-1 : Q')

def qSub (x y : Q') : Q' := x + (-y)

/-- The general affine Hahn row in independent left/right coordinates. -/
def hahnRowOneSymbolic (M N X Y : Q') : Q' :=
  X * qSub N Y + -(qSub M X * Y)

/-- The general quadratic Hahn row in independent left/right coordinates. -/
def hahnRowTwoSymbolic (M N X Y : Q') : Q' :=
  (X * qPred X) * (qSub N Y * qPred (qSub N Y)) +
    -((((2 : Q') * X) * qSub M X) * (Y * qSub N Y)) +
    (qSub M X * qPred (qSub M X)) * (Y * qPred Y)

private def eM : PolyExpr := .var 0
private def eN : PolyExpr := .var 1
private def eX : PolyExpr := .var 2
private def eY : PolyExpr := .var 3
private def eOne : PolyExpr := .const 1
private def eTwo : PolyExpr := .const 2

private def ePred (x : PolyExpr) : PolyExpr := .add x (.const (-1))
private def eSub (x y : PolyExpr) : PolyExpr := .add x (.neg y)

private def rowOneExpr (M N X Y : PolyExpr) : PolyExpr :=
  .add (.mul X (eSub N Y)) (.neg (.mul (eSub M X) Y))

private def rowTwoExpr (M N X Y : PolyExpr) : PolyExpr :=
  .add
    (.add
      (.mul (.mul X (ePred X))
        (.mul (eSub N Y) (ePred (eSub N Y))))
      (.neg (.mul (.mul (.mul eTwo X) (eSub M X))
        (.mul Y (eSub N Y)))))
    (.mul (.mul (eSub M X) (ePred (eSub M X)))
      (.mul Y (ePred Y)))

private def rowOneDiffLHS : PolyExpr :=
  .add
    (rowOneExpr eM eN (.add eX eOne) (ePred eY))
    (.neg (rowOneExpr eM eN eX eY))

private def rowOneDiffRHS : PolyExpr := .add eM eN

private def rowTwoDiffLHS : PolyExpr :=
  .add
    (rowTwoExpr eM eN (.add eX eOne) (ePred eY))
    (.neg (rowTwoExpr eM eN eX eY))

private def rowTwoDiffRHS : PolyExpr :=
  .mul
    (.mul eTwo (ePred (.add eM eN)))
    (rowOneExpr (ePred eM) (ePred eN) eX (ePred eY))

private theorem rowOneDiff_normal :
    normalize rowOneDiffLHS = normalize rowOneDiffRHS := by decide

private theorem rowTwoDiff_normal :
    normalize rowTwoDiffLHS = normalize rowTwoDiffRHS := by decide

private def rowEnv (M N X Y : Q') : Nat → Q'
  | 0 => M
  | 1 => N
  | 2 => X
  | _ => Y

/-- Exact affine forward difference, over arbitrary constructive rationals. -/
theorem hahnRowOneSymbolic_difference (M N X Y : Q') :
    (hahnRowOneSymbolic M N (X + 1) (qPred Y) +
      -(hahnRowOneSymbolic M N X Y)) ≈ M + N := by
  have h := poly_identity_of_normal_eq
    rowOneDiffLHS rowOneDiffRHS rowOneDiff_normal (rowEnv M N X Y)
  simpa only [rowOneDiffLHS, rowOneDiffRHS, rowOneExpr, rowEnv,
    hahnRowOneSymbolic, qSub, qPred, eSub, ePred, eM, eN, eX, eY, eOne,
    eval, ofInt_one, ofInt_neg_one, ofInt_two] using h

/-- Exact quadratic forward difference.  The scale is the prospective second
determinant pivot `2 * (M+N-1)`. -/
theorem hahnRowTwoSymbolic_difference (M N X Y : Q') :
    (hahnRowTwoSymbolic M N (X + 1) (qPred Y) +
      -(hahnRowTwoSymbolic M N X Y)) ≈
      ((2 : Q') * qPred (M + N)) *
        hahnRowOneSymbolic (qPred M) (qPred N) X (qPred Y) := by
  have h := poly_identity_of_normal_eq
    rowTwoDiffLHS rowTwoDiffRHS rowTwoDiff_normal (rowEnv M N X Y)
  simpa only [rowTwoDiffLHS, rowTwoDiffRHS, rowTwoExpr, rowOneExpr,
    rowEnv, hahnRowTwoSymbolic, hahnRowOneSymbolic, qSub, qPred, eSub,
    ePred, eM, eN, eX, eY, eOne, eTwo, eval, ofInt_one,
    ofInt_neg_one, ofInt_two] using h

/-! ## Natural-to-symbolic bridges -/

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

private theorem ofNat_succ_eq (a : Nat) :
    Q'.ofNat (a + 1) = Q'.ofNat a + 1 := by
  change Q'.ofNat (a + 1) = Q'.add (Q'.ofNat a) (Q'.ofNat 1)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = qSub (Q'.ofNat a) (Q'.ofNat b) := by
  unfold qSub
  change Q'.ofNat (a - b) =
    Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofNat b))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private theorem ofNat_add_eq (a b : Nat) :
    Q'.ofNat (a + b) = Q'.ofNat a + Q'.ofNat b := by
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem ofNat_mul_eq (a b : Nat) :
    Q'.ofNat (a * b) = Q'.ofNat a * Q'.ofNat b := by
  change Q'.ofNat (a * b) = Q'.mul (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.mul Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]

private theorem nat_falling_two_cast (a : Nat) :
    (a : Int) * ((a - 1 : Nat) : Int) =
      (a : Int) * ((a : Int) - 1) := by
  cases a with
  | zero => simp
  | succ a =>
      rw [show a + 1 - 1 = a by omega]
      push_cast
      congr 1
      omega

/-- The order-one factorial coefficient is the symbolic affine Hahn row on
every physical monomial coordinate. -/
theorem transvectFactorialCoeff_one_symbolic (m n i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    transvectFactorialCoeff m n 1 i j ≈
      hahnRowOneSymbolic (Q'.ofNat m) (Q'.ofNat n)
        (Q'.ofNat i) (Q'.ofNat j) := by
  refine Q'.eqv_trans _ _ _ (transvectFactorialCoeff_one m n i j) ?_
  unfold hahnRowOneSymbolic qSub Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, Int.mul_one]
  have hmi : ((m - i : Nat) : Int) = (m : Int) - (i : Int) := by omega
  have hnj : ((n - j : Nat) : Int) = (n : Int) - (j : Int) := by omega
  push_cast
  rw [hmi, hnj]
  simp only [Int.sub_eq_add_neg]

/-- The order-two factorial coefficient is the symbolic quadratic Hahn row on
every physical monomial coordinate, including all falling-factorial edges. -/
theorem transvectFactorialCoeff_two_symbolic (m n i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    transvectFactorialCoeff m n 2 i j ≈
      hahnRowTwoSymbolic (Q'.ofNat m) (Q'.ofNat n)
        (Q'.ofNat i) (Q'.ofNat j) := by
  refine Q'.eqv_trans _ _ _ (transvectFactorialCoeff_two m n i j) ?_
  unfold hahnRowTwoSymbolic qSub qPred Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, Int.mul_one,
    show (2 : Q').num = 2 from rfl,
    show ((2 : Q').den : Int) = 1 from rfl,
    show ((-1 : Q').num) = -1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl]
  have hmi : ((m - i : Nat) : Int) = (m : Int) - (i : Int) := by omega
  have hnj : ((n - j : Nat) : Int) = (n : Int) - (j : Int) := by omega
  have hfi := nat_falling_two_cast i
  have hfnj := nat_falling_two_cast (n - j)
  have hfmi := nat_falling_two_cast (m - i)
  have hfj := nat_falling_two_cast j
  push_cast
  rw [hfi, hfnj, hfmi, hfj, hmi, hnj]
  simp only [Int.sub_eq_add_neg]
  ac_rfl

/-! ## Adjacent coefficient laws -/

/-- Uniform affine adjacent-column law in independent source coordinates. -/
theorem transvectFactorialCoeff_one_adjacent (m n i j : Nat)
    (hi : i < m) (hj0 : 0 < j) (hj : j ≤ n) :
    (transvectFactorialCoeff m n 1 (i + 1) (j - 1) +
      -(transvectFactorialCoeff m n 1 i j)) ≈
      Q'.ofNat (m + n) := by
  have hshift := transvectFactorialCoeff_one_symbolic
    m n (i + 1) (j - 1) (by omega) (by omega)
  rw [ofNat_succ_eq, ofNat_sub_eq j 1 (by omega)] at hshift
  have hbase := transvectFactorialCoeff_one_symbolic m n i j (by omega) hj
  have hdiff := Q'.add_eqv_congr' hshift
    (Q'.neg_eqv_congr _ _ hbase)
  refine Q'.eqv_trans _ _ _ hdiff ?_
  refine Q'.eqv_trans _ (Q'.ofNat m + Q'.ofNat n) _
    (hahnRowOneSymbolic_difference _ _ _ _) ?_
  show (Q'.ofNat m + Q'.ofNat n).eqv (Q'.ofNat (m + n))
  show (Q'.ofNat m + Q'.ofNat n).num * (1 : Int) =
    (m + n : Int) * ((Q'.ofNat m + Q'.ofNat n).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- Uniform quadratic adjacent-column law.  This is the first nonlinear
instance of the general Hahn elimination recurrence. -/
theorem transvectFactorialCoeff_two_adjacent (m n i j : Nat)
    (hi : i < m) (hj0 : 0 < j) (hj : j ≤ n) :
    (transvectFactorialCoeff m n 2 (i + 1) (j - 1) +
      -(transvectFactorialCoeff m n 2 i j)) ≈
      Q'.ofNat (2 * (m + n - 1)) *
        transvectFactorialCoeff (m - 1) (n - 1) 1 i (j - 1) := by
  have hshift := transvectFactorialCoeff_two_symbolic
    m n (i + 1) (j - 1) (by omega) (by omega)
  rw [ofNat_succ_eq, ofNat_sub_eq j 1 (by omega)] at hshift
  have hbase := transvectFactorialCoeff_two_symbolic m n i j (by omega) hj
  have hdiff := Q'.add_eqv_congr' hshift
    (Q'.neg_eqv_congr _ _ hbase)
  have hred := transvectFactorialCoeff_one_symbolic
    (m - 1) (n - 1) i (j - 1) (by omega) (by omega)
  rw [ofNat_sub_eq m 1 (by omega), ofNat_sub_eq n 1 (by omega),
    ofNat_sub_eq j 1 (by omega)] at hred
  have hscale :
      Q'.ofNat (2 * (m + n - 1)) =
        (2 : Q') * qPred (Q'.ofNat m + Q'.ofNat n) := by
    rw [ofNat_mul_eq, ofNat_sub_eq (m + n) 1 (by omega), ofNat_add_eq]
    rfl
  rw [hscale]
  refine Q'.eqv_trans _ _ _ hdiff ?_
  refine Q'.eqv_trans _ _ _
    (hahnRowTwoSymbolic_difference _ _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hred)

/-! ## Shell-facing column elimination -/

/-- The exact requested adjacent-column identity for the affine Hahn row. -/
theorem hahnEntry_one_adjacent (m n t i : Nat)
    (him : i < m) (hit : i < t) (hjn : t - i ≤ n) :
    (hahnEntry m n t 1 (i + 1) + -(hahnEntry m n t 1 i)) ≈
      Q'.ofNat (1 * (m + n - 1 + 1)) *
        hahnEntry (m - 1) (n - 1) (t - 1) 0 i := by
  have hj0 : 0 < t - i := by omega
  have hshift : t - (i + 1) = t - i - 1 := by omega
  have hreduced : t - 1 - i = t - i - 1 := by omega
  unfold hahnEntry
  rw [hshift, hreduced]
  have hcore := transvectFactorialCoeff_one_adjacent
    m n i (t - i) him hj0 hjn
  have hscale : 1 * (m + n - 1 + 1) = m + n := by omega
  rw [hscale]
  refine Q'.eqv_trans _ (Q'.ofNat (m + n)) _ hcore ?_
  have hz := transvectFactorialCoeff_zero
    (m - 1) (n - 1) i (t - i - 1)
  exact Q'.eqv_symm (Q'.eqv_trans _ (Q'.ofNat (m + n) * 1) _
    (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _))

/-- The exact requested adjacent-column identity for the quadratic Hahn row. -/
theorem hahnEntry_two_adjacent (m n t i : Nat)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (_ht : 2 ≤ t)
    (him : i < m) (hit : i < t) (hjn : t - i ≤ n) :
    (hahnEntry m n t 2 (i + 1) + -(hahnEntry m n t 2 i)) ≈
      Q'.ofNat (2 * (m + n - 2 + 1)) *
        hahnEntry (m - 1) (n - 1) (t - 1) 1 i := by
  have hj0 : 0 < t - i := by omega
  have hshift : t - (i + 1) = t - i - 1 := by omega
  have hreduced : t - 1 - i = t - i - 1 := by omega
  unfold hahnEntry
  rw [hshift, hreduced]
  have hcore := transvectFactorialCoeff_two_adjacent
    m n i (t - i) him hj0 hjn
  have hscale : 2 * (m + n - 2 + 1) = 2 * (m + n - 1) := by omega
  rw [hscale]
  exact hcore

end YMGap.Continuum.SU2GeneralHahnAdjacentDifference

#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.hahnRowOneSymbolic_difference
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.hahnRowTwoSymbolic_difference
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.transvectFactorialCoeff_one_symbolic
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.transvectFactorialCoeff_two_symbolic
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.transvectFactorialCoeff_one_adjacent
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.transvectFactorialCoeff_two_adjacent
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.hahnEntry_one_adjacent
#print axioms YMGap.Continuum.SU2GeneralHahnAdjacentDifference.hahnEntry_two_adjacent
