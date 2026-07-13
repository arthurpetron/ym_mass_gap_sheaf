/-
The variable-anchor theta comparison is necessarily nonlocal in the mode
index.  This module records the exact first-cell obstruction, independently
of the Pascal/Bernstein development.
-/

import YMGap.Continuum.HarmonicThetaRepresentation
import YMGap.Continuum.ThetaResidualBernsteinPilot

namespace YMGap.Continuum.HarmonicThetaTermwiseFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.ThetaResidualBernsteinPilot

local infix:50 " ≈ " => Q'.eqv

private def twoThirds : Q' := Q'.mkPos 2 3 (by decide)
private def halfQ : Q' := Q'.mkPos 1 2 (by decide)
private def publicRetuneCube (w : Q') : Q' :=
  qpow (halfQ * ((1 : Q') + w)) 3

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private def thetaOneHorner : List Int → RingNormaliser.PolyExpr
  | [] => .const 0
  | c :: cs => .add (.const c)
      (.mul (.var 0) (thetaOneHorner cs))

private def firstTransportScaledL : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.mul w w
  .add
    (.mul (.const 8)
      (.mul w (.mul (.const 2) (.pow q 2))))
    (.mul (.pow w 2)
      (thetaOneHorner [1, 3, 3, -15, 0, 0, 4, 12, 12, 4]))

private def firstTransportScaledR : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.mul w w
  .mul (.pow (.add (.const 1) w) 3)
    (.add
      (.mul (.const 1) (.pow q 1))
      (.mul (.const 4) (.pow q 4)))

private theorem firstTransportScaled_normal :
    RingNormaliser.normalize firstTransportScaledL =
      RingNormaliser.normalize firstTransportScaledR := by
  decide

/-- Integer-scaled polynomial identity behind the first nonlocal reserve
move.  The second summand on the left is exactly the positive Bernstein
remainder from cutoff one. -/
theorem first_transport_scaled_identity (w : Q') :
    Q'.ofNat 8 * (w * halfThetaTerm w 1) +
        qpow w 2 * QPoly.eval thetaResidualOneP w ≈
      qpow ((1 : Q') + w) 3 *
        (integerThetaTerm w 1 + integerThetaTerm w 2) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    firstTransportScaledL firstTransportScaledR
    firstTransportScaled_normal (fun _ => w)
  simpa [firstTransportScaledL, firstTransportScaledR, thetaOneHorner,
    RingNormaliser.eval, RingNormaliser.qpow, thetaResidualOneP,
    QPoly.eval, halfThetaTerm, integerThetaTerm, qpow] using h

private theorem eight_mul_retuneCube (w : Q') :
    Q'.ofNat 8 * retuneCube w ≈ qpow ((1 : Q') + w) 3 := by
  change Q'.ofNat 8 * publicRetuneCube w ≈ qpow ((1 : Q') + w) 3
  unfold publicRetuneCube halfQ
  simp only [qpow]
  ring_qeqv

private def secondTransportScaledL : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.mul w w
  .add
    (.mul (.const 8)
      (.mul w
        (.add
          (.mul (.const 2) (.pow q 2))
          (.mul (.const 6) (.pow q 6)))))
    (.mul (.pow w 2)
      (thetaOneHorner
        [1, 3, 3, -15, 0, 0, 4, 12, 12, 4, 0, -48, 0, 0, 0, 0,
          9, 27, 27, 9]))

private def secondTransportScaledR : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.mul w w
  .mul (.pow (.add (.const 1) w) 3)
    (.add
      (.add
        (.mul (.const 1) (.pow q 1))
        (.mul (.const 4) (.pow q 4)))
      (.mul (.const 9) (.pow q 9)))

private theorem secondTransportScaled_normal :
    RingNormaliser.normalize secondTransportScaledL =
      RingNormaliser.normalize secondTransportScaledR := by
  decide

/-- The analogous integer-scaled identity for the first two half cells and
first three integer cells. -/
theorem second_transport_scaled_identity (w : Q') :
    Q'.ofNat 8 *
          (w * (halfThetaTerm w 1 + halfThetaTerm w 2)) +
        qpow w 2 * QPoly.eval thetaResidualTwoP w ≈
      qpow ((1 : Q') + w) 3 *
        ((integerThetaTerm w 1 + integerThetaTerm w 2) +
          integerThetaTerm w 3) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    secondTransportScaledL secondTransportScaledR
    secondTransportScaled_normal (fun _ => w)
  simpa [secondTransportScaledL, secondTransportScaledR, thetaOneHorner,
    RingNormaliser.eval, RingNormaliser.qpow, thetaResidualTwoP,
    QPoly.eval, halfThetaTerm, integerThetaTerm, qpow] using h

/-- Generic consumer for an integer-scaled theta reserve identity.  A
nonnegative remainder in

`8 L + P ≈ (1+w)³ I`

is exactly what is needed to conclude `L ≤ retuneCube(w) I`. -/
theorem scaled_theta_remainder_pays {w L I P : Q'}
    (hP0 : (0 : Q') ≤ P)
    (hscaled : Q'.ofNat 8 * L + P ≈
      qpow ((1 : Q') + w) 3 * I) :
    L ≤ retuneCube w * I := by
  have hLT : Q'.ofNat 8 * L ≤ qpow ((1 : Q') + w) 3 * I :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (Q'.ofNat 8 * L) P hP0)
      (Q'.le_of_eqv hscaled)
  have hright :
      Q'.ofNat 8 * (retuneCube w * I) ≈
        qpow ((1 : Q') + w) 3 * I := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 8) (retuneCube w) I)) ?_
    exact Q'.mul_eqv_congr_right _ _ I (eight_mul_retuneCube w)
  have hmul : Q'.ofNat 8 * L ≤
      Q'.ofNat 8 * (retuneCube w * I) :=
    Q'.le_trans' _ _ _ hLT (Q'.ge_of_eqv hright)
  exact Q'.le_of_mul_le_mul_left hmul (by decide)

theorem twoThirds_le_harmW (k : Nat) (hk : 1 ≤ k) :
    twoThirds ≤ harmW k := by
  show twoThirds.num * ((harmW k).den : Int) ≤
    (harmW k).num * twoThirds.den
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  unfold twoThirds harmW harmU oneSub unit
  simp only [Q'.mkPos_num, Q'.mkPos_den, Q'.add_num_cast,
    Q'.add_den_cast, Q'.neg_den, neg_num_cast, h1n, h1d,
    Int.one_mul, Int.mul_one]
  push_cast
  omega

/-- At the first nontrivial harmonic scale, the first half-integer theta
cell already exceeds the complete retune budget of the matching integer
cell.  Thus the target comparison cannot be proved term by term; reserve
must move between distinct theta modes. -/
theorem first_theta_cell_retune_fails_k1 :
    ¬ (harmW 1 * halfThetaTerm (harmW 1) 1 ≤
      retuneCube (harmW 1) * integerThetaTerm (harmW 1) 1) := by
  unfold harmW harmU oneSub unit retuneCube retuneBase
  unfold halfThetaTerm integerThetaTerm
  decide

private theorem first_cell_raw {w : Q'} (hw : twoThirds ≤ w) :
    retuneCube w * integerThetaTerm w 1 <
      w * halfThetaTerm w 1 := by
  change publicRetuneCube w * integerThetaTerm w 1 <
    w * halfThetaTerm w 1
  show (publicRetuneCube w * integerThetaTerm w 1).num *
      ((w * halfThetaTerm w 1).den : Int) <
    (w * halfThetaTerm w 1).num *
      (publicRetuneCube w * integerThetaTerm w 1).den
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  have hcross : 2 * (w.den : Int) ≤ 3 * w.num := by
    change twoThirds.num * (w.den : Int) ≤ w.num * twoThirds.den at hw
    unfold twoThirds at hw
    simp only [Q'.mkPos_num, Q'.mkPos_den] at hw
    omega
  have hd : (0 : Int) < (w.den : Int) := by
    exact_mod_cast w.den_pos
  have hn : (0 : Int) < w.num := by omega
  let s : Int := (w.den : Int) + w.num
  have hs : (0 : Int) < s := by dsimp [s]; omega
  have h2s : 2 * s ≤ 5 * w.num := by dsimp [s]; omega
  have hsq : (2 * s) * (2 * s) ≤
      (5 * w.num) * (5 * w.num) :=
    Int.mul_le_mul h2s h2s (by omega) (by omega)
  have hcubeRaw : ((2 * s) * (2 * s)) * (2 * s) ≤
      ((5 * w.num) * (5 * w.num)) * (5 * w.num) :=
    calc
      ((2 * s) * (2 * s)) * (2 * s) ≤
          ((5 * w.num) * (5 * w.num)) * (2 * s) :=
        Int.mul_le_mul_of_nonneg_right hsq (by omega)
      _ ≤ ((5 * w.num) * (5 * w.num)) * (5 * w.num) :=
        Int.mul_le_mul_of_nonneg_left h2s
          (Int.mul_nonneg (by omega) (by omega))
  have hcubeScaled : 8 * (s * s * s) ≤
      125 * (w.num * w.num * w.num) := by
    calc
      8 * (s * s * s) = ((2 * s) * (2 * s)) * (2 * s) := by
        rw [show (8 : Int) = 2 * 2 * 2 by decide]
        ac_rfl
      _ ≤ ((5 * w.num) * (5 * w.num)) * (5 * w.num) := hcubeRaw
      _ = 125 * (w.num * w.num * w.num) := by
        rw [show (125 : Int) = 5 * 5 * 5 by decide]
        ac_rfl
  have hn3 : (0 : Int) < w.num * w.num * w.num :=
    Int.mul_pos (Int.mul_pos hn hn) hn
  have h125 : 125 * (w.num * w.num * w.num) <
      128 * (w.num * w.num * w.num) :=
    Int.mul_lt_mul_of_pos_right (by decide) hn3
  have hcubic :
      ((w.den : Int) + w.num) * ((w.den : Int) + w.num) *
          ((w.den : Int) + w.num) <
        16 * w.num * w.num * w.num := by
    have h8 : 8 * (s * s * s) <
        8 * (16 * w.num * w.num * w.num) := by
      calc
        8 * (s * s * s) ≤ 125 * (w.num * w.num * w.num) := hcubeScaled
        _ < 128 * (w.num * w.num * w.num) := h125
        _ = 8 * (16 * w.num * w.num * w.num) := by
          rw [show (128 : Int) = 8 * 16 by decide]
          ac_rfl
    have hc := Int.lt_of_mul_lt_mul_left h8 (by decide : (0 : Int) ≤ 8)
    dsimp [s] at hc
    exact hc
  unfold publicRetuneCube halfQ integerThetaTerm halfThetaTerm
  simp only [qpow, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.add_num_cast, Q'.add_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, h1n, h1d,
    Int.one_mul, Int.mul_one]
  rw [show ((1 * 1 : Nat) : Int) = 1 by decide,
    show ((1 * (1 + 1) : Nat) : Int) = 2 by decide]
  simp only [Int.one_mul]
  have hn2 : (0 : Int) < w.num * w.num := Int.mul_pos hn hn
  have hd5 : (0 : Int) <
      (w.den : Int) * (w.den : Int) * (w.den : Int) *
        (w.den : Int) * (w.den : Int) := by
    exact Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos hd hd) hd) hd) hd
  have hscaled := Int.mul_lt_mul_of_pos_right
    (Int.mul_lt_mul_of_pos_right hcubic hn2) hd5
  calc
    ((w.den : Int) + w.num) * ((w.den : Int) + w.num) *
          ((w.den : Int) + w.num) * (w.num * w.num) *
        ((w.den : Int) * ((w.den : Int) * (w.den : Int) *
          ((w.den : Int) * (w.den : Int)))) =
      (((w.den : Int) + w.num) * ((w.den : Int) + w.num) *
        ((w.den : Int) + w.num) * (w.num * w.num)) *
        ((w.den : Int) * (w.den : Int) * (w.den : Int) *
          (w.den : Int) * (w.den : Int)) := by ac_rfl
    _ < ((16 * w.num * w.num * w.num) * (w.num * w.num)) *
        ((w.den : Int) * (w.den : Int) * (w.den : Int) *
          (w.den : Int) * (w.den : Int)) := hscaled
    _ = w.num * (2 * (w.num * w.num * (w.num * w.num))) *
        ((2 * (w.den : Int)) * (2 * (w.den : Int)) *
          (2 * (w.den : Int)) *
            ((w.den : Int) * (w.den : Int))) := by
      rw [show (16 : Int) = 2 * 2 * 2 * 2 by decide]
      ac_rfl

/-- **Uniform harmonic first-cell obstruction.**  At every scale `k≥1`, the
first half-integer theta cell is strictly larger than the whole retune budget
assigned to the first integer cell.  Consequently no proof of the growing
head can be termwise in the theta index; its positive certificate must move
reserve between different modes. -/
theorem first_theta_cell_retune_fails (k : Nat) (hk : 1 ≤ k) :
    ¬ (harmW k * halfThetaTerm (harmW k) 1 ≤
      retuneCube (harmW k) * integerThetaTerm (harmW k) 1) := by
  intro hle
  have hlt := first_cell_raw (twoThirds_le_harmW k hk)
  exact (Int.not_le.mpr hlt) hle

/-- There is no scale-uniform proof obtained by assigning each half-theta
cell only the retune budget of the integer cell with the same index. -/
theorem no_same_index_theta_allocation (k : Nat) (hk : 1 ≤ k) :
    ¬ (∀ n : Nat,
      harmW k * halfThetaTerm (harmW k) n ≤
        retuneCube (harmW k) * integerThetaTerm (harmW k) n) := by
  intro h
  exact first_theta_cell_retune_fails k hk (h 1)

/-! ## The first genuinely nonlocal transport cell -/

/-- The retune budgets of the first two integer modes together pay the first
half-integer cell.  This is the smallest possible nonlocal move: the
same-index allocation is refuted above, while the exact two-cell surplus is
`w² * thetaResidualOneP(w) / 8`. -/
theorem first_half_cell_paid_by_first_two_integer {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    w * halfThetaTerm w 1 ≤
      retuneCube w *
        (integerThetaTerm w 1 + integerThetaTerm w 2) := by
  let L := w * halfThetaTerm w 1
  let P := qpow w 2 * QPoly.eval thetaResidualOneP w
  let I := integerThetaTerm w 1 + integerThetaTerm w 2
  let T := qpow ((1 : Q') + w) 3 * I
  have hres : (0 : Q') ≤ QPoly.eval thetaResidualOneP w :=
    thetaResidualOne_nonneg hw0 hw1
  have hP0 : (0 : Q') ≤ P := by
    unfold P
    exact Q'.mul_nonneg _ _ (qpow_nonneg w hw0 2) hres
  have hscaledEq : Q'.ofNat 8 * L + P ≈ T := by
    dsimp [L, P, I, T]
    exact first_transport_scaled_identity w
  have hLT : Q'.ofNat 8 * L ≤ T :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (Q'.ofNat 8 * L) P hP0)
      (Q'.le_of_eqv hscaledEq)
  have hright :
      Q'.ofNat 8 * (retuneCube w * I) ≈ T := by
    unfold T
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 8) (retuneCube w) I)) ?_
    exact Q'.mul_eqv_congr_right _ _ I (eight_mul_retuneCube w)
  have hmul : Q'.ofNat 8 * L ≤
      Q'.ofNat 8 * (retuneCube w * I) :=
    Q'.le_trans' _ _ _ hLT (Q'.ge_of_eqv hright)
  exact Q'.le_of_mul_le_mul_left hmul (by decide)

/-- Harmonic specialization of the first two-cell reserve transfer. -/
theorem harmonic_first_half_cell_paid_by_first_two_integer (k : Nat) :
    harmW k * halfThetaTerm (harmW k) 1 ≤
      retuneCube (harmW k) *
        (integerThetaTerm (harmW k) 1 +
          integerThetaTerm (harmW k) 2) :=
  first_half_cell_paid_by_first_two_integer
    (harmW_nonneg k) (harmW_le_one k)

/-- The first three integer-mode budgets jointly pay the first two
half-integer cells.  This is the cutoff-two instance of the same exact
scaled-remainder mechanism. -/
theorem first_two_half_cells_paid_by_first_three_integer {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    w * (halfThetaTerm w 1 + halfThetaTerm w 2) ≤
      retuneCube w *
        ((integerThetaTerm w 1 + integerThetaTerm w 2) +
          integerThetaTerm w 3) := by
  apply scaled_theta_remainder_pays
  · exact Q'.mul_nonneg _ _ (qpow_nonneg w hw0 2)
      (thetaResidualTwo_nonneg hw0 hw1)
  · exact second_transport_scaled_identity w

/-- Harmonic specialization of the cumulative cutoff-two reserve
transfer. -/
theorem harmonic_first_two_half_cells_paid_by_first_three_integer
    (k : Nat) :
    harmW k *
        (halfThetaTerm (harmW k) 1 + halfThetaTerm (harmW k) 2) ≤
      retuneCube (harmW k) *
        ((integerThetaTerm (harmW k) 1 +
            integerThetaTerm (harmW k) 2) +
          integerThetaTerm (harmW k) 3) :=
  first_two_half_cells_paid_by_first_three_integer
    (harmW_nonneg k) (harmW_le_one k)

#print axioms first_theta_cell_retune_fails_k1
#print axioms twoThirds_le_harmW
#print axioms first_theta_cell_retune_fails
#print axioms no_same_index_theta_allocation
#print axioms first_transport_scaled_identity
#print axioms second_transport_scaled_identity
#print axioms scaled_theta_remainder_pays
#print axioms first_half_cell_paid_by_first_two_integer
#print axioms harmonic_first_half_cell_paid_by_first_two_integer
#print axioms first_two_half_cells_paid_by_first_three_integer
#print axioms harmonic_first_two_half_cells_paid_by_first_three_integer

end YMGap.Continuum.HarmonicThetaTermwiseFence
