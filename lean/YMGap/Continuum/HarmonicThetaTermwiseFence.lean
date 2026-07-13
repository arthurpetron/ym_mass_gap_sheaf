/-
The variable-anchor theta comparison is necessarily nonlocal in the mode
index.  This module records the exact first-cell obstruction, independently
of the Pascal/Bernstein development.
-/

import YMGap.Continuum.HarmonicThetaRepresentation

namespace YMGap.Continuum.HarmonicThetaTermwiseFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private def twoThirds : Q' := Q'.mkPos 2 3 (by decide)
private def halfQ : Q' := Q'.mkPos 1 2 (by decide)
private def publicRetuneCube (w : Q') : Q' :=
  qpow (halfQ * ((1 : Q') + w)) 3

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

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

#print axioms first_theta_cell_retune_fails_k1
#print axioms twoThirds_le_harmW
#print axioms first_theta_cell_retune_fails
#print axioms no_same_index_theta_allocation

end YMGap.Continuum.HarmonicThetaTermwiseFence
