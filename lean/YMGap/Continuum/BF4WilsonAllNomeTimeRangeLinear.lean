/-
# Linear operations on the witnessed original Wilson time-range closure

Every output below is a `RangeLimit`: its preimage stream and convergence
modulus are data. The construction stays in the original completion and does
not identify it with a physical OS sector or assert whole-carrier density.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
import YMGap.Continuum.BF4WilsonAllNomeRowLinear
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear (completedDist_smul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completedRealSmul)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit fromTime)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Rational scaling retains explicit original preimages and an explicit
modulus obtained from the existing squared scalar tolerance. -/
def rationalSmul {x : V} (c : Q') (R : RangeLimit hw0 hw1 x) :
    RangeLimit hw0 hw1 (S c x) where
  preimage := fun n => (scalarContinuous hw0 hw1 c).mapCauchy (R.preimage n)
  modulus := fun e => R.modulus (scalarTolerance c e)
  bound := by
    intro e he n hn
    have h := R.bound (scalarTolerance c e) (scalarTolerance_pos c he) n hn
    change RCle (dist (T 1 (S c (Class (R.preimage n)))) (S c x)) (rat e)
    rw [completedTime_smul, completedDist_smul]
    have hscaled := RCscale_mono (SumOfSquares.q_mul_self_nonneg c) h
    have hrat : RCscale (c*c) (rat (scalarTolerance c e)) =
        rat (c*c*scalarTolerance c e) :=
      Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))
    rw [hrat] at hscaled
    exact RCle_trans hscaled
      (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he))

/-- The zero vector is an original time image. -/
def zero : RangeLimit hw0 hw1 Z := by
  let X : (D).Cauchy := (D).constant (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero width)
  have h : T 1 (Class X) = Z := by
    change T 1 Z = Z
    exact completedTime_zero_element hw0 hw1 1
  exact h ▸ fromTime hw0 hw1 X

/-- Difference closure uses represented rows of the *supplied* time images.
The diagonal in `representedLimit` computes the new preimage stream. -/
def subtract {x y : V} (R : RangeLimit hw0 hw1 x)
    (S' : RangeLimit hw0 hw1 y) :
    RangeLimit hw0 hw1 (completedSub hw0 hw1 x y) := by
  let U := rangeRows hw0 hw1 R
  let W := rangeRows hw0 hw1 S'
  let rows := differenceRows hw0 hw1 U W
  have hrow (n : Nat) : rowPoint hw0 hw1 rows n =
      T 1 (Class (differenceCauchy hw0 hw1 (R.preimage n) (S'.preimage n))) := by
    dsimp [rows]
    rw [differenceRows_pin, rangeRows_point, rangeRows_point,
      ← completedTime_sub]
    rfl
  have hrows (n : Nat) : RangeLimit hw0 hw1 (rowPoint hw0 hw1 rows n) :=
    (hrow n).symm ▸ fromTime hw0 hw1
      (differenceCauchy hw0 hw1 (R.preimage n) (S'.preimage n))
  have hlimit : limit hw0 hw1 rows = completedSub hw0 hw1 x y := by
    rw [show rows = differenceRows hw0 hw1 U W from rfl,
      rowLimit_difference, rangeRows_limit, rangeRows_limit]
  exact hlimit ▸ representedLimit hw0 hw1 rows hrows

/-- Negation is a difference from the same original time-zero vector. -/
def negate {x : V} (R : RangeLimit hw0 hw1 x) :
    RangeLimit hw0 hw1 (N x) := by
  have h : completedSub hw0 hw1 Z x = N x := by
    unfold completedSub
    exact completedZero_add hw0 hw1 (N x)
  exact h ▸ subtract hw0 hw1 (zero hw0 hw1) R

private theorem neg_neg (x : V) : N (N x) = x := by
  change S (-1) (S (-1) x) = x
  rw [completedSmul_mul]
  exact (completedSmul_congr hw0 hw1
    (by decide : Q'.eqv ((-1 : Q')*(-1)) 1) x).trans
      (completedSmul_one hw0 hw1 x)

/-- Addition is difference from a witnessed negative. No uniform preimage
norm is required. -/
def add {x y : V} (R : RangeLimit hw0 hw1 x)
    (S' : RangeLimit hw0 hw1 y) : RangeLimit hw0 hw1 (A x y) := by
  have h : completedSub hw0 hw1 x (N y) = A x y := by
    unfold completedSub
    rw [neg_neg hw0 hw1 y]
  exact h ▸ subtract hw0 hw1 R (negate hw0 hw1 S')

/-- Every rational scalar row is in the witnessed sector; the already
computed scalar-row limit supplies the real-linear range witness. -/
def realSmul {x : V} (s : CReal) (cs : QCauchy s.approx)
    (R : RangeLimit hw0 hw1 x) :
    RangeLimit hw0 hw1 (completedRealSmul hw0 hw1 s cs x) := by
  let X := representative hw0 hw1 R
  let rows := scalarRows hw0 hw1 s cs X
  have hrows (n : Nat) : RangeLimit hw0 hw1 (rowPoint hw0 hw1 rows n) := by
    change RangeLimit hw0 hw1 (S (s.approx n) (Class X))
    rw [representative_pin hw0 hw1 R]
    exact rationalSmul hw0 hw1 (s.approx n) R
  have hlimit : limit hw0 hw1 rows = completedRealSmul hw0 hw1 s cs x := by
    change limit hw0 hw1 (scalarRows hw0 hw1 s cs X) = _
    rw [scalarRows_limit, representative_pin]
  exact hlimit ▸ representedLimit hw0 hw1 rows hrows

#print axioms rationalSmul
#print axioms zero
#print axioms subtract
#print axioms negate
#print axioms add
#print axioms realSmul

end YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear
