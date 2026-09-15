/-
# Explicit clipped coordinate and unit-isolating symbols

Clipping to [0,1] is a bounded rational 1-Lipschitz operation. Affine
compositions have constructed CtsMod and monotone vanishing data.
The coordinate symbol agrees with t on [0,1]; the filter clip(4t-3)
vanishes on t<=3/4 and equals one at t=1. Its squared support inequality
is pointwise rational data, not an assumed spectral projection.

Identification of its ORIGINAL operator with the original unit projection
is a subsequent theorem. No physical-scale or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus

namespace YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe (cap_step)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

def positivePart (t : Q') : Q' := if (0 : Q')≤t then t else 0

theorem positivePart_nonnegative (t : Q') : (0 : Q')≤positivePart t := by
  unfold positivePart
  split
  · assumption
  · exact Q'.le_refl' _

theorem positivePart_step (a b e : Q') (he : (0 : Q')≤e) (h : a≤b+e) :
    positivePart a≤positivePart b+e := by
  unfold positivePart
  by_cases ha : (0 : Q')≤a <;> by_cases hb : (0 : Q')≤b
  · rw [if_pos ha,if_pos hb]; exact h
  · rw [if_pos ha,if_neg hb]
    exact Q'.le_trans' _ _ _ h (Q'.add_le_add_right _ _ _ (Q'.le_of_not_le hb))
  · rw [if_neg ha,if_pos hb]
    exact Q'.zero_le_add _ _ hb he
  · rw [if_neg ha,if_neg hb]
    exact Q'.zero_le_add _ _ (Q'.le_refl' _) he

def clip (t : Q') : Q' := Q'.min' (positivePart t) 1

theorem clip_nonnegative (t : Q') : (0 : Q')≤clip t :=
  Q'.zero_le_min _ _ (positivePart_nonnegative t) Q'.zero_le_one

theorem clip_bound (t : Q') : Q'.abs (clip t)≤1 := by
  rw [abs_of_nonneg (clip_nonnegative t)]
  exact Q'.min_le_right

theorem clip_lipschitz (s t : Q') : Q'.abs (clip s-clip t)≤Q'.abs (s-t) := by
  apply abs_sub_le_of_bounds
  · exact cap_step _ _ _ (Q'.abs_nonneg _) (positivePart_step s t _ (Q'.abs_nonneg _)
      (le_add_of_sub_le (Q'.le_abs_self _)))
  · exact cap_step _ _ _ (Q'.abs_nonneg _) (positivePart_step t s _ (Q'.abs_nonneg _)
      (le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm t s)))))

theorem clip_interval (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) : clip t=t := by
  rw [clip,positivePart,if_pos ht,Q'.min',if_pos h1]

theorem clip_nonpositive (t : Q') (ht : t≤(0 : Q')) : Q'.eqv (clip t) 0 := by
  by_cases hp : (0 : Q')≤t
  · rw [clip_interval t hp (Q'.le_trans' _ _ _ ht Q'.zero_le_one)]
    exact Q'.eqv_of_le_le ht hp
  · rw [clip,positivePart,if_neg hp]
    decide

def coordinateSymbol : CtsMod where
  f := clip
  bound := 1
  ω := Q'.abs
  f_le := clip_bound
  ω_nn := Q'.abs_nonneg
  mod := fun s t d h => Q'.le_trans' _ _ _ (clip_lipschitz s t)
    (Q'.le_trans' _ _ _ h (Q'.le_abs_self d))

def coordinateVanishing : MonotoneOmegaVanishing coordinateSymbol where
  delta := fun e => e
  mono := fun _ _ h => h
  pos := fun _ h => h
  small := by
    intro e he
    change Q'.abs e≤e
    rw [abs_of_nonneg (Q'.le_of_lt he)]
    exact Q'.le_refl' _

theorem coordinate_value (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) : coordinateSymbol.f t=t :=
  clip_interval t ht h1

theorem affine_difference (a b s t : Q') : Q'.eqv ((a*s+b)-(a*t+b)) (a*(s-t)) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 2)) (.var 1)) (.neg (.add (.mul (.var 0) (.var 3)) (.var 1))))
    (.mul (.var 0) (.add (.var 2) (.neg (.var 3)))) (by decide)
    (fun | 0 => a | 1 => b | 2 => s | _ => t)

theorem affine_lipschitz (a b s t : Q') :
    Q'.abs (clip (a*s+b)-clip (a*t+b))≤Q'.abs a*Q'.abs (s-t) :=
  Q'.le_trans' _ _ _ (clip_lipschitz _ _)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (affine_difference a b s t))) (ExpNeg.abs_mul_le _ _))

def affineSymbol (a b : Q') : CtsMod where
  f := fun t => clip (a*t+b)
  bound := 1
  ω := fun d => Q'.abs a*Q'.abs d
  f_le := fun t => clip_bound (a*t+b)
  ω_nn := fun d => Q'.mul_nonneg _ _ (Q'.abs_nonneg a) (Q'.abs_nonneg d)
  mod := fun s t d h => Q'.le_trans' _ _ _ (affine_lipschitz a b s t)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ h (Q'.le_abs_self d)) (Q'.abs_nonneg a))

def affineVanishing (a b : Q') : MonotoneOmegaVanishing (affineSymbol a b) where
  delta := linearTolerance (Q'.abs a) (Q'.abs_nonneg a)
  mono := fun _ _ h => Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (Q'.recipPos_pos _ _))
  pos := fun _ he => linearTolerance_pos _ _ he
  small := by
    intro e he
    change Q'.abs a*Q'.abs (linearTolerance (Q'.abs a) (Q'.abs_nonneg a) e)≤e
    rw [abs_of_nonneg (Q'.le_of_lt (linearTolerance_pos _ _ he))]
    exact linearTolerance_budget _ (Q'.abs_nonneg a) he

def unitFilterSymbol : CtsMod := affineSymbol 4 (-3)

def unitFilterVanishing : MonotoneOmegaVanishing unitFilterSymbol := affineVanishing 4 (-3)

def filterEdge : Q' := Q'.mkPos 3 4 (by decide)

theorem unitFilter_at_one : Q'.eqv (unitFilterSymbol.f 1) 1 := by decide

theorem unitFilter_below (t : Q') (ht : t≤filterEdge) : Q'.eqv (unitFilterSymbol.f t) 0 := by
  apply clip_nonpositive
  have h := Q'.add_le_add_right _ _ (-3) (Q'.mul_le_mul_of_nonneg_left _ _ 4 ht (by decide))
  exact Q'.le_trans' _ _ _ h (by decide)

theorem unitFilter_support (t : Q') :
    filterEdge*(unitFilterSymbol.f t*unitFilterSymbol.f t)≤t*(unitFilterSymbol.f t*unitFilterSymbol.f t) := by
  by_cases ht : t≤filterEdge
  · have hz := unitFilter_below t ht
    have hs : Q'.eqv (unitFilterSymbol.f t*unitFilterSymbol.f t) 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (QPoly.q_mul_zero _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hs) (QPoly.q_mul_zero _)))
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hs) (QPoly.q_mul_zero _)))
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_not_le ht) (SumOfSquares.q_mul_self_nonneg _)

end YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.positivePart
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.positivePart_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.positivePart_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip_lipschitz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.clip_nonpositive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.coordinateSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.coordinateVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.coordinate_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.affine_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.affine_lipschitz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.affineSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.affineVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.unitFilterSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.unitFilterVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.filterEdge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.unitFilter_at_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.unitFilter_below
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols.unitFilter_support
