/-
# Quadratic increments after positive ORIGINAL lattice time

The SAME completed transfer satisfies
  ||T(n+j)x-T(n)x||^2 <= (j/(n+1))^2 ||x||^2.
The proof reuses the actual defect-range bound and the existing finite vector
sum, rather than replacing T or assuming an energy estimate. For the literal
dyadic unit excitation the norm is one. At n>=side(scale), j*spacing(scale)
therefore gives a nome/width-uniform geometric increment bound and a computed
positive clamped radius.

This is within each original carrier. It supplies neither changing-family
convergence nor a surviving positive-time norm, and the assigned geometric
spacing is not a proved physical Yang--Mills calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeAverages
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

namespace YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root_zero_depth)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect defect_time)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (timeDefect_bound)
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (vectorSum sum_norm_bound sum_defect)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "dist" => completedDist hw0 hw1

private theorem original_defect (x : V) :
    BF4WilsonAllNomeDyadicDefectDecay.defect hw0 hw1 0 x = defect hw0 hw1 x := by
  unfold BF4WilsonAllNomeDyadicDefectDecay.defect defect
  rw [root_zero_depth]

/-- The existing finite sum telescopes the actual integer-time increment. -/
theorem positiveLag_increment_sum (x : V) (n j : Nat) :
    vectorSum hw0 hw1 j (fun p => T p (T n (defect hw0 hw1 x))) =
      completedSub hw0 hw1 (T n x) (T (n+j) x) := by
  have h := sum_defect hw0 hw1 0 j (T n x)
  simp only [mesh_original, original_defect, defect_time] at h
  have hend := (completedTime_add hw0 hw1 j n x).symm
  rw [Nat.add_comm j n] at hend
  rw [hend] at h
  exact h

/-- Uniform in all strict nomes and widths, relative to the actual input norm.
The distance is squared; j=0 and n=0 are included. -/
theorem positiveLag_increment_bound (x : V) (n j : Nat) :
    RCle (dist (T (n+j) x) (T n x))
      (RCscale ((Q'.ofNat j*Q'.invSucc n)*(Q'.ofNat j*Q'.invSucc n)) (B x x)) := by
  let C := RCscale (Q'.invSucc n*Q'.invSucc n) (B x x)
  have hterms : ∀ p, p<j → RCle
      (B (T p (T n (defect hw0 hw1 x))) (T p (T n (defect hw0 hw1 x)))) C := by
    intro p _
    exact RCle_trans (completedInner_time_contraction hw0 hw1 p _)
      (timeDefect_bound hw0 hw1 n x)
  have h := sum_norm_bound hw0 hw1 j _ C hterms
  rw [positiveLag_increment_sum] at h
  change RCle (dist (T n x) (T (n+j) x))
    (RCscale (Q'.ofNat j*Q'.ofNat j)
      (RCscale (Q'.invSucc n*Q'.invSucc n) (B x x))) at h
  rw [completedDist_symm, RCscale_RCscale] at h
  have hc : Q'.eqv
      ((Q'.ofNat j*Q'.ofNat j)*(Q'.invSucc n*Q'.invSucc n))
      ((Q'.ofNat j*Q'.invSucc n)*(Q'.ofNat j*Q'.invSucc n)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => Q'.ofNat j | _ => Q'.invSucc n)
  rw [RCSignedPairBudget.scale_congr hc] at h
  exact h

private theorem scale_rational_one (q : Q') : RCscale q (Rq 1) = Rq q :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv q))

private theorem square_mono (a b : Q') (ha : (0 : Q') ≤ a)
    (hab : a ≤ b) : a*a ≤ b*b :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right a b a hab ha)
    (Q'.mul_le_mul_of_nonneg_left a b b hab (Q'.le_trans' _ _ _ ha hab))

/-- The geometric reciprocal is available without a coupling schedule. -/
theorem invSucc_le_spacing (scale n : Nat) (hn : side scale ≤ n) :
    Q'.invSucc n ≤ spacing scale := by
  have hcount : Q'.ofNat (side scale)*Q'.invSucc n ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (CReal.ofNat_le_ofNat (Nat.le_trans hn (Nat.le_succ n)))
        (Q'.invSucc_nonneg n))
      (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc n))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (spacing scale) hcount
    (Q'.le_of_lt (spacing_positive scale))
  have hp : Q'.eqv
      (spacing scale*(Q'.ofNat (side scale)*Q'.invSucc n)) (Q'.invSucc n) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (unit_side scale))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp.symm)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv _)))

variable (scale : Nat) (hwidth : side scale < width)

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)

/-- Literal constructed unit state; not a new normalized-state premise. -/
theorem dyadicUnit_positiveLag_increment_bound (n j : Nat) :
    RCle (dist (T (n+j) u) (T n u))
      (Rq ((Q'.ofNat j*Q'.invSucc n)*(Q'.ofNat j*Q'.invSucc n))) := by
  have h := positiveLag_increment_bound hw0 hw1 u n j
  rw [dyadicUnitExcitation_norm, scale_rational_one] at h
  exact h

/-- Quadratic geometric-time bound after assigned lag one, independent of nome
and width. It does not identify different completed carriers. -/
theorem dyadicUnit_positiveLag_spacing_bound (n j : Nat) (hn : side scale ≤ n) :
    RCle (dist (T (n+j) u) (T n u))
      (Rq ((Q'.ofNat j*spacing scale)*(Q'.ofNat j*spacing scale))) :=
  RCle_trans (dyadicUnit_positiveLag_increment_bound hw0 hw1 scale hwidth n j)
    (leEv_of_le (ofQ'_le_ofQ' (square_mono _ _
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg j) (Q'.invSucc_nonneg n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (invSucc_le_spacing scale n hn) (Q'.ofNat_nonneg j)))))

/-- A computed positive radius, clamped so radius squared <= epsilon. -/
def incrementRadius (epsilon : Q') : Q' := Q'.min' epsilon 1

theorem incrementRadius_positive (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < incrementRadius epsilon := by
  unfold incrementRadius Q'.min'
  split
  · exact he
  · decide

private theorem radius_square_small (epsilon : Q') (_he : (0 : Q') < epsilon)
    (a : Q') (ha : (0 : Q') ≤ a) (h : a ≤ incrementRadius epsilon) :
    a*a ≤ epsilon := by
  have heps : incrementRadius epsilon ≤ epsilon := by
    unfold incrementRadius Q'.min'
    split
    · exact Q'.le_of_eqv (Q'.eqv_refl _)
    · rename_i hnot
      show (1 : Q').num * (epsilon.den : Int) ≤ epsilon.num * ((1 : Q').den : Int)
      exact Int.le_of_lt (Int.not_le.mp hnot)
  have hone : incrementRadius epsilon ≤ 1 := by
    unfold incrementRadius Q'.min'
    split
    · assumption
    · exact Q'.le_of_eqv (Q'.eqv_refl _)
  have hmul := Q'.mul_le_mul_of_nonneg_left a 1 a
    (Q'.le_trans' _ _ _ h hone) ha
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv a))
      (Q'.le_trans' _ _ _ h heps))

/-- Explicit uniform small-increment support on SAME smoothed unit states.
No changing-family convergence or nonzero limiting smoothed norm is asserted. -/
theorem dyadicUnit_positiveLag_increment_small (epsilon : Q')
    (he : (0 : Q') < epsilon) (n j : Nat) (hn : side scale ≤ n)
    (hj : Q'.ofNat j*spacing scale ≤ incrementRadius epsilon) :
    RCle (dist (T (n+j) u) (T n u)) (Rq epsilon) :=
  RCle_trans (dyadicUnit_positiveLag_spacing_bound hw0 hw1 scale hwidth n j hn)
    (leEv_of_le (ofQ'_le_ofQ' (radius_square_small epsilon he _
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg j)
        (Q'.le_of_lt (spacing_positive scale))) hj)))

#print axioms positiveLag_increment_sum
#print axioms positiveLag_increment_bound
#print axioms invSucc_le_spacing
#print axioms dyadicUnit_positiveLag_increment_bound
#print axioms dyadicUnit_positiveLag_spacing_bound
#print axioms incrementRadius
#print axioms incrementRadius_positive
#print axioms dyadicUnit_positiveLag_increment_small

end YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement
