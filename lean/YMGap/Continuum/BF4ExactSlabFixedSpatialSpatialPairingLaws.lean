/-
# The actual spatial-limit reflected form on fixed-base presentations

The canonical chart is computed from the two original radii. All form laws
pass through the already constructed recentered original joint pairings.
The radical is derived from LIMIT Cauchy--Schwarz, never by asserting that
a limit-null presentation is null in any finite spatial box.

The constructive approximation modulus is retained as data. This supplies
the scalar form needed by its own seminorm completion. Base-inclusion
coherence, a width-independent strict temporal rate, physical spacing and
the continuum/all-group Yang--Mills target remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance (recenter_unit)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

theorem recenter_add {base : Nat} (r : Nat) (x y : PhysicalSpan base) :
    recenter r (addSpan x y) = addSpan (recenter r x) (recenter r y) := by
  apply Subtype.ext
  exact List.map_append

theorem recenter_smul {base : Nat} (r : Nat) (c : Q') (x : PhysicalSpan base) :
    recenter r (smulSpan c x) = smulSpan c (recenter r x) := by
  apply Subtype.ext
  simp only [recenter, smulSpan, translateSpan,
    BF4ExactSlabFixedSpatialReflectedForm.scaleSpan, List.map_map]
  rfl

theorem recenter_difference {base : Nat} (r : Nat) (x y : PhysicalSpan base) :
    recenter r (differenceSpan x y) = differenceSpan (recenter r x) (recenter r y) :=
  recenter_add r x (smulSpan (-1) y) |>.trans
    (congrArg (addSpan (recenter r x)) (recenter_smul r (-1) y))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

/-- The same spatial scalar, with a computed chart, not a selected subsequence. -/
def spatialPairing (x y : PhysicalSpan base) : CReal :=
  spatialLimit hw0 hw1 base (max (radius x.val) (radius y.val)) x y
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hsmall hd hs hb

/-- Actual approximation-modulus data for this constructed real. -/
def spatialPairingCauchy (x y : PhysicalSpan base) :
    QCauchy (spatialPairing hw0 hw1 base hsmall hd hs hb x y).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _
    (spatialCauchy hw0 hw1 base (max (radius x.val) (radius y.val)) x y
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) hsmall hd hs hb)

theorem spatialPairing_converges (x y : PhysicalSpan base) :
    ConvergesTo (fun r => jointPairing hw0 hw1 (paddedWidth base r) (recenter r x) (recenter r y))
      (spatialPairing hw0 hw1 base hsmall hd hs hb x y) :=
  jointPairing_spatial_converges hw0 hw1 base (max (radius x.val) (radius y.val)) x y
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hsmall hd hs hb

theorem spatialPairing_chart (x y : PhysicalSpan base) (H : Nat)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
      (spatialLimit hw0 hw1 base H x y hx hy hsmall hd hs hb) :=
  spatialLimit_chart_independent hw0 hw1 base (max (radius x.val) (radius y.val)) x y
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hsmall hd hs hb H hx hy

attribute [local irreducible] jointPairing spatialPairing

theorem spatialPairing_symm (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
      (spatialPairing hw0 hw1 base hsmall hd hs hb y x) :=
  Equiv_of_limit_of_equal
    (fun r => jointPairing_symm hw0 hw1 _ (recenter r x) (recenter r y))
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y x)

theorem spatialPairing_nonnegative (x : PhysicalSpan base) :
    leEv czero (spatialPairing hw0 hw1 base hsmall hd hs hb x x) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x x)
    (fun r => jointPairing_nonnegative hw0 hw1 _ (recenter r x))

theorem spatialPairing_unit_unit :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb (unit base) (unit base)) cone :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_unit]; exact jointPairing_unit_unit hw0 hw1 _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (unit base) (unit base))
    (convergesTo_const cone)

theorem spatialPairing_cauchySchwarz (x y : PhysicalSpan base) :
    leEv
      (mul (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
        (spatialPairing hw0 hw1 base hsmall hd hs hb x y))
      (mul (spatialPairing hw0 hw1 base hsmall hd hs hb x x)
        (spatialPairing hw0 hw1 base hsmall hd hs hb y y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x x)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y y))
    (fun r => jointPairing_cauchySchwarz hw0 hw1 _ (recenter r x) (recenter r y))

private theorem zero_of_square_le_zero (A : CReal)
    (h : leEv (mul A A) czero) : Equiv A czero := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- A presentation null only in the spatial limit annihilates this limit form. -/
theorem spatialPairing_radical_zero (x y : PhysicalSpan base)
    (hnull : Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x x) czero) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x y) czero := by
  have hzero : Equiv
      (mul (spatialPairing hw0 hw1 base hsmall hd hs hb x x)
        (spatialPairing hw0 hw1 base hsmall hd hs hb y y)) czero :=
    Equiv.trans (CReal.mul_congr_left hnull)
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((spatialPairing hw0 hw1 base hsmall hd hs hb y y).approx n)))
  exact zero_of_square_le_zero _ (leEv_trans
    (spatialPairing_cauchySchwarz hw0 hw1 base hsmall hd hs hb x y) (leEv_of_equiv hzero))

theorem spatialPairing_add_left (x y z : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb (addSpan x y) z)
      (add (spatialPairing hw0 hw1 base hsmall hd hs hb x z)
        (spatialPairing hw0 hw1 base hsmall hd hs hb y z)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_add]; exact jointPairing_add_left hw0 hw1 _ _ _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (addSpan x y) z)
    (TrigAddCReal.convergesTo_add
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x z)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y z))

theorem spatialPairing_add_right (x y z : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x (addSpan y z))
      (add (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
        (spatialPairing hw0 hw1 base hsmall hd hs hb x z)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_add]; exact jointPairing_add_right hw0 hw1 _ _ _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (addSpan y z))
    (TrigAddCReal.convergesTo_add
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x z))

theorem spatialPairing_smul_left (c : Q') (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb (smulSpan c x) y)
      (mul (ofQ' c) (spatialPairing hw0 hw1 base hsmall hd hs hb x y)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_smul]; exact jointPairing_smul_left hw0 hw1 _ c _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (smulSpan c x) y)
    (convergesTo_const_mul (ofQ' c)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y))

theorem spatialPairing_smul_right (c : Q') (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x (smulSpan c y))
      (mul (ofQ' c) (spatialPairing hw0 hw1 base hsmall hd hs hb x y)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_smul]; exact jointPairing_smul_right hw0 hw1 _ c _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (smulSpan c y))
    (convergesTo_const_mul (ofQ' c)
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y))

theorem spatialPairing_difference_left (x y z : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan x y) z)
      (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x z)
        (spatialPairing hw0 hw1 base hsmall hd hs hb y z)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_difference]; exact jointPairing_difference_left hw0 hw1 _ _ _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (differenceSpan x y) z)
    (TrigAddCReal.convergesTo_add
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x z)
      (TrigAddCReal.convergesTo_neg (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y z)))

theorem spatialPairing_difference_right (x y z : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x (differenceSpan y z))
      (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
        (spatialPairing hw0 hw1 base hsmall hd hs hb x z)) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_difference]; exact jointPairing_difference_right hw0 hw1 _ _ _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (differenceSpan y z))
    (TrigAddCReal.convergesTo_add
      (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)
      (TrigAddCReal.convergesTo_neg (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x z)))

theorem spatialPairing_difference_diagonal (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan x y) (differenceSpan x y))
      (sub
        (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x x)
          (spatialPairing hw0 hw1 base hsmall hd hs hb x y))
        (sub (spatialPairing hw0 hw1 base hsmall hd hs hb y x)
          (spatialPairing hw0 hw1 base hsmall hd hs hb y y))) :=
  Equiv_of_limit_of_equal
    (fun r => by rw [recenter_difference]; exact jointPairing_difference_diagonal hw0 hw1 _ _ _)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (differenceSpan x y) (differenceSpan x y))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add
        (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x x)
        (TrigAddCReal.convergesTo_neg (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y)))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y x)
          (TrigAddCReal.convergesTo_neg (spatialPairing_converges hw0 hw1 base hsmall hd hs hb y y)))))

#print axioms recenter_add
#print axioms recenter_smul
#print axioms recenter_difference
#print axioms spatialPairing
#print axioms spatialPairingCauchy
#print axioms spatialPairing_converges
#print axioms spatialPairing_chart
#print axioms spatialPairing_symm
#print axioms spatialPairing_nonnegative
#print axioms spatialPairing_unit_unit
#print axioms spatialPairing_cauchySchwarz
#print axioms spatialPairing_radical_zero
#print axioms spatialPairing_add_left
#print axioms spatialPairing_add_right
#print axioms spatialPairing_smul_left
#print axioms spatialPairing_smul_right
#print axioms spatialPairing_difference_left
#print axioms spatialPairing_difference_right
#print axioms spatialPairing_difference_diagonal

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
