/-
# Squared seminorm of the actual spatial limiting reflected form

The carrier retains the original finite-base physical signed presentations.
Squared distance is the spatial limiting pairing of their literal signed
difference. Unconditional distance laws pass through the proved recentered
joint-pairing convergence. Radical descent is instead proved from the
LIMITING Cauchy--Schwarz law: limit-nullity is never assumed to imply
nullity in any finite-width carrier.

This supplies the existing explicit-modulus completion interface for the
same spatial limiting form. It does not identify different base carriers,
extend the observable algebra, prove metric completeness, or supply a
width-independent strict physical gap or a continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (differenceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb

attribute [local irreducible] spatialPairing

/-- The same spatial limiting reflected form, evaluated on the actual difference. -/
def spatialDistSq (x y : PhysicalSpan base) : CReal :=
  P (differenceSpan x y) (differenceSpan x y)

/-- Constructed approximation-modulus data for this exact squared distance. -/
def spatialDistSqCauchy (x y : PhysicalSpan base) :
    QCauchy (spatialDistSq hw0 hw1 base hsmall hd hs hb x y).approx :=
  spatialPairingCauchy hw0 hw1 base hsmall hd hs hb (differenceSpan x y) (differenceSpan x y)

/-- Recenter the literal difference before taking the actual width limit. -/
theorem distSq_converges_spatial (x y : PhysicalSpan base) :
    ConvergesTo (fun r => jointDistSq hw0 hw1 (paddedWidth base r) (recenter r x) (recenter r y))
      (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) := by
  simpa only [spatialDistSq, jointDistSq, recenter_difference] using
    spatialPairing_converges hw0 hw1 base hsmall hd hs hb
      (differenceSpan x y) (differenceSpan x y)

theorem spatialDistSq_refl (x : PhysicalSpan base) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x x) czero :=
  Equiv_of_limit_of_equal
    (fun r => jointDistSq_refl hw0 hw1 (paddedWidth base r) (recenter r x))
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x x) (convergesTo_const czero)

theorem spatialDistSq_symm (x y : PhysicalSpan base) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x y)
      (spatialDistSq hw0 hw1 base hsmall hd hs hb y x) :=
  Equiv_of_limit_of_equal
    (fun r => jointDistSq_symm hw0 hw1 (paddedWidth base r) (recenter r x) (recenter r y))
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y)
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb y x)

theorem spatialDistSq_nonnegative (x y : PhysicalSpan base) :
    leEv czero (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) :=
  spatialPairing_nonnegative hw0 hw1 base hsmall hd hs hb (differenceSpan x y)

theorem spatialDistSq_triangle (x y z : PhysicalSpan base) :
    leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb x z)
      (add
        (add (spatialDistSq hw0 hw1 base hsmall hd hs hb x y)
          (spatialDistSq hw0 hw1 base hsmall hd hs hb x y))
        (add (spatialDistSq hw0 hw1 base hsmall hd hs hb y z)
          (spatialDistSq hw0 hw1 base hsmall hd hs hb y z))) :=
  leEv_of_convergesTo_le (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x z)
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y)
        (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y))
      (TrigAddCReal.convergesTo_add (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb y z)
        (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb y z)))
    (fun r => jointDistSq_triangle hw0 hw1 (paddedWidth base r)
      (recenter r x) (recenter r y) (recenter r z))

private theorem equiv_of_sub_zero {a b : CReal} (h : Equiv (sub a b) czero) :
    Equiv a b := by
  have hc : Equiv (add (sub a b) b) a :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv (a.approx n) (b.approx n))
  have hz : Equiv (add czero b) b :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (b.approx n)))
  exact hc.symm.trans ((Equiv_add h (Equiv.refl b)).trans hz)

/-- A null spatial-limit distance annihilates the spatial-limit form itself. -/
theorem spatialPairing_null_left {x x' : PhysicalSpan base}
    (hx : Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x x') czero)
    (y : PhysicalSpan base) : Equiv (P x y) (P x' y) := by
  have hz := spatialPairing_radical_zero hw0 hw1 base hsmall hd hs hb (differenceSpan x x') y hx
  exact equiv_of_sub_zero
    ((spatialPairing_difference_left hw0 hw1 base hsmall hd hs hb x x' y).symm.trans hz)

theorem spatialPairing_null_congr {x x' y y' : PhysicalSpan base}
    (hx : Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x x') czero)
    (hy : Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb y y') czero) :
    Equiv (P x y) (P x' y') :=
  (spatialPairing_null_left hw0 hw1 base hsmall hd hs hb hx y).trans
    ((spatialPairing_symm hw0 hw1 base hsmall hd hs hb x' y).trans
      ((spatialPairing_null_left hw0 hw1 base hsmall hd hs hb hy x').trans
        (spatialPairing_symm hw0 hw1 base hsmall hd hs hb y' x')))

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

/-- Zero limiting distance preserves this same limiting squared distance. -/
theorem spatialDistSq_null_congr {x x' y y' : PhysicalSpan base}
    (hx : Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x x') czero)
    (hy : Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb y y') czero) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x y)
      (spatialDistSq hw0 hw1 base hsmall hd hs hb x' y') :=
  (spatialPairing_difference_diagonal hw0 hw1 base hsmall hd hs hb x y).trans
    ((sub_congr
      (sub_congr (spatialPairing_null_congr hw0 hw1 base hsmall hd hs hb hx hx)
        (spatialPairing_null_congr hw0 hw1 base hsmall hd hs hb hx hy))
      (sub_congr (spatialPairing_null_congr hw0 hw1 base hsmall hd hs hb hy hx)
        (spatialPairing_null_congr hw0 hw1 base hsmall hd hs hb hy hy))).trans
      (spatialPairing_difference_diagonal hw0 hw1 base hsmall hd hs hb x' y').symm)

/-- Every field is proved for the actual spatial limiting reflected form. -/
def spatialSeminorm : SquaredSeminorm where
  Carrier := PhysicalSpan base
  distSq := spatialDistSq hw0 hw1 base hsmall hd hs hb
  distSq_refl := spatialDistSq_refl hw0 hw1 base hsmall hd hs hb
  distSq_symm := spatialDistSq_symm hw0 hw1 base hsmall hd hs hb
  distSq_nonneg := spatialDistSq_nonnegative hw0 hw1 base hsmall hd hs hb
  distSq_triangle := spatialDistSq_triangle hw0 hw1 base hsmall hd hs hb
  null_congr := spatialDistSq_null_congr hw0 hw1 base hsmall hd hs hb

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSqCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.distSq_converges_spatial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialPairing_null_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialPairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialDistSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm.spatialSeminorm
