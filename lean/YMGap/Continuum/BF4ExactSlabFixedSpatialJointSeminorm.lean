/-
# Squared seminorm of the cutoff-removed original reflected pairing

Squared distance is the actual joint pairing of the literal physical
signed difference. Its unconditional distance laws pass through the
proved cutoff limit. Null congruence instead uses Cauchy--Schwarz for the
limiting pairing: a null limit is not assumed null at any finite stage.

The supplied data therefore instantiate the existing choice-free
completion interface without identifying the cutoff-dependent carriers.
Nome and spatial width remain fixed. No metric completeness, completed
inner product, nonconstant excitation, or continuum gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
  (PhysicalSpan distSq distSq_refl distSq_symm distSq_nonnegative distSq_triangle)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- The SAME cutoff-removed reflected diagonal of the actual difference. -/
def jointDistSq (x y : PhysicalSpan width) : CReal :=
  jointPairing hw0 hw1 width (differenceSpan x y) (differenceSpan x y)

/-- The distance keeps its constructed approximation modulus as data. -/
def jointDistSqCauchy (x y : PhysicalSpan width) :
    QCauchy (jointDistSq hw0 hw1 width x y).approx :=
  jointPairingCauchy hw0 hw1 width (differenceSpan x y) (differenceSpan x y)

theorem distSq_converges_joint (x y : PhysicalSpan width) :
    ConvergesTo (fun stage => distSq hw0 hw1 width stage x y)
      (jointDistSq hw0 hw1 width x y) :=
  pairing_converges_jointPairing hw0 hw1 width (differenceSpan x y) (differenceSpan x y)

theorem jointDistSq_refl (x : PhysicalSpan width) :
    Equiv (jointDistSq hw0 hw1 width x x) czero :=
  Equiv_of_limit_of_equal (fun stage => distSq_refl hw0 hw1 width stage x)
    (distSq_converges_joint hw0 hw1 width x x) (convergesTo_const czero)

theorem jointDistSq_symm (x y : PhysicalSpan width) :
    Equiv (jointDistSq hw0 hw1 width x y) (jointDistSq hw0 hw1 width y x) :=
  Equiv_of_limit_of_equal (fun stage => distSq_symm hw0 hw1 width stage x y)
    (distSq_converges_joint hw0 hw1 width x y) (distSq_converges_joint hw0 hw1 width y x)

theorem jointDistSq_nonnegative (x y : PhysicalSpan width) :
    leEv czero (jointDistSq hw0 hw1 width x y) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (distSq_converges_joint hw0 hw1 width x y)
    (fun stage => distSq_nonnegative hw0 hw1 width stage x y)

theorem jointDistSq_triangle (x y z : PhysicalSpan width) :
    leEv (jointDistSq hw0 hw1 width x z)
      (add (add (jointDistSq hw0 hw1 width x y) (jointDistSq hw0 hw1 width x y))
        (add (jointDistSq hw0 hw1 width y z) (jointDistSq hw0 hw1 width y z))) :=
  leEv_of_convergesTo_le (distSq_converges_joint hw0 hw1 width x z)
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width x y)
        (distSq_converges_joint hw0 hw1 width x y))
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width y z)
        (distSq_converges_joint hw0 hw1 width y z)))
    (fun stage => distSq_triangle hw0 hw1 width stage x y z)

private theorem equiv_of_sub_zero {a b : CReal} (h : Equiv (sub a b) czero) :
    Equiv a b := by
  have hc : Equiv (add (sub a b) b) a :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv (a.approx n) (b.approx n))
  have hz : Equiv (add czero b) b :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (b.approx n)))
  exact hc.symm.trans ((Equiv_add h (Equiv.refl b)).trans hz)

/-- Limiting radical annihilation, not a passage of the conditional
finite-stage null theorem. No finite-stage nullity is asserted. -/
theorem jointPairing_null_left {x x' : PhysicalSpan width}
    (hx : Equiv (jointDistSq hw0 hw1 width x x') czero) (y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x' y) := by
  have hz := jointPairing_radical_zero hw0 hw1 width (differenceSpan x x') y hx
  exact equiv_of_sub_zero
    ((jointPairing_difference_left hw0 hw1 width x x' y).symm.trans hz)

theorem jointPairing_null_congr {x x' y y' : PhysicalSpan width}
    (hx : Equiv (jointDistSq hw0 hw1 width x x') czero)
    (hy : Equiv (jointDistSq hw0 hw1 width y y') czero) :
    Equiv (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x' y') :=
  (jointPairing_null_left hw0 hw1 width hx y).trans
    ((jointPairing_symm hw0 hw1 width x' y).trans
      ((jointPairing_null_left hw0 hw1 width hy x').trans
        (jointPairing_symm hw0 hw1 width y' x')))

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

/-- Zero limiting distance preserves that SAME limiting distance. -/
theorem jointDistSq_null_congr {x x' y y' : PhysicalSpan width}
    (hx : Equiv (jointDistSq hw0 hw1 width x x') czero)
    (hy : Equiv (jointDistSq hw0 hw1 width y y') czero) :
    Equiv (jointDistSq hw0 hw1 width x y) (jointDistSq hw0 hw1 width x' y') :=
  (jointPairing_difference_diagonal hw0 hw1 width x y).trans
    ((sub_congr
      (sub_congr (jointPairing_null_congr hw0 hw1 width hx hx)
        (jointPairing_null_congr hw0 hw1 width hx hy))
      (sub_congr (jointPairing_null_congr hw0 hw1 width hy hx)
        (jointPairing_null_congr hw0 hw1 width hy hy))).trans
      (jointPairing_difference_diagonal hw0 hw1 width x' y').symm)

/-- All fields are supplied for the actual cutoff-removed reflected form. -/
def jointSeminorm : SquaredSeminorm where
  Carrier := PhysicalSpan width
  distSq := jointDistSq hw0 hw1 width
  distSq_refl := jointDistSq_refl hw0 hw1 width
  distSq_symm := jointDistSq_symm hw0 hw1 width
  distSq_nonneg := jointDistSq_nonnegative hw0 hw1 width
  distSq_triangle := jointDistSq_triangle hw0 hw1 width
  null_congr := jointDistSq_null_congr hw0 hw1 width

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSqCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.distSq_converges_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointPairing_null_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointPairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointDistSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm.jointSeminorm
