/-
# Centered moments on the actual finite-support Wilson union

The connected scalar retains the maximum-base union pairing, original unit
and original physical time. Its Cauchy data are computed from those three
pairing representatives. The common-base pin identifies it with the
existing Wilson centeredTimeMoment, including at each stage's own base.

The previously proved sharp two-step bound and even-time positivity then
hold for every stage with the same nome-only rate. Physical lag is not a
Cauchy approximation index. No common support bound for a stream, exact
orthogonality of its terms, or new analytic input is required here.
-/

import YMGap.Continuum.BF4WilsonSpatialUnion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (inclusion_refl)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
  (centeredTimeMoment evenMoment_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap (evenMoment_first_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs

/-- Center the actual union pairing with its original normalized unit. -/
def centeredMoment (n : Nat) (x y : Stage) : CReal :=
  sub (P x (time n y)) (mul (P x unitStage) (P unitStage y))

/-- Computed arithmetic moduli of the SAME three chosen scalar representatives. -/
def centeredMomentCauchy (n : Nat) (x y : Stage) :
    QCauchy (centeredMoment hw0 hw1 hsmall hd hs n x y).approx :=
  let A := P x (time n y)
  let L := P x unitStage
  let R := P unitStage y
  let cA := pairingCauchy hw0 hw1 hsmall hd hs x (time n y)
  let cL := pairingCauchy hw0 hw1 hsmall hd hs x unitStage
  let cR := pairingCauchy hw0 hw1 hsmall hd hs unitStage y
  scalarAddCauchy A (neg (mul L R)) cA
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R cL cR))

attribute [local irreducible] pairing intrinsicForm

/-- Actual common-base coherence, including both unit marginals and physical time. -/
theorem centeredMoment_at_base (n : Nat) (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n x y)
      (centeredTimeMoment hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) n (atBase x hx) (atBase y hy)) := by
  have hu : 1 ≤ larger := Nat.lt_of_lt_of_le x.positive hx
  have ht := pairing_at_base hw0 hw1 hsmall hd hs x (time n y) larger hx hy
  have hl := pairing_at_base hw0 hw1 hsmall hd hs x unitStage larger hx hu
  have hr := pairing_at_base hw0 hw1 hsmall hd hs unitStage y larger hu hy
  simp only [atBase_time, atBase_unit] at ht hl hr
  have hm : Equiv (mul (P x unitStage) (P unitStage y))
      (mul
        (intrinsicForm hw0 hw1 hsmall hd hs
          (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (unit larger))
        (intrinsicForm hw0 hw1 hsmall hd hs
          (Nat.lt_of_lt_of_le x.positive hx) (unit larger) (atBase y hy))) :=
    (CReal.mul_congr_left hl).trans (TrigSignedAdd.mul_congr_right hr)
  exact Equiv_add ht (neg_congr hm)

/-- A diagonal moment uses only the particular stage's own positive base. -/
theorem centeredMoment_diagonal_pin (n : Nat) (x : Stage) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n x x)
      (centeredTimeMoment hw0 hw1 hsmall hd hs x.positive n x.value x.value) := by
  simpa only [atBase_self] using
    centeredMoment_at_base hw0 hw1 hsmall hd hs n x x x.base (Nat.le_refl _) (Nat.le_refl _)

/-- A fixed-base pair retains exactly its existing Wilson connected scalar. -/
theorem centeredMoment_ofExpression (n base : Nat) (hb : 0<base)
    (x y : IntrinsicExpression base) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n
        (ofExpression base hb x) (ofExpression base hb y))
      (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y) := by
  simpa only [atBase, ofExpression, inclusion_refl] using
    centeredMoment_at_base hw0 hw1 hsmall hd hs n
      (ofExpression base hb x) (ofExpression base hb y)
      base (Nat.le_refl _) (Nat.le_refl _)

/-- The same prefactor-free nome-dependent rate is independent of each stage's
base. This estimate does not require its original unit coefficient to vanish. -/
theorem centered_twoStep_bound (x : Stage) :
    leEv (centeredMoment hw0 hw1 hsmall hd hs 2 x x)
      (mul (ofQ' (twoStepRate w hd)) (centeredMoment hw0 hw1 hsmall hd hs 0 x x)) :=
  leEv_trans (leEv_of_equiv (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 2 x))
    (leEv_trans (evenMoment_first_le hw0 hw1 hsmall hd hs x.positive x.value)
      (leEv_of_equiv (TrigSignedAdd.mul_congr_right
        (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 0 x).symm)))

/-- Positivity is restricted to even original physical times. -/
theorem centered_even_nonnegative (n : Nat) (x : Stage) :
    leEv czero (centeredMoment hw0 hw1 hsmall hd hs (2*n) x x) :=
  leEv_trans (evenMoment_nonnegative hw0 hw1 hsmall hd hs x.positive x.value n)
    (leEv_of_equiv (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs (2*n) x).symm)

end YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centeredMoment
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centeredMomentCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centeredMoment_at_base
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centeredMoment_diagonal_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centeredMoment_ofExpression
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centered_twoStep_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm.centered_even_nonnegative
