/-
# Linear closure of represented ORIGINAL cyclic vectors

Addition of represented original Cauchy rows carries a shared explicit
modulus. Its limit is the original completed sum. Polynomial action also
retains a cyclic presentation, using products of the input polynomials.
These constructions supply rational linear combinations of cyclic inputs,
with exact state pins and without selecting quotient representatives.

No physical input or canonical frontier field is added. The fixed-spacing
represented sector is not identified with the full physical carrier here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (add_regroup)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (norm_add_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem sub_add (x y x' y' : Completion) :
    completedSub (completedAdd x y) (completedAdd x' y')=
      completedAdd (completedSub x x') (completedSub y y') := by
  unfold completedSub completedNeg
  rw [completedSmul_add]
  exact add_regroup _ _ _ _

theorem add_distance_bound (x y x' y' : Completion) :
    RCle (completedDist (completedAdd x y) (completedAdd x' y'))
      (RCadd (RCadd (completedDist x x') (completedDist x x'))
        (RCadd (completedDist y y') (completedDist y y'))) := by
  unfold completedDist
  rw [sub_add]
  exact norm_add_bound _ _

theorem add_close (x y x' y' : Completion) (epsilon : Q')
    (hx : RCle (completedDist x x') (rat (quarter epsilon)))
    (hy : RCle (completedDist y y') (rat (quarter epsilon))) :
    RCle (completedDist (completedAdd x y) (completedAdd x' y')) (rat epsilon) := by
  have h := RCle_trans (add_distance_bound x y x' y')
    (RCadd_le_add (RCadd_le_add hx hx) (RCadd_le_add hy hy))
  have hb : Q'.eqv ((quarter epsilon+quarter epsilon)+(quarter epsilon+quarter epsilon)) epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*epsilon))
        (ExpNeg.two_halves (HalfPow.half*epsilon))) (ExpNeg.two_halves epsilon)
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hb))

def addRows (R S : CauchyRows) : CauchyRows where
  row := fun n => addition.mapCauchy (R.row n) (S.row n)
  modulus := fun epsilon => max (R.modulus (quarter epsilon)) (S.modulus (quarter epsilon))
  isCauchy := by
    intro epsilon he m n hm hn
    exact add_close _ _ _ _ epsilon
      (R.isCauchy _ (quarter_pos he) m n
        (Nat.le_trans (Nat.le_max_left _ _) hm) (Nat.le_trans (Nat.le_max_left _ _) hn))
      (S.isCauchy _ (quarter_pos he) m n
        (Nat.le_trans (Nat.le_max_right _ _) hm) (Nat.le_trans (Nat.le_max_right _ _) hn))

theorem addRows_pin (R S : CauchyRows) (n : Nat) :
    rowPoint (addRows R S) n=completedAdd (rowPoint R n) (rowPoint S n) := rfl

def addLimitModulus (R S : CauchyRows) (epsilon : Q') : Nat :=
  max (rowLimitRate R (quarter epsilon)) (rowLimitRate S (quarter epsilon))

theorem addLimit_bound (R S : CauchyRows) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : addLimitModulus R S epsilon≤n) :
    RCle (completedDist (rowPoint (addRows R S) n) (completedAdd (rowLimit R) (rowLimit S))) (rat epsilon) :=
  add_close _ _ _ _ epsilon
    (rowLimit_bound R _ (quarter_pos he) n (Nat.le_trans (Nat.le_max_left _ _) hn))
    (rowLimit_bound S _ (quarter_pos he) n (Nat.le_trans (Nat.le_max_right _ _) hn))

theorem rowLimit_add (R S : CauchyRows) :
    rowLimit (addRows R S)=completedAdd (rowLimit R) (rowLimit S) :=
  rowLimit_eq_of_bound _ _ (addLimitModulus R S) (addLimit_bound R S)

def addPresentation (X Y : CyclicPresentation) : CyclicPresentation where
  rows := addRows X.rows Y.rows
  polynomial := fun n => QPoly.padd (X.polynomial n) (Y.polynomial n)
  point_pin := by
    intro n
    rw [addRows_pin,X.point_pin,Y.point_pin,operator_add]

theorem state_addPresentation (X Y : CyclicPresentation) :
    state (addPresentation X Y)=completedAdd (state X) (state Y) := rowLimit_add _ _

def polynomialPresentation (p : QPoly.Poly) (X : CyclicPresentation) : CyclicPresentation where
  rows := operatorRows p X.rows
  polynomial := fun n => QPoly.pmul p (X.polynomial n)
  point_pin := by
    intro n
    rw [operatorRows_pin,X.point_pin,operator_mul]

theorem state_polynomialPresentation (p : QPoly.Poly) (X : CyclicPresentation) :
    state (polynomialPresentation p X)=polynomialOperator p (state X) := operator_rowLimit _ _

def smulPresentation (c : Q') (X : CyclicPresentation) : CyclicPresentation := polynomialPresentation [c] X

theorem state_smulPresentation (c : Q') (X : CyclicPresentation) :
    state (smulPresentation c X)=completedSmul c (state X) :=
  (state_polynomialPresentation [c] X).trans (operator_constant c (state X))

def subPresentation (X Y : CyclicPresentation) : CyclicPresentation :=
  addPresentation X (smulPresentation (-1) Y)

theorem state_subPresentation (X Y : CyclicPresentation) :
    state (subPresentation X Y)=completedSub (state X) (state Y) := by
  rw [subPresentation,state_addPresentation,state_smulPresentation]
  rfl

end YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.sub_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.add_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.add_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.addRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.addRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.addLimitModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.addLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.rowLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.addPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.state_addPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.polynomialPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.state_polynomialPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.smulPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.state_smulPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.subPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear.state_subPresentation
