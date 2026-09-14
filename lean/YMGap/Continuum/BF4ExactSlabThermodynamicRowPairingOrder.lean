/-
# Order and equality pass through ORIGINAL represented pairing limits

The existing explicit two-slot pairing modulus supplies the common stage.
Rowwise order/equality and positivity therefore pass to the SAME original
row limits. Constant rows retain supplied Cauchy representatives and have
modulus zero; no representative is selected from an arbitrary quotient.

These are limit consequences, not new analytic assumptions or physical
spectral claims. They support original continuous operator form estimates.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (nested_error)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def constantRows (X : seminorm.Cauchy) : CauchyRows where
  row := fun _ => X
  modulus := fun _ => 0
  isCauchy := by
    intro epsilon he _ _ _ _
    rw [(completedDist_zero_iff _ _).mpr rfl]
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

theorem constantRows_pin (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (constantRows X) n=Quotient.mk seminorm.completionSetoid X := rfl

theorem rowLimit_constant (X : seminorm.Cauchy) :
    rowLimit (constantRows X)=Quotient.mk seminorm.completionSetoid X :=
  rowLimit_eq_of_bound _ _ (fun _ => 0)
    (fun epsilon he n _ => (constantRows X).isCauchy epsilon he n 0 (Nat.zero_le n) (Nat.le_refl 0))

theorem rowLimit_pairing_le (R S U V : CauchyRows)
    (h : ∀ n,RCle (completedInner (rowPoint R n) (rowPoint S n))
      (completedInner (rowPoint U n) (rowPoint V n))) :
    RCle (completedInner (rowLimit R) (rowLimit S)) (completedInner (rowLimit U) (rowLimit V)) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let d := HalfPow.half*epsilon
  have hd : (0 : Q')<d := ExpNeg.half_mul_pos epsilon he
  let n := max (pairingModulus R S d) (pairingModulus U V d)
  have hleft := (row_pairing_bound R S d hd n (Nat.le_max_left _ _)).2
  have hright := (row_pairing_bound U V d hd n (Nat.le_max_right _ _)).1
  have hb := RCle_trans hleft (RCadd_le_add (RCle_trans (h n) hright) (RCle_refl _))
  rw [nested_error] at hb
  exact RCle_trans hb (RCadd_le_add (RCle_refl _)
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (ExpNeg.two_halves epsilon))))

theorem rowLimit_pairing_eq (R S U V : CauchyRows)
    (h : ∀ n,completedInner (rowPoint R n) (rowPoint S n)=completedInner (rowPoint U n) (rowPoint V n)) :
    completedInner (rowLimit R) (rowLimit S)=completedInner (rowLimit U) (rowLimit V) :=
  RCle_antisymm (rowLimit_pairing_le R S U V (fun n => by rw [h n]; exact RCle_refl _))
    (rowLimit_pairing_le U V R S (fun n => by rw [h n]; exact RCle_refl _))

theorem rowLimit_pairing_nonnegative (R S : CauchyRows)
    (h : ∀ n,RCnonneg (completedInner (rowPoint R n) (rowPoint S n))) :
    RCnonneg (completedInner (rowLimit R) (rowLimit S)) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus R S epsilon
  exact RCle_trans (h n) (row_pairing_bound R S epsilon he n (Nat.le_refl n)).1

end YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.constantRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.constantRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.rowLimit_constant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.rowLimit_pairing_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.rowLimit_pairing_eq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder.rowLimit_pairing_nonnegative
