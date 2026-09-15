/-
# Eventual distance bounds pass to the SAME original row limits

Difference rows are computed from the existing original addition and
constant-polynomial action. Their limit is the original difference,
with their Cauchy data retained. An eventual pairing or squared-distance
inequality passes to the already-constructed limits by the explicit
pairing error estimate. The cutoff is consumed only in a logical proof;
no output representative or modulus is extracted from a Prop witness.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
import YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear (addRows addRows_pin rowLimit_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (operatorRows operatorRows_pin operator_rowLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator (operator_constant)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (pairingModulus row_pairing_bound)

def differenceRows (R S : CauchyRows) : CauchyRows := addRows R (operatorRows [(-1 : Q')] S)

theorem differenceRows_pin (R S : CauchyRows) (n : Nat) :
    rowPoint (differenceRows R S) n = completedSub (rowPoint R n) (rowPoint S n) := by
  unfold differenceRows
  rw [addRows_pin, operatorRows_pin, operator_constant]
  rfl

theorem rowLimit_difference (R S : CauchyRows) :
    rowLimit (differenceRows R S) = completedSub (rowLimit R) (rowLimit S) := by
  unfold differenceRows
  rw [rowLimit_add, operator_rowLimit, operator_constant]
  rfl

theorem rowLimit_pairing_eventual_le (R S : CauchyRows) (M : RC) (N : Nat)
    (h : ∀ n, N ≤ n → RCle (completedInner (rowPoint R n) (rowPoint S n)) M) :
    RCle (completedInner (rowLimit R) (rowLimit S)) M := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := max (pairingModulus R S epsilon) N
  exact RCle_trans (row_pairing_bound R S epsilon he n (Nat.le_max_left _ _)).2
    (RCadd_le_add (h n (Nat.le_max_right _ _)) (RCle_refl _))

theorem rowLimit_distance_eventual_le (R S : CauchyRows) (M : RC) (N : Nat)
    (h : ∀ n, N ≤ n → RCle (completedDist (rowPoint R n) (rowPoint S n)) M) :
    RCle (completedDist (rowLimit R) (rowLimit S)) M := by
  have hd : ∀ n, N ≤ n →
      RCle (completedInner (rowPoint (differenceRows R S) n) (rowPoint (differenceRows R S) n)) M := by
    intro n hn
    rw [differenceRows_pin]
    exact h n hn
  have hb := rowLimit_pairing_eventual_le (differenceRows R S) (differenceRows R S) M N hd
  rw [rowLimit_difference] at hb
  exact hb

end YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder.differenceRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder.differenceRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder.rowLimit_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder.rowLimit_pairing_eventual_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder.rowLimit_distance_eventual_le
