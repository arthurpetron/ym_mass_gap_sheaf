/-
# Infinitesimal phase of the constructed original physical Cayley limit

The represented second core supplies its ORIGINAL Rows and a computed
finite-product convergence rate.  Passing the checked finite tangent
through that rate gives the factor-two phase of the actual quotient limit.
This fixes no physical lattice spacing or logarithm of the transfer.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyInfinitesimal
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
import YMGap.Continuum.RationalScalarTwoSidedError

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows ofState rowsOfState ofRows_rowsOfState
    value value_injective value_ofState distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyInfinitesimal
  (orbit finite_product_tangent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "PD" => BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)
local notation "YType" =>
  CRealSeminormCompletion.SquaredSeminorm.Cauchy PD ×
    CRealSeminormCompletion.SquaredSeminorm.Cauchy PD
local notation "N" => normSq hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "dist" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def fourth (t : Q') : Q' := (t*t)*(t*t)

/-- The actual first second-core graph point has supplied original Cauchy
Rows; no completed-quotient representative is selected. -/
def coreRows (Y : YType) : R :=
  rowsOfState hw0 hw1
    (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1
      (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y))

theorem coreRows_input (Y : YType) :
    ofRows hw0 hw1 (coreRows hw0 hw1 Y) =
      In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y) := by
  unfold coreRows
  rw [ofRows_rowsOfState]
  apply value_injective hw0 hw1
  rw [value_ofState]
  change BF4WilsonAllNomeComplexSectorDerivative.stateValue hw0 hw1
      (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1
        (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)) =
    value hw0 hw1 (In (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1
      (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)))
  exact (BF4WilsonAllNomeComplexBondOSDerivative.value_input_ofPoint hw0 hw1
    (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)).symm

theorem coreRows_product (Y : YType) (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    productValue hw0 hw1 (coreRows hw0 hw1 Y) t ht n =
      orbit hw0 hw1 t ht
        (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)) n := by
  unfold productValue orbit
  rw [coreRows_input]

private theorem diff_trans (a b c : H) :
    A (diff hw0 hw1 a b) (diff hw0 hw1 b c) = diff hw0 hw1 a c := by
  have hassoc : ∀ x y z : H, A (A x y) z = A x (A y z) :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1
  have hcomm : ∀ x y : H, A x y = A y x :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_comm hw0 hw1
  unfold diff
  calc
    A (A a (cneg hw0 hw1 b)) (A b (cneg hw0 hw1 c)) =
        A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) := by
      calc
        A (A a (cneg hw0 hw1 b)) (A b (cneg hw0 hw1 c)) =
            A (A a (cneg hw0 hw1 b)) (A (cneg hw0 hw1 c) b) := by
              rw [hcomm b (cneg hw0 hw1 c)]
        _ = A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) := by
          calc
            A (A a (cneg hw0 hw1 b)) (A (cneg hw0 hw1 c) b) =
                A a (A (cneg hw0 hw1 b) (A (cneg hw0 hw1 c) b)) := hassoc _ _ _
            _ = A a (A (cneg hw0 hw1 c) (A (cneg hw0 hw1 b) b)) := by
                  rw [← hassoc (cneg hw0 hw1 b) (cneg hw0 hw1 c) b,
                    hcomm (cneg hw0 hw1 b) (cneg hw0 hw1 c),hassoc]
            _ = A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) :=
              (hassoc _ _ _).symm
    _ = A a (cneg hw0 hw1 c) := by
      rw [BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add,
        BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero]

private theorem error_exchange (a b x p : H) :
    A (diff hw0 hw1 a b) (A (diff hw0 hw1 b x) p) =
      A (diff hw0 hw1 a x) p := by
  calc
    A (diff hw0 hw1 a b) (A (diff hw0 hw1 b x) p) =
        A (A (diff hw0 hw1 a b) (diff hw0 hw1 b x)) p :=
          (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc
            hw0 hw1 _ _ _).symm
    _ = A (diff hw0 hw1 a x) p :=
      congrArg (fun v => A v p) (diff_trans hw0 hw1 a b x)

private theorem two_halves_error (c : Q') (z : RC) (e : Q') :
    RCadd
      (RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)))
      (RCadd (RCscale c z) (RCscale c z)) =
    RCadd (RCscale (c+c) z) (rat e) := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add
          (.add (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.add (.mul (.add (.var 1) (.var 1)) (.var 2))
          (.add (.var 0) (.var 0)))
        (by decide)
        (fun | 0 => HalfPow.half*e | 1 => c | _ => Z.approx n))
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e))))

/-- The constructed all-Rows limit has the exact `-2 i` infinitesimal
phase on its represented original second core. The error is fourth order
in the rational parameter in squared norm and pays the SAME second graph
output; it is not lattice-time or transfer-logarithm calibration. -/
theorem limitMap_secondCore_tangent (Y : YType) (t : Q')
    (ht : (0 : Q') < t) :
    let d := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
    let e := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
    RCle
      (N (A (diff hw0 hw1 (limitMap hw0 hw1 t ht (In d)) (In d))
        (imagScale hw0 hw1 t (A (Out d) (Out d)))))
      (RCscale ((368 : Q')*fourth t)
        (N (Out e))) := by
  dsimp only
  let d := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
  let e := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
  let x := In d
  let z := Out e
  let X := coreRows hw0 hw1 Y
  have hx : ofRows hw0 hw1 X = x := coreRows_input hw0 hw1 Y
  have hlink : Out d = In e :=
    BF4WilsonAllNomeComplexBondOSSecondCore.first_output_eq_second_input hw0 hw1 Y
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon hepsilon
  let q := HalfPow.half*epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  let n := BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.productLimitRate
    hw0 hw1 X t ht q
  have hlimit : RCle
      (dist (limitMap hw0 hw1 t ht x) (orbit hw0 hw1 t ht x n)) (rat q) := by
    rw [distance_symm]
    have h := limitMap_bound hw0 hw1 X t ht q hq n (Nat.le_refl n)
    rw [coreRows_product hw0 hw1 Y t ht n,hx] at h
    exact h
  have hfinite := finite_product_tangent hw0 hw1 t ht d e hlink n
  change RCle
    (N (A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) x)
      (imagScale hw0 hw1 t (A (Out d) (Out d)))))
    (RCscale ((184 : Q')*fourth t) (N z)) at hfinite
  let phase := imagScale hw0 hw1 t (A (Out d) (Out d))
  have hsum := RCle_trans
    (normSq_add_le hw0 hw1
      (diff hw0 hw1 (limitMap hw0 hw1 t ht x) (orbit hw0 hw1 t ht x n))
      (A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) x) phase))
    (RCadd_le_add
      (RCadd_le_add (by rw [← distance_eq_norm_difference]; exact hlimit)
        (by rw [← distance_eq_norm_difference]; exact hlimit))
      (RCadd_le_add hfinite hfinite))
  rw [error_exchange] at hsum
  have hcoef := two_halves_error
    ((184 : Q')*fourth t)
    (N z) epsilon
  have hdouble : Q'.eqv
      (((184 : Q')*fourth t)+((184 : Q')*fourth t))
      ((368 : Q')*fourth t) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 184) (.var 0)) (.mul (.const 184) (.var 0)))
      (.mul (.const 368) (.var 0)) (by decide)
      (fun _ => fourth t)
  rw [hcoef,scale_congr hdouble] at hsum
  exact hsum

#print axioms coreRows
#print axioms coreRows_input
#print axioms coreRows_product
#print axioms limitMap_secondCore_tangent

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal
