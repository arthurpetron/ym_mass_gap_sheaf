/-
# Centering-independent original-law tests retaining whole spectator forests

Each test pairs the original heat-dressed observable against a supplied
polynomial in a partially retained ORIGINAL interface. Cauchy--Schwarz
bounds its squared amplitude by the full original reflected norm times
its computed reference energy. Two such tests give a determinant floor
independent of every rational centering coefficient.

All test polynomials, retained forests, energies and minors are explicit
finite data. No minor positivity is postulated for a concrete test, and no
volume-independent normalized floor or thermodynamic excitation is claimed.
The open estimate must retain the spectator partition through normalization.
-/

import YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
import YMGap.Continuum.ReflectedSquareTreeTestForm

namespace YMGap.Continuum.BF4ExactSlabPartialInterfaceTests

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor (recentered)
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.ReflectedSquareTreeTestForm
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound (determinant determinant_shift)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))

def testAmplitude (choice : Nat → PartialChoice) (q : RatPoly) (e : PlaquetteExpression half) : Q' :=
  channelBilinearValue blocks (dressedLower w K e) q (retainedInterface hw K hK half choice)

def referenceEnergy (choice : Nat → PartialChoice) (q : RatPoly) : Q' :=
  channelBilinearValue blocks q q (retainedInterface hw K hK half choice)

theorem referenceEnergy_nonnegative (choice : Nat → PartialChoice) (q : RatPoly) :
    (0 : Q') ≤ referenceEnergy hw K hK half choice q :=
  (treeForm blocks _ (retainedInterface_nonnegative hw K hK half choice)).self_nonneg q

theorem testAmplitude_bound (choice : Nat → PartialChoice) (q : RatPoly) (e : PlaquetteExpression half) :
    testAmplitude hw K hK half choice q e * testAmplitude hw K hK half choice q e ≤
      rawForm w K e e * referenceEnergy hw K hK half choice q := by
  have h := cauchySchwarz blocks _ (retainedInterface_nonnegative hw K hK half choice) (dressedLower w K e) q
  have hn := Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagonal_pin blocks (dressedLower w K e) _))
    (retainedValue_le_rawForm hw K hK choice e)
  exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ _ hn (referenceEnergy_nonnegative hw K hK half choice q))

theorem testAmplitude_add (choice : Nat → PartialChoice) (q : RatPoly) (e f : PlaquetteExpression half) :
    testAmplitude hw K hK half choice q (.add e f) ≈
      testAmplitude hw K hK half choice q e + testAmplitude hw K hK half choice q f := by
  unfold testAmplitude dressedLower
  change channelBilinearValue blocks (polyMul (polyAdd (lower e) (lower f)) _) q _ ≈ _
  rw [polyMul_add_left_exact]
  exact pairing_add_left blocks _ _ _ _

theorem testAmplitude_smul (choice : Nat → PartialChoice) (q : RatPoly) (c : Q') (e : PlaquetteExpression half) :
    testAmplitude hw K hK half choice q (.smul c e) ≈ c * testAmplitude hw K hK half choice q e :=
  Q'.eqv_trans _ _ _
    (pairing_coeff_left blocks (RatPolyCoeffEqv.polyMul_smul_left c (lower e) _) q _)
    (pairing_smul_left blocks c (dressedLower w K e) q _)

theorem testAmplitude_recentered (choice : Nat → PartialChoice) (q : RatPoly) (e : PlaquetteExpression half) (c : Q') :
    testAmplitude hw K hK half choice q (recentered half e c) ≈
      testAmplitude hw K hK half choice q e + (-c) * testAmplitude hw K hK half choice q .unit :=
  Q'.eqv_trans _ _ _ (testAmplitude_add hw K hK half choice q e _)
    (Q'.add_eqv_congr_left _ _ _ (testAmplitude_smul hw K hK half choice q (-c) .unit))

variable (choice0 choice1 : Nat → PartialChoice) (q0 q1 : RatPoly)

local notation "A0" => testAmplitude hw K hK half choice0 q0
local notation "A1" => testAmplitude hw K hK half choice1 q1
local notation "E0" => referenceEnergy hw K hK half choice0 q0
local notation "E1" => referenceEnergy hw K hK half choice1 q1

def testMinor (e : PlaquetteExpression half) : Q' :=
  let d := determinant (A0 e) (A1 e) (A0 .unit) (A1 .unit)
  d*d

def referenceBudget : Q' :=
  2 * (E0 * (A1 .unit * A1 .unit) + E1 * (A0 .unit * A0 .unit))

theorem referenceBudget_nonnegative : (0 : Q') ≤ referenceBudget hw K hK half choice0 choice1 q0 q1 :=
  Q'.mul_nonneg _ _ (by decide) (Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (referenceEnergy_nonnegative hw K hK half choice0 q0) (SumOfSquares.q_mul_self_nonneg _))
    (Q'.mul_nonneg _ _ (referenceEnergy_nonnegative hw K hK half choice1 q1) (SumOfSquares.q_mul_self_nonneg _)))

theorem testMinor_recentered (e : PlaquetteExpression half) (c : Q') :
    testMinor hw K hK half choice0 choice1 q0 q1 (recentered half e c) ≈
      testMinor hw K hK half choice0 choice1 q0 q1 e := by
  have hd : determinant (A0 (recentered half e c)) (A1 (recentered half e c)) (A0 .unit) (A1 .unit) ≈
      determinant (A0 e) (A1 e) (A0 .unit) (A1 .unit) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (testAmplitude_recentered hw K hK half choice0 q0 e c))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (testAmplitude_recentered hw K hK half choice1 q1 e c))))
      (determinant_shift _ _ _ _ c)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hd) (Q'.mul_eqv_congr_left _ _ _ hd)

private theorem det_square_bound (a0 a1 b0 b1 : Q') :
    determinant a0 a1 b0 b1 * determinant a0 a1 b0 b1 ≤
      2*((a0*a0)*(b1*b1)+(a1*a1)*(b0*b0)) := by
  let minus := RingNormaliser.PolyExpr.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))
  let plus := RingNormaliser.PolyExpr.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg (a0*b1+a1*b0)))
    (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul minus minus) (.mul plus plus))
      (.mul (.const 2) (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))) (by decide)
      (fun | 0 => a0 | 1 => a1 | 2 => b0 | _ => b1)))

theorem testMinor_bound (e : PlaquetteExpression half) :
    testMinor hw K hK half choice0 choice1 q0 q1 e ≤
      rawForm w K e e * referenceBudget hw K hK half choice0 choice1 q0 q1 := by
  have h0 := Q'.mul_le_mul_of_nonneg_right _ _ _ (testAmplitude_bound hw K hK half choice0 q0 e)
    (SumOfSquares.q_mul_self_nonneg (A1 .unit))
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _ (testAmplitude_bound hw K hK half choice1 q1 e)
    (SumOfSquares.q_mul_self_nonneg (A0 .unit))
  have h := Q'.le_trans' _ _ _ (det_square_bound (A0 e) (A1 e) (A0 .unit) (A1 .unit))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add h0 h1) (by decide : (0 : Q') ≤ 2))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
    (.mul (.const 2) (.add (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4))))
    (.mul (.var 0) (.mul (.const 2) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4))))) (by decide)
    (fun | 0 => rawForm w K e e | 1 => E0 | 2 => E1 | 3 => A1 .unit*A1 .unit | _ => A0 .unit*A0 .unit)))

theorem every_recentered_bound (e : PlaquetteExpression half) (c : Q') :
    testMinor hw K hK half choice0 choice1 q0 q1 e ≤
      rawForm w K (recentered half e c) (recentered half e c) * referenceBudget hw K hK half choice0 choice1 q0 q1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (testMinor_recentered hw K hK half choice0 choice1 q0 q1 e c))
    (testMinor_bound hw K hK half choice0 choice1 q0 q1 _)

theorem floorDenominator_pos : (0 : Q') < referenceBudget hw K hK half choice0 choice1 q0 q1 + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (referenceBudget_nonnegative hw K hK half choice0 choice1 q0 q1))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def testFloor (e : PlaquetteExpression half) : Q' :=
  Q'.divPos (testMinor hw K hK half choice0 choice1 q0 q1 e)
    (referenceBudget hw K hK half choice0 choice1 q0 q1 + 1) (floorDenominator_pos hw K hK half choice0 choice1 q0 q1)

theorem testFloor_bound (e : PlaquetteExpression half) (c : Q') :
    testFloor hw K hK half choice0 choice1 q0 q1 e ≤ rawForm w K (recentered half e c) (recentered half e c) :=
  Q'.divPos_le_of_le_mul _ _ _ (Q'.le_trans' _ _ _ (every_recentered_bound hw K hK half choice0 choice1 q0 q1 e c)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one) (rawForm_nonnegative w hw K _)))

theorem testFloor_positive (e : PlaquetteExpression half)
    (hm : (0 : Q') < testMinor hw K hK half choice0 choice1 q0 q1 e) :
    (0 : Q') < testFloor hw K hK half choice0 choice1 q0 q1 e := Q'.divPos_pos _ _ _ hm

end YMGap.Continuum.BF4ExactSlabPartialInterfaceTests

#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.referenceEnergy
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.referenceEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testAmplitude_bound
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testAmplitude_add
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testAmplitude_smul
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testAmplitude_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testMinor
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.referenceBudget
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.referenceBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testMinor_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testMinor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.every_recentered_bound
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.floorDenominator_pos
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testFloor
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceTests.testFloor_positive
