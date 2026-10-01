/-
# The original odd marginal variance is energy plus bond norm

The normalized original finite identity E+B/Z=Var is retained at every
cutoff and exterior depth, with its actual finite center. The two proved
regulator rectangles construct the marginal variance's own QCauchy witness.
Its limit is the ORIGINAL ambient centered norm: the connected physical
bond norm is its one-step time pairing, not that ambient norm by itself.

This supplies an exact forward/backward join, not a scaling-small energy
estimate, a positive limiting excitation or a continuum construction.
-/

import YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve

namespace YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve
  (centered_transfer_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
  (normalizedCenteredTransferQuadratic)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
  (finiteEnergy energyCauchy energyLimit energyLimit_completed_pin
    energyCutoffThreshold energyTimeThreshold finiteEnergy_rectangle)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (singleSlice finiteScalar transferCauchy transferLimit transferLimit_completed_pin
    cutoffThreshold timeThreshold finiteScalar_rectangle)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeTimeForm (intrinsicForm_time_balance)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
  (centeredTimeMoment intrinsicForm_unit_invariant intrinsicForm_unit_invariant_right)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay
  (connected connected_source_pin)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks finiteEnergy finiteScalar intrinsicForm bondForm
  normalizedEnergy normalizedCenteredTransferQuadratic oddVariance oddMass

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

private theorem bondForm_time_pin (x y : IntrinsicExpression width) :
    bondForm hw0 hw1 x y =
      Quotient.mk crealSetoid (intrinsicForm hw0 hw1 x (advance 1 y)) := by
  unfold bondForm
  exact Quotient.sound (crossOdd_pin hw0 hw1 x y).symm

/-- The physical connected bond norm is the ORIGINAL ambient one-step
pairing of the centered vector; no diagonal-norm substitution is made. -/
theorem bond_connected_time_pairing (x : IntrinsicExpression width) :
    connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) =
      completedInner hw0 hw1 (centeredVector hw0 hw1 x)
        (completedTime hw0 hw1 1 (centeredVector hw0 hw1 x)) := by
  rw [connected_source_pin, advance_zero, bondForm_time_pin, bondForm_time_pin,
    bondForm_time_pin, centeredVector_time_pairing]
  apply Quotient.sound
  change Equiv
    (sub (intrinsicForm hw0 hw1 x (advance 1 x))
      (mul (intrinsicForm hw0 hw1 x (advance 1 (unit width)))
        (intrinsicForm hw0 hw1 (unit width) (advance 1 x))))
    (centeredTimeMoment hw0 hw1 1 x x)
  exact equiv_sub (Equiv.refl _)
    (Pivot2.mul_congr
      ((intrinsicForm_time_balance hw0 hw1 1 x (unit width)).symm.trans
        (intrinsicForm_unit_invariant hw0 hw1 1 x))
      (intrinsicForm_unit_invariant_right hw0 hw1 1 x))

variable (e : WindowExpression width) (he : Within 0 e)

/-- The SAME original odd marginal variance at the actual finite regulators. -/
def finiteVariance (k t : Nat) : Q' :=
  oddVariance hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) t (sourcePolynomial e)

attribute [local irreducible] finiteVariance

private theorem normalize_budget {a b z v : Q'} (hz : (0 : Q') < z)
    (h : a+b ≈ z*v) :
    v ≈ a*Q'.recipPos z hz+b*Q'.recipPos z hz := by
  let r := Q'.recipPos z hz
  have hc : (z*v)*r ≈ v :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => z | 1 => v | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv z hz)) (Q'.one_mul_eqv v))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _).symm
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r h) hc))

include he in
/-- Normalize E+B=Z*Var using ONLY the original positive odd partition. -/
theorem finiteVariance_budget_pin (k t : Nat) :
    finiteVariance hw0 hw1 e k t ≈
      finiteEnergy hw0 hw1 e k t+finiteScalar hw0 hw1 e k t := by
  have hf : SupportedQuaternionBlocks (N width) (sourcePolynomial e) := by
    simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he
  unfold finiteVariance finiteEnergy finiteScalar normalizedEnergy normalizedCenteredTransferQuadratic
  exact normalize_budget
    (oddMass_positive hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) t)
    (centered_transfer_quadratic_pin hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) t hf)

private theorem add_close {a b c d epsilon : Q'}
    (ha : a ≤ c+HalfPow.half*epsilon) (hb : b ≤ d+HalfPow.half*epsilon) :
    a+b ≤ (c+d)+epsilon := by
  let q := HalfPow.half*epsilon
  have h := Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ b ha)
    (Q'.add_le_add_left (c+q) _ _ hb)
  have hr : (c+q)+(d+q) ≈ (c+d)+epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
        (by decide) (fun | 0 => c | 1 => d | _ => q))
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr)

def varianceCutoffThreshold (epsilon : Q') : Nat :=
  max (energyCutoffThreshold hw0 hw1 e (HalfPow.half*epsilon))
    (cutoffThreshold hw0 hw1 e he (HalfPow.half*epsilon))

def varianceTimeThreshold (epsilon : Q') : Nat :=
  max (energyTimeThreshold hw0 hw1 e (HalfPow.half*epsilon))
    (timeThreshold hw0 hw1 e he (HalfPow.half*epsilon))

/-- Moving finite means are handled by the exact energy/bond decomposition. -/
theorem finiteVariance_rectangle (epsilon : Q') (hp : (0 : Q') < epsilon)
    (k t j s : Nat)
    (hk : varianceCutoffThreshold hw0 hw1 e he epsilon ≤ k)
    (ht : varianceTimeThreshold hw0 hw1 e he epsilon ≤ t)
    (hj : varianceCutoffThreshold hw0 hw1 e he epsilon ≤ j)
    (hs : varianceTimeThreshold hw0 hw1 e he epsilon ≤ s) :
    finiteVariance hw0 hw1 e k t ≤ finiteVariance hw0 hw1 e j s+epsilon ∧
      finiteVariance hw0 hw1 e j s ≤ finiteVariance hw0 hw1 e k t+epsilon := by
  let delta := HalfPow.half*epsilon
  have hd := ExpNeg.half_mul_pos epsilon hp
  have hE := finiteEnergy_rectangle hw0 hw1 e he delta hd k t j s
    (Nat.le_trans (Nat.le_max_left _ _) hk) (Nat.le_trans (Nat.le_max_left _ _) ht)
    (Nat.le_trans (Nat.le_max_left _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hs)
  have hB := finiteScalar_rectangle hw0 hw1 e he delta hd k t j s
    (Nat.le_trans (Nat.le_max_right _ _) hk) (Nat.le_trans (Nat.le_max_right _ _) ht)
    (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_right _ _) hs)
  have step (a b c d : Nat)
      (henergy : finiteEnergy hw0 hw1 e a b ≤ finiteEnergy hw0 hw1 e c d+delta)
      (hbond : finiteScalar hw0 hw1 e a b ≤ finiteScalar hw0 hw1 e c d+delta) :
      finiteVariance hw0 hw1 e a b ≤ finiteVariance hw0 hw1 e c d+epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (finiteVariance_budget_pin hw0 hw1 e he a b))
      (Q'.le_trans' _ _ _ (add_close henergy hbond)
        (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ epsilon
          (Q'.eqv_symm (finiteVariance_budget_pin hw0 hw1 e he c d)))))
  exact ⟨step k t j s hE.1 hB.1, step j s k t hE.2 hB.2⟩

/-- Explicit Type-valued modulus for the actual finite marginal variance. -/
def varianceCauchy : QCauchy (fun s => finiteVariance hw0 hw1 e s s) where
  M epsilon := max (varianceCutoffThreshold hw0 hw1 e he epsilon)
    (varianceTimeThreshold hw0 hw1 e he epsilon)
  bound := fun epsilon hp i j hi hj =>
    finiteVariance_rectangle hw0 hw1 e he epsilon hp i i j j
      (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_right _ _) hi)
      (Nat.le_trans (Nat.le_max_left _ _) hj) (Nat.le_trans (Nat.le_max_right _ _) hj)

def varianceLimit : CReal := ofQ'CauchySeq _ (varianceCauchy hw0 hw1 e he)

theorem varianceLimit_approx (epsilon : Q') (hp : (0 : Q') < epsilon) (k t p : Nat)
    (hk : varianceCutoffThreshold hw0 hw1 e he epsilon ≤ k)
    (ht : varianceTimeThreshold hw0 hw1 e he epsilon ≤ t)
    (hrep : (varianceCauchy hw0 hw1 e he).M epsilon ≤ p) :
    finiteVariance hw0 hw1 e k t ≤ (varianceLimit hw0 hw1 e he).approx p+epsilon ∧
      (varianceLimit hw0 hw1 e he).approx p ≤ finiteVariance hw0 hw1 e k t+epsilon := by
  let c := varianceCauchy hw0 hw1 e he
  let s := QMhat _ c p
  have hsp : c.M epsilon ≤ s := Nat.le_trans hrep (self_le_QMhat _ c p)
  exact finiteVariance_rectangle hw0 hw1 e he epsilon hp k t s s hk ht
    (Nat.le_trans (Nat.le_max_left _ _) hsp) (Nat.le_trans (Nat.le_max_right _ _) hsp)

attribute [local irreducible] varianceCauchy varianceLimit energyCauchy transferCauchy
  energyLimit transferLimit

private theorem addStream_converges {a b : Nat → Q'} {A B : CReal}
    (ha : ConvergesTo (fun s => ofQ' (a s)) A)
    (hb : ConvergesTo (fun s => ofQ' (b s)) B) :
    ConvergesTo (fun s => ofQ' (a s+b s)) (CReal.add A B) := by
  have hs := TrigAddCReal.convergesTo_add ha hb
  have hp (s : Nat) : Equiv (ofQ' (a s+b s)) (CReal.add (ofQ' (a s)) (ofQ' (b s))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  exact TrigAddCReal.convergesTo_congr_seq hp hs

theorem varianceLimit_budget_pin :
    Equiv (varianceLimit hw0 hw1 e he)
      (CReal.add (energyLimit hw0 hw1 e he) (transferLimit hw0 hw1 e he)) :=
  Equiv_of_limit_of_equal
    (fun s => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => finiteVariance_budget_pin hw0 hw1 e he s s))
    (by unfold varianceLimit; exact convergesTo_ofQ'CauchySeq _ (varianceCauchy hw0 hw1 e he))
    (addStream_converges
      (by unfold energyLimit; exact convergesTo_ofQ'CauchySeq _ (energyCauchy hw0 hw1 e he))
      (by unfold transferLimit; exact convergesTo_ofQ'CauchySeq _ (transferCauchy hw0 hw1 e he)))

private theorem RCsub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

/-- The limit of marginal variance is the ORIGINAL ambient centered norm.
Energy plus physical bond norm, not physical bond norm alone, equals it. -/
theorem varianceLimit_completed_pin :
    Quotient.mk crealSetoid (varianceLimit hw0 hw1 e he) =
      completedInner hw0 hw1 (centeredVector hw0 hw1 (singleSlice e he))
        (centeredVector hw0 hw1 (singleSlice e he)) := by
  have h : Quotient.mk crealSetoid (varianceLimit hw0 hw1 e he) =
      RCadd (Quotient.mk crealSetoid (energyLimit hw0 hw1 e he))
        (Quotient.mk crealSetoid (transferLimit hw0 hw1 e he)) :=
    Quotient.sound (varianceLimit_budget_pin hw0 hw1 e he)
  rw [energyLimit_completed_pin, transferLimit_completed_pin, bond_connected_time_pairing] at h
  exact h.trans (RCsub_add_cancel _ _)

#print axioms bond_connected_time_pairing
#print axioms finiteVariance
#print axioms finiteVariance_budget_pin
#print axioms varianceCutoffThreshold
#print axioms varianceTimeThreshold
#print axioms finiteVariance_rectangle
#print axioms varianceCauchy
#print axioms varianceLimit
#print axioms varianceLimit_approx
#print axioms varianceLimit_budget_pin
#print axioms varianceLimit_completed_pin

end YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
