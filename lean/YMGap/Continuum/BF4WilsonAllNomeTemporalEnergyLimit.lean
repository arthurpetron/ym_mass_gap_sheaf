/-
# Actual temporal energy converges to the original completed time loss

For any supplied radius-zero signed Wilson expression, twice the ACTUAL
normalized finite energy is one fixed squared-increment insertion in the
original one-step window. Common padding handles units without selecting a
quotient representative. Existing independent heat/time estimates therefore
construct the energy's own QCauchy witness and CReal limit. The limit is the
one-step loss of the existing centered vector under the original transfer.

Nome and width are fixed. No spatial/spacing passage, scaling-small energy
bound, nonzero continuum survival, angular limit or Clay closure is supplied.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
import YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement

namespace YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (source_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
  (windowRatio_padded_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump jump_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy normalizedEnergy_window normalizedEnergy_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (source_difference)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
  (differenceAt squareAt square_within increment state increment_reflected_pin)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_loss_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (reindexQuaternionPolynomial_neg)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] originalWindowScalar baseLinks

private theorem padded_neg {blocks : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

/-- The WHOLE signed source difference is retained, including unit terms. -/
theorem source_square_jump {width : Nat} (e : WindowExpression width) :
    PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (sourcePolynomial (squareAt e 1))
      (polyMul (jump width (sourcePolynomial e))
        (jump width (sourcePolynomial e))) := by
  have hs : PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (sourcePolynomial (BF4ExactSlabFixedSpatialWilsonCenteredWindow.shift 1 e))
      (SU2QuaternionPartialFactorizedHaar.liftBoundary (N width) (sourcePolynomial e)) := by
    simpa only [Nat.one_mul] using source_shift ((1+1)*(N width)) 1 e
  have hd : PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (sourcePolynomial (differenceAt e 1)) (jump width (sourcePolynomial e)) :=
    (PaddedPolynomialCoeffEqv.of_coeff (source_difference e _)).trans
      ((PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg hs))
  exact hd.mul hd

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (e : WindowExpression width) (he : Within 0 e)

include he in
private theorem single_support : SupportedQuaternionBlocks (N width) (sourcePolynomial e) := by
  simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he

/-- Literal finite energy with its original terminal source and partition. -/
def finiteEnergy (k t : Nat) : Q' :=
  normalizedEnergy hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) t (sourcePolynomial e)

include he in
theorem finiteEnergy_nonnegative (k t : Nat) :
    (0 : Q') ≤ finiteEnergy hw0 hw1 e k t :=
  normalizedEnergy_nonnegative hw0 hw1 _ width (Nat.le_add_right _ _) t
    (single_support e he)

include he in
/-- One fixed signed squared-increment insertion, SAME finite action and Z. -/
theorem finite_increment_pin (k t : Nat) :
    originalWindowScalar hw0 hw1 1 (squareAt e 1) k t t ≈
      (2 : Q')*finiteEnergy hw0 hw1 e k t := by
  have hj := jump_supported width (single_support e he)
  have hsq : SupportedQuaternionBlocks ((1+1)*(N width))
      (polyMul (jump width (sourcePolynomial e)) (jump width (sourcePolynomial e))) := by
    simpa only [show (1 : Nat)+1=2 by rfl, Nat.two_mul] using supported_polyMul hj hj
  exact Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 _ (square_within he 1) k t t)
    (Q'.eqv_trans _ _ _
      (windowRatio_padded_congr hw0 hw1 _ width (Nat.le_add_right _ _) t 1 t
        (source_supported 1 _ (square_within he 1)) hsq (source_square_jump e))
      (Q'.eqv_symm (normalizedEnergy_window hw0 hw1 _ width
        (Nat.le_add_right _ _) t (single_support e he))))

private theorem half_double (a : Q') : HalfPow.half*((2 : Q')*a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ a (by decide : HalfPow.half*(2 : Q') ≈ 1))
      (Q'.one_mul_eqv a))

include he in
theorem finiteEnergy_half_pin (k t : Nat) :
    finiteEnergy hw0 hw1 e k t ≈
      HalfPow.half*originalWindowScalar hw0 hw1 1 (squareAt e 1) k t t :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (half_double _))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (finite_increment_pin hw0 hw1 e he k t)))

private theorem half_bound {a b c d epsilon : Q'}
    (ha : a ≈ HalfPow.half*c) (hb : b ≈ HalfPow.half*d)
    (h : c ≤ d+(2 : Q')*epsilon) : a ≤ b+epsilon := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half h (by decide)
  have hr : HalfPow.half*(d+(2 : Q')*epsilon) ≈ b+epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_symm hb) (half_double epsilon))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

/-- Computed heat and time thresholds for the actual energy, not its mean. -/
def energyCutoffThreshold (epsilon : Q') : Nat :=
  jointCutoffThreshold hw0 hw1 1 (squareAt e 1) ((2 : Q')*epsilon)

def energyTimeThreshold (epsilon : Q') : Nat :=
  jointTimeThreshold hw0 hw1 (squareAt e 1) ((2 : Q')*epsilon)

include he in
/-- Both finite regulators vary independently with a SINGLE fixed insertion. -/
theorem finiteEnergy_rectangle (epsilon : Q') (hp : (0 : Q') < epsilon)
    (k t j s : Nat)
    (hk : energyCutoffThreshold hw0 hw1 e epsilon ≤ k)
    (ht : energyTimeThreshold hw0 hw1 e epsilon ≤ t)
    (hj : energyCutoffThreshold hw0 hw1 e epsilon ≤ j)
    (hs : energyTimeThreshold hw0 hw1 e epsilon ≤ s) :
    finiteEnergy hw0 hw1 e k t ≤ finiteEnergy hw0 hw1 e j s+epsilon ∧
      finiteEnergy hw0 hw1 e j s ≤ finiteEnergy hw0 hw1 e k t+epsilon := by
  have hr := originalJoint_rectangle hw0 hw1 1 (squareAt e 1) (square_within he 1)
    ((2 : Q')*epsilon) (Q'.mul_pos (by decide : (0 : Q') < 2) hp) k t j s hk ht hj hs
  exact ⟨half_bound (finiteEnergy_half_pin hw0 hw1 e he k t)
      (finiteEnergy_half_pin hw0 hw1 e he j s) hr.1,
    half_bound (finiteEnergy_half_pin hw0 hw1 e he j s)
      (finiteEnergy_half_pin hw0 hw1 e he k t) hr.2⟩

/-- Type-valued modulus for the ACTUAL normalized finite energy. -/
def energyCauchy : QCauchy (fun s => finiteEnergy hw0 hw1 e s s) where
  M epsilon := max (energyCutoffThreshold hw0 hw1 e epsilon)
    (energyTimeThreshold hw0 hw1 e epsilon)
  bound := fun epsilon hp i j hi hj =>
    finiteEnergy_rectangle hw0 hw1 e he epsilon hp i i j j
      (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_right _ _) hi)
      (Nat.le_trans (Nat.le_max_left _ _) hj) (Nat.le_trans (Nat.le_max_right _ _) hj)

def energyLimit : CReal := ofQ'CauchySeq _ (energyCauchy hw0 hw1 e he)

/-- Full late rectangle versus the limit's explicitly indexed representative. -/
theorem energyLimit_approx (epsilon : Q') (hp : (0 : Q') < epsilon) (k t p : Nat)
    (hk : energyCutoffThreshold hw0 hw1 e epsilon ≤ k)
    (ht : energyTimeThreshold hw0 hw1 e epsilon ≤ t)
    (hrep : (energyCauchy hw0 hw1 e he).M epsilon ≤ p) :
    finiteEnergy hw0 hw1 e k t ≤ (energyLimit hw0 hw1 e he).approx p+epsilon ∧
      (energyLimit hw0 hw1 e he).approx p ≤ finiteEnergy hw0 hw1 e k t+epsilon := by
  let c := energyCauchy hw0 hw1 e he
  let s := QMhat _ c p
  have hsp : c.M epsilon ≤ s := Nat.le_trans hrep (self_le_QMhat _ c p)
  exact finiteEnergy_rectangle hw0 hw1 e he epsilon hp k t s s hk ht
    (Nat.le_trans (Nat.le_max_left _ _) hsp) (Nat.le_trans (Nat.le_max_right _ _) hsp)

attribute [local irreducible] finiteEnergy energyCauchy energyLimit originalJointLimit intrinsicForm

private theorem halfStream_converges {a : Nat → Q'} {A : CReal}
    (ha : ConvergesTo (fun s => ofQ' (a s)) A) :
    ConvergesTo (fun s => ofQ' (HalfPow.half*a s)) (mul (ofQ' HalfPow.half) A) := by
  have h := Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
    (convergesTo_const (ofQ' HalfPow.half)) ha
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) h

/-- The constructed actual-energy limit is half the existing increment limit. -/
theorem energyLimit_increment_pin :
    Equiv (energyLimit hw0 hw1 e he) (mul (ofQ' HalfPow.half) (increment hw0 hw1 e he 1)) :=
  Equiv_of_limit_of_equal
    (fun s => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => finiteEnergy_half_pin hw0 hw1 e he s s))
    (by unfold energyLimit; exact convergesTo_ofQ'CauchySeq _ (energyCauchy hw0 hw1 e he))
    (halfStream_converges
      (originalJoint_diagonal_converges hw0 hw1 1 (squareAt e 1) (square_within he 1)))

/-- Original reflected time LOSS, not the squared norm of the vector difference. -/
theorem energyLimit_reflected_pin :
    Equiv (energyLimit hw0 hw1 e he)
      (sub (intrinsicForm hw0 hw1 (state e he) (state e he))
        (intrinsicForm hw0 hw1 (state e he) (advance 1 (state e he)))) :=
  (energyLimit_increment_pin hw0 hw1 e he).trans
    ((Pivot2.mul_congr_right (increment_reflected_pin hw0 hw1 e he 1)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => half_double _)))

/-- Exact temporal-energy consumer on the EXISTING centered-vector carrier. -/
theorem energyLimit_completed_pin :
    Quotient.mk crealSetoid (energyLimit hw0 hw1 e he) =
      RCsub
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (completedTime hw0 hw1 1 (centeredVector hw0 hw1 (state e he)))) := by
  rw [centeredVector_loss_pin]
  exact Quotient.sound (energyLimit_reflected_pin hw0 hw1 e he)

#print axioms source_square_jump
#print axioms finiteEnergy
#print axioms finiteEnergy_nonnegative
#print axioms finite_increment_pin
#print axioms finiteEnergy_half_pin
#print axioms energyCutoffThreshold
#print axioms energyTimeThreshold
#print axioms finiteEnergy_rectangle
#print axioms energyCauchy
#print axioms energyLimit
#print axioms energyLimit_approx
#print axioms energyLimit_increment_pin
#print axioms energyLimit_reflected_pin
#print axioms energyLimit_completed_pin

end YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
