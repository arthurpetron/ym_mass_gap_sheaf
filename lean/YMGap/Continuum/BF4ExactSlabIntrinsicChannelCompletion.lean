/-
# Original channel functionals on the original completed OS carrier

The dense coefficient tolerance gives a computed outer Cauchy rate;
the original numerator moduli give per-term inner regularity. Their
diagonal limit descends through the EXISTING completion relation, without
choosing representatives. Rational linearity and the SAME positive
observable-independent norm floor pass to that completion.

OPEN: completed channel separation/resolution, actual time-translation
compatibility, range approximation, volume and physical-scale control,
Hamiltonian identification and continuum/Clay. Dense separation is not
silently promoted to completed separation.
-/

import YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)

def coefficientSequence (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) (n : Nat) : CReal :=
  coefficient w hw0 hw1 N l (X.seq n)

def coefficientRawRate (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  X.modulus (coefficientTolerance w hw0 N l epsilon)

theorem coefficientSequence_raw_bound (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    LeRatBound (coefficientSequence w hw0 hw1 N l X) (coefficientRawRate w hw0 hw1 N l X) :=
  fun epsilon he m n hm hn => coefficient_close w hw0 hw1 N l (X.seq m) (X.seq n) epsilon he
    (X.isCauchy _ (coefficientTolerance_positive w hw0 N l he) m n hm hn)

def coefficientRate (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) : Q' → Nat :=
  closedRate canonicalReciprocalIndexData (coefficientRawRate w hw0 hw1 N l X)

theorem coefficientRate_antitone (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    MmonoPred (coefficientRate w hw0 hw1 N l X) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (coefficientRawRate w hw0 hw1 N l X)

theorem coefficientSequence_bound (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    LeRatBound (coefficientSequence w hw0 hw1 N l X) (coefficientRate w hw0 hw1 N l X) :=
  LeRatBound.closed canonicalReciprocalIndexData (coefficientSequence_raw_bound w hw0 hw1 N l X)

def coefficientReg (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) (n : Nat) : Q' → Nat :=
  (coefficientLimitCauchy w hw0 hw1 half (polyMul (lower (X.seq n)) l.channel)).M

theorem coefficientSequence_regular (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    RegPred (coefficientSequence w hw0 hw1 N l X) (coefficientReg w hw0 hw1 N l X) :=
  fun n => (coefficientLimitCauchy w hw0 hw1 half (polyMul (lower (X.seq n)) l.channel)).bound

/-- Numerical representative, computed from the supplied physical Cauchy data. -/
def representativeCoefficient (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) : CReal :=
  completeLimitFromRate (coefficientSequence w hw0 hw1 N l X) (coefficientRate w hw0 hw1 N l X)
    (coefficientReg w hw0 hw1 N l X) (coefficientSequence_regular w hw0 hw1 N l X)
    (coefficientSequence_bound w hw0 hw1 N l X)

theorem coefficientSequence_converges (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    ConvergesTo (coefficientSequence w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l X) :=
  convergesTo_completeLimitFromRate _ _ _ (coefficientSequence_regular w hw0 hw1 N l X)
    (coefficientSequence_bound w hw0 hw1 N l X) (coefficientRate_antitone w hw0 hw1 N l X)

def representativeCoefficientCauchy (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    QCauchy (representativeCoefficient w hw0 hw1 N l X).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (coefficientSequence_regular w hw0 hw1 N l X)
        (coefficientSequence_bound w hw0 hw1 N l X) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (coefficientSequence_regular w hw0 hw1 N l X)
        (coefficientSequence_bound w hw0 hw1 N l X) epsilon he j i hji hj).symm

def coefficientCloseRate (N : Nat) (l : Leaf (actualTree N)) {X Y : (D).Cauchy}
    (h : (D).Close X Y) (epsilon : Q') : Nat := h.modulus (coefficientTolerance w hw0 N l epsilon)

theorem coefficientSequence_close (N : Nat) (l : Leaf (actualTree N)) {X Y : (D).Cauchy}
    (h : (D).Close X Y) (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : coefficientCloseRate w hw0 hw1 N l h epsilon ≤ n) :
    leRat (CReal.sub (coefficientSequence w hw0 hw1 N l X n) (coefficientSequence w hw0 hw1 N l Y n)) epsilon ∧
    leRat (CReal.sub (coefficientSequence w hw0 hw1 N l Y n) (coefficientSequence w hw0 hw1 N l X n)) epsilon :=
  coefficient_close w hw0 hw1 N l (X.seq n) (Y.seq n) epsilon he
    (h.close _ (coefficientTolerance_positive w hw0 N l he) n hn)

theorem representativeCoefficient_welldef (N : Nat) (l : Leaf (actualTree N)) {X Y : (D).Cauchy}
    (h : (D).Close X Y) :
    Equiv (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l Y) := by
  apply Equiv_of_limit_of_close (coefficientSequence_converges w hw0 hw1 N l X)
    (coefficientSequence_converges w hw0 hw1 N l Y)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨coefficientCloseRate w hw0 hw1 N l h (HalfPow.half * epsilon), fun n hn => ?_⟩
  have hs := coefficientSequence_close w hw0 hw1 N l h (HalfPow.half * epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat hs.1 hs.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Extension on the existing physical completion, by well-defined quotient elimination. -/
def completedCoefficient (N : Nat) (l : Leaf (actualTree N)) : Completion w hw0 hw1 half → RC :=
  Quotient.lift (fun X => Quotient.mk crealSetoid (representativeCoefficient w hw0 hw1 N l X))
    (fun _ _ h => by
      rcases h with ⟨h⟩
      exact Quotient.sound (representativeCoefficient_welldef w hw0 hw1 N l h))

theorem completedCoefficient_mk (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    completedCoefficient w hw0 hw1 N l (Quotient.mk (D).completionSetoid X) =
      Quotient.mk crealSetoid (representativeCoefficient w hw0 hw1 N l X) := rfl

theorem representativeCoefficient_constant (N : Nat) (l : Leaf (actualTree N)) (e : PlaquetteExpression half) :
    Equiv (representativeCoefficient w hw0 hw1 N l ((D).constant e)) (coefficient w hw0 hw1 N l e) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (coefficient w hw0 hw1 N l e))
    (coefficientSequence_converges w hw0 hw1 N l ((D).constant e)) (convergesTo_const _)

theorem completedCoefficient_embedExpression (N : Nat) (l : Leaf (actualTree N)) (e : PlaquetteExpression half) :
    completedCoefficient w hw0 hw1 N l (embedExpression w hw0 hw1 e) =
      Quotient.mk crealSetoid (coefficient w hw0 hw1 N l e) :=
  Quotient.sound (representativeCoefficient_constant w hw0 hw1 N l e)

theorem completedCoefficient_embedQuotient (N : Nat) (l : Leaf (actualTree N)) (x : Carrier w hw0 hw1 half) :
    completedCoefficient w hw0 hw1 N l (embedQuotient w hw0 hw1 x) = quotientCoefficient w hw0 hw1 N l x := by
  refine Quotient.inductionOn x ?_
  exact completedCoefficient_embedExpression w hw0 hw1 N l

theorem representativeCoefficient_add (N : Nat) (l : Leaf (actualTree N)) (X Y : (D).Cauchy) :
    Equiv (representativeCoefficient w hw0 hw1 N l ((addition w hw0 hw1).mapCauchy X Y))
      (CReal.add (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l Y)) :=
  Equiv_of_limit_of_equal (fun n => coefficient_add w hw0 hw1 N l (X.seq n) (Y.seq n))
    (coefficientSequence_converges w hw0 hw1 N l ((addition w hw0 hw1).mapCauchy X Y))
    (TrigAddCReal.convergesTo_add (coefficientSequence_converges w hw0 hw1 N l X)
      (coefficientSequence_converges w hw0 hw1 N l Y))

theorem representativeCoefficient_smul (N : Nat) (l : Leaf (actualTree N)) (c : Q') (X : (D).Cauchy) :
    Equiv (representativeCoefficient w hw0 hw1 N l ((scalarContinuous w hw0 hw1 c).mapCauchy X))
      (CReal.mul (ofQ' c) (representativeCoefficient w hw0 hw1 N l X)) :=
  Equiv_of_limit_of_equal (fun n => coefficient_smul w hw0 hw1 N l c (X.seq n))
    (coefficientSequence_converges w hw0 hw1 N l ((scalarContinuous w hw0 hw1 c).mapCauchy X))
    (convergesTo_const_mul (ofQ' c) (coefficientSequence_converges w hw0 hw1 N l X))

theorem completedCoefficient_add (N : Nat) (l : Leaf (actualTree N)) (x y : Completion w hw0 hw1 half) :
    completedCoefficient w hw0 hw1 N l (completedAdd w hw0 hw1 x y) =
      RCadd (completedCoefficient w hw0 hw1 N l x) (completedCoefficient w hw0 hw1 N l y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeCoefficient_add w hw0 hw1 N l X Y)

theorem completedCoefficient_smul (N : Nat) (l : Leaf (actualTree N)) (c : Q') (x : Completion w hw0 hw1 half) :
    completedCoefficient w hw0 hw1 N l (completedSmul w hw0 hw1 c x) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedCoefficient w hw0 hw1 N l x) := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (representativeCoefficient_smul w hw0 hw1 N l c X)

theorem completedCoefficient_zero (N : Nat) (l : Leaf (actualTree N)) :
    completedCoefficient w hw0 hw1 N l (completedZero w hw0 hw1 half) = RCzero :=
  (completedCoefficient_embedExpression w hw0 hw1 N l (zeroExpression half)).trans
    (Quotient.sound (coefficient_zero w hw0 hw1 N l))

theorem representativeCoefficient_norm_bound (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy) :
    leEv (CReal.mul (ofQ' (intrinsicNormFloor w hw0 N l))
      (CReal.mul (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l X)))
      (representativeInner w hw0 hw1 X X) :=
  leEv_of_convergesTo_le
    (convergesTo_const_mul (ofQ' (intrinsicNormFloor w hw0 N l))
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (coefficientSequence_converges w hw0 hw1 N l X) (coefficientSequence_converges w hw0 hw1 N l X)))
    (pairSequence_converges w hw0 hw1 X X)
    (fun n => intrinsic_normalized_energy_bound w hw0 hw1 (X.seq n) N l)

/-- The same explicit F controls every state of the ORIGINAL completion. -/
theorem completedCoefficient_norm_bound (N : Nat) (l : Leaf (actualTree N)) (x : Completion w hw0 hw1 half) :
    RCle (RCmul (Quotient.mk crealSetoid (ofQ' (intrinsicNormFloor w hw0 N l)))
      (RCmul (completedCoefficient w hw0 hw1 N l x) (completedCoefficient w hw0 hw1 N l x)))
      (completedInner w hw0 hw1 x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeCoefficient_norm_bound w hw0 hw1 N l

theorem representativeCoefficient_difference_bound (N : Nat) (l : Leaf (actualTree N)) (X Y : (D).Cauchy) :
    leEv (CReal.mul (ofQ' (intrinsicNormFloor w hw0 N l))
      (CReal.mul (CReal.sub (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l Y))
        (CReal.sub (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l Y))))
      (representativeDist w hw0 hw1 X Y) := by
  have hs := TrigAddCReal.convergesTo_add (coefficientSequence_converges w hw0 hw1 N l X)
    (TrigAddCReal.convergesTo_neg (coefficientSequence_converges w hw0 hw1 N l Y))
  exact leEv_of_convergesTo_le (convergesTo_const_mul (ofQ' (intrinsicNormFloor w hw0 N l))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hs hs))
    (representativeDist_converges w hw0 hw1 X Y)
    (fun n => coefficient_difference_bound w hw0 hw1 N l (X.seq n) (Y.seq n))

/-- The SAME squared-distance tolerance works for all original completed states. -/
theorem completedCoefficient_close (N : Nat) (l : Leaf (actualTree N)) (x y : Completion w hw0 hw1 half)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (h : RCle (completedDist w hw0 hw1 x y) (Quotient.mk crealSetoid (ofQ' (coefficientTolerance w hw0 N l epsilon)))) :
    RCle (RCsub (completedCoefficient w hw0 hw1 N l x) (completedCoefficient w hw0 hw1 N l y))
      (Quotient.mk crealSetoid (ofQ' epsilon)) ∧
    RCle (RCsub (completedCoefficient w hw0 hw1 N l y) (completedCoefficient w hw0 hw1 N l x))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  have hs := weighted_square_small _ (intrinsicNormFloor_positive w hw0 N l) _ epsilon he
    (leEv_trans (representativeCoefficient_difference_bound w hw0 hw1 N l X Y) h)
  exact ⟨hs.1, leRat_of_equiv
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))) hs.2⟩

/-- Requested coefficient accuracy gives a concrete original-state approximant. -/
def coefficientApproximationIndex (N : Nat) (l : Leaf (actualTree N)) (epsilon : Q') : Nat :=
  (coefficientTolerance w hw0 N l epsilon).den

theorem completedCoefficient_approximant (N : Nat) (l : Leaf (actualTree N)) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : coefficientApproximationIndex w hw0 N l epsilon ≤ n) :
    RCle (RCsub (Quotient.mk crealSetoid (coefficient w hw0 hw1 N l (approximant w hw0 hw1 X n)))
      (completedCoefficient w hw0 hw1 N l (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) ∧
    RCle (RCsub (completedCoefficient w hw0 hw1 N l (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (coefficient w hw0 hw1 N l (approximant w hw0 hw1 X n))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hd : RCle (completedDist w hw0 hw1 (embedExpression w hw0 hw1 (approximant w hw0 hw1 X n))
      (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (coefficientTolerance w hw0 N l epsilon))) :=
    RCle_trans (approximant_bound w hw0 hw1 X n)
      (leEv_le_ofQ'_of_approx_le (fun _ => invSucc_le_of_den (coefficientTolerance_positive w hw0 N l he) hn))
  have hc := completedCoefficient_close w hw0 hw1 N l _ _ epsilon he hd
  rw [completedCoefficient_embedExpression] at hc
  exact hc

end YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion

#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientRawRate
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientRate
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientReg
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficientCauchy
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientCloseRate
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_welldef
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_mk
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_constant
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_embedQuotient
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_add
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_smul
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_add
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_smul
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_zero
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.representativeCoefficient_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_close
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.coefficientApproximationIndex
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion.completedCoefficient_approximant
