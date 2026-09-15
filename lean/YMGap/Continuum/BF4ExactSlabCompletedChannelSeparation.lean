/-
# The original channel coefficients separate the original completed states

If every completed coefficient of x vanishes, each fixed packet of a
dense e is the limit of that same packet on e-X_n. Whole-packet domination
therefore bounds it by the ORIGINAL completed distance from e to x.
Dense packet reconstruction gives norm(e)^2 <= dist(e,x)^2. The explicit
physical Cauchy modulus then makes the dense approximants' norms tend to
zero. Positive definiteness of the existing completed pairing gives x=0.

All limits and moduli used here are the existing original ones; no new
limit is manufactured from erased convergence witnesses. This is finite-
volume channel separation, not a transfer-kernel theorem, range density,
full-space time-zero continuity, physical gap or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabWholePacketNormBound

namespace YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion
open YMGap.Continuum.BF4ExactSlabWholePacketNormBound
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

private theorem half_chain (a b c epsilon : Q')
    (h : a ≤ b + HalfPow.half * epsilon) (h' : b ≤ c + HalfPow.half * epsilon) : a ≤ c + epsilon :=
  Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h')
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)))))

private theorem convergence_equiv {s : Nat → CReal} {A B : CReal}
    (hs : ConvergesTo s A) (hAB : Equiv A B) : ConvergesTo s B := by
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  obtain ⟨N, hN⟩ := hs (HalfPow.half * epsilon) hh
  obtain ⟨K, hK⟩ := hAB (HalfPow.half * epsilon) hh
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL⟩ := hN n hn
  refine ⟨max K L, fun k hk => ?_⟩
  have hkK := Nat.le_trans (Nat.le_max_left K L) hk
  have hkL := Nat.le_trans (Nat.le_max_right K L) hk
  exact ⟨half_chain _ _ _ epsilon (hL k hkL).1 (hK k hkK).1,
    half_chain _ _ _ epsilon (hK k hkK).2 (hL k hkL).2⟩

private theorem limit_upper_tail {s : Nat → CReal} {A : CReal}
    (hs : ConvergesTo s A) (b : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (s n) (ofQ' b)) : leEv A (ofQ' b) := by
  have ht : ConvergesTo (fun n => s (max n base)) A := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hs epsilon he
    exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le ht (convergesTo_const (ofQ' b)) (fun n => h (max n base) (Nat.le_max_right _ _))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)

/-- Finite algebra of the existing limits. Every actual tree leaf, including
multiplicity, supplies its convergence; no independent link variables are assumed. -/
theorem energyLimit_converges_of_leaves (p : Nat → RatPoly) (q : RatPoly) : (t : SquareTree) →
    (∀ l : Leaf t, ConvergesTo (fun n => coefficientLimit w hw0 hw1 half (polyMul (p n) l.channel))
      (coefficientLimit w hw0 hw1 half (polyMul q l.channel))) →
    ConvergesTo (fun n => energyLimit w hw0 hw1 half (p n) t) (energyLimit w hw0 hw1 half q t)
  | .zero, _ => convergesTo_const (ofQ' 0)
  | .term v r, h => convergesTo_const_mul (ofQ' v)
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (h (.here v r)) (h (.here v r)))
  | .add s t, h => TrigAddCReal.convergesTo_add
      (energyLimit_converges_of_leaves p q s (fun l => h (.left l)))
      (energyLimit_converges_of_leaves p q t (fun l => h (.right l)))

theorem residualCoefficient_converges (N : Nat) (l : Leaf (actualTree N))
    (e : PlaquetteExpression half) (X : (D).Cauchy)
    (hz : Equiv (representativeCoefficient w hw0 hw1 N l X) czero) :
    ConvergesTo (fun n => coefficient w hw0 hw1 N l (subtract e (X.seq n))) (coefficient w hw0 hw1 N l e) := by
  have hs := TrigAddCReal.convergesTo_add (convergesTo_const (coefficient w hw0 hw1 N l e))
    (TrigAddCReal.convergesTo_neg (coefficientSequence_converges w hw0 hw1 N l X))
  apply convergence_equiv (TrigAddCReal.convergesTo_congr_seq
    (fun n => (coefficient_sub w hw0 hw1 N l e (X.seq n)).symm) hs)
  exact (CReal.sub_congr_right hz).trans (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv ((coefficient w hw0 hw1 N l e).approx n))))

theorem densePacket_bound_of_zero_coefficients (e : PlaquetteExpression half) (X : (D).Cauchy) (N : Nat)
    (hz : ∀ l : Leaf (actualTree N), Equiv (representativeCoefficient w hw0 hw1 N l X) czero) :
    leEv (normalizedPacket w hw0 hw1 e N) (representativeDist w hw0 hw1 ((D).constant e) X) :=
  leEv_of_convergesTo_le
    (convergesTo_const_mul (actionReciprocal w hw0 hw1 half)
      (energyLimit_converges_of_leaves w hw0 hw1 (fun n => lower (subtract e (X.seq n))) (lower e)
        (actualTree N) (fun l => residualCoefficient_converges w hw0 hw1 N l e X (hz l))))
    (representativeDist_converges w hw0 hw1 ((D).constant e) X)
    (fun n => normalizedPacket_norm_bound w hw0 hw1 (subtract e (X.seq n)) N)

/-- The estimate is for every dense e against the SAME completed state x. -/
theorem denseNorm_bound_of_zero_coefficients (e : PlaquetteExpression half) (X : (D).Cauchy)
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N), Equiv (representativeCoefficient w hw0 hw1 N l X) czero) :
    leEv (form w hw0 hw1 e e) (representativeDist w hw0 hw1 ((D).constant e) X) :=
  normalizedPacket_reconstruction_bound w hw0 hw1 e _
    (fun N => densePacket_bound_of_zero_coefficients w hw0 hw1 e X N (hz N))

theorem representativeInner_zero_of_coefficients_zero (X : (D).Cauchy)
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N), Equiv (representativeCoefficient w hw0 hw1 N l X) czero) :
    Equiv (representativeInner w hw0 hw1 X X) czero := by
  apply equiv_of_leEv_leEv ?_ (representativeInner_nonnegative w hw0 hw1 X)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  have hb : leEv (representativeInner w hw0 hw1 X X) (ofQ' (HalfPow.half * epsilon)) :=
    limit_upper_tail (pairSequence_converges w hw0 hw1 X X) _ (X.modulus (HalfPow.half * epsilon))
      (fun n hn => leEv_trans (denseNorm_bound_of_zero_coefficients w hw0 hw1 (X.seq n) X hz)
        (constantApproximation_bound w hw0 hw1 X _ hh n hn))
  obtain ⟨M, hM⟩ := hb (HalfPow.half * epsilon) hh
  refine ⟨M, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (hM n hn) (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
    (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

theorem completed_zero_of_coefficients_zero (x : Completion w hw0 hw1 half)
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N), completedCoefficient w hw0 hw1 N l x = RCzero) :
    x = completedZero w hw0 hw1 half := by
  apply (completedInner_posdef w hw0 hw1 x).mp
  revert hz
  refine Quotient.inductionOn x ?_
  intro X hz
  exact Quotient.sound (representativeInner_zero_of_coefficients_zero w hw0 hw1 X
    (fun N l => Quotient.exact (hz N l)))

theorem completed_zero_iff_coefficients_zero (x : Completion w hw0 hw1 half) :
    x = completedZero w hw0 hw1 half ↔
      ∀ N : Nat, ∀ l : Leaf (actualTree N), completedCoefficient w hw0 hw1 N l x = RCzero :=
  ⟨fun hx N l => by rw [hx, completedCoefficient_zero], completed_zero_of_coefficients_zero w hw0 hw1 x⟩

theorem representativeCoefficient_sub (N : Nat) (l : Leaf (actualTree N)) (X Y : (D).Cauchy) :
    Equiv (representativeCoefficient w hw0 hw1 N l (differenceCauchy w hw0 hw1 X Y))
      (CReal.sub (representativeCoefficient w hw0 hw1 N l X) (representativeCoefficient w hw0 hw1 N l Y)) :=
  Equiv_of_limit_of_equal (fun n => coefficient_sub w hw0 hw1 N l (X.seq n) (Y.seq n))
    (coefficientSequence_converges w hw0 hw1 N l (differenceCauchy w hw0 hw1 X Y))
    (TrigAddCReal.convergesTo_add (coefficientSequence_converges w hw0 hw1 N l X)
      (TrigAddCReal.convergesTo_neg (coefficientSequence_converges w hw0 hw1 N l Y)))

theorem completedCoefficient_sub (N : Nat) (l : Leaf (actualTree N)) (x y : Completion w hw0 hw1 half) :
    completedCoefficient w hw0 hw1 N l (completedSub w hw0 hw1 x y) =
      RCsub (completedCoefficient w hw0 hw1 N l x) (completedCoefficient w hw0 hw1 N l y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeCoefficient_sub w hw0 hw1 N l X Y)

/-- Joint injectivity of the ORIGINAL completed coefficient family. -/
theorem completedCoefficients_injective (x y : Completion w hw0 hw1 half)
    (h : ∀ N : Nat, ∀ l : Leaf (actualTree N),
      completedCoefficient w hw0 hw1 N l x = completedCoefficient w hw0 hw1 N l y) : x = y := by
  have hz := completed_zero_of_coefficients_zero w hw0 hw1 (completedSub w hw0 hw1 x y)
    (fun N l => by rw [completedCoefficient_sub, h N l]; exact rc_sub_self _)
  have he := congrArg (fun z => completedAdd w hw0 hw1 z y) hz
  change completedAdd w hw0 hw1 (completedSub w hw0 hw1 x y) y =
    completedAdd w hw0 hw1 (completedZero w hw0 hw1 half) y at he
  rw [completedSub_add_cancel, completedZero_add] at he
  exact he

theorem completed_eq_iff_coefficients_eq (x y : Completion w hw0 hw1 half) :
    x = y ↔ ∀ N : Nat, ∀ l : Leaf (actualTree N),
      completedCoefficient w hw0 hw1 N l x = completedCoefficient w hw0 hw1 N l y :=
  ⟨fun h N l => congrArg (completedCoefficient w hw0 hw1 N l) h,
    completedCoefficients_injective w hw0 hw1 x y⟩

end YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation

#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.energyLimit_converges_of_leaves
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.residualCoefficient_converges
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.densePacket_bound_of_zero_coefficients
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.denseNorm_bound_of_zero_coefficients
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.representativeInner_zero_of_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.completed_zero_of_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.completed_zero_iff_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.representativeCoefficient_sub
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.completedCoefficient_sub
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.completedCoefficients_injective
#print axioms YMGap.Continuum.BF4ExactSlabCompletedChannelSeparation.completed_eq_iff_coefficients_eq
