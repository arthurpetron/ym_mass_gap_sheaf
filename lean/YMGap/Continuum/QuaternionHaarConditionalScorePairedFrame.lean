/-
# Exact paired three-square energy of the ORIGINAL coupled score

The score A*Dij b-b*Dij A is a decomposable four-coordinate bivector.
Its Plucker relation cancels the cross terms in BOTH paired triples, so
their three square sums equal the existing six-plane square sum exactly.
Arbitrary A, b and output multipliers are retained; no sphere relation,
positivity, reciprocal, or normalization hypothesis is needed.

Consumer: the ORIGINAL exactScoreAngularBudget, with its literal output
weight, can be rewritten using either paired triple. This file proves only
coefficient identities. It does not identify geodesic quaternion frames,
covariant Hessians, a Harnack estimate, an OS norm, or an interacting gap.
-/

import YMGap.Continuum.QuaternionHaarConditionalScoreGradient
import YMGap.Continuum.QuaternionHaarLinearAngularEnergy

namespace YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)

/-- A literal decomposable bivector; only four coordinates are used below. -/
def wedgeEntry (x F : Nat → RatPoly) (i j : Nat) : RatPoly :=
  polyAdd (polyMul (x i) (F j)) (polyNeg (polyMul (x j) (F i)))

/-- The signed four-coordinate Plucker combination. -/
def plucker (S : Nat → Nat → RatPoly) : RatPoly :=
  polyAdd (polyMul (S 0 1) (S 2 3))
    (polyAdd (polyNeg (polyMul (S 0 2) (S 1 3)))
      (polyMul (S 0 3) (S 1 2)))

private def wedgeExpr (i j : Nat) : PolyExpr :=
  .add (.mul (.var i) (.var (4+j)))
    (.neg (.mul (.var j) (.var (4+i))))

private def wedgeEnvironment (x F : Nat → RatPoly) : Nat → RatPoly
  | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3
  | 4 => F 0 | 5 => F 1 | 6 => F 2 | _ => F 3

/-- Exact Plucker cancellation, without a unit-radius premise. -/
theorem decomposable_plucker (x F : Nat → RatPoly) :
    RatPolyCoeffEqv (plucker (wedgeEntry x F)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (wedgeExpr 0 1) (wedgeExpr 2 3))
      (.add (.neg (.mul (wedgeExpr 0 2) (wedgeExpr 1 3)))
        (.mul (wedgeExpr 0 3) (wedgeExpr 1 2))))
    (.const 0) (by decide) (wedgeEnvironment x F)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)

/-- The vacuum-subtracted ordinary coordinate first jet, not a quotient. -/
def scoreFirstJet (i : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (polyMul A (ratDerivative i b))
    (polyNeg (polyMul b (ratDerivative i A)))

/-- The actual angular conditional score is the coordinate wedge of its
actual first jet. No differentiation of an auxiliary coefficient occurs. -/
theorem conditionalScore_firstJet_pin (i j : Nat) (A b : RatPoly) :
    RatPolyCoeffEqv (conditionalScore i j A b)
      (polyAdd (polyMul (polyVar i) (scoreFirstJet j A b))
        (polyNeg (polyMul (polyVar j) (scoreFirstJet i A b)))) := by
  have hd (p : RatPoly) : RatPolyCoeffEqv (angularDerivative i j p)
      (polyAdd (polyMul (polyVar i) (ratDerivative j p))
        (polyNeg (polyMul (polyVar j) (ratDerivative i p)))) :=
    (RatPolyCoeffEqv.refl _).add (neg_smul _).symm
  refine (((RatPolyCoeffEqv.refl A).mul (hd b)).add
    (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl b).mul (hd A)))).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.var 2) (.add (.mul (.var 0) (.var 4))
        (.neg (.mul (.var 1) (.var 5)))))
      (.neg (.mul (.var 3) (.add (.mul (.var 0) (.var 6))
        (.neg (.mul (.var 1) (.var 7)))))))
    (.add
      (.mul (.var 0) (.add (.mul (.var 2) (.var 4))
        (.neg (.mul (.var 3) (.var 6)))))
      (.neg (.mul (.var 1) (.add (.mul (.var 2) (.var 5))
        (.neg (.mul (.var 3) (.var 7)))))))
    (by decide) (fun
      | 0 => polyVar i | 1 => polyVar j | 2 => A | 3 => b
      | 4 => ratDerivative j b | 5 => ratDerivative i b
      | 6 => ratDerivative j A | _ => ratDerivative i A)

private theorem plucker_congr (S T : Nat → Nat → RatPoly)
    (h : ∀ i j, RatPolyCoeffEqv (S i j) (T i j)) :
    RatPolyCoeffEqv (plucker S) (plucker T) :=
  ((h 0 1).mul (h 2 3)).add
    ((RatPolyCoeffEqv.neg ((h 0 2).mul (h 1 3))).add ((h 0 3).mul (h 1 2)))

/-- Plucker cancellation for the actual score on ANY original output block. -/
theorem conditionalScore_plucker (s : Nat) (A b : RatPoly) :
    RatPolyCoeffEqv
      (plucker (fun i j => conditionalScore (4*s+i) (4*s+j) A b)) polyZero :=
  (plucker_congr _ _ (fun i j =>
    conditionalScore_firstJet_pin (4*s+i) (4*s+j) A b)).trans
      (decomposable_plucker (fun i => polyVar (4*s+i))
        (fun i => scoreFirstJet (4*s+i) A b))

private def pairedPlus (S : Nat → Nat → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (S 0 1) (S 2 3)
  | 1 => polyAdd (S 0 2) (polyNeg (S 1 3))
  | _ => polyAdd (S 0 3) (S 1 2)

private def pairedMinus (S : Nat → Nat → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (S 0 1) (polyNeg (S 2 3))
  | 1 => polyAdd (S 0 2) (S 1 3)
  | _ => polyAdd (S 0 3) (polyNeg (S 1 2))

/-- Literal three-square sum in the same polynomial ring. -/
def threeSquare (f : Fin 3 → RatPoly) : RatPoly :=
  polyAdd (polyMul (f 0) (f 0))
    (polyAdd (polyMul (f 1) (f 1)) (polyMul (f 2) (f 2)))

/-- The (+,-,+) complementary-plane triple of ORIGINAL coupled scores. -/
def pairedScorePlus (s : Nat) (A b : RatPoly) : Fin 3 → RatPoly :=
  pairedPlus (fun i j => conditionalScore (4*s+i) (4*s+j) A b)

/-- The opposite complementary-plane triple of ORIGINAL coupled scores. -/
def pairedScoreMinus (s : Nat) (A b : RatPoly) : Fin 3 → RatPoly :=
  pairedMinus (fun i j => conditionalScore (4*s+i) (4*s+j) A b)

private theorem sixSquare_congr (S T : Nat → Nat → RatPoly)
    (h : ∀ i j, RatPolyCoeffEqv (S i j) (T i j)) :
    RatPolyCoeffEqv (six (fun i j => polyMul (S i j) (S i j)))
      (six (fun i j => polyMul (T i j) (T i j))) :=
  ((h 0 1).mul (h 0 1)).add (((h 0 2).mul (h 0 2)).add
    (((h 0 3).mul (h 0 3)).add (((h 1 2).mul (h 1 2)).add
      (((h 1 3).mul (h 1 3)).add ((h 2 3).mul (h 2 3))))))

private def squareExpr (e : PolyExpr) : PolyExpr := .mul e e

private def pairedPlusExpr : PolyExpr :=
  .add
    (squareExpr (.add (wedgeExpr 0 1) (wedgeExpr 2 3)))
    (.add (squareExpr (.add (wedgeExpr 0 2) (.neg (wedgeExpr 1 3))))
      (squareExpr (.add (wedgeExpr 0 3) (wedgeExpr 1 2))))

private def pairedMinusExpr : PolyExpr :=
  .add
    (squareExpr (.add (wedgeExpr 0 1) (.neg (wedgeExpr 2 3))))
    (.add (squareExpr (.add (wedgeExpr 0 2) (wedgeExpr 1 3)))
      (squareExpr (.add (wedgeExpr 0 3) (.neg (wedgeExpr 1 2)))))

private def sixSquareExpr : PolyExpr :=
  .add (squareExpr (wedgeExpr 0 1)) (.add (squareExpr (wedgeExpr 0 2))
    (.add (squareExpr (wedgeExpr 0 3)) (.add (squareExpr (wedgeExpr 1 2))
      (.add (squareExpr (wedgeExpr 1 3)) (squareExpr (wedgeExpr 2 3))))))

private theorem decomposable_plusSquare (x F : Nat → RatPoly) :
    RatPolyCoeffEqv (threeSquare (pairedPlus (wedgeEntry x F)))
      (six (fun i j => polyMul (wedgeEntry x F i j) (wedgeEntry x F i j))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq pairedPlusExpr sixSquareExpr
    (by decide) (wedgeEnvironment x F)

private theorem decomposable_minusSquare (x F : Nat → RatPoly) :
    RatPolyCoeffEqv (threeSquare (pairedMinus (wedgeEntry x F)))
      (six (fun i j => polyMul (wedgeEntry x F i j) (wedgeEntry x F i j))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq pairedMinusExpr sixSquareExpr
    (by decide) (wedgeEnvironment x F)

private theorem plusSquare_congr (S T : Nat → Nat → RatPoly)
    (h : ∀ i j, RatPolyCoeffEqv (S i j) (T i j)) :
    RatPolyCoeffEqv (threeSquare (pairedPlus S)) (threeSquare (pairedPlus T)) := by
  have h0 := (h 0 1).add (h 2 3)
  have h1 := (h 0 2).add (RatPolyCoeffEqv.neg (h 1 3))
  have h2 := (h 0 3).add (h 1 2)
  exact (h0.mul h0).add ((h1.mul h1).add (h2.mul h2))

private theorem minusSquare_congr (S T : Nat → Nat → RatPoly)
    (h : ∀ i j, RatPolyCoeffEqv (S i j) (T i j)) :
    RatPolyCoeffEqv (threeSquare (pairedMinus S)) (threeSquare (pairedMinus T)) := by
  have h0 := (h 0 1).add (RatPolyCoeffEqv.neg (h 2 3))
  have h1 := (h 0 2).add (h 1 3)
  have h2 := (h 0 3).add (RatPolyCoeffEqv.neg (h 1 2))
  exact (h0.mul h0).add ((h1.mul h1).add (h2.mul h2))

/-- Exact plus-triple energy: no factor two and no radius normalization. -/
theorem plusSquare_eq_sixScoreSquare (s : Nat) (A b : RatPoly) :
    RatPolyCoeffEqv (threeSquare (pairedScorePlus s A b))
      (six (fun i j => polyMul (conditionalScore (4*s+i) (4*s+j) A b)
        (conditionalScore (4*s+i) (4*s+j) A b))) := by
  let S := fun i j => conditionalScore (4*s+i) (4*s+j) A b
  let T := wedgeEntry (fun i => polyVar (4*s+i)) (fun i => scoreFirstJet (4*s+i) A b)
  have h (i j : Nat) : RatPolyCoeffEqv (S i j) (T i j) :=
    conditionalScore_firstJet_pin (4*s+i) (4*s+j) A b
  exact (plusSquare_congr S T h).trans
    ((decomposable_plusSquare _ _).trans (sixSquare_congr S T h).symm)

/-- Exact opposite-triple energy, with the same six original scores. -/
theorem minusSquare_eq_sixScoreSquare (s : Nat) (A b : RatPoly) :
    RatPolyCoeffEqv (threeSquare (pairedScoreMinus s A b))
      (six (fun i j => polyMul (conditionalScore (4*s+i) (4*s+j) A b)
        (conditionalScore (4*s+i) (4*s+j) A b))) := by
  let S := fun i j => conditionalScore (4*s+i) (4*s+j) A b
  let T := wedgeEntry (fun i => polyVar (4*s+i)) (fun i => scoreFirstJet (4*s+i) A b)
  have h (i j : Nat) : RatPolyCoeffEqv (S i j) (T i j) :=
    conditionalScore_firstJet_pin (4*s+i) (4*s+j) A b
  exact (minusSquare_congr S T h).trans
    ((decomposable_minusSquare _ _).trans (sixSquare_congr S T h).symm)

/-- Preserve any literal ORIGINAL output multiplier, without a sign premise. -/
theorem plusSquare_weighted_pin (s : Nat) (A b W : RatPoly) :
    RatPolyCoeffEqv (polyMul W (threeSquare (pairedScorePlus s A b)))
      (polyMul W (six (fun i j => polyMul (conditionalScore (4*s+i) (4*s+j) A b)
        (conditionalScore (4*s+i) (4*s+j) A b)))) :=
  (plusSquare_eq_sixScoreSquare s A b).mul_left W

theorem minusSquare_weighted_pin (s : Nat) (A b W : RatPoly) :
    RatPolyCoeffEqv (polyMul W (threeSquare (pairedScoreMinus s A b)))
      (polyMul W (six (fun i j => polyMul (conditionalScore (4*s+i) (4*s+j) A b)
        (conditionalScore (4*s+i) (4*s+j) A b)))) :=
  (minusSquare_eq_sixScoreSquare s A b).mul_left W

end YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame

#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.decomposable_plucker
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.conditionalScore_firstJet_pin
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.conditionalScore_plucker
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.plusSquare_eq_sixScoreSquare
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.minusSquare_eq_sixScoreSquare
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.plusSquare_weighted_pin
#print axioms YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame.minusSquare_weighted_pin
