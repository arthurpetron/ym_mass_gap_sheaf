/-
# Finite polynomial translations by actual completed quaternion Points

Finite RC evaluation uses the existing quotient coordinates, without choosing
real representatives. Exact head Haar leaves a rational tail polynomial; its
evaluation at any actual Point equals the ORIGINAL one-block Haar moment.
The unintegrated polynomial is separately pinned to completedMul, in both
Hamilton orders. All degrees and both central signs are retained.

This is a finite polynomial moment statement. It does not construct Haar on
arbitrary continuous Point-functions, compactness, or a physical gap.
-/

import YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation
import YMGap.RepTheory.RationalQuaternionCompletedMatrix

namespace YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation

local infix:50 " ≈ " => Q'.eqv

def rational (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

def rcPower (x : RC) : Nat → RC
  | 0 => rational 1
  | n+1 => RCmul (rcPower x n) x

def rcMonomialFrom (rho : Nat → RC) : Nat → List Nat → RC
  | _, [] => rational 1
  | i, e::m => RCmul (rcPower (rho i) e) (rcMonomialFrom rho (i+1) m)

/-- Finite multivariate evaluation; no representatives of the RC inputs. -/
def evalRC (rho : Nat → RC) : RatPoly → RC
  | [] => rational 0
  | t::p => RCadd (RCmul (rational t.2) (rcMonomialFrom rho 0 t.1)) (evalRC rho p)

private def realPower (x : CReal) : Nat → CReal
  | 0 => ofQ' 1
  | n+1 => CReal.mul (realPower x n) x

private def realMonomialFrom (rho : Nat → CReal) : Nat → List Nat → CReal
  | _, [] => ofQ' 1
  | i, e::m => CReal.mul (realPower (rho i) e) (realMonomialFrom rho (i+1) m)

private def evalReal (rho : Nat → CReal) : RatPoly → CReal
  | [] => ofQ' 0
  | t::p => CReal.add (CReal.mul (ofQ' t.2) (realMonomialFrom rho 0 t.1)) (evalReal rho p)

private theorem realPower_approx (x : CReal) (n : Nat) : ∀ e,
    (realPower x e).approx n = qpow (x.approx n) e
  | 0 => rfl
  | e+1 => congrArg (fun z => z*x.approx n) (realPower_approx x n e)

private theorem realMonomial_approx (rho : Nat → CReal) (n : Nat) : ∀ i m,
    (realMonomialFrom rho i m).approx n = evalMonoFrom (fun j => (rho j).approx n) i m
  | _, [] => rfl
  | i, e::m => by
      change (realPower (rho i) e).approx n * (realMonomialFrom rho (i+1) m).approx n = _
      rw [realPower_approx, realMonomial_approx rho n (i+1) m]
      rfl

private theorem evalReal_approx (rho : Nat → CReal) (n : Nat) : ∀ p,
    (evalReal rho p).approx n = evalRatPoly (fun j => (rho j).approx n) p
  | [] => rfl
  | t::p => by
      change t.2*(realMonomialFrom rho 0 t.1).approx n+(evalReal rho p).approx n = _
      rw [realMonomial_approx, evalReal_approx rho n p]
      rfl

private theorem rcPower_mk (x : CReal) : ∀ e,
    rcPower (Quotient.mk crealSetoid x) e = Quotient.mk crealSetoid (realPower x e)
  | 0 => rfl
  | e+1 => by
      change RCmul (rcPower (Quotient.mk crealSetoid x) e) (Quotient.mk crealSetoid x) = _
      rw [rcPower_mk x e]
      rfl

private theorem rcMonomial_mk (rho : Nat → CReal) : ∀ i m,
    rcMonomialFrom (fun j => Quotient.mk crealSetoid (rho j)) i m =
      Quotient.mk crealSetoid (realMonomialFrom rho i m)
  | _, [] => rfl
  | i, e::m => by
      change RCmul (rcPower (Quotient.mk crealSetoid (rho i)) e)
        (rcMonomialFrom (fun j => Quotient.mk crealSetoid (rho j)) (i+1) m) = _
      rw [rcPower_mk, rcMonomial_mk rho (i+1) m]
      rfl

private theorem evalRC_mk (rho : Nat → CReal) : ∀ p,
    evalRC (fun j => Quotient.mk crealSetoid (rho j)) p = Quotient.mk crealSetoid (evalReal rho p)
  | [] => rfl
  | t::p => by
      change RCadd (RCmul (rational t.2)
        (rcMonomialFrom (fun j => Quotient.mk crealSetoid (rho j)) 0 t.1))
        (evalRC (fun j => Quotient.mk crealSetoid (rho j)) p) = _
      rw [rcMonomial_mk, evalRC_mk rho p]
      rfl

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem rational_eval_congr (rho : Nat → Q') {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

/-- Coefficient equality transports through SUPPLIED real rows, with no choice. -/
theorem evalRC_coeffEqv_supplied (rho : Nat → CReal) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    evalRC (fun j => Quotient.mk crealSetoid (rho j)) p =
      evalRC (fun j => Quotient.mk crealSetoid (rho j)) q := by
  rw [evalRC_mk, evalRC_mk]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  rw [evalReal_approx, evalReal_approx]
  exact rational_eval_congr _ h

def pointEnvironment (x : Point) : Nat → RC
  | 0 => pointCoordinate 0 x
  | 1 => pointCoordinate 1 x
  | 2 => pointCoordinate 2 x
  | 3 => pointCoordinate 3 x
  | _ => rational 0

private def rowEnvironment (X : CauchyPoint) : Nat → CReal
  | 0 => rowCoordinate X 0
  | 1 => rowCoordinate X 1
  | 2 => rowCoordinate X 2
  | 3 => rowCoordinate X 3
  | _ => ofQ' 0

private theorem environment_mk (X : CauchyPoint) : ∀ i,
    pointEnvironment (Quotient.mk chordSeminorm.completionSetoid X) i =
      Quotient.mk crealSetoid (rowEnvironment X i)
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _+4 => rfl

private theorem environment_approx (X : CauchyPoint) (n : Nat) : ∀ i,
    (rowEnvironment X i).approx n = quaternionCoordinates (X.seq n).val i
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _+4 => rfl

def pointEval (x : Point) (p : RatPoly) : RC := evalRC (pointEnvironment x) p

private theorem pointEval_mk (X : CauchyPoint) (p : RatPoly) :
    pointEval (Quotient.mk chordSeminorm.completionSetoid X) p =
      Quotient.mk crealSetoid (evalReal (rowEnvironment X) p) := by
  unfold pointEval
  rw [funext (environment_mk X)]
  exact evalRC_mk _ _

theorem pointEval_coeffEqv (x : Point) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    pointEval x p = pointEval x q := by
  refine Quotient.inductionOn x ?_
  intro X
  unfold pointEval
  rw [funext (environment_mk X)]
  exact evalRC_coeffEqv_supplied _ h

private theorem weighted_haar (blocks : Nat) : ∀ p : RatPoly,
    ratWeightedSum (quaternionHaarMono blocks) p = quaternionHaar blocks p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*quaternionHaarMono blocks t.1+z) (weighted_haar blocks p)

private theorem haar_congr (blocks : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  simpa only [weighted_haar] using h (quaternionHaarMono blocks)

private theorem zero_haar_evaluate (rho : Nat → Q') : ∀ p : RatPoly,
    quaternionHaar 0 (evaluateTail 0 rho p) ≈ evalRatPoly rho p
  | [] => Q'.eqv_refl _
  | _::p => Q'.add_eqv_congr' (Q'.mul_one_eqv _) (zero_haar_evaluate rho p)

private theorem head_evaluation (rho : Nat → Q') (p : RatPoly) :
    quaternionHaar 1 (evaluateTail 4 rho p) ≈ evalRatPoly rho (partialHaarHead p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead 0 _))
    (Q'.eqv_trans _ _ _ (haar_congr 0 (partialHaarHead_evaluate 0 rho p))
      (zero_haar_evaluate rho _))

private def translated (right : Bool) : PolyQuaternion :=
  if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion

/-- Exact head integration followed by evaluation at the ACTUAL Point multiplier. -/
def completedTranslatedHaar (right : Bool) (g : Point) (p : RatPoly) : RC :=
  pointEval g (partialHaarHead (translatedHeadPolynomial (translated right) p))

/-- All degrees, both Hamilton orders, and the original rational Haar moment. -/
theorem completedTranslatedHaar_invariant (right : Bool) (g : Point)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    completedTranslatedHaar right g p = rational (quaternionHaar 1 p) := by
  refine Quotient.inductionOn g ?_
  intro G
  unfold completedTranslatedHaar
  rw [pointEval_mk]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  rw [evalReal_approx]
  have he : (fun j => (rowEnvironment G j).approx n) = quaternionCoordinates (G.seq n).val :=
    funext (environment_approx G n)
  rw [he]
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_evaluation _ _))
    (fixedTranslatedPolynomial_haar right (G.seq n) p hp)

private def splice {A : Type} (keep : Nat) (head tail : Nat → A) (i : Nat) : A :=
  if i < keep then head i else tail (i-keep)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem mono_shift (rho : Nat → Q') (s : Nat) : ∀ m i,
    evalMonoFrom rho (s+i) m = evalMonoFrom (fun j => rho (s+j)) i m
  | [], _ => rfl
  | _::m, i => by
      simp only [evalMonoFrom]
      rw [show s+i+1=s+(i+1) from Nat.add_assoc _ _ _, mono_shift rho s m (i+1)]

private theorem mono_cons (rho : Nat → Q') (e : Nat) (m : List Nat) :
    evalMono rho (e::m) = qpow (rho 0) e * evalMono (fun j => rho (j+1)) m := by
  unfold evalMono
  simp only [evalMonoFrom]
  congr 1
  simpa only [Nat.add_zero, Nat.add_comm] using mono_shift rho 1 m 0

private theorem mono_splice : ∀ keep (head tail : Nat → Q') m,
    evalMono (splice keep head tail) m ≈ evalMono head (m.take keep)*evalMono tail (m.drop keep)
  | 0, head, tail, m => by
      simpa only [splice, Nat.not_lt_zero, if_false, Nat.sub_zero, List.take_zero,
        List.drop_zero, evalMono, evalMonoFrom] using Q'.eqv_symm (Q'.one_mul_eqv (evalMono tail m))
  | _+1, _, _, [] => by change (1 : Q') ≈ 1*1; decide
  | keep+1, head, tail, e::m => by
      rw [mono_cons, List.take_succ_cons, List.drop_succ_cons, mono_cons]
      have hs : (fun j => splice (keep+1) head tail (j+1)) = splice keep (fun j => head (j+1)) tail := by
        funext j
        unfold splice
        by_cases hj : j < keep
        · simp only [hj, Nat.succ_lt_succ_iff, if_true]
        · simp only [hj, Nat.succ_lt_succ_iff, if_false, Nat.add_sub_add_right]
      rw [hs]
      have hz : splice (keep+1) head tail 0 = head 0 := by simp [splice]
      rw [hz]
      exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (mono_splice keep _ _ m))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem specialized_eval (keep : Nat) (head tail : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly head (evaluateTail keep tail p) ≈ evalRatPoly (splice keep head tail) p
  | [] => Q'.eqv_refl _
  | t::p => by
      apply Q'.add_eqv_congr' _ (specialized_eval keep head tail p)
      change (t.2*evalMono tail (t.1.drop keep))*evalMono head (t.1.take keep) ≈ _
      refine Q'.eqv_trans _ (t.2*(evalMono head (t.1.take keep)*evalMono tail (t.1.drop keep))) _ ?_ ?_
      · exact poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
          (fun | 0 => t.2 | 1 => evalMono tail (t.1.drop keep) | _ => evalMono head (t.1.take keep))
      · exact mc (Q'.eqv_refl _) (Q'.eqv_symm (mono_splice keep head tail t.1))

/-- Literal unintegrated translated polynomial on two actual Point inputs. -/
def completedTranslatedEval (right : Bool) (g x : Point) (p : RatPoly) : RC :=
  evalRC (splice 4 (pointEnvironment x) (pointEnvironment g))
    (translatedHeadPolynomial (translated right) p)

private theorem translated_rational_eval (right : Bool) (g x : UnitNorm)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    evalRatPoly (splice 4 (quaternionCoordinates x.val) (quaternionCoordinates g.val))
      (translatedHeadPolynomial (translated right) p) ≈
      evalRatPoly (quaternionCoordinates (if right then RationalQuaternion.mul x.val g.val
        else RationalQuaternion.mul g.val x.val)) p :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (specialized_eval 4 _ _ _))
    (fixedTranslatedPolynomial_eval right g x p hp)

/-- The polynomial denotes the SAME completed Hamilton action, in both orders. -/
theorem completedTranslatedEval_action (right : Bool) (g x : Point)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    completedTranslatedEval right g x p =
      pointEval (if right then completedMul x g else completedMul g x) p := by
  refine Quotient.inductionOn₂ g x ?_
  intro G X
  have he : splice 4 (pointEnvironment (Quotient.mk chordSeminorm.completionSetoid X))
      (pointEnvironment (Quotient.mk chordSeminorm.completionSetoid G)) =
      (fun j => Quotient.mk crealSetoid (splice 4 (rowEnvironment X) (rowEnvironment G) j)) := by
    funext j
    unfold splice
    split <;> exact environment_mk _ _
  unfold completedTranslatedEval
  rw [he, evalRC_mk]
  cases right <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    rw [completedMul,
      YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm.BinaryQuadraticLipschitz.completionMap_mk] <;>
    rw [pointEval_mk] <;>
    apply Quotient.sound <;>
    apply SumOfSquares.Equiv_of_approx_eqv <;>
    intro n <;>
    rw [evalReal_approx, evalReal_approx]
  all_goals
    have hs : (fun j => (splice 4 (rowEnvironment X) (rowEnvironment G) j).approx n) =
        splice 4 (quaternionCoordinates (X.seq n).val) (quaternionCoordinates (G.seq n).val) := by
      funext j
      unfold splice
      split <;> exact environment_approx _ _ _
    rw [hs]
  · have ho : (fun j => (rowEnvironment (multiplication.mapCauchy G X) j).approx n) =
        quaternionCoordinates (UnitNorm.mul (G.seq n) (X.seq n)).val :=
      funext (environment_approx _ n)
    rw [ho]
    exact translated_rational_eval false (G.seq n) (X.seq n) p hp
  · have ho : (fun j => (rowEnvironment (multiplication.mapCauchy X G) j).approx n) =
        quaternionCoordinates (UnitNorm.mul (X.seq n) (G.seq n)).val :=
      funext (environment_approx _ n)
    rw [ho]
    exact translated_rational_eval true (G.seq n) (X.seq n) p hp

end YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation

#print axioms YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.evalRC_coeffEqv_supplied
#print axioms YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.pointEval_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.completedTranslatedHaar_invariant
#print axioms YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.completedTranslatedEval_action
