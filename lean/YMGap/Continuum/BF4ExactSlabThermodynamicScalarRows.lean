/-
# Scalar approximation rows recover the ORIGINAL real-scalar action

An explicitly QCauchy scalar stream is a uniform sequence of constant
polynomials. The original polynomial-row construction therefore supplies
actual Cauchy rows and their modulus. Pairing limits identify their limit
with the EXISTING completedRealSmul, without selecting a quotient scalar
or vector representative. The auxiliary propositional convergence lemmas
only compare constructed limits; the output and its rate remain data.
This supplies the scalar leg of the real-time derivative limit passage.
No generator or physical/continuum/Clay conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative

namespace YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinSequenceWrap (eval_single)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit (representativeInner)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear (completedInner_smul_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator (operator_constant)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal (convergesTo_mul_general)

local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- The existing explicit pairing modulus gives convergence of the actual real representatives. -/
theorem pairing_converges (R S : CauchyRows) :
    ConvergesTo (fun n => representativeInner (R.row n) (S.row n)) (pairingRepresentative R S) := by
  intro epsilon he
  let d := HalfPow.half*epsilon
  have hd : (0 : Q')<d := ExpNeg.half_mul_pos epsilon he
  refine ⟨pairingModulus R S d,fun n hn => ?_⟩
  have hb := row_pairing_bound R S d hd n hn
  obtain ⟨N,hN⟩ := hb.1 d hd
  obtain ⟨M,hM⟩ := hb.2 d hd
  refine ⟨max N M,fun j hj => ?_⟩
  have budget (q : Q') : Q'.eqv ((q+d)+d) (q+epsilon) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))
  exact ⟨Q'.le_trans' _ _ _ (hN j (Nat.le_trans (Nat.le_max_left _ _) hj)) (Q'.le_of_eqv (budget _)),
    Q'.le_trans' _ _ _ (hM j (Nat.le_trans (Nat.le_max_right _ _) hj)) (Q'.le_of_eqv (budget _))⟩

/-- Eventual order is used only to compare already-constructed limits. -/
theorem limit_le_of_eventual {a b : Nat → CReal} {A B : CReal}
    (ha : ConvergesTo a A) (hb : ConvergesTo b B) (N : Nat)
    (h : ∀ n,N≤n → leEv (a n) (b n)) : leEv A B := by
  have shift {f : Nat → CReal} {L : CReal} (hf : ConvergesTo f L) :
      ConvergesTo (fun n => f (max n N)) L := by
    intro epsilon he
    obtain ⟨K,hK⟩ := hf epsilon he
    exact ⟨K,fun n hn => hK (max n N) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le (shift ha) (shift hb) (fun n => h (max n N) (Nat.le_max_right _ _))

def scalarSequence (s : CReal) (cs : QCauchy s.approx) : UniformSequence where
  polynomial := fun n => [s.approx n]
  modulus := cs.M
  cauchy := by
    intro epsilon he m n hm hn t _ _
    have h := cs.bound epsilon he m n hm hn
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_single _ t))
        (Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (eval_single _ t)))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_single _ t))
        (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (eval_single _ t))))⟩

def scalarRows (s : CReal) (cs : QCauchy s.approx) (X : seminorm.Cauchy) : CauchyRows :=
  actionRows (scalarSequence s cs) X

theorem scalarRows_pin (s : CReal) (cs : QCauchy s.approx) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (scalarRows s cs X) n=completedSmul (s.approx n) (point X) := by
  rw [scalarRows,actionRows_pin]
  exact operator_constant _ _

theorem scalar_pairing_limit (s : CReal) (cs : QCauchy s.approx) (X Y : seminorm.Cauchy) :
    Equiv (pairingRepresentative (scalarRows s cs X) (constantRows Y))
      (CReal.mul s (representativeInner X Y)) := by
  apply Equiv_of_limit_of_equal (aSeq:=fun n => representativeInner ((scalarRows s cs X).row n) ((constantRows Y).row n))
    (bSeq:=fun n => CReal.mul (ofQ' (s.approx n)) (representativeInner X Y))
  · intro n
    apply Quotient.exact (s:=crealSetoid)
    change completedInner (rowPoint (scalarRows s cs X) n) (rowPoint (constantRows Y) n)=
      RCmul (Quotient.mk crealSetoid (ofQ' (s.approx n))) (completedInner (point X) (point Y))
    rw [scalarRows_pin,constantRows_pin,completedInner_smul_left]
  · exact pairing_converges _ _
  · exact convergesTo_mul_general (convergesTo_self s) (convergesTo_const _)

/-- The limit is the OLD real-scalar action, not a new compatible operation. -/
theorem scalarRows_limit (s : CReal) (cs : QCauchy s.approx) (X : seminorm.Cauchy) :
    rowLimit (scalarRows s cs X)=completedRealSmul s cs (point X) := by
  apply completed_eq_of_pairings
  intro y
  refine Quotient.inductionOn y ?_
  intro Y
  have h : Quotient.mk crealSetoid (pairingRepresentative (scalarRows s cs X) (constantRows Y))=
      Quotient.mk crealSetoid (CReal.mul s (representativeInner X Y)) :=
    Quotient.sound (scalar_pairing_limit s cs X Y)
  change completedInner (rowLimit (scalarRows s cs X)) (rowLimit (constantRows Y))=
    RCmul (Quotient.mk crealSetoid s) (completedInner (point X) (point Y)) at h
  rw [rowLimit_constant] at h
  rw [completedInner_realSmul_left]
  exact h

def scalarLimitRate (s : CReal) (cs : QCauchy s.approx) (X : seminorm.Cauchy) : Q' → Nat :=
  rowLimitRate (scalarRows s cs X)

theorem scalar_limit_bound (s : CReal) (cs : QCauchy s.approx) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : scalarLimitRate s cs X epsilon≤n) :
    RCle (BF4ExactSlabThermodynamicCompletedGeometry.completedDist (completedSmul (s.approx n) (point X))
      (completedRealSmul s cs (point X))) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := rowLimit_bound (scalarRows s cs X) epsilon he n hn
  rw [scalarRows_pin,scalarRows_limit] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.pairing_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.limit_le_of_eventual
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalarSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalarRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalarRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalar_pairing_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalarRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalarLimitRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows.scalar_limit_bound
