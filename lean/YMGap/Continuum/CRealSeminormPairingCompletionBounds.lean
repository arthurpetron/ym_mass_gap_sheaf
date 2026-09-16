/-
# Computed pairing ceilings on a constructive squared-seminorm carrier

The interface records only a dense pairing, its actual approximation
moduli, an anchor estimate and quantitative continuity. It neither assumes
a completed pairing nor a uniform bound on an arbitrary Cauchy stream.
The existing scalar-ceiling construction computes one anchor ceiling,
and the anchor estimate gives an eventual ceiling for the whole stream.

The scalar helpers imported from the earlier plaquette modules are fully
generic in their CReal/rational arguments. No physical pairing, carrier,
action or limiting hypothesis enters this generic construction.
-/

import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.CRealSeminormPairingCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling)

/-- Quantitative dense-pairing data. Symmetry and positivity are needed only
by their corresponding output laws, not for constructing this completion.
This is an algebraic completion interface, not a physical frontier input. -/
structure PairingData (D : SquaredSeminorm) where
  pairing : D.Carrier → D.Carrier → CReal
  pairingCauchy : ∀ x y, QCauchy (pairing x y).approx
  diagonal_anchor_bound : ∀ x anchor,
    leEv (pairing x x)
      (add (add (D.distSq x anchor) (D.distSq x anchor))
        (add (pairing anchor anchor) (pairing anchor anchor)))
  pairing_close : ∀ (x x' y y' : D.Carrier) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q'), (0 : Q') < epsilon →
    leEv (D.distSq x x') (ofQ' (pairingTolerance B hB epsilon)) →
    leEv (D.distSq y y') (ofQ' (pairingTolerance B hB epsilon)) →
    leEv (pairing y y) (ofQ' B) → leEv (pairing x' x') (ofQ' B) →
    leRat (sub (pairing x y) (pairing x' y')) epsilon ∧
      leRat (sub (pairing x' y') (pairing x y)) epsilon

variable {D : SquaredSeminorm} (P : PairingData D)

/-- A rational ceiling computed from the supplied dense scalar modulus. -/
def diagonalCeiling (x : D.Carrier) : Q' :=
  scalarCeiling (P.pairing x x) (P.pairingCauchy x x)

theorem diagonalCeiling_nonnegative (x : D.Carrier) :
    (0 : Q') ≤ diagonalCeiling P x := scalarCeiling_nonnegative _ _

theorem diagonal_le_ceiling (x : D.Carrier) :
    leEv (P.pairing x x) (ofQ' (diagonalCeiling P x)) := by
  let c := P.pairingCauchy x x
  intro epsilon he
  refine ⟨c.M 1, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (scalar_approx_le_ceiling (P.pairing x x) c n hn)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he)))

/-- Retain the given squared-distance modulus, without any regularization. -/
def normBase {D : SquaredSeminorm} (_P : PairingData D) (X : D.Cauchy) : Nat := X.modulus 1

def normCeiling (X : D.Cauchy) : Q' :=
  (1+1) + (diagonalCeiling P (X.seq (normBase P X)) +
    diagonalCeiling P (X.seq (normBase P X)))

theorem normCeiling_nonnegative (X : D.Cauchy) :
    (0 : Q') ≤ normCeiling P X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative P _)
      (diagonalCeiling_nonnegative P _))

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (add (add A A) (add B B)) (ofQ' ((a+a)+(b+b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

/-- The constructed stream ceiling; no uniform boundedness premise occurs. -/
theorem diagonal_le_normCeiling (X : D.Cauchy)
    (n : Nat) (hn : normBase P X ≤ n) :
    leEv (P.pairing (X.seq n) (X.seq n)) (ofQ' (normCeiling P X)) := by
  let anchor := X.seq (normBase P X)
  have hdist : leEv (D.distSq (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase P X) hn (Nat.le_refl _)
  exact leEv_trans (P.diagonal_anchor_bound (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling P anchor))

end YMGap.Continuum.CRealSeminormPairingCompletion

#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.PairingData
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.diagonalCeiling
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.diagonalCeiling_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.diagonal_le_ceiling
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.normBase
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.normCeiling
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.normCeiling_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.diagonal_le_normCeiling
