/-
# Explicit approximation in the ORIGINAL completed squared distance

A supplied Cauchy representative X has the computed original expression
X.seq(X.modulus(epsilon)) within squared distance epsilon of its class.
No representative of an arbitrary quotient state is selected.

The quarter-tolerance two-segment bound and sixteenth-tolerance
three-segment bound will control the diagonal of supplied Cauchy rows.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry

def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

theorem quarter_pos {epsilon : Q'} (he : (0 : Q') < epsilon) : (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

private theorem half_le_self {epsilon : Q'} (he : (0 : Q') < epsilon) : HalfPow.half * epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (ExpNeg.half_mul_pos _ he)))
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

theorem quarter_le_self {epsilon : Q'} (he : (0 : Q') < epsilon) : quarter epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _ (half_le_self (ExpNeg.half_mul_pos _ he)) (half_le_self he)

private theorem four_quarters (epsilon : Q') :
    Q'.eqv ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon)) (ExpNeg.two_halves (HalfPow.half * epsilon)))
    (ExpNeg.two_halves epsilon)

theorem invSucc_le_of_den {epsilon : Q'} (he : (0 : Q') < epsilon) {n : Nat} (hn : epsilon.den ≤ n) :
    Q'.invSucc n ≤ epsilon :=
  Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le epsilon he)

private theorem limit_le_of_eventually {s : Nat → CReal} {L : CReal}
    (hs : ConvergesTo s L) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (s n) (ofQ' bound)) : leEv L (ofQ' bound) := by
  have ht : ConvergesTo (fun n => s (max n base)) L := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hs epsilon he
    exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le ht (convergesTo_const (ofQ' bound)) (fun n => h (max n base) (Nat.le_max_right _ _))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

theorem representativeDist_le_of_eventually (X Y : (D).Cauchy) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (distSq w hw0 hw1 (X.seq n) (Y.seq n)) (ofQ' bound)) :
    leEv (representativeDist w hw0 hw1 X Y) (ofQ' bound) :=
  limit_le_of_eventually (representativeDist_converges w hw0 hw1 X Y) bound base h

theorem constantApproximation_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (completedDist w hw0 hw1 (embedExpression w hw0 hw1 (X.seq n)) (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  representativeDist_le_of_eventually w hw0 hw1 ((D).constant (X.seq n)) X epsilon (X.modulus epsilon)
    (fun m hm => X.isCauchy epsilon he n m hn hm)

/-- A canonical approximant from supplied representative data, not from quotient choice. -/
def approximant (X : (D).Cauchy) (n : Nat) : PlaquetteExpression half := X.seq (X.modulus (Q'.invSucc n))

theorem approximant_bound (X : (D).Cauchy) (n : Nat) :
    RCle (completedDist w hw0 hw1 (embedExpression w hw0 hw1 (approximant w hw0 hw1 X n))
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) :=
  constantApproximation_bound w hw0 hw1 X (Q'.invSucc n) (Q'.invSucc_pos n) _ (Nat.le_refl _)

theorem completedDist_two_segment (x y z : Completion w hw0 hw1 half) (epsilon : Q')
    (hxy : RCle (completedDist w hw0 hw1 x y) (Quotient.mk crealSetoid (ofQ' (quarter epsilon))))
    (hyz : RCle (completedDist w hw0 hw1 y z) (Quotient.mk crealSetoid (ofQ' (quarter epsilon)))) :
    RCle (completedDist w hw0 hw1 x z) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hsum := RCadd_le_add (RCadd_le_add hxy hxy) (RCadd_le_add hyz hyz)
  have h := RCle_trans (completedDist_triangle w hw0 hw1 x y z) hsum
  have hbudget : RCle
      (Quotient.mk crealSetoid (ofQ' ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (four_quarters epsilon))
  exact RCle_trans h hbudget

theorem completedDist_three_segment (a b c d : Completion w hw0 hw1 half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hab : RCle (completedDist w hw0 hw1 a b) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hbc : RCle (completedDist w hw0 hw1 b c) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hcd : RCle (completedDist w hw0 hw1 c d) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))) :
    RCle (completedDist w hw0 hw1 a d) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hac := completedDist_two_segment w hw0 hw1 a b c (quarter epsilon) hab hbc
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) :=
    leEv_le_ofQ'_of_approx_le (fun _ => quarter_le_self (quarter_pos he))
  exact completedDist_two_segment w hw0 hw1 a c d epsilon hac (RCle_trans hcd hrelax)

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.quarter
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.quarter_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.quarter_le_self
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.invSucc_le_of_den
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.representativeDist_le_of_eventually
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.constantApproximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.approximant
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.approximant_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.completedDist_two_segment
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation.completedDist_three_segment
