/-
# Constructive approximation in the ORIGINAL thermodynamic completed distance

A supplied Cauchy representative returns an actual nearby presentation and
its original squared-distance error bound. Canonical approximants use its
own modulus at invSucc n. No representative of a quotient state is selected.

The quarter- and sixteenth-tolerance distance estimates support diagonal
limits of supplied Cauchy rows. Only generic rational tolerance facts are
reused from the finite module; every distance below is thermodynamic.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos quarter_le_self invSucc_le_of_den)

private theorem four_quarters (epsilon : Q') :
    Q'.eqv ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon)) (ExpNeg.two_halves (HalfPow.half * epsilon)))
    (ExpNeg.two_halves epsilon)

private theorem limit_le_of_eventually {s : Nat → CReal} {L : CReal}
    (hs : ConvergesTo s L) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (s n) (ofQ' bound)) : leEv L (ofQ' bound) := by
  have ht : ConvergesTo (fun n => s (max n base)) L := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hs epsilon he
    exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le ht (convergesTo_const (ofQ' bound)) (fun n => h (max n base) (Nat.le_max_right _ _))

local notation "D" => seminorm

theorem representativeDist_le_of_eventually (X Y : (D).Cauchy) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (distSq (X.seq n) (Y.seq n)) (ofQ' bound)) :
    leEv (representativeDist X Y) (ofQ' bound) :=
  limit_le_of_eventually (representativeDist_converges X Y) bound base h

theorem constantApproximation_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (completedDist (embedPresentation (X.seq n)) (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  representativeDist_le_of_eventually ((D).constant (X.seq n)) X epsilon (X.modulus epsilon)
    (fun m hm => X.isCauchy epsilon he n m hn hm)

/-- The nearby ORIGINAL presentation and its certified error are returned together. -/
def approximationData (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' p : Presentation,
      RCle (completedDist (embedPresentation p) (Quotient.mk (D).completionSetoid X))
        (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  ⟨X.seq (X.modulus epsilon), constantApproximation_bound X epsilon he _ (Nat.le_refl _)⟩

/-- A canonical approximant from supplied representative data, not from quotient choice. -/
def approximant (X : (D).Cauchy) (n : Nat) : Presentation := X.seq (X.modulus (Q'.invSucc n))

theorem approximant_bound (X : (D).Cauchy) (n : Nat) :
    RCle (completedDist (embedPresentation (approximant X n))
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) :=
  constantApproximation_bound X (Q'.invSucc n) (Q'.invSucc_pos n) _ (Nat.le_refl _)

theorem completedDist_two_segment (x y z : Completion) (epsilon : Q')
    (hxy : RCle (completedDist x y) (Quotient.mk crealSetoid (ofQ' (quarter epsilon))))
    (hyz : RCle (completedDist y z) (Quotient.mk crealSetoid (ofQ' (quarter epsilon)))) :
    RCle (completedDist x z) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hsum := RCadd_le_add (RCadd_le_add hxy hxy) (RCadd_le_add hyz hyz)
  have h := RCle_trans (completedDist_triangle x y z) hsum
  have hbudget : RCle
      (Quotient.mk crealSetoid (ofQ' ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (four_quarters epsilon))
  exact RCle_trans h hbudget

theorem completedDist_three_segment (a b c d : Completion) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hab : RCle (completedDist a b) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hbc : RCle (completedDist b c) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hcd : RCle (completedDist c d) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))) :
    RCle (completedDist a d) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hac := completedDist_two_segment a b c (quarter epsilon) hab hbc
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) :=
    leEv_le_ofQ'_of_approx_le (fun _ => quarter_le_self (quarter_pos he))
  exact completedDist_two_segment a c d epsilon hac (RCle_trans hcd hrelax)

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.representativeDist_le_of_eventually
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.constantApproximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.approximationData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.approximant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.approximant_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.completedDist_two_segment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation.completedDist_three_segment
