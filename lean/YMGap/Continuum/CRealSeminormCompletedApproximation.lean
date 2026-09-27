/-
# Quantitative dense approximation in a supplied completed distance

The input supplies the actual distance on an existing squared-seminorm
completion, its representative-distance limit, and the distance laws. It
does NOT supply completeness. Every approximation below is computed from
the given Cauchy representative and its own modulus; no representative of
a quotient point is selected.

The quarter/sixteenth estimates are the finite geometric ingredients for
diagonal limits of supplied Cauchy rows. Physical instances must prove all
distance pins and laws on their original carrier.
-/

import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.CRealSeminormCompletedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos quarter_le_self invSucc_le_of_den)

/-- Distance data on the SAME existing completion, without a completeness
field or any choice of representatives. -/
structure DistanceData (D : SquaredSeminorm) where
  representativeDist : D.Cauchy → D.Cauchy → CReal
  representativeDist_converges : ∀ X Y,
    ConvergesTo (fun n => D.distSq (X.seq n) (Y.seq n)) (representativeDist X Y)
  completedDist : D.Completion → D.Completion → RC
  completedDist_mk : ∀ X Y,
    completedDist (Quotient.mk D.completionSetoid X) (Quotient.mk D.completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist X Y)
  completedDist_nonnegative : ∀ x y, RCnonneg (completedDist x y)
  completedDist_symm : ∀ x y, completedDist x y = completedDist y x
  completedDist_triangle : ∀ x y z,
    RCle (completedDist x z)
      (RCadd (RCadd (completedDist x y) (completedDist x y))
        (RCadd (completedDist y z) (completedDist y z)))
  completedDist_zero_iff : ∀ x y, completedDist x y = RCzero ↔ x = y

private theorem four_quarters (epsilon : Q') :
    Q'.eqv ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon)))
    (ExpNeg.two_halves epsilon)

private theorem limit_le_of_eventually {s : Nat → CReal} {L : CReal}
    (hs : ConvergesTo s L) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (s n) (ofQ' bound)) : leEv L (ofQ' bound) := by
  have ht : ConvergesTo (fun n => s (max n base)) L := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hs epsilon he
    exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le ht (convergesTo_const (ofQ' bound))
    (fun n => h (max n base) (Nat.le_max_right _ _))

variable {D : SquaredSeminorm} (P : DistanceData D)

theorem representativeDist_constant (x y : D.Carrier) :
    Equiv (P.representativeDist (D.constant x) (D.constant y)) (D.distSq x y) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (D.distSq x y))
    (P.representativeDist_converges (D.constant x) (D.constant y))
    (convergesTo_const (D.distSq x y))

/-- The original dense distance, not a separately assumed embedding metric. -/
theorem completedDist_embedRep (x y : D.Carrier) :
    P.completedDist (D.embedRep x) (D.embedRep y) = Quotient.mk crealSetoid (D.distSq x y) := by
  change P.completedDist (Quotient.mk D.completionSetoid (D.constant x))
    (Quotient.mk D.completionSetoid (D.constant y)) = _
  rw [P.completedDist_mk]
  exact Quotient.sound (representativeDist_constant P x y)

theorem representativeDist_le_of_eventually (X Y : D.Cauchy) (bound : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (D.distSq (X.seq n) (Y.seq n)) (ofQ' bound)) :
    leEv (P.representativeDist X Y) (ofQ' bound) :=
  limit_le_of_eventually (P.representativeDist_converges X Y) bound base h

theorem constantApproximation_bound (X : D.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (P.completedDist (D.embedRep (X.seq n)) (Quotient.mk D.completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  change RCle (P.completedDist (Quotient.mk D.completionSetoid (D.constant (X.seq n)))
    (Quotient.mk D.completionSetoid X)) _
  rw [P.completedDist_mk]
  exact representativeDist_le_of_eventually P (D.constant (X.seq n)) X epsilon
    (X.modulus epsilon) (fun m hm => X.isCauchy epsilon he n m hn hm)

/-- Both the original dense point and its error certificate are returned. -/
def approximationData (X : D.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' x : D.Carrier,
      RCle (P.completedDist (D.embedRep x) (Quotient.mk D.completionSetoid X))
        (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  ⟨X.seq (X.modulus epsilon), constantApproximation_bound P X epsilon he _ (Nat.le_refl _)⟩

/-- Sampling uses only the supplied representative's modulus. -/
def approximant (_P : DistanceData D) (X : D.Cauchy) (n : Nat) : D.Carrier :=
  X.seq (X.modulus (Q'.invSucc n))

theorem approximant_bound (X : D.Cauchy) (n : Nat) :
    RCle (P.completedDist (D.embedRep (approximant P X n))
      (Quotient.mk D.completionSetoid X)) (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) :=
  constantApproximation_bound P X (Q'.invSucc n) (Q'.invSucc_pos n) _ (Nat.le_refl _)

theorem completedDist_two_segment (x y z : D.Completion) (epsilon : Q')
    (hxy : RCle (P.completedDist x y) (Quotient.mk crealSetoid (ofQ' (quarter epsilon))))
    (hyz : RCle (P.completedDist y z) (Quotient.mk crealSetoid (ofQ' (quarter epsilon)))) :
    RCle (P.completedDist x z) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hsum := RCadd_le_add (RCadd_le_add hxy hxy) (RCadd_le_add hyz hyz)
  have h := RCle_trans (P.completedDist_triangle x y z) hsum
  have hbudget : RCle
      (Quotient.mk crealSetoid (ofQ' ((quarter epsilon + quarter epsilon) +
        (quarter epsilon + quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (four_quarters epsilon))
  exact RCle_trans h hbudget

theorem completedDist_three_segment (a b c d : D.Completion) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hab : RCle (P.completedDist a b) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hbc : RCle (P.completedDist b c) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
    (hcd : RCle (P.completedDist c d) (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))) :
    RCle (P.completedDist a d) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hac := completedDist_two_segment P a b c (quarter epsilon) hab hbc
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon))))
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) :=
    leEv_le_ofQ'_of_approx_le (fun _ => quarter_le_self (quarter_pos he))
  exact completedDist_two_segment P a c d epsilon hac (RCle_trans hcd hrelax)

/-- A dense equality determines two nonexpansive maps into any separated
squared-distance target. Neither target completeness nor a rational-valued
pre-Hilbert presentation is needed. The approximant is sampled using the
supplied source representative's own modulus. -/
theorem maps_eq_of_dense {Target : Type}
    (targetDist : Target → Target → RC)
    (target_eq : ∀ a b, (∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (targetDist a b) (Quotient.mk crealSetoid (ofQ' epsilon))) → a = b)
    (target_two_segment : ∀ a b c (epsilon : Q'),
      RCle (targetDist a b) (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) →
      RCle (targetDist b c) (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) →
      RCle (targetDist a c) (Quotient.mk crealSetoid (ofQ' epsilon)))
    (f g : D.Completion → Target)
    (hf : ∀ x y, RCle (targetDist (f x) (f y)) (P.completedDist x y))
    (hg : ∀ x y, RCle (targetDist (g x) (g y)) (P.completedDist x y))
    (dense : ∀ s, f (D.embedRep s) = g (D.embedRep s))
    (x : D.Completion) : f x = g x := by
  refine Quotient.inductionOn x ?_
  intro X
  let current : D.Completion := Quotient.mk D.completionSetoid X
  apply target_eq
  intro epsilon hepsilon
  let n := X.modulus (quarter epsilon)
  let near := D.embedRep (X.seq n)
  have hnear : RCle (P.completedDist near current)
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) :=
    constantApproximation_bound P X (quarter epsilon) (quarter_pos hepsilon)
      n (Nat.le_refl _)
  have hfar : RCle (P.completedDist current near)
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) := by
    rw [P.completedDist_symm current near]
    exact hnear
  have hleft := RCle_trans (hf current near) hfar
  have hright := RCle_trans (hg near current) hnear
  have hmiddle : f near = g near := dense (X.seq n)
  rw [← hmiddle] at hright
  exact target_two_segment (f current) (f near) (g current) epsilon hleft hright

end YMGap.Continuum.CRealSeminormCompletedApproximation

#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.DistanceData
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.representativeDist_constant
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.completedDist_embedRep
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.representativeDist_le_of_eventually
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.constantApproximation_bound
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.approximationData
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.approximant
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.approximant_bound
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.completedDist_two_segment
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.completedDist_three_segment
#print axioms YMGap.Continuum.CRealSeminormCompletedApproximation.maps_eq_of_dense
