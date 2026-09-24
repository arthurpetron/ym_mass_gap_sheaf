/-
# Retained heat substitution respects finite-coordinate equality

Trailing-zero padding changes coefficient probes on raw exponent lists, but
does not change any in-carrier coordinate. Transport that precise prefix
relation through the actual substitution and reinsertion. The consumer is
harmonic heat reproduction after a head-fixing change of tail coordinates.
No equality of unpadded coefficient lists is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
import YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion

namespace YMGap.Continuum.SU2QuaternionRetainedImagePrefix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

/-- Once both polynomials are supported in the compared prefix, their
agreement extends to any larger spectator carrier (or a smaller prefix).
Coordinates outside the original carrier are zero on both sides. -/
theorem prefix_on_supported {small large : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv small p q)
    (hp : SupportedQuaternionBlocks small p)
    (hq : SupportedQuaternionBlocks small q) :
    QuaternionPrefixPolynomialEqv large p q := by
  induction h with
  | nil => exact .nil
  | @cons s t p q ht _ ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact ht.coefficient
        · intro i _
          by_cases hi : i < 4*small
          · exact ht.exponent i hi
          · have hs : s.1.length ≤ i := Nat.le_trans (hp s List.mem_cons_self)
                (Nat.le_of_not_gt hi)
            have ht' : t.1.length ≤ i := Nat.le_trans (hq t List.mem_cons_self)
                (Nat.le_of_not_gt hi)
            simp only [exponentAt, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hs, List.getElem?_eq_none ht', Option.getD_none]
      · exact ih (fun u hu => hp u (List.mem_cons_of_mem s hu))
          (fun u hu => hq u (List.mem_cons_of_mem t hu))

/-- Removing four head coordinates retains precisely the tail prefix. -/
theorem dropHeadPolynomial_prefix {tail : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (tail+1) p q) :
    QuaternionPrefixPolynomialEqv tail (dropHeadPolynomial p) (dropHeadPolynomial q) := by
  induction h with
  | nil => exact .nil
  | @cons s t _ _ ht _ ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact ht.coefficient
        · intro i hi
          change exponentAt (s.1.drop 4) i = exponentAt (t.1.drop 4) i
          rw [exponentAt_drop, exponentAt_drop]
          exact ht.exponent (4+i) (by omega)
      · exact ih

/-- Inserting one empty head block preserves the tail prefix, including its
explicit padding. -/
theorem liftHead_prefix {tail : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv tail p q) :
    QuaternionPrefixPolynomialEqv (tail+1) (liftHead p) (liftHead q) := by
  induction h with
  | nil => exact .nil
  | @cons s t _ _ ht _ ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact ht.coefficient
        · intro i hi
          by_cases hhead : i < 4
          · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
            rcases hc with rfl | rfl | rfl | rfl <;> rfl
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hhead)
            change exponentAt (0::0::0::0::s.1) (4+j) =
              exponentAt (0::0::0::0::t.1) (4+j)
            simpa only [Nat.add_comm 4 j, exponentAt, List.getD_cons_succ] using
              ht.exponent j (by omega)
      · exact ih

/-- Actual retained substitution, not an assumed coordinate image. -/
theorem substituteRetained_prefix {tail : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (tail+1) p q) :
    QuaternionPrefixPolynomialEqv tail (substituteRetained p) (substituteRetained q) :=
  dropHeadPolynomial_prefix
    (translatedHeadPolynomial_prefix (by omega)
      (PolyQuaternion.coordinateVariable 1) h)

/-- The full original carrier is restored on both sides. -/
theorem retainedImage_prefix {tail : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (tail+1) p q) :
    QuaternionPrefixPolynomialEqv (tail+1) (retainedImage p) (retainedImage q) :=
  liftHead_prefix (substituteRetained_prefix h)

end YMGap.Continuum.SU2QuaternionRetainedImagePrefix

#print axioms YMGap.Continuum.SU2QuaternionRetainedImagePrefix.prefix_on_supported
#print axioms YMGap.Continuum.SU2QuaternionRetainedImagePrefix.dropHeadPolynomial_prefix
#print axioms YMGap.Continuum.SU2QuaternionRetainedImagePrefix.liftHead_prefix
#print axioms YMGap.Continuum.SU2QuaternionRetainedImagePrefix.substituteRetained_prefix
#print axioms YMGap.Continuum.SU2QuaternionRetainedImagePrefix.retainedImage_prefix
