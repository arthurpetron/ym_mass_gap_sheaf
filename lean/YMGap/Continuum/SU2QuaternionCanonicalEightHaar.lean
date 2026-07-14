/-
# Exact product-Haar positivity on the canonical eight-coordinate carrier

The dense `List Nat` carrier used to derive the quaternion moment formula is
convenient for recursion, but it has trailing-zero aliases.  Boundary exchange
therefore lives on the strict `Fin 8 -> Nat` monomial carrier instead.  This
file gives the exact embedding from that canonical carrier into the derived
moment model, proves that it preserves multiplication, and transports the
all-degree square theorem.  The resulting normalized positive functional has
no assumed positivity field.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
import YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

namespace YMGap.Continuum.SU2QuaternionCanonicalEightHaar

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

local infix:50 " ≈ " => Q'.eqv

/-- The unique dense length-eight representative of a canonical monomial. -/
def mono8ToList (m : Mono8) : List Nat :=
  [m 0, m 1, m 2, m 3, m 4, m 5, m 6, m 7]

def embedTerm8 (t : Term8) : RatTerm := (mono8ToList t.1, t.2)

def embedPoly8 (p : Poly8) : RatPoly := p.map embedTerm8

theorem mono8ToList_length (m : Mono8) : (mono8ToList m).length = 8 := by
  rfl

theorem mono8ToList_mul (a b : Mono8) :
    mono8ToList (monoMul8 a b) = monoMul (mono8ToList a) (mono8ToList b) := by
  rfl

theorem embedTerm8_mul (a b : Term8) :
    embedTerm8 (termMul8 a b) =
      (monoMul (embedTerm8 a).1 (embedTerm8 b).1,
        (embedTerm8 a).2 * (embedTerm8 b).2) := by
  apply Prod.ext
  · exact mono8ToList_mul a.1 b.1
  · rfl

theorem embedPoly8_supported (p : Poly8) : Supported8 (embedPoly8 p) := by
  intro t ht
  simp only [embedPoly8, List.mem_map] at ht
  rcases ht with ⟨u, hu, rfl⟩
  exact Nat.le_of_eq (mono8ToList_length u.1)

private theorem embedTerm8_map_mul (a : Term8) (q : Poly8) :
    List.map embedTerm8 (q.map fun b => termMul8 a b) =
      (embedPoly8 q).map fun b =>
        (monoMul (embedTerm8 a).1 b.1, (embedTerm8 a).2 * b.2) := by
  induction q with
  | nil => rfl
  | cons b q ih =>
      change
        embedTerm8 (termMul8 a b) ::
            List.map embedTerm8 (q.map fun u => termMul8 a u) =
          (monoMul (embedTerm8 a).1 (embedTerm8 b).1,
              (embedTerm8 a).2 * (embedTerm8 b).2) ::
            ((embedPoly8 q).map fun u =>
              (monoMul (embedTerm8 a).1 u.1, (embedTerm8 a).2 * u.2))
      rw [embedTerm8_mul, ih]

/-- Canonical multiplication is represented literally by dense polynomial
multiplication in the moment model. -/
theorem embedPoly8_mul (p q : Poly8) :
    embedPoly8 (polyMul8 p q) = polyMul (embedPoly8 p) (embedPoly8 q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change
        List.map embedTerm8
            ((q.map fun b => termMul8 a b) ++ polyMul8 p q) =
          ((embedPoly8 q).map fun b =>
              (monoMul (embedTerm8 a).1 b.1, (embedTerm8 a).2 * b.2)) ++
            polyMul (embedPoly8 p) (embedPoly8 q)
      rw [List.map_append, embedTerm8_map_mul]
      change
        ((embedPoly8 q).map fun b =>
            (monoMul (embedTerm8 a).1 b.1, (embedTerm8 a).2 * b.2)) ++
            embedPoly8 (polyMul8 p q) =
          ((embedPoly8 q).map fun b =>
            (monoMul (embedTerm8 a).1 b.1, (embedTerm8 a).2 * b.2)) ++
            polyMul (embedPoly8 p) (embedPoly8 q)
      rw [ih]

/-- Exact product-Haar expectation on canonical polynomials. -/
def canonicalProductHaar (p : Poly8) : Q' := productHaar (embedPoly8 p)

/-- The derived all-degree square theorem transported to the strict carrier. -/
theorem canonicalProductHaar_square_nonneg (p : Poly8) :
    (0 : Q') ≤ canonicalProductHaar (polyMul8 p p) := by
  rw [canonicalProductHaar, embedPoly8_mul]
  exact productHaar_square_nonneg (embedPoly8 p) (embedPoly8_supported p)

theorem canonicalProductHaar_normalized :
    canonicalProductHaar polyOne8 = 1 := by
  decide

/-- A concrete normalized positive functional on the canonical carrier. -/
def canonicalProductHaarFunctional :
    ProbFunctional canonicalQuaternionPairAlg where
  E := canonicalProductHaar
  normalized := canonicalProductHaar_normalized
  positive := canonicalProductHaar_square_nonneg

end YMGap.Continuum.SU2QuaternionCanonicalEightHaar

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaar.embedPoly8_mul
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaar.canonicalProductHaar_square_nonneg
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaar.canonicalProductHaarFunctional
