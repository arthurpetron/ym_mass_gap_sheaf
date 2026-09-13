/-
# Polynomial and noncommutative holonomy naturality of Haar block embeddings

The finite Haar embedding preserves the literal signed polynomial operations.
Constants and all-spin characters agree up to harmless trailing-zero padding,
using the existing coefficient-sensitive prefix relation. Coordinate variables
go to the explicitly selected target blocks. Quaternion multiplication keeps
its original order; no commutativity of quaternion holonomies is invoked.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

variable {source target : Nat} (E : BlockEmbedding source target)

theorem exponents_mul (left right : List Nat) :
    E.exponents (monoMul left right) = monoMul (E.exponents left) (E.exponents right) := by
  apply natList_eq_of_length_getD
  · rw [E.exponents_length, monoMul_length_of_equal ((E.exponents_length left).trans (E.exponents_length right).symm), E.exponents_length]
  · intro c hc
    rw [E.exponents_length] at hc
    change exponentAt (E.exponents (monoMul left right)) c = exponentAt (monoMul (E.exponents left) (E.exponents right)) c
    rw [E.exponent_pin _ hc, exponentAt_monoMul, exponentAt_monoMul, E.exponent_pin _ hc, E.exponent_pin _ hc]

theorem polynomial_add (p q : RatPoly) : E.polynomial (polyAdd p q) = polyAdd (E.polynomial p) (E.polynomial q) :=
  List.map_append

theorem polynomial_mul (p q : RatPoly) : E.polynomial (polyMul p q) = polyMul (E.polynomial p) (E.polynomial q) := by
  simp only [polynomial, polyMul, List.map_flatMap, List.flatMap_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatPoly => p.flatMap f)
  funext t
  apply congrArg (fun f : RatTerm → RatTerm => q.map f)
  funext s
  simp only [Function.comp_apply]
  rw [E.exponents_mul]

theorem polynomial_smul (c : Q') (p : RatPoly) : E.polynomial (polySmul c p) = polySmul c (E.polynomial p) := by
  unfold polynomial polySmul
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => p.map f)
  funext term
  rfl

theorem polynomial_neg (p : RatPoly) : E.polynomial (polyNeg p) = polyNeg (E.polynomial p) := by
  unfold polynomial polyNeg
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => p.map f)
  funext term
  rfl

theorem polynomial_one_prefix : QuaternionPrefixPolynomialEqv target (E.polynomial polyOne) polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · refine ⟨Q'.eqv_refl 1, ?_⟩
    intro c hc
    rw [E.exponent_pin _ hc]
    rfl
  · exact .nil

theorem polynomial_character (p : RatPoly) : ∀ spin,
    QuaternionPrefixPolynomialEqv target (E.polynomial (characterPolynomial p spin)) (characterPolynomial (E.polynomial p) spin)
  | 0 => E.polynomial_one_prefix
  | 1 => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polySmul 2 p)) (polySmul 2 (E.polynomial p))
      rw [E.polynomial_smul]
      exact .refl _ _
  | spin+2 => by
      change QuaternionPrefixPolynomialEqv target
        (E.polynomial (polyAdd (polyMul (polySmul 2 p) (characterPolynomial p (spin+1))) (polySmul (-1) (characterPolynomial p spin))))
        (polyAdd (polyMul (polySmul 2 (E.polynomial p)) (characterPolynomial (E.polynomial p) (spin+1)))
          (polySmul (-1) (characterPolynomial (E.polynomial p) spin)))
      rw [E.polynomial_add, E.polynomial_mul, E.polynomial_smul, E.polynomial_smul]
      exact ((QuaternionPrefixPolynomialEqv.refl _ _).mul (polynomial_character p (spin+1))).append
        ((polynomial_character p spin).smul (-1))

theorem polynomial_var {i c : Nat} (hi : i < source) (hc : c < 4) :
    QuaternionPrefixPolynomialEqv target (E.polynomial (polyVar (4*i+c))) (polyVar (4*E.block i+c)) := by
  apply QuaternionPrefixPolynomialEqv.cons
  · refine ⟨Q'.eqv_refl 1, ?_⟩
    intro d hd
    rw [E.exponent_pin _ hd, exponentAt_varMono, exponentAt_varMono]
    by_cases he : 4*E.index (d/4)+d%4 = 4*i+c
    · have hidx : E.index (d/4) = i := by omega
      have hblock := (E.index_eq_block hi).mp hidx
      have htarget : d = 4*E.block i+c := by omega
      rw [if_pos he, if_pos htarget]
    · have hne : d ≠ 4*E.block i+c := by
        intro htarget
        have hdiv : d/4 = E.block i := by omega
        have hmod : d%4 = c := by omega
        exact he (by rw [hdiv, hmod, E.index_block hi])
      rw [if_neg he, if_neg hne]
  · exact .nil

def quaternion (q : PolyQuaternion) : PolyQuaternion where
  scalar := E.polynomial q.scalar
  iPart := E.polynomial q.iPart
  jPart := E.polynomial q.jPart
  kPart := E.polynomial q.kPart

theorem quaternion_conj (q : PolyQuaternion) : E.quaternion (PolyQuaternion.conj q) = PolyQuaternion.conj (E.quaternion q) := by
  cases q
  simp only [quaternion, PolyQuaternion.conj, E.polynomial_neg]

theorem quaternion_mul (p q : PolyQuaternion) :
    E.quaternion (PolyQuaternion.mul p q) = PolyQuaternion.mul (E.quaternion p) (E.quaternion q) := by
  cases p
  cases q
  simp only [quaternion, PolyQuaternion.mul, E.polynomial_add, E.polynomial_mul, E.polynomial_neg]

theorem quaternion_one : QuaternionPrefixPolyQuaternionEqv target (E.quaternion PolyQuaternion.one) PolyQuaternion.one :=
  ⟨E.polynomial_one_prefix, .nil, .nil, .nil⟩

theorem quaternion_coordinate {i : Nat} (hi : i < source) :
    QuaternionPrefixPolyQuaternionEqv target (E.quaternion (PolyQuaternion.coordinateVariable i)) (PolyQuaternion.coordinateVariable (E.block i)) :=
  ⟨E.polynomial_var (c := 0) hi (by omega), E.polynomial_var (c := 1) hi (by omega),
   E.polynomial_var (c := 2) hi (by omega), E.polynomial_var (c := 3) hi (by omega)⟩

theorem character_of_quaternion {p q : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv target (E.quaternion p) q) (spin : Nat) :
    QuaternionPrefixPolynomialEqv target (E.polynomial (characterPolynomial p.scalar spin)) (characterPolynomial q.scalar spin) :=
  (E.polynomial_character p.scalar spin).trans (h.scalar.character spin)

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.exponents_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_add
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_smul
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_neg
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_one_prefix
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_character
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_var
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.quaternion
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.quaternion_conj
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.quaternion_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.quaternion_one
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.quaternion_coordinate
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.character_of_quaternion
