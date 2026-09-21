/-
# Exact block lift of quaternion words

Adjoining fresh quaternion blocks commutes with Hamilton multiplication and
conjugation, and shifts coordinate quaternions by the corresponding block
offset.  Consequently a coefficient-level padded identification of every
letter extends to the ordered Wilson word.  The final statement is purely
algebraic: it supplies neither support nor a Haar change-of-variables claim.
-/

import YMGap.Continuum.SU2QuaternionCoordinateColumnLift
import YMGap.Continuum.SU2QuaternionTranslationWordComposition
import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

namespace YMGap.Continuum.QuaternionHaarWordLift

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition

/-- Adjoin `n` fresh quaternion blocks to every scalar coordinate polynomial. -/
def liftQuaternion (n : Nat) (q : PolyQuaternion) : PolyQuaternion where
  scalar := liftBoundary n q.scalar
  iPart := liftBoundary n q.iPart
  jPart := liftBoundary n q.jPart
  kPart := liftBoundary n q.kPart

/-- Quaternion lifting commutes exactly with Hamilton multiplication. -/
theorem liftQuaternion_mul (n : Nat) (p q : PolyQuaternion) :
    liftQuaternion n (PolyQuaternion.mul p q) =
      PolyQuaternion.mul (liftQuaternion n p) (liftQuaternion n q) := by
  simp only [liftQuaternion, PolyQuaternion.mul, lift_product, lift_add, lift_neg]

/-- Quaternion lifting commutes exactly with quaternion conjugation. -/
theorem liftQuaternion_conj (n : Nat) (q : PolyQuaternion) :
    liftQuaternion n (PolyQuaternion.conj q) =
      PolyQuaternion.conj (liftQuaternion n q) := by
  simp only [liftQuaternion, PolyQuaternion.conj, lift_neg]

/-- Lifting a coordinate quaternion shifts its block index exactly. -/
theorem liftQuaternion_coordinateVariable (n i : Nat) :
    liftQuaternion n (PolyQuaternion.coordinateVariable i) =
      PolyQuaternion.coordinateVariable (n + i) := by
  simp only [liftQuaternion, PolyQuaternion.coordinateVariable, lift_var]
  congr 2 <;> omega

private theorem padded_of_components {blocks : Nat} {p q : PolyQuaternion}
    (hs : PaddedPolynomialCoeffEqv blocks p.scalar q.scalar)
    (hi : PaddedPolynomialCoeffEqv blocks p.iPart q.iPart)
    (hj : PaddedPolynomialCoeffEqv blocks p.jPart q.jPart)
    (hk : PaddedPolynomialCoeffEqv blocks p.kPart q.kPart) :
    PaddedQuaternionCoeffEqv blocks p q := by
  exact ⟨hs, hi, hj, hk⟩

/-- The lifted quaternion unit agrees coefficientwise with the unit after any
common carrier padding. -/
theorem liftQuaternion_one (blocks n : Nat) :
    PaddedQuaternionCoeffEqv blocks (liftQuaternion n PolyQuaternion.one)
      PolyQuaternion.one := by
  apply padded_of_components
  all_goals dsimp only [liftQuaternion, PolyQuaternion.one]
  · exact lift_one blocks n
  · rw [lift_zero]
    exact .refl _ _
  · rw [lift_zero]
    exact .refl _ _
  · rw [lift_zero]
    exact .refl _ _

/-- Letterwise padded coefficient identities extend to the ordered word.
No carrier-support conclusion is implicit in this theorem. -/
theorem wordWith_lift (blocks n : Nat)
    (left right : OrientedBF4Link → PolyQuaternion) (edges : List OrientedBF4Link)
    (hfactor : ∀ e, e ∈ edges →
      PaddedQuaternionCoeffEqv blocks (liftQuaternion n (left e)) (right e)) :
    PaddedQuaternionCoeffEqv blocks
      (liftQuaternion n (wordWith left edges)) (wordWith right edges) := by
  induction edges with
  | nil =>
      exact liftQuaternion_one blocks n
  | cons e es ih =>
      change PaddedQuaternionCoeffEqv blocks
        (liftQuaternion n (PolyQuaternion.mul (left e) (wordWith left es)))
        (PolyQuaternion.mul (right e) (wordWith right es))
      rw [liftQuaternion_mul]
      exact (hfactor e List.mem_cons_self).mul
        (ih (fun f hf => hfactor f (List.mem_cons_of_mem e hf)))

end YMGap.Continuum.QuaternionHaarWordLift

#print axioms YMGap.Continuum.QuaternionHaarWordLift.liftQuaternion
#print axioms YMGap.Continuum.QuaternionHaarWordLift.liftQuaternion_mul
#print axioms YMGap.Continuum.QuaternionHaarWordLift.liftQuaternion_conj
#print axioms YMGap.Continuum.QuaternionHaarWordLift.liftQuaternion_coordinateVariable
#print axioms YMGap.Continuum.QuaternionHaarWordLift.liftQuaternion_one
#print axioms YMGap.Continuum.QuaternionHaarWordLift.wordWith_lift
