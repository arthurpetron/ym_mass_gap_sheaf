/-
# A computable finite square budget on the original Haar carrier

Actual per-entry square certificates compile to a certificate for the
square of their polynomial sum. The explicit cap uses the existing
two-term rule 2*a+2*b, retaining repetitions and list order. Its exact
homogeneity retains a common approximation rate without an additive loss.

This deliberately coarse finite-family budget is not volume-uniform and
does not estimate the interacting signed cost in the temporal energy.
-/

import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.QuaternionHaarFiniteSquareBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv

/-- The computed cap follows exactly the existing square-addition compiler. -/
def sumCap {A : Type} (caps : A → Q') : List A → Q'
  | [] => 0
  | i :: ids => sumBound (caps i) (sumCap caps ids)

theorem sumCap_nonnegative {A : Type} (caps : A → Q') :
    ∀ ids : List A, (∀ i, i ∈ ids → (0 : Q') ≤ caps i) →
      (0 : Q') ≤ sumCap caps ids
  | [], _ => Q'.le_refl' 0
  | i :: ids, hc =>
      Q'.zero_le_add _ _
        (Q'.zero_le_add _ _ (hc i List.mem_cons_self) (hc i List.mem_cons_self))
        (Q'.zero_le_add _ _
          (sumCap_nonnegative caps ids (fun j hj => hc j (List.mem_cons_of_mem i hj)))
          (sumCap_nonnegative caps ids (fun j hj => hc j (List.mem_cons_of_mem i hj))))

private theorem sumBound_scale (r a b : Q') :
    sumBound (r*a) (r*b) ≈ r*sumBound a b :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.mul_add_eqv r a a))
      (Q'.eqv_symm (Q'.mul_add_eqv r b b)))
    (Q'.eqv_symm (Q'.mul_add_eqv r (a+a) (b+b)))

/-- No positivity premise is needed for this exact scalar identity. -/
theorem sumCap_scale {A : Type} (caps : A → Q') (ids : List A) (r : Q') :
    sumCap (fun i => r*caps i) ids ≈ r*sumCap caps ids := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv r)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_eqv_congr' ih ih))
        (sumBound_scale r (caps i) (sumCap caps ids))

private def zeroSquare (blocks : Nat) : SquareBound blocks polyZero 0 :=
  SquareBound.ofCoeff (by intro t ht; cases ht)
    (RatPolyCoeffEqv.zero_smul polyOne).symm
    (SquareBound.changeCap (by decide : (0 : Q')*0 ≈ 0) (SquareBound.constant blocks 0))

/-- Witness-bearing finite summation of the supplied square certificates.
There is no separate positivity assumption: each bound carries its own. -/
def sumSquareBound {A : Type} {blocks : Nat} (f : A → RatPoly) (caps : A → Q') :
    (ids : List A) → (∀ i, i ∈ ids → SquareBound blocks (f i) (caps i)) →
      SquareBound blocks (polySum (ids.map f)) (sumCap caps ids)
  | [], _ => zeroSquare blocks
  | i :: ids, P => (P i List.mem_cons_self).add
      (sumSquareBound f caps ids (fun j hj => P j (List.mem_cons_of_mem i hj)))

/-- The certified square bound controls its actual Haar integral. -/
theorem squareHaar {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : SquareBound blocks p c) : quaternionHaar blocks (polyMul p p) ≤ c := by
  let I : Interval blocks (polyMul p p) c :=
    ⟨supported_polyMul P.support P.support, P.nonnegative, P.certificate,
      (Certificate.constant blocks c P.nonnegative).add (Certificate.square p P.support)⟩
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) I.haar_bound

#print axioms sumCap
#print axioms sumCap_nonnegative
#print axioms sumCap_scale
#print axioms sumSquareBound
#print axioms squareHaar

end YMGap.Continuum.QuaternionHaarFiniteSquareBudget
