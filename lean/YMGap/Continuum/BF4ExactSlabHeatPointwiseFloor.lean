/-
# The strict heat floor on ORIGINAL shared-link face polynomials

Evaluation of the actual faceHeatPolynomial at ANY rational environment is
exactly the ordinary heat-character prefix with K+1 terms. The proved
finite cutoff therefore gives a positive face floor whenever that face's
scalar coordinate lies in [-1,1]. Multiplication gives the floor b(q)^F
for an arbitrary list of faces, with overlapping link variables retained.

This module proves polynomial evaluation statements, NOT Haar order
preservation. The class-coordinate box hypotheses are explicit. No Haar
independence, interacting action floor, vacuum or spectral gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
import YMGap.Continuum.SU2PointwiseHeatStrictFloor

namespace YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatStrictFloor

local infix:50 " ≈ " => Q'.eqv

private theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by
      simp only [List.cons_append, finitePolySum, sum_append f xs ys, polyAdd, List.append_assoc]

/-- Evaluation commutes with the actual finite polynomial-prefix fold. -/
theorem eval_finitePolySum_range (rho : Nat → Q') (f : Nat → RatPoly) : ∀ N : Nat,
    evalRatPoly rho (finitePolySum f (List.range N)) ≈ finSum (fun i => evalRatPoly rho (f i)) N
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
      rw [List.range_succ, sum_append]
      exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr' (eval_finitePolySum_range rho f N)
          (by simp only [finitePolySum, polyAdd, polyZero, List.append_nil]; exact Q'.eqv_refl _))

/-- No change of heat coefficients, face word, or cutoff convention:
the actual K-cutoff face contains precisely K+1 original character terms. -/
theorem eval_faceHeatPolynomial_eqv (w : Q') (K extent id : Nat) (rho : Nat → Q') :
    evalRatPoly rho (faceHeatPolynomial w K extent id)
      ≈ standardPointwiseHeatPartial w (evalRatPoly rho (faceScalar extent id)) (K + 1) := by
  rw [faceHeatPolynomial_eq_sum]
  apply Q'.eqv_trans _ _ _ (eval_finitePolySum_range rho _ (K + 1))
  apply finSum_eqv_congr
  intro spin
  exact Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
    (Q'.mul_eqv_congr_left _ _ _ (eval_characterPolynomial rho _ spin))

/-- Strict pointwise floor for the original geometric face polynomial. -/
theorem finiteFloor_le_eval_faceHeatPolynomial {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent id : Nat) (rho : Nat → Q')
    (hK : finiteCutoff w ≤ K + 1)
    (hxLower : (-(1 : Q')) ≤ evalRatPoly rho (faceScalar extent id))
    (hxUpper : evalRatPoly rho (faceScalar extent id) ≤ (1 : Q')) :
    finiteFloor w ≤ evalRatPoly rho (faceHeatPolynomial w K extent id) :=
  Q'.le_trans' _ _ _ (finiteFloor_le_standardPointwiseHeatPartial hw0 hw1 hxLower hxUpper _ hK)
    (Q'.ge_of_eqv (eval_faceHeatPolynomial_eqv w K extent id rho))

/-- The face-count-dependent product floor as rational data. -/
def productFloor (w : Q') (ids : List Nat) : Q' := finiteFloor w ^ ids.length

theorem productFloor_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (ids : List Nat) :
    (0 : Q') < productFloor w ids := HKPos.pow_pos (finiteFloor_pos hw0 hw1) _

/-- Shared link variables are retained: this is the original polynomial
product at one common environment, not a product of Haar expectations. -/
theorem productFloor_le_eval_heatProduct {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (rho : Nat → Q')
    (hK : finiteCutoff w ≤ K + 1) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → (-(1 : Q')) ≤ evalRatPoly rho (faceScalar extent id)
      ∧ evalRatPoly rho (faceScalar extent id) ≤ (1 : Q')) →
    productFloor w ids ≤ evalRatPoly rho (polynomialProduct (faceHeatPolynomial w K extent) ids)
  | [], _ => Q'.ge_of_eqv (evalRatPoly_one rho)
  | id :: ids, hbox => by
      have hf := finiteFloor_le_eval_faceHeatPolynomial hw0 hw1 K extent id rho hK
        (hbox id List.mem_cons_self).1 (hbox id List.mem_cons_self).2
      have ht := productFloor_le_eval_heatProduct hw0 hw1 K extent rho hK ids
        (fun j hj => hbox j (List.mem_cons_of_mem id hj))
      exact Q'.le_trans' _ _ _
        (HKConv.mul_le_mul' (Q'.le_of_lt (finiteFloor_pos hw0 hw1))
          (Q'.le_trans' _ _ _ (Q'.le_of_lt (productFloor_pos hw0 hw1 ids)) ht) hf ht)
        (Q'.ge_of_eqv (evalRatPoly_mul rho _ _))

end YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor

#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.eval_finitePolySum_range
#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.eval_faceHeatPolynomial_eqv
#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.finiteFloor_le_eval_faceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.productFloor
#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.productFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor.productFloor_le_eval_heatProduct
