/-
# The signed square of a positional finite family

The square of the actual sum equals its single-cut diagonal sum plus two
copies of the positional pair-cut sum. Repeated entries remain separate
occurrences, and no signed cross term is discarded. The accompanying finite
sum identities pass this equality through the original weighted Haar form.

This is finite algebra, not a bound on the action-dependent cross remainder
or a construction of a stable decomposition of arbitrary observables.
-/

import YMGap.Continuum.QuaternionHaarFamilyErasure

namespace YMGap.Continuum.QuaternionHaarFamilySquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_append)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
  (coeffEvalExpr_eqv_of_normalize_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFamilyErasure

local infix:50 " ≈ " => Q'.eqv

/-- Positional single cuts list every original occurrence exactly once. -/
theorem singleCuts_map_fst {A : Type} (ids : List A) :
    (singleCuts ids).map Prod.fst = ids := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
      simpa only [singleCuts, List.map_cons, List.map_map, Function.comp_def] using
        congrArg (List.cons i) ih

private theorem singleCuts_map {A B : Type} (f : A → B) (ids : List A) :
    (singleCuts ids).map (fun c => f c.1) = ids.map f := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map f) (singleCuts_map_fst ids)

/-- The exact diagonal sum, in the same single-cut indexing as the energy cost. -/
def diagonalSum {A : Type} (f : A → RatPoly) (ids : List A) : RatPoly :=
  polySum ((singleCuts ids).map (fun c => polyMul (f c.1) (f c.1)))

/-- The exact signed cross sum, with each positional unordered pair once. -/
def crossSum {A : Type} (f : A → RatPoly) (ids : List A) : RatPoly :=
  polySum ((pairCuts ids).map (fun c => polyMul (f c.1) (f c.2.1)))

/-- The diagonal has exactly the original list's multiplicities. -/
theorem diagonalSum_eq {A : Type} (f : A → RatPoly) (ids : List A) :
    diagonalSum f ids = polySum (ids.map (fun i => polyMul (f i) (f i))) :=
  congrArg polySum (singleCuts_map (fun i => polyMul (f i) (f i)) ids)

private theorem diagonal_cons {A : Type} (f : A → RatPoly) (i : A) (ids : List A) :
    diagonalSum f (i :: ids) = polyAdd (polyMul (f i) (f i)) (diagonalSum f ids) := by
  rw [diagonalSum_eq, diagonalSum_eq]
  rfl

private theorem cross_cons {A : Type} (f : A → RatPoly) (i : A) (ids : List A) :
    RatPolyCoeffEqv (crossSum f (i :: ids))
      (polyAdd (polyMul (f i) (polySum (ids.map f))) (crossSum f ids)) := by
  have hh : RatPolyCoeffEqv
      (polySum ((singleCuts ids).map (fun c => polyMul (f i) (f c.1))))
      (polyMul (f i) (polySum (ids.map f))) := by
    rw [singleCuts_map (fun j => polyMul (f i) (f j)) ids]
    simpa only [List.map_map, Function.comp_def] using
      (RatPolyCoeffEqv.mul_polySum_right (f i) (ids.map f)).symm
  have hs := (RatPolyCoeffEqv.polySum_append
    ((singleCuts ids).map (fun c => polyMul (f i) (f c.1)))
    ((pairCuts ids).map (fun c => polyMul (f c.1) (f c.2.1)))).symm.trans
      (hh.add (RatPolyCoeffEqv.refl (crossSum f ids)))
  simpa only [crossSum, pairCuts, List.map_append, List.map_map, Function.comp_def] using hs

private theorem square_add (x s : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd x s) (polyAdd x s))
      (polyAdd (polyAdd (polyMul x x) (polyMul s s))
        (polyAdd (polyMul x s) (polyMul x s))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
    (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
    (by decide) (fun | 0 => x | _ => s)

private theorem square_reassociate (x d c m : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd x (polyAdd d (polyAdd c c))) (polyAdd m m))
      (polyAdd (polyAdd x d) (polyAdd (polyAdd m c) (polyAdd m c))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 2))))
      (.add (.var 3) (.var 3)))
    (.add (.add (.var 0) (.var 1))
      (.add (.add (.var 3) (.var 2)) (.add (.var 3) (.var 2))))
    (by decide) (fun | 0 => x | 1 => d | 2 => c | _ => m)

/-- The full sum square is its diagonal plus twice the signed pair sum.
No distinctness hypothesis is needed: all indexing is by list occurrence. -/
theorem sumSquare_expansion {A : Type} (f : A → RatPoly) (ids : List A) :
    RatPolyCoeffEqv (polyMul (polySum (ids.map f)) (polySum (ids.map f)))
      (polyAdd (diagonalSum f ids) (polyAdd (crossSum f ids) (crossSum f ids))) := by
  induction ids with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons i ids ih =>
      change RatPolyCoeffEqv
        (polyMul (polyAdd (f i) (polySum (ids.map f)))
          (polyAdd (f i) (polySum (ids.map f)))) _
      have hsub := ((RatPolyCoeffEqv.refl (polyMul (f i) (f i))).add ih).add
        (RatPolyCoeffEqv.refl
          (polyAdd (polyMul (f i) (polySum (ids.map f)))
            (polyMul (f i) (polySum (ids.map f)))))
      have hc := cross_cons f i ids
      rw [diagonal_cons]
      exact (square_add (f i) (polySum (ids.map f))).trans
        (hsub.trans ((square_reassociate (polyMul (f i) (f i))
          (diagonalSum f ids) (crossSum f ids) (polyMul (f i) (polySum (ids.map f)))).trans
            ((RatPolyCoeffEqv.refl _).add (hc.add hc)).symm))

/-- Pointwise rational equivalence passes through an indexed finite sum. -/
theorem qListSum_congr {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≈ g i) :
    qListSum (ids.map f) ≈ qListSum (ids.map g) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.eqv_refl _
  | cons i ids ih =>
      intro h
      exact Q'.add_eqv_congr' (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Finite signed sums preserve addition without a positivity premise. -/
theorem qListSum_add {A : Type} (ids : List A) (f g : A → Q') :
    qListSum (ids.map (fun i => f i + g i)) ≈
      qListSum (ids.map f) + qListSum (ids.map g) := by
  induction ids with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => f i | 1 => g i | 2 => qListSum (ids.map f) | _ => qListSum (ids.map g)))

/-- A signed rational scale factors out of an indexed sum. -/
theorem qListSum_scale {A : Type} (ids : List A) (f : A → Q') (c : Q') :
    qListSum (ids.map (fun i => c * f i)) ≈ c * qListSum (ids.map f) := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

/-- The original weighted Haar pairing is additive, even for a signed weight. -/
theorem haar_weighted_add (blocks : Nat) (mu p q : RatPoly) :
    quaternionHaar blocks (polyMul mu (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul mu p) + quaternionHaar blocks (polyMul mu q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right mu p q))
    (quaternionHaar_append _ _ _)

/-- Exact weighted Haar integration of a finite polynomial sum. -/
theorem haar_weighted_sum (blocks : Nat) (mu : RatPoly) (ps : List RatPoly) :
    quaternionHaar blocks (polyMul mu (polySum ps)) ≈
      qListSum (ps.map (fun p => quaternionHaar blocks (polyMul mu p))) := by
  induction ps with
  | nil => exact haar_of_coeff (RatPolyCoeffEqv.mul_zero_right mu)
  | cons p ps ih =>
      exact Q'.eqv_trans _ _ _ (haar_weighted_add blocks mu p (polySum ps))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

/-- Indexed form, matching the single-cut and pair-cut lists of the cost. -/
theorem haar_weighted_sum_indexed {A : Type} (blocks : Nat) (mu : RatPoly)
    (f : A → RatPoly) (ids : List A) :
    quaternionHaar blocks (polyMul mu (polySum (ids.map f))) ≈
      qListSum (ids.map (fun i => quaternionHaar blocks (polyMul mu (f i)))) := by
  simpa only [List.map_map, Function.comp_def] using
    (haar_weighted_sum blocks mu (ids.map f))

end YMGap.Continuum.QuaternionHaarFamilySquare

#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.singleCuts_map_fst
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.diagonalSum
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.crossSum
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.diagonalSum_eq
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.sumSquare_expansion
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.qListSum_congr
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.qListSum_add
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.qListSum_scale
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.haar_weighted_add
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.haar_weighted_sum
#print axioms YMGap.Continuum.QuaternionHaarFamilySquare.haar_weighted_sum_indexed
