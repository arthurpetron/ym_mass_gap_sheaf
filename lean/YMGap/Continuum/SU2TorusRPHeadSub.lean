/-
# Torus RP assembly (b3): the head shear substitution is a `RingSub`, and its action on link variables

* `head_ringSub T`: `translatedHeadPolynomial T` is a `RingSub n` for every quaternion `T`. Here `mul`/`smul` come from
  the existing coefficient lemmas via `pe_of_coeff`, `add` is literal, and `neg`/`one` are new.
* `head_coord0`: the head link variable is sent to `T` (componentwise `PE`), e.g. `T = A·L` for the split.
* `head_tail`: every other coordinate variable is fixed (literal, existing).
Combined with `SU2TorusRPSubst.TK_word_sub`, a split crossing link enters every plaquette word as the product `T`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** Still to do: the conj flip as a `RingSub` (its product law exists only
up to support guards), the geometry (c) and the assembly (d).
-/

import YMGap.Continuum.SU2TorusRPReindex
import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix

namespace YMGap.Continuum.SU2TorusRPHeadSub

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul varMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
  (translatedHeadPolynomial translatedHeadTerm translatedHeadMonomial headTailLiftTerm ratPolyPow)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
  (translatedHeadPolynomial_mul translatedHeadPolynomial_add translatedHeadPolynomial_smul)
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm sm_congr sm_flatMap sm_map pe_refl pe_symm pe_trans pe_append
  pe_mulL pe_mulR pe_comm pe_const)
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub pe_neg pe_mul2)
open YMGap.Continuum.SU2TorusRPKernel (pe_of_coeff)

section
variable (n : Nat)

theorem pe_mul_neg (M X : RatPoly) : PE n (polyMul M (polyNeg X)) (polyNeg (polyMul M X)) := fun m => by
  unfold phi
  simp only [polyMul, polyNeg, List.map_flatMap, List.map_map]
  refine Q'.eqv_trans _ _ _ (sm_flatMap _ _ M) (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (sm_flatMap _ _ M)))
  refine sm_congr M fun s _ => ?_
  rw [sm_map, sm_map]
  exact sm_congr X fun t _ => Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv _ _)

theorem pe_one_mul (X : RatPoly) : PE n (polyMul polyOne X) X := pe_const n 1 (Q'.eqv_refl 1) X

theorem pe_four : PE n [([0, 0, 0, 0], (1 : Q'))] polyOne := YMGap.Continuum.SU2TorusRPCore.pe_zeros n 4

end

variable {n : Nat}

theorem head_neg (T : PolyQuaternion) : ∀ p : RatPoly,
    PE n (translatedHeadPolynomial T (polyNeg p)) (polyNeg (translatedHeadPolynomial T p))
  | [] => pe_refl n _
  | t :: r => by
    show PE n (polyAdd (polyMul (translatedHeadMonomial T _ _ _ _) (polyNeg (headTailLiftTerm t)))
        (translatedHeadPolynomial T (polyNeg r)))
      (polyNeg (polyAdd (translatedHeadTerm T t) (translatedHeadPolynomial T r)))
    rw [show polyNeg (polyAdd (translatedHeadTerm T t) (translatedHeadPolynomial T r)) =
      polyAdd (polyNeg (translatedHeadTerm T t)) (polyNeg (translatedHeadPolynomial T r)) by
        simp [polyNeg, polyAdd]]
    exact pe_append n (pe_mul_neg n _ _) (head_neg T r)

theorem head_one (T : PolyQuaternion) : PE n (translatedHeadPolynomial T polyOne) polyOne := by
  show PE n (polyMul (polyMul polyOne (polyMul polyOne (polyMul polyOne polyOne))) [([0, 0, 0, 0], 1)] ++ []) polyOne
  rw [List.append_nil]
  refine pe_trans n (pe_mul2 n (pe_trans n (pe_one_mul n _) (pe_trans n (pe_one_mul n _) (pe_one_mul n _)))
    (pe_four n)) ?_
  exact pe_one_mul n _

theorem head_ringSub (T : PolyQuaternion) : RingSub n (translatedHeadPolynomial T) where
  mul p q := pe_of_coeff n (translatedHeadPolynomial_mul T p q)
  add p q := by rw [translatedHeadPolynomial_add]; exact pe_refl n _
  smul c p := pe_of_coeff n (translatedHeadPolynomial_smul T c p)
  neg p := head_neg T p
  one := head_one T

/-- The head coordinate quaternion is sent to `T`. -/
theorem head_coord0 (T : PolyQuaternion) :
    QPE n (qsub (translatedHeadPolynomial T) (PolyQuaternion.coordinateVariable 0)) T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show PE n (polyMul (polyMul (polyMul polyOne T.scalar) (polyMul polyOne (polyMul polyOne polyOne)))
      [([0, 0, 0, 0], 1)] ++ []) T.scalar
    rw [List.append_nil]
    exact pe_trans n (pe_mul2 n (pe_trans n (pe_mul2 n (pe_one_mul n _) (pe_trans n (pe_one_mul n _)
      (pe_one_mul n _))) (pe_trans n (pe_comm n _ _) (pe_one_mul n _))) (pe_four n))
      (pe_trans n (pe_comm n _ _) (pe_one_mul n _))
  · show PE n (polyMul (polyMul polyOne (polyMul (polyMul polyOne T.iPart) (polyMul polyOne polyOne)))
      [([0, 0, 0, 0], 1)] ++ []) T.iPart
    rw [List.append_nil]
    exact pe_trans n (pe_mul2 n (pe_trans n (pe_one_mul n _) (pe_trans n (pe_mul2 n (pe_one_mul n _)
      (pe_one_mul n _)) (pe_trans n (pe_comm n _ _) (pe_one_mul n _)))) (pe_four n))
      (pe_trans n (pe_comm n _ _) (pe_one_mul n _))
  · show PE n (polyMul (polyMul polyOne (polyMul polyOne (polyMul (polyMul polyOne T.jPart) polyOne)))
      [([0, 0, 0, 0], 1)] ++ []) T.jPart
    rw [List.append_nil]
    exact pe_trans n (pe_mul2 n (pe_trans n (pe_one_mul n _) (pe_trans n (pe_one_mul n _)
      (pe_trans n (pe_comm n _ _) (pe_trans n (pe_one_mul n _) (pe_one_mul n _))))) (pe_four n))
      (pe_trans n (pe_comm n _ _) (pe_one_mul n _))
  · show PE n (polyMul (polyMul polyOne (polyMul polyOne (polyMul polyOne (polyMul polyOne T.kPart))))
      [([0, 0, 0, 0], 1)] ++ []) T.kPart
    rw [List.append_nil]
    exact pe_trans n (pe_mul2 n (pe_trans n (pe_one_mul n _) (pe_trans n (pe_one_mul n _)
      (pe_trans n (pe_one_mul n _) (pe_one_mul n _)))) (pe_four n))
      (pe_trans n (pe_comm n _ _) (pe_one_mul n _))

/-- Every other block's coordinate quaternion is fixed. -/
theorem head_tail (T : PolyQuaternion) (b : Nat) (hb : 1 ≤ b) :
    qsub (translatedHeadPolynomial T) (PolyQuaternion.coordinateVariable b) = PolyQuaternion.coordinateVariable b := by
  have h := YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.translatedHeadPolynomial_tail_coordinate T
  simp only [qsub, PolyQuaternion.coordinateVariable, h (4 * b) (by omega), h (4 * b + 1) (by omega),
    h (4 * b + 2) (by omega), h (4 * b + 3) (by omega)]

end YMGap.Continuum.SU2TorusRPHeadSub

#print axioms YMGap.Continuum.SU2TorusRPHeadSub.head_ringSub
#print axioms YMGap.Continuum.SU2TorusRPHeadSub.head_coord0
#print axioms YMGap.Continuum.SU2TorusRPHeadSub.head_tail
