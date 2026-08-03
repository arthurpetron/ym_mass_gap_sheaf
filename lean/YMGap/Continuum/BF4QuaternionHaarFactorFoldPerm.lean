/-
# Permuting scalar factors under exact quaternion product Haar

This small algebraic module is shared by the exact reflection proof and the
vacuum interior reduction.  It deliberately has no slab-geometry dependency.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

namespace YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- A permutation of scalar polynomial factors is invisible after exact
product-Haar integration.  The arbitrary left insertion makes the induction
compositional. -/
theorem quaternionHaar_factorFold_perm
    {A : Type} (blocks : Nat) (factor : A → RatPoly)
    {left right : List A} (hperm : left.Perm right) :
    ∀ insertion : RatPoly,
      quaternionHaar blocks
          (polyMul insertion
            (left.foldr
              (fun item total => polyMul (factor item) total)
              polyOne)) ≈
        quaternionHaar blocks
          (polyMul insertion
            (right.foldr
              (fun item total => polyMul (factor item) total)
              polyOne)) := by
  induction hperm with
  | nil =>
      intro insertion
      exact Q'.eqv_refl _
  | cons item hperm induction =>
      intro insertion
      simp only [List.foldr]
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (quaternionHaar_polyMul_assoc blocks insertion
            (factor item) _)) ?_
      exact Q'.eqv_trans _ _ _
        (induction (polyMul insertion (factor item)))
        (quaternionHaar_polyMul_assoc blocks insertion (factor item) _)
  | swap first second rest =>
      intro insertion
      simp only [List.foldr]
      let tail := rest.foldr
        (fun item total => polyMul (factor item) total) polyOne
      have hleft := Q'.eqv_symm
        (quaternionHaar_polyMul_assoc blocks insertion
          (factor second) (polyMul (factor first) tail))
      have hswap := quaternionHaar_polyMul_four_swap blocks insertion
        (factor second) (factor first) tail
      have hright := quaternionHaar_polyMul_assoc blocks insertion
        (factor first) (polyMul (factor second) tail)
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ hswap hright)
  | trans hfirst hsecond inductionFirst inductionSecond =>
      intro insertion
      exact Q'.eqv_trans _ _ _
        (inductionFirst insertion) (inductionSecond insertion)

end YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm

#print axioms YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm.quaternionHaar_factorFold_perm
