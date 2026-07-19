/-
# Product-Haar Gram fence for the adjacent-even two-face production patch

The literal cutoff-two two-face production patch already has a proved
nonsymmetric corner.  Any kernel obtained by pairing one common family of
half-polynomials with the exact finite-product quaternion Haar functional,

    H(left,right) = Haar(half(left) * half(right)),

is symmetric because raw polynomial multiplication is commutative after
finite-product Haar evaluation.  Consequently the existing production patch
cannot be represented in that common-half product-Haar Gram form, for any
number of quaternion blocks and any proposed half-polynomial family.

Precise scope: this is a fence against identifying the uncompressed `K = 2`
two-face sequential patch with a common-half product-Haar Gram.  It neither
settles nor corrects the full adjacent-even endpoint operator after physical
reachable-state compression.

Next comparison obligation: the smallest closed fixed-face sector to test is
the radius-zero, cutoff-one elementary cube with all six faces fundamental.
The production fusion activity for such a bivalent cube is already reduced
to the sixth power of the fundamental face coefficient, while a true oriented
matrix-coefficient calculation is expected to carry the Euler/Schur factor
`2^(8-12) = 1/16`.  That `1/16` cube value is an inferred mathematical target,
not a theorem currently proved in the repository.  The first four-valent
closed test should retain the two fundamental invariant channels and compare
against the already proved Racah entries `1/4, 3/4, 3/4, 1/4`, rather than
replace their projector by the scalar multiplicity two.  Neither closed
oriented RatPoly-to-spin comparison is claimed here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
import YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

namespace YMGap.Continuum.SU2QuaternionAdjacentEvenTwoFaceProductHaarFence

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator

local infix:50 " ≈ " => Q'.eqv

/-- The nonsymmetric cutoff-two two-face production patch admits no
common-half exact product-Haar Gram realization, independently of the chosen
finite quaternion-block count and polynomial half-family. -/
theorem adjacentEvenTwoFaceProductionPatch_not_productHaarGram
    (blockCount : Nat) (half : Nat → RatPoly) :
    ¬ (∀ left right,
      adjacentEvenTwoFaceProductionPatchMatrix left right ≈
        finiteProductHaar blockCount
          (polyMul (half left) (half right))) := by
  intro hrealization
  apply adjacentEvenTwoFaceProductionPatch_not_symmetric
  exact Q'.eqv_trans _ _ _ (hrealization 0 1)
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_comm
        blockCount (half 0) (half 1))
      (Q'.eqv_symm (hrealization 1 0)))

end YMGap.Continuum.SU2QuaternionAdjacentEvenTwoFaceProductHaarFence

#print axioms YMGap.Continuum.SU2QuaternionAdjacentEvenTwoFaceProductHaarFence.adjacentEvenTwoFaceProductionPatch_not_productHaarGram
