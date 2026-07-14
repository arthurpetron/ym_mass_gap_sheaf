/-
# Boundary-exchange symmetry of the canonical product-Haar functional

The strict canonical boundary exchange must preserve the reference state
before it can serve as a Euclidean time action.  This file proves that fact
from the exact monomial formula.  The proof passes through the ordinary
coefficient-times-moment fold, avoiding any appeal to an abstract invariance
axiom.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightHaar
import YMGap.Continuum.SU2QuaternionHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

theorem productHaarMono_mono8_swap (m : Mono8) :
    productHaarMono (mono8ToList (swapMono8 m)) ≈
      productHaarMono (mono8ToList m) := by
  change
    sphereMoment4 (m 4) (m 5) (m 6) (m 7) *
        sphereMoment4 (m 0) (m 1) (m 2) (m 3) ≈
      sphereMoment4 (m 0) (m 1) (m 2) (m 3) *
        sphereMoment4 (m 4) (m 5) (m 6) (m 7)
  exact Q'.mul_comm_eqv _ _

private theorem productHaarLinearSum_embed_swap : ∀ p : Poly8,
    productHaarLinearSum (embedPoly8 (swapPoly8 p)) ≈
      productHaarLinearSum (embedPoly8 p)
  | [] => Q'.eqv_refl 0
  | t :: p => by
      change
        t.2 * productHaarMono (mono8ToList (swapMono8 t.1)) +
            productHaarLinearSum (embedPoly8 (swapPoly8 p)) ≈
          t.2 * productHaarMono (mono8ToList t.1) +
            productHaarLinearSum (embedPoly8 p)
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_left t.2 _ _
          (productHaarMono_mono8_swap t.1))
        (productHaarLinearSum_embed_swap p)

/-- Exact invariance of the canonical Haar state under strict boundary
exchange. -/
theorem canonicalProductHaar_swap_invariant (p : Poly8) :
    canonicalProductHaar (swapPoly8 p) ≈ canonicalProductHaar p := by
  refine Q'.eqv_trans _
    (productHaarLinearSum (embedPoly8 (swapPoly8 p))) _
    (productHaar_eqv_linearSum _) ?_
  refine Q'.eqv_trans _ (productHaarLinearSum (embedPoly8 p)) _
    (productHaarLinearSum_embed_swap p) ?_
  exact Q'.eqv_symm (productHaar_eqv_linearSum _)

end YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry.productHaarMono_mono8_swap
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry.canonicalProductHaar_swap_invariant
