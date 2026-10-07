/-
# Torus RP (d4a): adding fresh Haar blocks

`haar_extend`: a polynomial supported on the first `blocks` quaternion blocks has the same Haar integral over
`blocks + extra` blocks. This is the first step of the concrete crossing split (fresh split variables `ΘB`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPCrossProd
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension

namespace YMGap.Continuum.SU2TorusRPExtend

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection

theorem haar_tailMarginal_supported (blocks extra : Nat) : ∀ p : RatPoly,
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks blocks p →
    (quaternionHaar blocks (YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tailMarginal blocks extra p)).eqv
      (quaternionHaar blocks p)
  | [], _ => Q'.eqv_refl _
  | t :: p, h => by
      have ht : t.1.length ≤ 4 * blocks := h t (List.mem_cons_self ..)
      change ((t.2 * quaternionHaarMono extra (t.1.drop (4*blocks))) *
          quaternionHaarMono blocks (t.1.take (4*blocks)) +
          quaternionHaar blocks (YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tailMarginal blocks extra p)).eqv
        (t.2 * quaternionHaarMono blocks t.1 + quaternionHaar blocks p)
      rw [List.drop_eq_nil_of_le ht, List.take_of_length_le ht]
      refine Q'.add_eqv_congr' ?_
        (haar_tailMarginal_supported blocks extra p fun s hs => h s (List.mem_cons_of_mem _ hs))
      refine Q'.mul_eqv_congr_right _ _ _ ?_
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (quaternionHaarMono_one extra)) (Q'.mul_one_eqv _)

theorem haar_extend (blocks extra : Nat) (p : RatPoly)
    (h : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks blocks p) :
    (quaternionHaar (blocks + extra) p).eqv (quaternionHaar blocks p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (YMGap.Continuum.SU2QuaternionHaarCertificateExtension.haar_tailMarginal
    blocks extra p)) (haar_tailMarginal_supported blocks extra p h)

end YMGap.Continuum.SU2TorusRPExtend

#print axioms YMGap.Continuum.SU2TorusRPExtend.haar_extend
