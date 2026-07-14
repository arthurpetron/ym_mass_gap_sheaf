/-
# Linear Haar pairing laws on the canonical eight-coordinate carrier

The canonical carrier was introduced after the dense moment calculation, so
its positive functional initially exposed only normalization and positivity.
This file transports the exact additive, homogeneous, commutative, and
associative pairing laws needed for a non-vacuous Haar-test quotient.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry
import YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

namespace YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

local infix:50 " ≈ " => Q'.eqv

theorem embedPoly8_add (p q : Poly8) :
    embedPoly8 (polyAdd8 p q) = polyAdd (embedPoly8 p) (embedPoly8 q) := by
  exact List.map_append

theorem embedPoly8_smul (c : Q') : ∀ p : Poly8,
    embedPoly8 (polySmul8 c p) = polySmul c (embedPoly8 p)
  | [] => rfl
  | t :: p => by
      change (mono8ToList t.1, c * t.2) ::
          embedPoly8 (polySmul8 c p) =
        (mono8ToList t.1, c * t.2) :: polySmul c (embedPoly8 p)
      rw [embedPoly8_smul c p]

theorem canonicalProductHaar_add (p q : Poly8) :
    canonicalProductHaar (polyAdd8 p q) ≈
      canonicalProductHaar p + canonicalProductHaar q := by
  unfold canonicalProductHaar
  rw [embedPoly8_add]
  exact productHaar_add _ _

theorem canonicalProductHaar_smul (c : Q') (p : Poly8) :
    canonicalProductHaar (polySmul8 c p) ≈
      c * canonicalProductHaar p := by
  unfold canonicalProductHaar
  rw [embedPoly8_smul]
  exact productHaar_smul c _

theorem canonicalProductHaar_mul_comm (p q : Poly8) :
    canonicalProductHaar (polyMul8 p q) ≈
      canonicalProductHaar (polyMul8 q p) := by
  unfold canonicalProductHaar
  rw [embedPoly8_mul, embedPoly8_mul]
  exact productHaar_polyMul_comm _ _

theorem canonicalProductHaar_mul_assoc (p q r : Poly8) :
    canonicalProductHaar (polyMul8 (polyMul8 p q) r) ≈
      canonicalProductHaar (polyMul8 p (polyMul8 q r)) := by
  unfold canonicalProductHaar
  rw [embedPoly8_mul, embedPoly8_mul, embedPoly8_mul, embedPoly8_mul]
  exact productHaar_polyMul_assoc _ _ _

theorem canonicalProductHaar_mul_middle_comm (p q r : Poly8) :
    canonicalProductHaar (polyMul8 p (polyMul8 q r)) ≈
      canonicalProductHaar (polyMul8 p (polyMul8 r q)) := by
  unfold canonicalProductHaar
  rw [embedPoly8_mul, embedPoly8_mul, embedPoly8_mul, embedPoly8_mul]
  exact productHaar_polyMul_middle_comm _ _ _

theorem canonicalProductHaar_mul_add_left (p q r : Poly8) :
    canonicalProductHaar (polyMul8 (polyAdd8 p q) r) ≈
      canonicalProductHaar (polyMul8 p r) +
        canonicalProductHaar (polyMul8 q r) := by
  have hmul : polyMul8 (polyAdd8 p q) r =
      polyAdd8 (polyMul8 p r) (polyMul8 q r) := by
    simp [polyMul8, polyAdd8]
  rw [hmul]
  exact canonicalProductHaar_add _ _

theorem canonicalProductHaar_mul_add_right (p q r : Poly8) :
    canonicalProductHaar (polyMul8 p (polyAdd8 q r)) ≈
      canonicalProductHaar (polyMul8 p q) +
        canonicalProductHaar (polyMul8 p r) := by
  refine Q'.eqv_trans _
    (canonicalProductHaar (polyMul8 (polyAdd8 q r) p)) _
    (canonicalProductHaar_mul_comm p (polyAdd8 q r)) ?_
  refine Q'.eqv_trans _
    (canonicalProductHaar (polyMul8 q p) +
      canonicalProductHaar (polyMul8 r p)) _
    (canonicalProductHaar_mul_add_left q r p) ?_
  exact QPoly.q_add_congr
    (canonicalProductHaar_mul_comm q p)
    (canonicalProductHaar_mul_comm r p)

private theorem scaled_haarRow (c : Q') (a : RatTerm) : ∀ q : RatPoly,
    haarRow (a.1, c * a.2) q ≈ c * haarRow a q
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | b :: q => by
      refine Q'.eqv_trans _
        (c * ((a.2 * b.2) * productHaarMono (monoMul a.1 b.1)) +
          c * haarRow a q) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _
            ((c * a.2) * (b.2 * productHaarMono (monoMul a.1 b.1))) _
            (Q'.mul_assoc_eqv (c * a.2) b.2 _)
            (Q'.eqv_trans _
              (c * (a.2 * (b.2 * productHaarMono (monoMul a.1 b.1)))) _
              (Q'.mul_assoc_eqv c a.2 _)
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.eqv_symm (Q'.mul_assoc_eqv a.2 b.2 _)))))
          (scaled_haarRow c a q)
      · exact Q'.eqv_symm (Q'.mul_add_eqv c _ _)

private theorem scaled_haarBilinear_left (c : Q') : ∀ p q : RatPoly,
    haarBilinear (polySmul c p) q ≈ c * haarBilinear p q
  | [], _ => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | a :: p, q => by
      change haarRow (a.1, c * a.2) q +
          haarBilinear (polySmul c p) q ≈
        c * (haarRow a q + haarBilinear p q)
      refine Q'.eqv_trans _
        (c * haarRow a q + c * haarBilinear p q) _
        (QPoly.q_add_congr (scaled_haarRow c a q)
          (scaled_haarBilinear_left c p q)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c _ _)

private theorem productHaar_polyMul_smul_left (c : Q') (p q : RatPoly) :
    productHaar (polyMul (polySmul c p) q) ≈
      c * productHaar (polyMul p q) := by
  refine Q'.eqv_trans _ (haarBilinear (polySmul c p) q) _
    (productHaar_polyMul_eq_bilinear _ _) ?_
  refine Q'.eqv_trans _ (c * haarBilinear p q) _
    (scaled_haarBilinear_left c p q) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (productHaar_polyMul_eq_bilinear p q))

theorem canonicalProductHaar_mul_smul_left (c : Q') (p q : Poly8) :
    canonicalProductHaar (polyMul8 (polySmul8 c p) q) ≈
      c * canonicalProductHaar (polyMul8 p q) := by
  unfold canonicalProductHaar
  rw [embedPoly8_mul, embedPoly8_mul, embedPoly8_smul]
  exact productHaar_polyMul_smul_left c _ _

theorem canonicalProductHaar_mul_smul_right (c : Q') (p q : Poly8) :
    canonicalProductHaar (polyMul8 p (polySmul8 c q)) ≈
      c * canonicalProductHaar (polyMul8 p q) := by
  refine Q'.eqv_trans _
    (canonicalProductHaar (polyMul8 (polySmul8 c q) p)) _
    (canonicalProductHaar_mul_comm p (polySmul8 c q)) ?_
  refine Q'.eqv_trans _
    (c * canonicalProductHaar (polyMul8 q p)) _
    (canonicalProductHaar_mul_smul_left c q p) ?_
  exact Q'.mul_eqv_congr_left c _ _
    (canonicalProductHaar_mul_comm q p)

end YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity.canonicalProductHaar_add
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity.canonicalProductHaar_mul_add_right
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity.canonicalProductHaar_mul_smul_right
