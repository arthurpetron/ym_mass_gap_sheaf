/-
# Literal sphere-ideal annihilation for quaternion product Haar

The radius descent theorem says multiplication by `r_g^2` or `r_h^2`
does not change the exact moment functional.  Here that equality is converted
into literal annihilation of the two polynomial generators `r_g^2 - 1` and
`r_h^2 - 1`, first termwise and then on every finite polynomial.
-/

import YMGap.Continuum.SU2QuaternionHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionHaarSphereIdealAnnihilation

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 100000
set_option maxRecDepth 10000

/-- The literal first-sphere generator `g_0^2+⋯+g_3^2-1`. -/
def gSphereIdealGenerator : RatPoly :=
  [([2], 1), ([0, 2], 1), ([0, 0, 2], 1), ([0, 0, 0, 2], 1),
    ([], -1)]

/-- The literal second-sphere generator `h_0^2+⋯+h_3^2-1`. -/
def hSphereIdealGenerator : RatPoly :=
  [([0, 0, 0, 0, 2], 1), ([0, 0, 0, 0, 0, 2], 1),
    ([0, 0, 0, 0, 0, 0, 2], 1), ([0, 0, 0, 0, 0, 0, 0, 2], 1),
    ([], -1)]

private theorem monoMul_nil_right (m : List Nat) : monoMul m [] = m := by
  cases m <;> rfl

private theorem four_plus_tail (a b c d n : Q') :
    a + (b + (c + (d + n))) ≈ (a + (b + (c + d))) + n := by
  have hcdn : c + (d + n) ≈ (c + d) + n :=
    Q'.eqv_symm (Q'.add_assoc_eqv c d n)
  have hbcdn : b + (c + (d + n)) ≈ (b + (c + d)) + n :=
    Q'.eqv_trans _ (b + ((c + d) + n)) _
      (Q'.add_eqv_congr_left _ _ _ hcdn)
      (Q'.eqv_symm (Q'.add_assoc_eqv b (c + d) n))
  exact Q'.eqv_trans _ (a + ((b + (c + d)) + n)) _
    (Q'.add_eqv_congr_left _ _ _ hbcdn)
    (Q'.eqv_symm (Q'.add_assoc_eqv a (b + (c + d)) n))

private theorem four_left_factor (h a b c d : Q') :
    h * a + (h * b + (h * c + h * d)) ≈
      h * (a + (b + (c + d))) := by
  have hcd : h * c + h * d ≈ h * (c + d) :=
    Q'.eqv_symm (Q'.mul_add_eqv h c d)
  have hbcd : h * b + (h * c + h * d) ≈
      h * (b + (c + d)) :=
    Q'.eqv_trans _ (h * b + h * (c + d)) _
      (Q'.add_eqv_congr_left _ _ _ hcd)
      (Q'.eqv_symm (Q'.mul_add_eqv h b (c + d)))
  exact Q'.eqv_trans _ (h * a + h * (b + (c + d))) _
    (Q'.add_eqv_congr_left _ _ _ hbcd)
    (Q'.eqv_symm (Q'.mul_add_eqv h a (b + (c + d))))

private theorem scaled_four_radius (q a b c d z : Q')
    (hradius : a + (b + (c + d)) ≈ z) :
    (q * 1) * a + ((q * 1) * b + ((q * 1) * c + (q * 1) * d)) ≈
      q * z := by
  have hq : q * 1 ≈ q := Q'.mul_one_eqv q
  refine Q'.eqv_trans _ (q * a + (q * b + (q * c + q * d))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ hq)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hq)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ hq)
          (Q'.mul_eqv_congr_right _ _ _ hq)))
  · exact Q'.eqv_trans _ (q * (a + (b + (c + d)))) _
      (four_left_factor _ _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ hradius)

private theorem scaled_radius_generator_zero (q a b c d z : Q')
    (hradius : a + (b + (c + d)) ≈ z) :
    (q * 1) * a +
      ((q * 1) * b +
        ((q * 1) * c + ((q * 1) * d + (q * (-1)) * z))) ≈ 0 := by
  have hpos := scaled_four_radius q a b c d z hradius
  have hnegCoeff : q * (-1) ≈ -q := by
    exact Q'.eqv_trans _ (-(q * 1)) _
      (Q'.mul_neg_eqv q 1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv q))
  have hnegTerm : (q * (-1)) * z ≈ -(q * z) := by
    exact Q'.eqv_trans _ ((-q) * z) _
      (Q'.mul_eqv_congr_right _ _ _ hnegCoeff)
      (Q'.neg_mul_eqv q z)
  refine Q'.eqv_trans _
    (((q * 1) * a +
      ((q * 1) * b + ((q * 1) * c + (q * 1) * d))) +
        (q * (-1)) * z) _ (four_plus_tail _ _ _ _ _) ?_
  refine Q'.eqv_trans _ (q * z + (q * (-1)) * z) _
    (Q'.add_eqv_congr_right _ _ _ hpos) ?_
  refine Q'.eqv_trans _ (q * z + -(q * z)) _
    (Q'.add_eqv_congr_left _ _ _ hnegTerm) ?_
  exact Q'.eqv_trans _ (-(q * z) + q * z) _
    (Q'.add_comm_eqv _ _) (Q'.neg_add_self_eqv _)

private theorem productHaar_gGenerator_single (m : List Nat) (q : Q') :
    productHaar (polyMul [(m, q)] gSphereIdealGenerator) ≈ 0 := by
  refine Q'.eqv_trans _
    (productHaarLinearSum (polyMul [(m, q)] gSphereIdealGenerator)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) * productHaarMono (monoMul m [2]) +
      ((q * 1) * productHaarMono (monoMul m [0, 2]) +
        ((q * 1) * productHaarMono (monoMul m [0, 0, 2]) +
          ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 2]) +
            ((q * (-1)) * productHaarMono (monoMul m []) + 0)))) ≈ 0
  rw [monoMul_nil_right]
  rw [Q'.add_zero']
  exact scaled_radius_generator_zero _ _ _ _ _ _
    (productHaarMono_mul_gRadius m)

private theorem productHaar_hGenerator_single (m : List Nat) (q : Q') :
    productHaar (polyMul [(m, q)] hSphereIdealGenerator) ≈ 0 := by
  refine Q'.eqv_trans _
    (productHaarLinearSum (polyMul [(m, q)] hSphereIdealGenerator)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 2]) +
      ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 0, 2]) +
        ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 2]) +
          ((q * 1) *
              productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 0, 2]) +
            ((q * (-1)) * productHaarMono (monoMul m []) + 0)))) ≈ 0
  rw [monoMul_nil_right]
  rw [Q'.add_zero']
  exact scaled_radius_generator_zero _ _ _ _ _ _
    (productHaarMono_mul_hRadius m)

/-- The exact product-Haar functional kills every multiple of the first
sphere equation. -/
theorem productHaar_gSphereIdeal_annihilation : ∀ p : RatPoly,
    productHaar (polyMul p gSphereIdealGenerator) ≈ 0
  | [] => Q'.eqv_refl 0
  | t :: p => by
      have hmul :
          polyMul (t :: p) gSphereIdealGenerator =
            polyMul [t] gSphereIdealGenerator ++
              polyMul p gSphereIdealGenerator := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [t] gSphereIdealGenerator) +
          productHaar (polyMul p gSphereIdealGenerator)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (productHaar_gGenerator_single t.1 t.2)
          (productHaar_gSphereIdeal_annihilation p)) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- The exact product-Haar functional kills every multiple of the second
sphere equation. -/
theorem productHaar_hSphereIdeal_annihilation : ∀ p : RatPoly,
    productHaar (polyMul p hSphereIdealGenerator) ≈ 0
  | [] => Q'.eqv_refl 0
  | t :: p => by
      have hmul :
          polyMul (t :: p) hSphereIdealGenerator =
            polyMul [t] hSphereIdealGenerator ++
              polyMul p hSphereIdealGenerator := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [t] hSphereIdealGenerator) +
          productHaar (polyMul p hSphereIdealGenerator)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (productHaar_hGenerator_single t.1 t.2)
          (productHaar_hSphereIdeal_annihilation p)) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

end YMGap.Continuum.SU2QuaternionHaarSphereIdealAnnihilation

#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdealAnnihilation.productHaar_gSphereIdeal_annihilation
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdealAnnihilation.productHaar_hSphereIdeal_annihilation
