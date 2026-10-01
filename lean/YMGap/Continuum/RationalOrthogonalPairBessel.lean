/-
# Sharp rational Bessel bound for an orthogonal equal-norm pair

This is an algebraic consequence of a rational positive pre-inner form and
literal linear operations on its carrier. The phase vector is made with the
two rational pairings themselves. No quotient-real representative, inverse
norm, or nonzero-norm decision is needed.
-/

import YMGap.Continuum.OSReconstructionProgress
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.RationalOrthogonalPairBessel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem q_lt_of_not_ge {a b : Q'} (h : ¬ b ≤ a) : a < b :=
  Int.not_le.mp h

variable {V : Type} (F : PreInnerForm V)
  (add : V → V → V) (smul : Q' → V → V)
  (pair_add_right : ∀ x y z : V,
    F.B x (add y z) ≈ F.B x y + F.B x z)
  (pair_smul_right : ∀ (c : Q') (x y : V),
    F.B x (smul c y) ≈ c * F.B x y)
  (pair_symm : ∀ x y : V, F.B x y ≈ F.B y x)

include pair_add_right pair_symm in
private theorem pair_add_left (x y z : V) :
    F.B (add x y) z ≈ F.B x z + F.B y z :=
  Q'.eqv_trans _ _ _ (pair_symm _ _)
    (Q'.eqv_trans _ _ _ (pair_add_right _ _ _)
      (Q'.add_eqv_congr' (pair_symm _ _) (pair_symm _ _)))

include pair_smul_right pair_symm in
private theorem pair_smul_left (c : Q') (x y : V) :
    F.B (smul c x) y ≈ c * F.B x y :=
  Q'.eqv_trans _ _ _ (pair_symm _ _)
    (Q'.eqv_trans _ _ _ (pair_smul_right c _ _)
      (Q'.mul_eqv_congr_left c _ _ (pair_symm _ _)))

/-- The phase-aligned rational test for two orthogonal directions. -/
def phaseVector (x y z : V) : V :=
  add (smul (F.B x y) y) (smul (F.B x z) z)

include pair_add_right pair_smul_right in
private theorem phase_pairing (x y z : V) :
    F.B x (phaseVector F add smul x y z) ≈
      F.B x y * F.B x y + F.B x z * F.B x z := by
  unfold phaseVector
  exact Q'.eqv_trans _ _ _ (pair_add_right _ _ _)
    (Q'.add_eqv_congr'
      (pair_smul_right (F.B x y) x y)
      (pair_smul_right (F.B x z) x z))

include pair_add_right pair_smul_right pair_symm in
private theorem phase_norm (x y z : V)
    (horth : F.B y z ≈ 0) (hnorm : F.B z z ≈ F.B y y) :
    F.B (phaseVector F add smul x y z)
        (phaseVector F add smul x y z) ≈
      (F.B x y * F.B x y + F.B x z * F.B x z) * F.B y y := by
  let a := F.B x y
  let b := F.B x z
  let C := F.B y y
  let ay := smul a y
  let bz := smul b z
  have haa : F.B ay ay ≈ a*a*C := by
    exact Q'.eqv_trans _ _ _
      (pair_smul_left F smul pair_smul_right pair_symm a y ay)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a _ _ (pair_smul_right a y y))
        (Q'.eqv_symm (Q'.mul_assoc_eqv a a C)))
  have hab : F.B ay bz ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (pair_smul_left F smul pair_smul_right pair_symm a y bz) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (pair_smul_right b y z)) ?_
    refine Q'.eqv_trans _ ((a*b)*F.B y z) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv a b (F.B y z))) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a*b) _ _ horth)
      (QPoly.q_mul_zero (a*b))
  have hbb : F.B bz bz ≈ b*b*C := by
    refine Q'.eqv_trans _ _ _
      (pair_smul_left F smul pair_smul_right pair_symm b z bz) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left b _ _ (pair_smul_right b z z)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b b (F.B z z))) ?_
    exact Q'.mul_eqv_congr_left (b*b) _ _ hnorm
  unfold phaseVector
  refine Q'.eqv_trans _ _ _
    (pair_add_left F add pair_add_right pair_symm ay bz
      (add ay bz)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (pair_add_right ay ay bz)
      (pair_add_right bz ay bz)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' haa hab)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (pair_symm bz ay) hab)
        hbb)) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.const 0))
      (.add (.const 0) (.mul (.mul (.var 1) (.var 1)) (.var 2))))
    (.mul
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.var 2))
    (by decide) (fun | 0 => a | 1 => b | _ => C)

include add smul pair_add_right pair_smul_right pair_symm in
/-- Sharp two-vector Bessel inequality for an orthogonal equal-norm pair.
It remains valid when the common norm or both pairings vanish. -/
theorem orthogonal_pair_bessel (x y z : V)
    (horth : F.B y z ≈ 0) (hnorm : F.B z z ≈ F.B y y) :
    F.B x y * F.B x y + F.B x z * F.B x z ≤
      F.B x x * F.B y y := by
  let L := F.B x y * F.B x y + F.B x z * F.B x z
  by_cases hLnonpos : L ≤ (0 : Q')
  · have hXY : (0 : Q') ≤ F.B x x * F.B y y :=
      Q'.mul_nonneg _ _ (F.self_nonneg x) (F.self_nonneg y)
    exact Q'.le_trans' _ _ _ hLnonpos hXY
  · have hLpos : (0 : Q') < L := q_lt_of_not_ge hLnonpos
    have hcs := F.cauchy_schwarz x
      (phaseVector F add smul x y z)
    have hscaled : L*L ≤ L*(F.B x x * F.B y y) := by
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (phase_pairing F add smul pair_add_right pair_smul_right x y z))
          (Q'.mul_eqv_congr_left _ _ _
            (phase_pairing F add smul pair_add_right pair_smul_right x y z))))
        (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (F.B x x) _ _
              (phase_norm F add smul pair_add_right pair_smul_right pair_symm
                x y z horth hnorm))
            (poly_identity_of_normal_eq
              (.mul (.var 0) (.mul (.var 1) (.var 2)))
              (.mul (.var 1) (.mul (.var 0) (.var 2)))
              (by decide)
              (fun | 0 => F.B x x | 1 => L | _ => F.B y y)))))
    exact Q'.le_of_mul_le_mul_left hscaled hLpos

end YMGap.Continuum.RationalOrthogonalPairBessel

#print axioms YMGap.Continuum.RationalOrthogonalPairBessel.phaseVector
#print axioms YMGap.Continuum.RationalOrthogonalPairBessel.orthogonal_pair_bessel
