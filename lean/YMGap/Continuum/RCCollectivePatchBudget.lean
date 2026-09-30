/-
# Collective patch budgets without taking absolute values of cross terms

The patch square is D+C, the global signed part is E+C, and D is the
incidence-weighted diagonal. The SAME C cancels. This elementary order
argument consumes a patch lower bound; it does not construct one.
-/

import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.RCCollectivePatchBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

private theorem upper_rearrange (d : Q') (E C : RC) :
    RCadd (RCscale d E) C =
      RCadd (RCadd E C) (RCscale (d + -(1 : Q')) E) := by
  refine Quotient.inductionOn₂ E C ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 1) (.var 2))
        (.mul (.add (.var 0) (.neg (.const 1))) (.var 1))) (by decide)
      (fun | 0 => d | 1 => X.approx n | _ => Y.approx n)))

/-- An incidence cap bounds the aggregate of patch squares by the original
global square plus its exact diagonal correction. Cross terms stay signed. -/
theorem patch_square_upper (d : Q') (E D C A H : RC)
    (hpatch : A = RCadd D C) (hdiag : RCle D (RCscale d E))
    (hglobal : RCle (RCadd E C) H) :
    RCle A (RCadd H (RCscale (d + -(1 : Q')) E)) := by
  rw [hpatch]
  have h := RCadd_le_add hdiag (RCle_refl C)
  rw [upper_rearrange] at h
  exact RCle_trans h (RCadd_le_add hglobal (RCle_refl _))

private theorem subtract_diag (g : Q') (D : RC) :
    RCsub (RCscale g D) D = RCneg (RCscale ((1 : Q') + -g) D) := by
  refine Quotient.inductionOn D ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.var 1)))
      (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))) (by decide)
      (fun | 0 => g | _ => X.approx n)))

private theorem subtract_cancel (D C : RC) : RCsub (RCadd D C) D = C := by
  refine Quotient.inductionOn₂ D C ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => X.approx n | _ => Y.approx n)))

private theorem margin_rearrange (d g : Q') (E : RC) :
    RCadd E (RCneg (RCscale ((1 : Q') + -g) (RCscale d E))) =
      RCscale ((1 : Q') + -(d * ((1 : Q') + -g))) E := by
  refine Quotient.inductionOn E ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 2) (.neg (.mul (.add (.const 1) (.neg (.var 1)))
        (.mul (.var 0) (.var 2)))))
      (.mul (.add (.const 1) (.neg (.mul (.var 0)
        (.add (.const 1) (.neg (.var 1)))))) (.var 2)) (by decide)
      (fun | 0 => d | 1 => g | _ => X.approx n)))

/-- A collective patch lower bound leaves the margin 1-d*(1-g). This is
conditional on the actual patch estimate, not an assumed global gap. -/
theorem generator_lower (d g : Q') (hg : g ≤ (1 : Q'))
    (E D C A H : RC) (hpatch : A = RCadd D C)
    (hdiag : RCle D (RCscale d E)) (hglobal : RCle (RCadd E C) H)
    (hlower : RCle (RCscale g D) A) :
    RCle (RCscale ((1 : Q') + -(d * ((1 : Q') + -g))) E) H := by
  have hc := RCadd_le_add hlower (RCle_refl (RCneg D))
  change RCle (RCsub (RCscale g D) D) (RCsub A D) at hc
  rw [hpatch, subtract_diag, subtract_cancel] at hc
  have hdefect : (0 : Q') ≤ (1 : Q') + -g := Q'.sub_nonneg_of_le hg
  have hpay := neg_mono (RCscale_mono hdefect hdiag)
  have h := RCadd_le_add (RCle_refl E) (RCle_trans hpay hc)
  rw [margin_rearrange] at h
  exact RCle_trans h hglobal

#print axioms patch_square_upper
#print axioms generator_lower

end YMGap.Continuum.RCCollectivePatchBudget
