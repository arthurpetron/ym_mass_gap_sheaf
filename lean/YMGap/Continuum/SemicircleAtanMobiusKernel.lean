/-
# Exact Möbius kernels for the rational atan change of variables

This module isolates the pointwise algebra behind tangent addition.  For

    phi_r(x) = (r+x)/(1-rx),

it proves the exact divided-difference identity and the cleared transformed
left/right rectangle identities for the kernel `2/(1+x^2)`.  These are the
finite rational atoms needed to compare a uniform Riemann sum on `[0,t]`
with the induced nonuniform sum on `[r,phi_r(t)]`.
-/

import YMGap.Continuum.SemicircleAtanRationalEndpoint
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SemicircleAtanMobiusKernel

open YMGap.Constructive

def mobiusDen (r x : Q') : Q' := (1 : Q') + -(r*x)

def mobius (r x : Q') (hden : (0 : Q') < mobiusDen r x) : Q' :=
  Q'.divPos (r+x) (mobiusDen r x) hden

theorem mobius_mul_den (r x : Q') (hden : (0 : Q') < mobiusDen r x) :
    (mobius r x hden * mobiusDen r x).eqv (r+x) :=
  Q'.divPos_mul_eqv _ _ hden

theorem mobius_kernel_cleared (r x : Q')
    (hden : (0 : Q') < mobiusDen r x) :
    (((1 : Q') + mobius r x hden * mobius r x hden) *
        (mobiusDen r x * mobiusDen r x)).eqv
      (((1 : Q') + r*r) * ((1 : Q') + x*x)) := by
  exact YMGap.Continuum.SemicircleAtanMachinPath.tanAdd_kernel_cleared r x hden

private def diffShuffleL : RingNormaliser.PolyExpr :=
  .mul (.add (.var 1) (.neg (.var 0))) (.mul (.var 2) (.var 3))

private def diffShuffleR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.mul (.var 1) (.var 3)) (.var 2))
    (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3)))

private theorem diffShuffle_normal :
    RingNormaliser.normalize diffShuffleL =
      RingNormaliser.normalize diffShuffleR := by decide

private theorem diff_shuffle (X Y A B : Q') :
    ((Y + -X) * (A*B)).eqv ((Y*B)*A + -((X*A)*B)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    diffShuffleL diffShuffleR diffShuffle_normal
    (fun
      | 0 => X
      | 1 => Y
      | 2 => A
      | _ => B)
  simpa [diffShuffleL, diffShuffleR, RingNormaliser.eval] using h

private def shuffleAL : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))

private def shuffleAR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 1) (.var 3))
    (.mul (.var 2) (.mul (.var 0) (.var 4)))

private def shuffleARevR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 1) (.var 3))
    (.mul (.var 2) (.mul (.var 4) (.var 0)))

private theorem shuffleA_normal :
    RingNormaliser.normalize shuffleAL =
      RingNormaliser.normalize shuffleAR := by decide

private theorem shuffleARev_normal :
    RingNormaliser.normalize shuffleAL =
      RingNormaliser.normalize shuffleARevR := by decide

private theorem shuffleA (a b c d e : Q') :
    (a * ((b*c)*(d*e))).eqv ((b*d)*(c*(a*e))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    shuffleAL shuffleAR shuffleA_normal
    (fun
      | 0 => a
      | 1 => b
      | 2 => c
      | 3 => d
      | _ => e)
  simpa [shuffleAL, shuffleAR, RingNormaliser.eval] using h

private theorem shuffleARev (a b c d e : Q') :
    (a * ((b*c)*(d*e))).eqv ((b*d)*(c*(e*a))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    shuffleAL shuffleARevR shuffleARev_normal
    (fun
      | 0 => a
      | 1 => b
      | 2 => c
      | 3 => d
      | _ => e)
  simpa [shuffleAL, shuffleARevR, RingNormaliser.eval] using h

private def shuffleBL : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 4))

private def shuffleBR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 1) (.var 2))
    (.mul (.var 4) (.mul (.var 0) (.var 3)))

private theorem shuffleB_normal :
    RingNormaliser.normalize shuffleBL =
      RingNormaliser.normalize shuffleBR := by decide

private theorem shuffleB (a b c d e : Q') :
    (a * (((b*c)*d)*e)).eqv ((b*c)*(e*(a*d))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    shuffleBL shuffleBR shuffleB_normal
    (fun
      | 0 => a
      | 1 => b
      | 2 => c
      | 3 => d
      | _ => e)
  simpa [shuffleBL, shuffleBR, RingNormaliser.eval] using h

private def shuffleCL : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))

private def shuffleCR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))

private theorem shuffleC_normal :
    RingNormaliser.normalize shuffleCL =
      RingNormaliser.normalize shuffleCR := by decide

private theorem shuffleC (a b c d : Q') :
    ((a*b)*(c*d)).eqv ((a*d)*(c*b)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    shuffleCL shuffleCR shuffleC_normal
    (fun
      | 0 => a
      | 1 => b
      | 2 => c
      | _ => d)
  simpa [shuffleCL, shuffleCR, RingNormaliser.eval] using h

private theorem diff_rearrange (r x y X Y : Q') :
    ((Y + -X) * (mobiusDen r x * mobiusDen r y)).eqv
      ((Y * mobiusDen r y) * mobiusDen r x +
        -((X * mobiusDen r x) * mobiusDen r y)) := by
  exact diff_shuffle X Y (mobiusDen r x) (mobiusDen r y)

private def diffNumeratorL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 2))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))))
    (.neg
      (.mul (.add (.var 0) (.var 1))
        (.add (.const 1) (.neg (.mul (.var 0) (.var 2))))))

private def diffNumeratorR : RingNormaliser.PolyExpr :=
  .mul
    (.add (.const 1) (.mul (.var 0) (.var 0)))
    (.add (.var 2) (.neg (.var 1)))

private theorem diffNumerator_normal :
    RingNormaliser.normalize diffNumeratorL =
      RingNormaliser.normalize diffNumeratorR := by decide

private theorem diff_numerator_identity (r x y : Q') :
    (((r+y) * mobiusDen r x) + -((r+x) * mobiusDen r y)).eqv
      (((1 : Q') + r*r) * (y + -x)) := by
  unfold mobiusDen
  have h := RingNormaliser.poly_identity_of_normal_eq
    diffNumeratorL diffNumeratorR diffNumerator_normal
    (fun
      | 0 => r
      | 1 => x
      | _ => y)
  simpa [diffNumeratorL, diffNumeratorR, RingNormaliser.eval] using h

/-- Exact rational divided difference of the tangent-addition Möbius map. -/
theorem mobius_diff_cleared (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x)
    (hy : (0 : Q') < mobiusDen r y) :
    ((mobius r y hy + -mobius r x hx) *
        (mobiusDen r x * mobiusDen r y)).eqv
      (((1 : Q') + r*r) * (y + -x)) := by
  refine Q'.eqv_trans _ _ _
    (diff_rearrange r x y (mobius r x hx) (mobius r y hy)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ (mobiusDen r x)
        (mobius_mul_den r y hy))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ (mobiusDen r y)
          (mobius_mul_den r x hx)))) ?_
  exact diff_numerator_identity r x y

private theorem scaled_left_rearrange
    (r x y X Y : Q') :
    (mobiusDen r x *
      ((2 * (Y + -X)) * (((1 : Q') + x*x) * mobiusDen r y))).eqv
      ((2 * ((1 : Q') + x*x)) *
        ((Y + -X) * (mobiusDen r x * mobiusDen r y))) := by
  exact shuffleA (mobiusDen r x) 2 (Y + -X)
    ((1 : Q') + x*x) (mobiusDen r y)

private theorem scaled_left_target_rearrange
    (r x y X : Q') :
    (mobiusDen r x *
      ((2 * (y + -x) * mobiusDen r x) * ((1 : Q') + X*X))).eqv
      ((2 * (y + -x)) *
        (((1 : Q') + X*X) * (mobiusDen r x * mobiusDen r x))) := by
  exact shuffleB (mobiusDen r x) 2 (y + -x)
    (mobiusDen r x) ((1 : Q') + X*X)

private theorem scaled_left_middle_rearrange (r x y : Q') :
    ((2 * ((1 : Q') + x*x)) *
        (((1 : Q') + r*r) * (y + -x))).eqv
      ((2 * (y + -x)) *
        (((1 : Q') + r*r) * ((1 : Q') + x*x))) := by
  exact shuffleC 2 ((1 : Q') + x*x) ((1 : Q') + r*r) (y + -x)

/-- Cleared left-rectangle substitution identity:

`2 (phi(y)-phi(x))/(1+phi(x)^2)
   = [2(y-x)/(1+x^2)] * (1-rx)/(1-ry)`.

The theorem keeps all denominators cleared, which is the form consumed by
the rational Darboux comparison. -/
theorem mobius_left_rectangle_cleared (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x)
    (hy : (0 : Q') < mobiusDen r y) :
    ((2 * (mobius r y hy + -mobius r x hx)) *
        (((1 : Q') + x*x) * mobiusDen r y)).eqv
      ((2 * (y + -x) * mobiusDen r x) *
        ((1 : Q') + mobius r x hx * mobius r x hx)) := by
  apply Q'.mul_left_cancel_of_pos hx
  refine Q'.eqv_trans _ _ _
    (scaled_left_rearrange r x y (mobius r x hx) (mobius r y hy)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (2 * ((1 : Q') + x*x)) _ _
      (mobius_diff_cleared r x y hx hy)) ?_
  refine Q'.eqv_trans _ _ _ (scaled_left_middle_rearrange r x y) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (2 * (y + -x)) _ _
      (Q'.eqv_symm (mobius_kernel_cleared r x hx))) ?_
  exact Q'.eqv_symm
    (scaled_left_target_rearrange r x y (mobius r x hx))

private theorem scaled_right_rearrange
    (r x y X Y : Q') :
    (mobiusDen r y *
      ((2 * (Y + -X)) * (((1 : Q') + y*y) * mobiusDen r x))).eqv
      ((2 * ((1 : Q') + y*y)) *
        ((Y + -X) * (mobiusDen r x * mobiusDen r y))) := by
  exact shuffleARev (mobiusDen r y) 2 (Y + -X)
    ((1 : Q') + y*y) (mobiusDen r x)

private theorem scaled_right_target_rearrange
    (r x y Y : Q') :
    (mobiusDen r y *
      ((2 * (y + -x) * mobiusDen r y) * ((1 : Q') + Y*Y))).eqv
      ((2 * (y + -x)) *
        (((1 : Q') + Y*Y) * (mobiusDen r y * mobiusDen r y))) := by
  exact shuffleB (mobiusDen r y) 2 (y + -x)
    (mobiusDen r y) ((1 : Q') + Y*Y)

private theorem scaled_right_middle_rearrange (r x y : Q') :
    ((2 * ((1 : Q') + y*y)) *
        (((1 : Q') + r*r) * (y + -x))).eqv
      ((2 * (y + -x)) *
        (((1 : Q') + r*r) * ((1 : Q') + y*y))) := by
  exact shuffleC 2 ((1 : Q') + y*y) ((1 : Q') + r*r) (y + -x)

/-- The symmetric cleared right-rectangle substitution identity. -/
theorem mobius_right_rectangle_cleared (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x)
    (hy : (0 : Q') < mobiusDen r y) :
    ((2 * (mobius r y hy + -mobius r x hx)) *
        (((1 : Q') + y*y) * mobiusDen r x)).eqv
      ((2 * (y + -x) * mobiusDen r y) *
        ((1 : Q') + mobius r y hy * mobius r y hy)) := by
  apply Q'.mul_left_cancel_of_pos hy
  refine Q'.eqv_trans _ _ _
    (scaled_right_rearrange r x y (mobius r x hx) (mobius r y hy)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (2 * ((1 : Q') + y*y)) _ _
      (mobius_diff_cleared r x y hx hy)) ?_
  refine Q'.eqv_trans _ _ _ (scaled_right_middle_rearrange r x y) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (2 * (y + -x)) _ _
      (Q'.eqv_symm (mobius_kernel_cleared r y hy))) ?_
  exact Q'.eqv_symm
    (scaled_right_target_rearrange r x y (mobius r y hy))

end YMGap.Continuum.SemicircleAtanMobiusKernel

#print axioms YMGap.Continuum.SemicircleAtanMobiusKernel.mobius_diff_cleared
#print axioms YMGap.Continuum.SemicircleAtanMobiusKernel.mobius_left_rectangle_cleared
#print axioms YMGap.Continuum.SemicircleAtanMobiusKernel.mobius_right_rectangle_cleared
