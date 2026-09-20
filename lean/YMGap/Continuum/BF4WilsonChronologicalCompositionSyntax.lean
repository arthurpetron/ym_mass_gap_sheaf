/-
# Syntax for composing bounded chronological Wilson programs

Composition replaces the identity-like vacuum leaves of the first program by
the second program.  Dagger reverses the primitive time-zero/time factors.
These are only syntax and cap identities; action semantics are proved in the
operator layer.
-/

import YMGap.Continuum.BF4WilsonChronologicalOperator

namespace YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound characterBound)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

def compose {base : Nat} : Program base → Program base → Program base
  | .vacuum, q => q
  | .zero, _ => .zero
  | .add p r, q => .add (compose p q) (compose r q)
  | .smul c p, q => .smul c (compose p q)
  | .time n p, q => .time n (compose p q)
  | .multiply L spin p, q => .multiply L spin (compose p q)

def dagger {base : Nat} : Program base → Program base
  | .vacuum => .vacuum
  | .zero => .zero
  | .add p q => .add (dagger p) (dagger q)
  | .smul c p => .smul c (dagger p)
  | .time n p => compose (dagger p) (.time n .vacuum)
  | .multiply L spin p => compose (dagger p) (.multiply L spin .vacuum)

private theorem sumBound_mul (a b c : Q') :
    Q'.eqv (sumBound a b * c) (sumBound (a*c) (b*c)) :=
  poly_identity_of_normal_eq
    (.mul (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1))) (.var 2))
    (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
      (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))) (by decide)
    (fun i => if i = 0 then a else if i = 1 then b else c)

theorem squaredCap_compose {base : Nat} (p q : Program base) :
    Q'.eqv (squaredCap (compose p q)) (squaredCap p * squaredCap q) := by
  induction p generalizing q with
  | vacuum => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | zero => exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | add p r hp hr =>
      simp only [compose, squaredCap]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (hp q) (hp q)) (Q'.add_eqv_congr' (hr q) (hr q)))
        (Q'.eqv_symm (sumBound_mul _ _ _))
  | smul c p hp =>
      simp only [compose, squaredCap]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hp q))
        (Q'.eqv_symm (Q'.mul_assoc_eqv (c*c) (squaredCap p) (squaredCap q)))
  | time n p hp =>
      simp only [compose, squaredCap]
      exact hp q
  | multiply L spin p hp =>
      simp only [compose, squaredCap]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hp q))
        (Q'.eqv_symm (Q'.mul_assoc_eqv (characterBound spin)
          (squaredCap p) (squaredCap q)))

theorem squaredCap_dagger {base : Nat} (p : Program base) :
    Q'.eqv (squaredCap (dagger p)) (squaredCap p) := by
  induction p with
  | vacuum => exact Q'.eqv_refl _
  | zero => exact Q'.eqv_refl _
  | add p q hp hq =>
      simp only [dagger, squaredCap]
      exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hp hp) (Q'.add_eqv_congr' hq hq)
  | smul c p hp =>
      simp only [dagger, squaredCap]
      exact Q'.mul_eqv_congr_left _ _ _ hp
  | time n p hp =>
      simp only [dagger]
      exact Q'.eqv_trans _ _ _ (squaredCap_compose _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hp)
  | multiply L spin p hp =>
      simp only [dagger]
      exact Q'.eqv_trans _ _ _ (squaredCap_compose _ _)
        (Q'.eqv_trans _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hp)
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv (characterBound spin))))
          (Q'.mul_comm_eqv _ _))

#print axioms compose
#print axioms dagger
#print axioms squaredCap_compose
#print axioms squaredCap_dagger

end YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax
