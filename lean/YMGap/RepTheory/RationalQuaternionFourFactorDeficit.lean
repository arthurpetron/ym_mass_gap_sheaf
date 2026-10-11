/-
# Four-factor scalar deficit for actual rational unit quaternions

The literal squared chord to the identity is twice the scalar deficit.
Two balanced levels of the product estimate bound the deficit of a
four-factor Hamilton word by four times the sum of its factor deficits.
Semantic associativity supplies the stated left-associated word.  Factors
may themselves be unit-quaternion inverses; no commutation is used.

This is the finite quaternion estimate for a local-Casimir small-region
argument.  The adapter from a literal corrected-slab plaquette evaluation to
these four unit factors is not constructed here.  No original-action,
partition, entropy, or mass-gap estimate is asserted by this leaf.
-/

import YMGap.RepTheory.RationalQuaternionCauchyGroup

namespace YMGap.RepTheory.RationalQuaternionFourFactorDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private def v (i : Nat) : PE := .var i

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a+c ≈ b+d := Q'.eqv_trans _ _ _
  (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)

private theorem unit_refl (x : UnitNorm) : x.Equivalent x :=
  RationalQuaternion.semanticSetoid.iseqv.refl x.val

private theorem raw_chord_to_one (r i j k : Q') :
    ((r + -1)*(r + -1)+(i + -0)*(i + -0))+
      ((j + -0)*(j + -0)+(k + -0)*(k + -0)) ≈
      (((r*r+i*i)+(j*j+k*k))+1)+ -(2*r) :=
  poly_identity_of_normal_eq
    (((v 0 + -1)*(v 0 + -1)+(v 1 + -0)*(v 1 + -0))+
      ((v 2 + -0)*(v 2 + -0)+(v 3 + -0)*(v 3 + -0)))
    ((((v 0*v 0+v 1*v 1)+(v 2*v 2+v 3*v 3))+1)+ -(2*v 0))
    (by decide) (fun | 0 => r | 1 => i | 2 => j | _ => k)

private theorem two_deficit (r : Q') : (1+1)+ -(2*r) ≈ 2*(1 + -r) :=
  poly_identity_of_normal_eq ((1+1)+ -(2*v 0)) (2*(1 + -(v 0)))
    (by decide) (fun _ => r)

/-- The actual unit-norm relation converts squared chord to scalar deficit. -/
theorem chord_to_one (u : UnitNorm) :
    chord u unitOne ≈ 2*(1 + -u.val.r) := by
  have hraw : chord u unitOne ≈ (normSq u.val+1)+ -(2*u.val.r) :=
    raw_chord_to_one u.val.r u.val.i u.val.j u.val.k
  exact Q'.eqv_trans _ _ _ hraw (Q'.eqv_trans _ _ _
    (ac (ac u.unitNorm (Q'.eqv_refl 1)) (Q'.eqv_refl _))
    (two_deficit u.val.r))

private theorem repeated_pair (a b : Q') :
    (a+a)+(b+b) ≈ 2*(a+b) :=
  poly_identity_of_normal_eq ((v 0+v 0)+(v 1+v 1)) (2*(v 0+v 1))
    (by decide) (fun | 0 => a | _ => b)

private theorem pair_to_one (a b : UnitNorm) :
    chord (UnitNorm.mul a b) unitOne ≤
      2*(chord a unitOne+chord b unitOne) := by
  have hone := chord_congr (unit_refl (UnitNorm.mul a b))
    (UnitNorm.one_mul unitOne)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hone)
    (Q'.le_trans' _ _ _ (chord_product a unitOne b unitOne)
      (Q'.le_of_eqv (repeated_pair _ _)))

private theorem double_pairs (a b : Q') :
    2*(2*a+2*b) ≈ 4*(a+b) :=
  poly_identity_of_normal_eq (2*(2*v 0+2*v 1)) (4*(v 0+v 1))
    (by decide) (fun | 0 => a | _ => b)

/-- Balanced four-factor squared-chord bound on the original unit carrier. -/
theorem four_factor_chord (a b c d : UnitNorm) :
    chord (UnitNorm.mul (UnitNorm.mul a b) (UnitNorm.mul c d)) unitOne ≤
      4*((chord a unitOne+chord b unitOne)+
        (chord c unitOne+chord d unitOne)) := by
  have hp := Q'.add_le_add (pair_to_one a b) (pair_to_one c d)
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ 2 hp (by decide)
  exact Q'.le_trans' _ _ _ (pair_to_one (UnitNorm.mul a b) (UnitNorm.mul c d))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (double_pairs _ _)))

private theorem four_doubled (a b c d : Q') :
    4*((2*a+2*b)+(2*c+2*d)) ≈ 2*(4*((a+b)+(c+d))) :=
  poly_identity_of_normal_eq
    (4*((2*v 0+2*v 1)+(2*v 2+2*v 3)))
    (2*(4*((v 0+v 1)+(v 2+v 3))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

/-- Scalar deficit of the left-associated word, with the factor sum grouped
explicitly.  This also applies when any arguments are unit inverses. -/
theorem four_factor_deficit (a b c d : UnitNorm) :
    1 + -(UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r ≤
      4*(((1 + -a.val.r)+(1 + -b.val.r))+
        ((1 + -c.val.r)+(1 + -d.val.r))) := by
  let left := UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d
  have hassoc := chord_congr (UnitNorm.mul_assoc (UnitNorm.mul a b) c d)
    (unit_refl unitOne)
  have hleft := Q'.le_trans' _ _ _ (Q'.ge_of_eqv (chord_to_one left))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) (four_factor_chord a b c d))
  have hsum := ac (ac (chord_to_one a) (chord_to_one b))
    (ac (chord_to_one c) (chord_to_one d))
  have hscale := Q'.mul_eqv_congr_left 4 _ _ hsum
  have hright := Q'.eqv_trans _ _ _ hscale
    (four_doubled (1 + -a.val.r) (1 + -b.val.r)
      (1 + -c.val.r) (1 + -d.val.r))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hleft (Q'.le_of_eqv hright)) (by decide)

#print axioms chord_to_one
#print axioms four_factor_chord
#print axioms four_factor_deficit

end YMGap.RepTheory.RationalQuaternionFourFactorDeficit
