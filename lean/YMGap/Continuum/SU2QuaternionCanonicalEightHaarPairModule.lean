/-
# Haar-test quotient module for the canonical quaternion carrier

Two canonical polynomials are equivalent here when every exact product-Haar
pairing against a polynomial test agrees.  This relation is non-vacuous and,
unlike raw list equality, is stable under commutative addition and
multiplication.  It is also the relation directly consumed by the interacting
Wilson expectation.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity

namespace YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity
open YMGap.Continuum.WilsonGNS.WilsonGNSData

local infix:50 " ≈ " => Q'.eqv

/-- Equality against every exact Haar polynomial test. -/
def CanonicalHaarPairEqv (p q : Poly8) : Prop :=
  ∀ r, canonicalProductHaar (polyMul8 r p) ≈
    canonicalProductHaar (polyMul8 r q)

theorem canonicalProductHaar_mul_zero_right (r : Poly8) :
    canonicalProductHaar (polyMul8 r polyZero8) ≈ 0 := by
  have hz : polyMul8 r polyZero8 = polyZero8 := by
    simp [polyMul8, polyZero8]
  rw [hz]
  exact Q'.eqv_refl 0

private theorem neg_one_mul_eqv (x : Q') :
    (-(1 : Q')) * x ≈ -x := by
  refine Q'.eqv_trans _ (-(1 * x)) _ (Q'.neg_mul_eqv 1 x) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x)

/-- The exact Haar-test relation carries the algebra/module operations needed
by the Wilson GNS constructor.  Negation is scalar multiplication by `-1`, so
all quotient laws use the same derived homogeneous pairing identity. -/
def canonicalHaarPairModule :
    CarrierModule canonicalQuaternionPairAlg where
  veq := CanonicalHaarPairEqv
  veq_refl := fun p r => Q'.eqv_refl _
  veq_symm := fun h r => Q'.eqv_symm (h r)
  veq_trans := fun h₁ h₂ r => Q'.eqv_trans _ _ _ (h₁ r) (h₂ r)
  zero := polyZero8
  add := polyAdd8
  neg := polySmul8 (-(1 : Q'))
  smul := polySmul8
  add_congr := by
    intro a a' b b' ha hb r
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r a) +
        canonicalProductHaar (polyMul8 r b)) _
      (canonicalProductHaar_mul_add_right r a b) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r a') +
        canonicalProductHaar (polyMul8 r b')) _
      (QPoly.q_add_congr (ha r) (hb r)) ?_
    exact Q'.eqv_symm (canonicalProductHaar_mul_add_right r a' b')
  neg_congr := by
    intro a a' h r
    refine Q'.eqv_trans _
      ((-(1 : Q')) * canonicalProductHaar (polyMul8 r a)) _
      (canonicalProductHaar_mul_smul_right (-(1 : Q')) r a) ?_
    refine Q'.eqv_trans _
      ((-(1 : Q')) * canonicalProductHaar (polyMul8 r a')) _
      (Q'.mul_eqv_congr_left _ _ _ (h r)) ?_
    exact Q'.eqv_symm
      (canonicalProductHaar_mul_smul_right (-(1 : Q')) r a')
  smul_congr := by
    intro s a a' h r
    refine Q'.eqv_trans _
      (s * canonicalProductHaar (polyMul8 r a)) _
      (canonicalProductHaar_mul_smul_right s r a) ?_
    refine Q'.eqv_trans _
      (s * canonicalProductHaar (polyMul8 r a')) _
      (Q'.mul_eqv_congr_left s _ _ (h r)) ?_
    exact Q'.eqv_symm (canonicalProductHaar_mul_smul_right s r a')
  add_assoc := by
    intro a b c r
    change canonicalProductHaar
        (polyMul8 r (polyAdd8 (polyAdd8 a b) c)) ≈
      canonicalProductHaar
        (polyMul8 r (polyAdd8 a (polyAdd8 b c)))
    rw [polyAdd8, polyAdd8, List.append_assoc]
    exact Q'.eqv_refl _
  add_comm := by
    intro a b r
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r a) +
        canonicalProductHaar (polyMul8 r b)) _
      (canonicalProductHaar_mul_add_right r a b) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r b) +
        canonicalProductHaar (polyMul8 r a)) _
      (Q'.add_comm_eqv _ _) ?_
    exact Q'.eqv_symm (canonicalProductHaar_mul_add_right r b a)
  zero_add := by
    intro a r
    exact Q'.eqv_refl _
  neg_add := by
    intro a r
    refine Q'.eqv_trans _
      (canonicalProductHaar
          (polyMul8 r (polySmul8 (-(1 : Q')) a)) +
        canonicalProductHaar (polyMul8 r a)) _
      (canonicalProductHaar_mul_add_right r _ a) ?_
    refine Q'.eqv_trans _
      ((-(1 : Q')) * canonicalProductHaar (polyMul8 r a) +
        canonicalProductHaar (polyMul8 r a)) _
      (QPoly.q_add_congr
        (canonicalProductHaar_mul_smul_right (-(1 : Q')) r a)
        (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _
      (-canonicalProductHaar (polyMul8 r a) +
        canonicalProductHaar (polyMul8 r a)) _
      (QPoly.q_add_congr (neg_one_mul_eqv _) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.neg_add_self_eqv _) ?_
    exact Q'.eqv_symm (canonicalProductHaar_mul_zero_right r)
  mul_congr := by
    intro a a' b b' ha hb r
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r a) b)) _
      (Q'.eqv_symm (canonicalProductHaar_mul_assoc r a b)) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r a) b')) _
      (hb (polyMul8 r a)) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r (polyMul8 a b'))) _
      (canonicalProductHaar_mul_assoc r a b') ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r (polyMul8 b' a))) _
      (canonicalProductHaar_mul_middle_comm r a b') ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r b') a)) _
      (Q'.eqv_symm (canonicalProductHaar_mul_assoc r b' a)) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r b') a')) _
      (ha (polyMul8 r b')) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r (polyMul8 b' a'))) _
      (canonicalProductHaar_mul_assoc r b' a') ?_
    exact canonicalProductHaar_mul_middle_comm r b' a'
  star_congr := fun h => h
  star_add := by
    intro a b r
    exact Q'.eqv_refl _
  star_smul := by
    intro s a r
    exact Q'.eqv_refl _
  mul_add_right := by
    intro a b c r
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r (polyMul8 c (polyAdd8 a b)))) _
      (canonicalProductHaar_mul_middle_comm r (polyAdd8 a b) c) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r c) (polyAdd8 a b))) _
      (Q'.eqv_symm
        (canonicalProductHaar_mul_assoc r c (polyAdd8 a b))) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (polyMul8 r c) a) +
        canonicalProductHaar (polyMul8 (polyMul8 r c) b)) _
      (canonicalProductHaar_mul_add_right (polyMul8 r c) a b) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 r (polyMul8 a c)) +
        canonicalProductHaar (polyMul8 r (polyMul8 b c))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (Q'.eqv_trans _
          (canonicalProductHaar (polyMul8 r (polyMul8 c a))) _
          (canonicalProductHaar_mul_assoc r c a)
          (canonicalProductHaar_mul_middle_comm r c a))
        (Q'.eqv_trans _
          (canonicalProductHaar (polyMul8 r (polyMul8 c b))) _
          (canonicalProductHaar_mul_assoc r c b)
          (canonicalProductHaar_mul_middle_comm r c b))
    · exact Q'.eqv_symm
        (canonicalProductHaar_mul_add_right r (polyMul8 a c)
          (polyMul8 b c))
  smul_mul := by
    intro s a b r
    refine Q'.eqv_trans _
      (canonicalProductHaar
        (polyMul8 r (polyMul8 b (polySmul8 s a)))) _
      (canonicalProductHaar_mul_middle_comm r (polySmul8 s a) b) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar
        (polyMul8 (polyMul8 r b) (polySmul8 s a))) _
      (Q'.eqv_symm
        (canonicalProductHaar_mul_assoc r b (polySmul8 s a))) ?_
    refine Q'.eqv_trans _
      (s * canonicalProductHaar (polyMul8 (polyMul8 r b) a)) _
      (canonicalProductHaar_mul_smul_right s (polyMul8 r b) a) ?_
    refine Q'.eqv_trans _
      (s * canonicalProductHaar (polyMul8 r (polyMul8 b a))) _
      (Q'.mul_eqv_congr_left s _ _
        (canonicalProductHaar_mul_assoc r b a)) ?_
    refine Q'.eqv_trans _
      (s * canonicalProductHaar (polyMul8 r (polyMul8 a b))) _
      (Q'.mul_eqv_congr_left s _ _
        (canonicalProductHaar_mul_middle_comm r b a)) ?_
    exact Q'.eqv_symm
      (canonicalProductHaar_mul_smul_right s r (polyMul8 a b))

end YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule.CanonicalHaarPairEqv
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule.canonicalHaarPairModule
