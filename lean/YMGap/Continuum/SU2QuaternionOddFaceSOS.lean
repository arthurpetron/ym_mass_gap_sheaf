/-
# Quaternion sum of squares for the odd SU(2) face channels

The odd Chebyshev half-angle identity is

    1 + T_{2k+1}(x) ≃ (1+x) C_k(x)^2.

On the rational unit three-sphere

    x^2 + y1^2 + y2^2 + y3^2 ≃ 1,

the remaining factor has the literal four-square decomposition

    2(1+x) ≃ (1+x)^2 + y1^2 + y2^2 + y3^2.

Multiplying these two identities gives an all-order, square-root-free SOS
certificate for every odd character channel.  The final section sums those
pointwise certificates and combines them with the odd Chebyshev telescope.
All additions in the public statements use the fixed left association shown
there, so downstream product-Haar code can consume the certificate directly.

# Axiom gate

No `Classical`, no choice, no `sorry`/`admit`, no custom axiom, and no
`native_decide`.
-/

import YMGap.Continuum.ChebOddFaceSOS

namespace YMGap.Continuum.SU2QuaternionOddFaceSOS

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOddFaceSOS
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-! ## Reflected polynomial kernels

The four identities below require distributivity as well as reassociation.
They are therefore discharged through the proved constructive ring normaliser
rather than by expanding the numerator/denominator representation of `Q'`.
-/

private def psq (a : PolyExpr) : PolyExpr := .mul a a

private def quaternionExpansionLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let y1 : PolyExpr := .var 1
  let y2 : PolyExpr := .var 2
  let y3 : PolyExpr := .var 3
  .add (.add (.add
    (psq (.add (.const 1) x)) (psq y1)) (psq y2)) (psq y3)

private def quaternionExpansionRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let y1 : PolyExpr := .var 1
  let y2 : PolyExpr := .var 2
  let y3 : PolyExpr := .var 3
  .add (.add (.const 1) (.mul (.const 2) x))
    (.add (.add (.add (psq x) (psq y1)) (psq y2)) (psq y3))

private theorem quaternionExpansion_normal :
    normalize quaternionExpansionLHS = normalize quaternionExpansionRHS := by
  decide

private theorem quaternion_expansion_ring (x y1 y2 y3 : Q') :
    (((((1 : Q') + x) * ((1 : Q') + x) + y1 * y1) + y2 * y2) +
        y3 * y3) ≈
      ((1 : Q') + (2 : Q') * x) +
        (((x * x + y1 * y1) + y2 * y2) + y3 * y3) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then x else if r = 1 then y1 else
      if r = 2 then y2 else y3
  have h := poly_identity_of_normal_eq
    quaternionExpansionLHS quaternionExpansionRHS
    quaternionExpansion_normal ρ
  simpa [eval, quaternionExpansionLHS, quaternionExpansionRHS, psq,
    RingNormaliser.qpow, ρ] using h

private def affineDoubleLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  .add (.add (.const 1) (.mul (.const 2) x)) (.const 1)

private def affineDoubleRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  .mul (.const 2) (.add (.const 1) x)

private theorem affineDouble_normal :
    normalize affineDoubleLHS = normalize affineDoubleRHS := by decide

private theorem affine_double_ring (x : Q') :
    ((1 : Q') + (2 : Q') * x) + (1 : Q') ≈
      (2 : Q') * ((1 : Q') + x) := by
  have h := poly_identity_of_normal_eq affineDoubleLHS affineDoubleRHS
    affineDouble_normal (fun _ => x)
  simpa [eval, affineDoubleLHS, affineDoubleRHS,
    RingNormaliser.qpow] using h

private def scaleAssociationLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let c : PolyExpr := .var 1
  .mul (.const 2) (.mul (.add (.const 1) x) (psq c))

private def scaleAssociationRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let c : PolyExpr := .var 1
  .mul (.mul (.const 2) (.add (.const 1) x)) (psq c)

private theorem scaleAssociation_normal :
    normalize scaleAssociationLHS = normalize scaleAssociationRHS := by decide

private theorem scale_association_ring (x c : Q') :
    (2 : Q') * (((1 : Q') + x) * (c * c)) ≈
      ((2 : Q') * ((1 : Q') + x)) * (c * c) := by
  let ρ : Nat → Q' := fun r => if r = 0 then x else c
  have h := poly_identity_of_normal_eq scaleAssociationLHS scaleAssociationRHS
    scaleAssociation_normal ρ
  simpa [eval, scaleAssociationLHS, scaleAssociationRHS, psq,
    RingNormaliser.qpow, ρ] using h

private def quaternionScaleLHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let y1 : PolyExpr := .var 1
  let y2 : PolyExpr := .var 2
  let y3 : PolyExpr := .var 3
  let c : PolyExpr := .var 4
  .mul
    (.add (.add (.add
      (psq (.add (.const 1) x)) (psq y1)) (psq y2)) (psq y3))
    (psq c)

private def quaternionScaleRHS : PolyExpr :=
  let x : PolyExpr := .var 0
  let y1 : PolyExpr := .var 1
  let y2 : PolyExpr := .var 2
  let y3 : PolyExpr := .var 3
  let c : PolyExpr := .var 4
  .add (.add (.add
    (psq (.mul (.add (.const 1) x) c)) (psq (.mul y1 c)))
    (psq (.mul y2 c))) (psq (.mul y3 c))

private theorem quaternionScale_normal :
    normalize quaternionScaleLHS = normalize quaternionScaleRHS := by decide

private theorem quaternion_scale_ring (x y1 y2 y3 c : Q') :
    (((((1 : Q') + x) * ((1 : Q') + x) + y1 * y1) + y2 * y2) +
        y3 * y3) * (c * c) ≈
      ((((((1 : Q') + x) * c) * (((1 : Q') + x) * c) +
        (y1 * c) * (y1 * c)) + (y2 * c) * (y2 * c)) +
        (y3 * c) * (y3 * c)) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then x else if r = 1 then y1 else if r = 2 then y2 else
      if r = 3 then y3 else c
  have h := poly_identity_of_normal_eq quaternionScaleLHS quaternionScaleRHS
    quaternionScale_normal ρ
  simpa [eval, quaternionScaleLHS, quaternionScaleRHS, psq,
    RingNormaliser.qpow, ρ] using h

/-! ## 1. The rational unit-quaternion square identity -/

/-- The rational unit-three-sphere equation, with a fixed left association. -/
def OnUnitQuaternionSphere (x y1 y2 y3 : Q') : Prop :=
  (((x * x + y1 * y1) + y2 * y2) + y3 * y3) ≈ (1 : Q')

/-- On the rational unit three-sphere, `2(1+x)` is a literal sum of four
squares.  No square root, sign decision, or selected parametrisation occurs. -/
theorem two_mul_one_add_eq_quaternion_squares
    (x y1 y2 y3 : Q')
    (hsphere : OnUnitQuaternionSphere x y1 y2 y3) :
    (2 : Q') * ((1 : Q') + x) ≈
      (((((1 : Q') + x) * ((1 : Q') + x) + y1 * y1) + y2 * y2) +
        y3 * y3) := by
  refine Q'.eqv_symm ?_
  calc
    (((((1 : Q') + x) * ((1 : Q') + x) + y1 * y1) + y2 * y2) +
          y3 * y3)
        ≈ ((1 : Q') + (2 : Q') * x) +
            (((x * x + y1 * y1) + y2 * y2) + y3 * y3) := by
          exact quaternion_expansion_ring x y1 y2 y3
    _ ≈ ((1 : Q') + (2 : Q') * x) + (1 : Q') :=
      Q'.add_eqv_congr_left _ _ _ hsphere
    _ ≈ (2 : Q') * ((1 : Q') + x) := by
      exact affine_double_ring x

/-! ## 2. Pointwise odd-character SOS -/

/-- The four literal quaternion squares carrying the odd half-angle feature
`C_k(x)`.  The fixed left association is part of the interface. -/
def oddQuaternionSquares (k : Nat) (x y1 y2 y3 : Q') : Q' :=
  ((((((1 : Q') + x) * C k x) * (((1 : Q') + x) * C k x) +
      (y1 * C k x) * (y1 * C k x)) +
    (y2 * C k x) * (y2 * C k x)) +
  (y3 * C k x) * (y3 * C k x))

/-- Multiplying the unit-quaternion square identity by `C_k(x)^2` gives four
literal squares.  This is the direct bridge from the odd half-angle weight to
a rational polynomial SOS. -/
theorem two_mul_odd_half_angle_eq_quaternion_squares
    (k : Nat) (x y1 y2 y3 : Q')
    (hsphere : OnUnitQuaternionSphere x y1 y2 y3) :
    (2 : Q') *
        (((1 : Q') + x) * (C k x * C k x)) ≈
      oddQuaternionSquares k x y1 y2 y3 := by
  calc
    (2 : Q') * (((1 : Q') + x) * (C k x * C k x))
        ≈ ((2 : Q') * ((1 : Q') + x)) * (C k x * C k x) := by
          exact scale_association_ring x (C k x)
    _ ≈ (((((1 : Q') + x) * ((1 : Q') + x) + y1 * y1) + y2 * y2) +
          y3 * y3) * (C k x * C k x) :=
      Q'.mul_eqv_congr_right _ _ _
        (two_mul_one_add_eq_quaternion_squares x y1 y2 y3 hsphere)
    _ ≈ oddQuaternionSquares k x y1 y2 y3 := by
      unfold oddQuaternionSquares
      exact quaternion_scale_ring x y1 y2 y3 (C k x)

/-- **Odd SU(2) face-channel SOS.**  On the rational unit three-sphere,
twice `1+T_{2k+1}(x)` is the explicit sum of the four displayed squares. -/
theorem two_mul_one_add_T_odd_eq_quaternion_squares
    (k : Nat) (x y1 y2 y3 : Q')
    (hsphere : OnUnitQuaternionSphere x y1 y2 y3) :
    (2 : Q') * ((1 : Q') + T (2 * k + 1) x) ≈
      oddQuaternionSquares k x y1 y2 y3 := by
  calc
    (2 : Q') * ((1 : Q') + T (2 * k + 1) x)
        ≈ (2 : Q') * (((1 : Q') + x) * (C k x * C k x)) :=
      Q'.mul_eqv_congr_left _ _ _ (one_add_T_odd_eq_sos k x)
    _ ≈ oddQuaternionSquares k x y1 y2 y3 :=
      two_mul_odd_half_angle_eq_quaternion_squares k x y1 y2 y3 hsphere

/-! ## 3. Finite summed certificate -/

/-- The finite sum of the four-square odd-channel certificates through level
`m`. -/
def oddQuaternionSOSSum (m : Nat) (x y1 y2 y3 : Q') : Q' :=
  finSum (fun k => oddQuaternionSquares k x y1 y2 y3) (m + 1)

/-- The summed odd half-angle SOS is exactly the sum of the corresponding
four-square quaternion certificates. -/
theorem two_mul_oddSOSSum_eq_quaternionSOSSum
    (m : Nat) (x y1 y2 y3 : Q')
    (hsphere : OnUnitQuaternionSphere x y1 y2 y3) :
    (2 : Q') * oddSOSSum m x ≈
      oddQuaternionSOSSum m x y1 y2 y3 := by
  unfold oddSOSSum oddQuaternionSOSSum
  calc
    (2 : Q') *
        finSum (fun k => ((1 : Q') + x) * (C k x * C k x)) (m + 1)
        ≈ finSum
            (fun k => (2 : Q') *
              (((1 : Q') + x) * (C k x * C k x))) (m + 1) :=
          const_mul_finSum
            (fun k => ((1 : Q') + x) * (C k x * C k x)) (2 : Q') (m + 1)
    _ ≈ finSum (fun k => oddQuaternionSquares k x y1 y2 y3) (m + 1) :=
      finSum_eqv_congr _ _
        (fun k =>
          two_mul_odd_half_angle_eq_quaternion_squares
            k x y1 y2 y3 hsphere) (m + 1)

/-- **Summed odd SU(2) face-channel SOS.**  The second-kind odd character plus
its dimension is a finite sum of explicit rational quaternion squares. -/
theorem odd_face_character_eq_quaternionSOSSum
    (m : Nat) (x y1 y2 y3 : Q')
    (hsphere : OnUnitQuaternionSphere x y1 y2 y3) :
    Q'.ofNat (2 * m + 2) + U (2 * m + 1) x ≈
      oddQuaternionSOSSum m x y1 y2 y3 := by
  calc
    Q'.ofNat (2 * m + 2) + U (2 * m + 1) x
        ≈ (2 : Q') * oddSOSSum m x := odd_sos_sum m x
    _ ≈ oddQuaternionSOSSum m x y1 y2 y3 :=
      two_mul_oddSOSSum_eq_quaternionSOSSum m x y1 y2 y3 hsphere

end YMGap.Continuum.SU2QuaternionOddFaceSOS

#print axioms YMGap.Continuum.SU2QuaternionOddFaceSOS.two_mul_one_add_eq_quaternion_squares
#print axioms YMGap.Continuum.SU2QuaternionOddFaceSOS.two_mul_one_add_T_odd_eq_quaternion_squares
#print axioms YMGap.Continuum.SU2QuaternionOddFaceSOS.odd_face_character_eq_quaternionSOSSum
