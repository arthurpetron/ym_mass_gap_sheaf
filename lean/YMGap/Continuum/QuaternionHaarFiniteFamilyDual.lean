/-
# Finite-family dual energy from a two-branch positive recurrence

For factors A_i >= h >= 0 and signed tests x_i, define the product K,
one-erasure flow L, and signed quadratic cost Q recursively:
 K' = A*K,  L' = K*x+A*L,
 Q' = K*x^2+A*Q+2h*x*L.
The polynomial K*z^2+2h*L*z*b+h*Q*b^2 has an explicit square certificate:
 F_cons(z,b)=(A-h)*F_tail(z,b)+h*F_tail(z+x*b,b).

Thus one Cauchy--Schwarz inequality controls an arbitrary finite family
with no cardinality prefactor. Signed cross terms remain in Q. This does
not bound Q by a marginal variance or construct a complete decomposition.
-/

import YMGap.Continuum.QuaternionHaarTwoFactorDual

namespace YMGap.Continuum.QuaternionHaarFiniteFamilyDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.OSReconstructionProgress (PreInnerForm)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The original product, with no erasure. -/
def product : List (RatPoly × RatPoly) → RatPoly
  | [] => polyOne
  | p::ps => polyMul p.1 (product ps)

/-- Sum of one-factor-erased products times their signed tests. -/
def flow : List (RatPoly × RatPoly) → RatPoly
  | [] => cap 0
  | p::ps => polyAdd (polyMul (product ps) p.2) (polyMul p.1 (flow ps))

/-- Diagonal one-erasure costs plus signed twice-erased cross terms. -/
def cost (h : Q') : List (RatPoly × RatPoly) → RatPoly
  | [] => cap 0
  | p::ps => polyAdd
      (polyAdd (polyMul (product ps) (polyMul p.2 p.2)) (polyMul p.1 (cost h ps)))
      (polyMul (cap h) (polyAdd (polyMul p.2 (flow ps)) (polyMul p.2 (flow ps))))

/-- Two polynomial arguments keep all signed rational scalings constructive. -/
def quadratic (h : Q') (ps : List (RatPoly × RatPoly)) (z b : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (product ps) (polyMul z z))
      (polyMul (cap h) (polyMul (flow ps) (polyAdd (polyMul z b) (polyMul z b)))))
    (polyMul (cap h) (polyMul (cost h ps) (polyMul b b)))

/-- The finite-family recurrence, coefficientwise and with shared variables. -/
theorem quadratic_cons (h : Q') (p : RatPoly × RatPoly) (ps : List (RatPoly × RatPoly))
    (z b : RatPoly) :
    RatPolyCoeffEqv (quadratic h (p::ps) z b)
      (polyAdd
        (polyMul (polyAdd p.1 (polyNeg (cap h))) (quadratic h ps z b))
        (polyMul (cap h) (quadratic h ps (polyAdd z (polyMul p.2 b)) b))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 6) (.var 6))) (.mul (.var 5) (.mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3))) (.add (.mul (.var 6) (.var 7)) (.mul (.var 6) (.var 7)))))) (.mul (.var 5) (.mul (.add (.add (.mul (.var 2) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 4))) (.mul (.var 5) (.add (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))))) (.mul (.var 7) (.var 7)))))
    (.add (.mul (.add (.var 0) (.neg (.var 5))) (.add (.add (.mul (.var 2) (.mul (.var 6) (.var 6))) (.mul (.var 5) (.mul (.var 3) (.add (.mul (.var 6) (.var 7)) (.mul (.var 6) (.var 7)))))) (.mul (.var 5) (.mul (.var 4) (.mul (.var 7) (.var 7)))))) (.mul (.var 5) (.add (.add (.mul (.var 2) (.mul (.add (.var 6) (.mul (.var 1) (.var 7))) (.add (.var 6) (.mul (.var 1) (.var 7))))) (.mul (.var 5) (.mul (.var 3) (.add (.mul (.add (.var 6) (.mul (.var 1) (.var 7))) (.var 7)) (.mul (.add (.var 6) (.mul (.var 1) (.var 7))) (.var 7)))))) (.mul (.var 5) (.mul (.var 4) (.mul (.var 7) (.var 7))))))) (by decide) (fun
      | 0 => p.1 | 1 => p.2 | 2 => product ps | 3 => flow ps
      | 4 => cost h ps | 5 => cap h | 6 => z | _ => b)

/-- A certificate producer, not an assumed many-link positive-form field. -/
def quadraticCertificate {n : Nat} (h : Q') (hh : (0 : Q') ≤ h) :
    (ps : List (RatPoly × RatPoly)) →
    (∀ p, p ∈ ps → Certificate n (polyAdd p.1 (polyNeg (cap h)))) →
    (∀ p, p ∈ ps → SupportedQuaternionBlocks n p.2) →
    (z b : RatPoly) → SupportedQuaternionBlocks n z → SupportedQuaternionBlocks n b →
    Certificate n (quadratic h ps z b)
  | [], _, _, z, b, hz, _ => .ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.const 1) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.const 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))) (.mul (.var 0) (.mul (.const 0) (.mul (.var 2) (.var 2)))))
        (.mul (.var 1) (.var 1)) (by decide) (fun | 0 => cap h | 1 => z | _ => b))
      (.square z hz)
  | p::ps, C, hx, z, b, hz, hb => .ofCoeff (quadratic_cons h p ps z b)
      (((C p List.mem_cons_self).mul
        (quadraticCertificate h hh ps (fun q hq => C q (List.mem_cons_of_mem p hq))
          (fun q hq => hx q (List.mem_cons_of_mem p hq)) z b hz hb)).add
        ((Certificate.constant n h hh).mul
          (quadraticCertificate h hh ps (fun q hq => C q (List.mem_cons_of_mem p hq))
            (fun q hq => hx q (List.mem_cons_of_mem p hq)) (polyAdd z (polyMul p.2 b)) b
            (supported_add hz (supported_polyMul (hx p List.mem_cons_self) hb)) hb)))

private theorem scalar_cs (J M C : Q')
    (hn : ∀ s r : Q', (0 : Q') ≤ s*s*J+(2 : Q')*(s*r)*M+r*r*C) :
    M*M ≤ J*C := by
  let F : PreInnerForm Bool := {
    B := fun a b => match a,b with
      | true,true => J | true,false => M | false,true => M | false,false => C
    nonnegQuad := by
      intro s r a b
      cases a <;> cases b
      · exact Q'.le_trans' _ _ _ (hn 0 (s+r)) (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.add (.add (.mul (.mul (.const 0) (.const 0)) (.var 2)) (.mul (.mul (.const 2) (.mul (.const 0) (.add (.var 0) (.var 1)))) (.var 3))) (.mul (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (.var 4)))
            (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 4)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 4))) (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
            (fun | 0 => s | 1 => r | 2 => J | 3 => M | _ => C)))
      · exact Q'.le_trans' _ _ _ (hn r s) (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.mul (.mul (.const 2) (.mul (.var 1) (.var 0))) (.var 3))) (.mul (.mul (.var 0) (.var 0)) (.var 4)))
            (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 4)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3))) (.mul (.mul (.var 1) (.var 1)) (.var 2))) (by decide)
            (fun | 0 => s | 1 => r | 2 => J | 3 => M | _ => C)))
      · exact hn s r
      · exact Q'.le_trans' _ _ _ (hn (s+r) 0) (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.add (.add (.mul (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (.var 2)) (.mul (.mul (.const 2) (.mul (.add (.var 0) (.var 1)) (.const 0))) (.var 3))) (.mul (.mul (.const 0) (.const 0)) (.var 4)))
            (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 2))) (.mul (.mul (.var 1) (.var 1)) (.var 2))) (by decide)
            (fun | 0 => s | 1 => r | 2 => J | 3 => M | _ => C)))
  }
  exact F.cauchy_schwarz true false

private theorem cap_supported (n : Nat) (c : Q') : SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem haar_cap (n : Nat) (c : Q') (p : RatPoly) :
    H n (polyMul (cap c) p) ≈ c*H n p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p)) (quaternionHaar_polySmul n c p)

private theorem quadratic_haar (n : Nat) (h s r : Q') (mu : RatPoly)
    (ps : List (RatPoly × RatPoly)) (z : RatPoly) :
    H n (polyMul mu (quadratic h ps (polyMul (cap s) z) (cap r))) ≈
      s*s*H n (polyMul mu (polyMul (product ps) (polyMul z z))) +
      (2 : Q')*(s*r)*(h*H n (polyMul mu (polyMul (flow ps) z))) +
      r*r*(h*H n (polyMul mu (cost h ps))) := by
  have hp := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.add (.mul (.var 1) (.mul (.mul (.var 6) (.var 5)) (.mul (.var 6) (.var 5)))) (.mul (.var 4) (.mul (.var 2) (.add (.mul (.mul (.var 6) (.var 5)) (.var 7)) (.mul (.mul (.var 6) (.var 5)) (.var 7)))))) (.mul (.var 4) (.mul (.var 3) (.mul (.var 7) (.var 7))))))
    (.add (.add (.mul (.var 6) (.mul (.var 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 5) (.var 5)))))) (.mul (.const 2) (.mul (.var 6) (.mul (.var 7) (.mul (.var 4) (.mul (.var 0) (.mul (.var 2) (.var 5)))))))) (.mul (.var 7) (.mul (.var 7) (.mul (.var 4) (.mul (.var 0) (.var 3)))))) (by decide) (fun
      | 0 => mu | 1 => product ps | 2 => flow ps | 3 => cost h ps
      | 4 => cap h | 5 => z | 6 => cap s | _ => cap r)
  have ht := Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := n) hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (haar_cap n s _) (Q'.mul_eqv_congr_left _ _ _ (haar_cap n s _)))
            (Q'.eqv_trans _ _ _ (haar_cap n 2 _) (Q'.mul_eqv_congr_left _ _ _
              (Q'.eqv_trans _ _ _ (haar_cap n s _) (Q'.mul_eqv_congr_left _ _ _
                (Q'.eqv_trans _ _ _ (haar_cap n r _) (Q'.mul_eqv_congr_left _ _ _ (haar_cap n h _)))))))))
        (Q'.eqv_trans _ _ _ (haar_cap n r _) (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (haar_cap n r _) (Q'.mul_eqv_congr_left _ _ _ (haar_cap n h _)))))))
  exact Q'.eqv_trans _ _ _ ht (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2))) (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.mul (.var 5) (.var 3)))))) (.mul (.var 1) (.mul (.var 1) (.mul (.var 5) (.var 4)))))
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.mul (.var 5) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 5) (.var 4))))
    (by decide) (fun
      | 0 => s | 1 => r | 2 => H n (polyMul mu (polyMul (product ps) (polyMul z z)))
      | 3 => H n (polyMul mu (polyMul (flow ps) z))
      | 4 => H n (polyMul mu (cost h ps)) | _ => h))

/-- One shared energy budget for EVERY finite list. There is no list-length
factor, and no absolute value is applied to the signed cost. -/
theorem finite_family_dual {n : Nat} {h : Q'} (hh : (0 : Q') < h)
    (ps : List (RatPoly × RatPoly))
    (C : ∀ p, p ∈ ps → Certificate n (polyAdd p.1 (polyNeg (cap h))))
    (hx : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p.2)
    {mu z : RatPoly} (M : Certificate n mu) (hz : SupportedQuaternionBlocks n z) :
    h*(H n (polyMul mu (polyMul (flow ps) z))*H n (polyMul mu (polyMul (flow ps) z))) ≤
      H n (polyMul mu (polyMul (product ps) (polyMul z z))) *
        H n (polyMul mu (cost h ps)) := by
  let J := H n (polyMul mu (polyMul (product ps) (polyMul z z)))
  let L := H n (polyMul mu (polyMul (flow ps) z))
  let Q := H n (polyMul mu (cost h ps))
  have hn (s r : Q') : (0 : Q') ≤ s*s*J+(2 : Q')*(s*r)*(h*L)+r*r*(h*Q) :=
    Q'.le_trans' _ _ _
      (M.mul (quadraticCertificate h (Q'.le_of_lt hh) ps C hx
        (polyMul (cap s) z) (cap r) (supported_polyMul (cap_supported n s) hz)
        (cap_supported n r))).haar_nonnegative
      (Q'.le_of_eqv (quadratic_haar n h s r mu ps z))
  have hcs := scalar_cs J (h*L) (h*Q) hn
  have hl : (h*L)*(h*L) ≈ h*(h*(L*L)) := poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => h | _ => L)
  have hr : J*(h*Q) ≈ h*(J*Q) := poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => J | 1 => h | _ => Q)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hr))) hh

/-- Completing the SAME certified quadratic at z=-h*z0, b=1 gives a
nonnegative cost remainder when the flow pairing matches the product norm.
There is no strict-norm assumption or division by that norm. The consumer
uses one-sided tests, not jumps, to obtain its joint signed marginal cost. -/
theorem finite_family_completed_square {n : Nat} {h : Q'} (hh : (0 : Q') < h)
    (ps : List (RatPoly × RatPoly))
    (C : ∀ p, p ∈ ps → Certificate n (polyAdd p.1 (polyNeg (cap h))))
    (hx : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p.2)
    {mu z : RatPoly} (M : Certificate n mu) (hz : SupportedQuaternionBlocks n z)
    (hmatch : H n (polyMul mu (polyMul (flow ps) z)) ≈
      H n (polyMul mu (polyMul (product ps) (polyMul z z)))) :
    h * H n (polyMul mu (polyMul (product ps) (polyMul z z))) ≤
      H n (polyMul mu (cost h ps)) := by
  let J := H n (polyMul mu (polyMul (product ps) (polyMul z z)))
  let L := H n (polyMul mu (polyMul (flow ps) z))
  let Q := H n (polyMul mu (cost h ps))
  have hn : (0 : Q') ≤ (-h)*(-h)*J+(2 : Q')*((-h)*1)*(h*L)+1*1*(h*Q) :=
    Q'.le_trans' _ _ _
      (M.mul (quadraticCertificate h (Q'.le_of_lt hh) ps C hx
        (polyMul (cap (-h)) z) (cap 1)
        (supported_polyMul (cap_supported n (-h)) hz) (cap_supported n 1))).haar_nonnegative
      (Q'.le_of_eqv (quadratic_haar n h (-h) 1 mu ps z))
  have he : (-h)*(-h)*J+(2 : Q')*((-h)*1)*(h*L)+1*1*(h*Q) ≈ h*(Q + -(h*J)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hmatch)))
        (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.neg (.var 0)) (.neg (.var 0))) (.var 1))
          (.mul (.mul (.const 2) (.mul (.neg (.var 0)) (.const 1))) (.mul (.var 0) (.var 1))))
          (.mul (.mul (.const 1) (.const 1)) (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 0) (.var 1)))))
        (by decide) (fun | 0 => h | 1 => J | _ => Q))
  exact Q'.le_of_sub_nonneg (Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv h))
      (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))) hh)

end YMGap.Continuum.QuaternionHaarFiniteFamilyDual

#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.product
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.flow
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.cost
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.quadratic_cons
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.quadraticCertificate
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.finite_family_dual
#print axioms YMGap.Continuum.QuaternionHaarFiniteFamilyDual.finite_family_completed_square
