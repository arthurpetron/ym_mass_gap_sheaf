/-
# Two-factor dual control retaining the signed cross term

For certified mu >= 0 and A,B >= h > 0, four positive weights give
  h (H[mu B z x] + H[mu A z y])^2
    <= H[mu A B z^2] (H[mu B x^2] + H[mu A y^2] + 2h H[mu x y]).
The cross term is signed. No separate Cauchy--Schwarz bound or absolute
value is applied to it. The consumer specializes A,B to two actual kinetic
factors and z,x,y to jumps in the original temporal energy.

The four-cell identity is
 AB z^2 - 2h z(Bx+Ay) + h(Bx^2+Ay^2+2hxy)
 = (A-h)(B-h)z^2 + h(B-h)(z-x)^2
   + h(A-h)(z-y)^2 + h^2(z-x-y)^2.
No inverse, square root, orthogonality, or global spectral bound is assumed.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarTwoFactorDual

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
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.OSReconstructionProgress (PreInnerForm)
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private def addForm {V : Type} (F G : PreInnerForm V) : PreInnerForm V where
  B a b := F.B a b + G.B a b
  nonnegQuad s r a b := Q'.le_trans' _ _ _
    (Q'.zero_le_add _ _ (F.nonnegQuad s r a b) (G.nonnegQuad s r a b))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3))) (.mul (.mul (.var 1) (.var 1)) (.var 4))) (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 5)) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 6))) (.mul (.mul (.var 1) (.var 1)) (.var 7))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.add (.var 2) (.var 5))) (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.add (.var 3) (.var 6)))) (.mul (.mul (.var 1) (.var 1)) (.add (.var 4) (.var 7))))
      (by decide) (fun
        | 0 => s | 1 => r | 2 => F.B a a | 3 => F.B a b | 4 => F.B b b
        | 5 => G.B a a | 6 => G.B a b | _ => G.B b b)))

private def pairForm {n : Nat} {W p q : RatPoly} (C : Certificate n W)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    PreInnerForm Bool :=
  let F := (weightedGNSData n W C).toPreInnerForm
  let pick : Bool → {r : RatPoly // SupportedQuaternionBlocks n r}
    | true => ⟨p,hp⟩ | false => ⟨q,hq⟩
  { B := fun a b => F.B (pick a) (pick b)
    nonnegQuad := fun s r a b => F.nonnegQuad s r (pick a) (pick b) }

private theorem cap_supported (n : Nat) (c : Q') : SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem haar_sum4 (n : Nat) (p q r s : RatPoly) :
    (H n p + H n q) + (H n r + H n s) ≈
      H n (polyAdd (polyAdd p q) (polyAdd r s)) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm (quaternionHaar_append n p q))
      (Q'.eqv_symm (quaternionHaar_append n r s)))
    (Q'.eqv_symm (quaternionHaar_append n _ _))

private theorem haar_cap (n : Nat) (c : Q') (p : RatPoly) :
    H n (polyMul (cap c) p) ≈ c*H n p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p)) (quaternionHaar_polySmul n c p)

/-- Two positive kinetic factors share one energy budget, with their signed
cross pairing retained. Positivity of the four weights is constructed. -/
theorem two_factor_dual {n : Nat} {mu A B z x y : RatPoly} {h : Q'}
    (hh : (0 : Q') < h) (M : Certificate n mu)
    (CA : Certificate n (polyAdd A (polyNeg (cap h))))
    (CB : Certificate n (polyAdd B (polyNeg (cap h))))
    (hz : SupportedQuaternionBlocks n z) (hx : SupportedQuaternionBlocks n x)
    (hy : SupportedQuaternionBlocks n y) :
    h * ((weightedPair n (polyMul mu B) z x + weightedPair n (polyMul mu A) z y) *
      (weightedPair n (polyMul mu B) z x + weightedPair n (polyMul mu A) z y)) ≤
    weightedPair n (polyMul (polyMul mu A) B) z z *
      (weightedPair n (polyMul mu B) x x + weightedPair n (polyMul mu A) y y +
        h*(weightedPair n mu x y + weightedPair n mu x y)) := by
  let Ch := Certificate.constant n h (Q'.le_of_lt hh)
  let F0 := pairForm ((M.mul CA).mul CB) hz (cap_supported n 0)
  let F1 := pairForm ((M.mul Ch).mul CB) hz hx
  let F2 := pairForm ((M.mul Ch).mul CA) hz hy
  let F3 := pairForm ((M.mul Ch).mul Ch) hz (supported_add hx hy)
  let F := addForm (addForm F0 F1) (addForm F2 F3)
  let J := weightedPair n (polyMul (polyMul mu A) B) z z
  let L := weightedPair n (polyMul mu B) z x + weightedPair n (polyMul mu A) z y
  let Q := weightedPair n (polyMul mu B) x x + weightedPair n (polyMul mu A) y y +
    h*(weightedPair n mu x y + weightedPair n mu x y)
  let env : Nat → RatPoly := fun
    | 0 => mu | 1 => A | 2 => B | 3 => cap h | 4 => z | 5 => x | _ => y
  have huu : F.B true true ≈ J :=
    Q'.eqv_trans _ _ _ (haar_sum4 n _ _ _ _) (haar_of_coeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.mul (.var 4) (.var 4)) (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))) (.add (.var 2) (.neg (.var 3))))) (.mul (.mul (.var 4) (.var 4)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 2) (.neg (.var 3)))))) (.add (.mul (.mul (.var 4) (.var 4)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 1) (.neg (.var 3))))) (.mul (.mul (.var 4) (.var 4)) (.mul (.mul (.var 0) (.var 3)) (.var 3)))))
        (.mul (.mul (.var 4) (.var 4)) (.mul (.mul (.var 0) (.var 1)) (.var 2))) (by decide) env))
  have huv : F.B true false ≈ h*L :=
    Q'.eqv_trans _ _ _ (haar_sum4 n _ _ _ _)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.mul (.var 4) (.const 0)) (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))) (.add (.var 2) (.neg (.var 3))))) (.mul (.mul (.var 4) (.var 5)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 2) (.neg (.var 3)))))) (.add (.mul (.mul (.var 4) (.var 6)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 1) (.neg (.var 3))))) (.mul (.mul (.var 4) (.add (.var 5) (.var 6))) (.mul (.mul (.var 0) (.var 3)) (.var 3)))))
        (.mul (.var 3) (.add (.mul (.mul (.var 4) (.var 5)) (.mul (.var 0) (.var 2))) (.mul (.mul (.var 4) (.var 6)) (.mul (.var 0) (.var 1))))) (by decide) env))
        (Q'.eqv_trans _ _ _ (haar_cap n h _)
          (Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_append n _ _))))
  have hvv : F.B false false ≈ h*Q :=
    Q'.eqv_trans _ _ _ (haar_sum4 n _ _ _ _)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.mul (.const 0) (.const 0)) (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))) (.add (.var 2) (.neg (.var 3))))) (.mul (.mul (.var 5) (.var 5)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 2) (.neg (.var 3)))))) (.add (.mul (.mul (.var 6) (.var 6)) (.mul (.mul (.var 0) (.var 3)) (.add (.var 1) (.neg (.var 3))))) (.mul (.mul (.add (.var 5) (.var 6)) (.add (.var 5) (.var 6))) (.mul (.mul (.var 0) (.var 3)) (.var 3)))))
        (.mul (.var 3) (.add (.add (.mul (.mul (.var 5) (.var 5)) (.mul (.var 0) (.var 2))) (.mul (.mul (.var 6) (.var 6)) (.mul (.var 0) (.var 1)))) (.mul (.var 3) (.add (.mul (.mul (.var 5) (.var 6)) (.var 0)) (.mul (.mul (.var 5) (.var 6)) (.var 0)))))) (by decide) env))
        (Q'.eqv_trans _ _ _ (haar_cap n h _)
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
              (Q'.add_eqv_congr' (quaternionHaar_append n _ _)
                (Q'.eqv_trans _ _ _ (haar_cap n h _)
                  (Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_append n _ _))))))))
  have hcs : (h*L)*(h*L) ≤ J*(h*Q) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul huv huv))
      (Q'.le_trans' _ _ _ (F.cauchy_schwarz true false) (Q'.le_of_eqv (qmul huu hvv)))
  have hl : (h*L)*(h*L) ≈ h*(h*(L*L)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => h | _ => L)
  have hr : J*(h*Q) ≈ h*(J*Q) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => J | 1 => h | _ => Q)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hr))) hh

end YMGap.Continuum.QuaternionHaarTwoFactorDual

#print axioms YMGap.Continuum.QuaternionHaarTwoFactorDual.two_factor_dual
