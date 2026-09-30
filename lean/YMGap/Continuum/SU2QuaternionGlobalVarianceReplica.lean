/-
# Global variance as an exact original two-copy Haar square

For an arbitrary supported weight and observable, two independent copies
give twice the unnormalized variance determinant. No positivity, inverse,
conditional law, or canonical-path estimate is used in this identity.
-/

import YMGap.Continuum.SU2QuaternionHaarMarkovContraction
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.SU2QuaternionGlobalVarianceReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction (haar_split_pairing)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

def replicaDifference (n : Nat) (f : RatPoly) : RatPoly :=
  polyAdd f (polyNeg (liftBoundary n f))

private theorem support_first {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f := by
  intro term ht
  exact Nat.le_trans (hf term ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))

private theorem support_neg {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (polyNeg f) := by
  intro term ht
  obtain ⟨t, hs, rfl⟩ := List.mem_map.mp ht
  exact hf t hs

theorem replicaDifference_supported {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) (replicaDifference n f) :=
  supported_add (support_first hf) (support_neg (lift_supported hf n))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1))
        (haar_neg n p)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem jump_expansion (e f g : RatPoly) :
    RatPolyCoeffEqv
      (polyMul e (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g))))
      (polyAdd
        (polyMul e (polyAdd (polyMul f f) (polyMul g g)))
        (polyAdd (polyNeg (polyMul e (polyMul f g)))
          (polyNeg (polyMul e (polyMul f g))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
      (.add (.var 1) (.neg (.var 2)))))
    (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1))
      (.mul (.var 2) (.var 2))))
      (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))))
    (by decide) (fun | 0 => e | 1 => f | _ => g)

private theorem diagonal_first (n : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks n W) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar (n+n)
      (polyMul (polyMul W (liftBoundary n W)) (polyMul f f)) ≈
      quaternionHaar n (polyMul W (polyMul f f)) * quaternionHaar n W := by
  have h : RatPolyCoeffEqv
      (polyMul (polyMul W (liftBoundary n W)) (polyMul f f))
      (polyMul (polyMul W (polyMul f f)) (liftBoundary n W)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
      (by decide) (fun | 0 => W | 1 => liftBoundary n W | _ => f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h)
    (haar_split_pairing (supported_polyMul hW (supported_polyMul hf hf)) W)

private theorem diagonal_second (n : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks n W) :
    quaternionHaar (n+n)
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul (liftBoundary n f) (liftBoundary n f))) ≈
      quaternionHaar n W * quaternionHaar n (polyMul W (polyMul f f)) := by
  have h : RatPolyCoeffEqv
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul (liftBoundary n f) (liftBoundary n f)))
      (polyMul W (liftBoundary n (polyMul W (polyMul f f)))) := by
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => W | 1 => liftBoundary n W | _ => liftBoundary n f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h) (haar_split_pairing hW _)

private theorem cross_pair (n : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks n W) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar (n+n)
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul f (liftBoundary n f))) ≈
      quaternionHaar n (polyMul W f) * quaternionHaar n (polyMul W f) := by
  have h : RatPolyCoeffEqv
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul f (liftBoundary n f)))
      (polyMul (polyMul W f) (liftBoundary n (polyMul W f))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide)
      (fun | 0 => W | 1 => liftBoundary n W | 2 => f | _ => liftBoundary n f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h)
    (haar_split_pairing (supported_polyMul hW hf) _)

/-- The two-copy square is twice the unnormalized variance determinant of
the SAME one-copy weight. No positive-mass or inverse hypothesis is needed. -/
theorem global_variance_identity (n : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks n W) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar (n+n)
      (polyMul (polyMul W (liftBoundary n W))
        (polyMul (replicaDifference n f) (replicaDifference n f))) ≈
      2 * (quaternionHaar n W * quaternionHaar n (polyMul W (polyMul f f)) +
        -(quaternionHaar n (polyMul W f) * quaternionHaar n (polyMul W f))) := by
  let e := polyMul W (liftBoundary n W)
  let g := liftBoundary n f
  let Z := quaternionHaar n W
  let F := quaternionHaar n (polyMul W (polyMul f f))
  let M := quaternionHaar n (polyMul W f)
  have hdiag : quaternionHaar (n+n)
      (polyMul e (polyAdd (polyMul f f) (polyMul g g))) ≈ F*Z + Z*F :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.add_eqv_congr' (diagonal_first n W f hW hf)
        (diagonal_second n W f hW))
  have hcross : quaternionHaar (n+n) (polyMul e (polyMul f g)) ≈ M*M :=
    cross_pair n W f hW hf
  have hnegs : quaternionHaar (n+n)
      (polyAdd (polyNeg (polyMul e (polyMul f g)))
        (polyNeg (polyMul e (polyMul f g)))) ≈ -(M*M) + -(M*M) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hcross))
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hcross)))
  have hscalar : (F*Z + Z*F) + (-(M*M) + -(M*M)) ≈
      2 * (Z*F + -(M*M)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
        (.add (.neg (.mul (.var 2) (.var 2)))
          (.neg (.mul (.var 2) (.var 2)))))
      (.mul (.const 2) (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.var 2)))))
      (by decide) (fun | 0 => Z | 1 => F | _ => M)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (jump_expansion e f g))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hdiag hnegs) hscalar))

#print axioms replicaDifference
#print axioms replicaDifference_supported
#print axioms global_variance_identity

end YMGap.Continuum.SU2QuaternionGlobalVarianceReplica
