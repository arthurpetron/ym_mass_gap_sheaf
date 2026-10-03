/-
# Constant and one actual heat mode in the kinetic quadratic

Subtract the two literal Haar coefficients from an arbitrary signed source.
The positive kinetic square of that residual gives a division-free two-mode
floor. The mode identities are tested identities for the SAME product heat,
not an eigenvector assertion for an interacting transfer. No strict density,
normalizer, spectral theorem or scaling assertion is used.
-/

import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatTwoModeFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_one)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one haar_of_coeff)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local infix:50 " ≈ " => Q'.eqv

/-- The actual positive kinetic form retains BOTH original Haar projections.
The supported source is arbitrary and may contain every action factor. -/
theorem kineticPair_two_mode_floor (n : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) (a : Q')
    (heigen : SupportedHaarEqv n (productMap n w K ids f) (polySmul a f))
    (hfirst : quaternionHaar n f ≈ 0)
    (hsecond : quaternionHaar n (polyMul f f) ≈ 1)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n p * quaternionHaar n p +
        a*(quaternionHaar n (polyMul p f)*quaternionHaar n (polyMul p f)) ≤
      kineticPair n w K ids p p := by
  let D := kineticGNSData n w hw K ids hids
  let P : D.V := ⟨p,hp⟩
  let U : D.V := ⟨polyOne,supported_one n⟩
  let F : D.V := ⟨f,hf⟩
  let m := quaternionHaar n p
  let z := quaternionHaar n (polyMul p f)
  let cost := m*m+a*(z*z)
  have hmean (v : RatPoly) (hv : SupportedQuaternionBlocks n v) :
      kineticPair n w K ids v polyOne ≈ quaternionHaar n v :=
    Q'.eqv_trans _ _ _ (productMap_one n w K ids hnd hids v hv)
      (haar_of_coeff (RatPolyCoeffEqv.mul_one v))
  have hmode (v : RatPoly) (hv : SupportedQuaternionBlocks n v) :
      kineticPair n w K ids v f ≈ a*quaternionHaar n (polyMul v f) :=
    Q'.eqv_trans _ _ _ (heigen v hv)
      (quaternionHaar_polyMul_smul_right n a v f)
  have hPU : D.B P U ≈ m := hmean p hp
  have hPF : D.B P F ≈ a*z := hmode p hp
  have hUU : D.B U U ≈ 1 := Q'.eqv_trans _ _ _ (hmean polyOne (supported_one n)) (haar_one n)
  have hUF : D.B U F ≈ 0 :=
    Q'.eqv_trans _ _ _ (D.B_symm U F)
      (Q'.eqv_trans _ _ _ (hmean f hf) hfirst)
  have hFF : D.B F F ≈ a :=
    Q'.eqv_trans _ _ _ (hmode f hf)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ hsecond) (Q'.mul_one_eqv a))
  let Q := D.add (D.smul m U) (D.smul z F)
  have hPQ : D.B P Q ≈ cost :=
    Q'.eqv_trans _ _ _ (D.B_add_right P (D.smul m U) (D.smul z F))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (D.B_smul_right m P U) (Q'.mul_eqv_congr_left m _ _ hPU))
        (Q'.eqv_trans _ _ _ (D.B_smul_right z P F) (Q'.mul_eqv_congr_left z _ _ hPF)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 1))))
          (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 1) (.var 1))))
          (by decide) (fun
            | 0 => m
            | 1 => z
            | _ => a)))
  have hQQ : D.B Q Q ≈ cost :=
    Q'.eqv_trans _ _ _ (D.diag_expand m z U F)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left m _ _ (Q'.mul_eqv_congr_left m _ _ hUU))
          (Q'.mul_eqv_congr_left m _ _ (Q'.mul_eqv_congr_left z _ _ hUF)))
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left z _ _ (Q'.mul_eqv_congr_left m _ _ hUF))
          (Q'.mul_eqv_congr_left z _ _ (Q'.mul_eqv_congr_left z _ _ hFF))))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.mul (.var 0) (.const 1)))
            (.mul (.var 0) (.mul (.var 1) (.const 0))))
            (.add (.mul (.var 1) (.mul (.var 0) (.const 0)))
              (.mul (.var 1) (.mul (.var 1) (.var 2)))))
          (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 1) (.var 1))))
          (by decide) (fun
            | 0 => m
            | 1 => z
            | _ => a)))
  let R := D.add (D.smul 1 P) (D.smul (-1) Q)
  have hres : D.B R R + cost ≈ D.B P P := by
    have hexp := D.diag_expand 1 (-1) P Q
    have hreplace := Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl (1*(1*D.B P P)))
        (Q'.mul_eqv_congr_left 1 _ _ (Q'.mul_eqv_congr_left (-1) _ _ hPQ)))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (-1) _ _ (Q'.mul_eqv_congr_left 1 _ _ hPQ))
        (Q'.mul_eqv_congr_left (-1) _ _ (Q'.mul_eqv_congr_left (-1) _ _ hQQ)))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hexp hreplace) (Q'.eqv_refl cost))
      (poly_identity_of_normal_eq
        (.add (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
          (.mul (.const 1) (.mul (.const (-1)) (.var 1))))
          (.add (.mul (.const (-1)) (.mul (.const 1) (.var 1)))
            (.mul (.const (-1)) (.mul (.const (-1)) (.var 1))))) (.var 1))
        (.var 0) (by decide) (fun
          | 0 => D.B P P
          | _ => cost))
  have hpos := Q'.add_le_add_right 0 (D.B R R) cost (D.self_nonneg R)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' cost)))
    (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hres))

#print axioms kineticPair_two_mode_floor

end YMGap.Continuum.SU2QuaternionProductHeatTwoModeFloor
