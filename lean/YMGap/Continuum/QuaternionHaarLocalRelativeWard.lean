/-
# Original-block relative Ward budget

The signed derivative of one complete positive weight is bounded by the
same-weight centered square and angular square, first at one original
quaternion block and then on an arbitrary explicit block list.  The list
may repeat blocks; its literal length is charged.  No weight floor,
head-linearity, source replacement, or scaling assertion is used.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularYoung
import YMGap.Continuum.SU2QuaternionWeightedCasimirWard

namespace YMGap.Continuum.QuaternionHaarLocalRelativeWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativeAngularYoung
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sixValue_affine (a : Q') (b : Nat → Nat → Q') :
    sixValue (fun i j => a + b i j) ≈ 6*a + sixValue b :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.add (.add (.var 0) (.var 2))
        (.add (.add (.var 0) (.var 3))
          (.add (.add (.var 0) (.var 4))
            (.add (.add (.var 0) (.var 5)) (.add (.var 0) (.var 6)))))))
    (.add (.mul (.const 6) (.var 0))
      (.add (.var 1) (.add (.var 2) (.add (.var 3)
        (.add (.var 4) (.add (.var 5) (.var 6)))))))
    (by decide) (fun
      | 0 => a | 1 => b 0 1 | 2 => b 0 2 | 3 => b 0 3
      | 4 => b 1 2 | 5 => b 1 3 | _ => b 2 3)

/-- Six original planes on an arbitrary in-range block.  The relative
certificate is required at each literal coordinate pair `4*b+i,4*b+j`.
The signed residual need not have either sign. -/
theorem block_residual_lower (n b : Nat) (hb : b < n)
    {W f : RatPoly} {C : Q'} (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound n (4*b+i) (4*b+j) W C)
    (hf : SupportedQuaternionBlocks n f) (c : Q') :
    -(2 * blockResidual n b W f c) ≤
      6*(C*C)*H n (polyMul W
        (polyMul (polyAdd f (polySmul (-c) polyOne))
          (polyAdd f (polySmul (-c) polyOne)))) +
        blockEnergy n b W f := by
  let a := polyAdd f (polySmul (-c) polyOne)
  let A := H n (polyMul W (polyMul a a))
  let r := fun i j => H n
    (polyMul (polyMul a (blockAngularDerivative b i j W))
      (blockAngularDerivative b i j f))
  let e := fun i j => H n
    (polyMul W (polyMul (blockAngularDerivative b i j f)
      (blockAngularDerivative b i j f)))
  have ha : SupportedQuaternionBlocks n a :=
    supported_add hf (polySmul_supported (supported_one n) (-c))
  have hp (i j : Nat) (hi : i < 4) (hj : j < 4) :
      -(2*r i j) ≤ (C*C)*A + e i j := by
    have hdf : SupportedQuaternionBlocks n (blockAngularDerivative b i j f) :=
      angularDerivative_supported_at (i := 4*b+i) (j := 4*b+j)
        (by omega) (by omega) hf
    have hy := relative_young_lower (R i j hi hj) hC ha
      hdf
    have he : H n
        (polyMul (blockAngularDerivative b i j W)
          (polyMul a (blockAngularDerivative b i j f))) ≈ r i j :=
      haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
        (fun | 0 => blockAngularDerivative b i j W
             | 1 => a | _ => blockAngularDerivative b i j f))
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left 2 _ _ he))) hy
  have hs := sixValue_mono _ _ hp
  have hl : -(2*blockResidual n b W f c) ≈
      sixValue (fun i j => -(2*r i j)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv 2 (sixValue r)))
      (Q'.eqv_trans _ _ _ (sixValue_mul_left (-2) r)
        (sixValue_congr _ _ (fun i j _ _ => Q'.neg_mul_eqv 2 (r i j))))
  have hr : sixValue (fun i j => (C*C)*A + e i j) ≈
      6*(C*C)*A + blockEnergy n b W f :=
    Q'.eqv_trans _ _ _ (sixValue_affine ((C*C)*A) e)
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (Q'.mul_assoc_eqv 6 (C*C) A))
        (Q'.eqv_symm (haar_six n W
          (fun i j => polyMul (blockAngularDerivative b i j f)
            (blockAngularDerivative b i j f)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

private theorem qsum_mono {I : Type} (xs : List I) (left right : I → Q')
    (h : ∀ x, x ∈ xs → left x ≤ right x) :
    qListSum (xs.map left) ≤ qListSum (xs.map right) := by
  revert h
  induction xs with
  | nil => intro _; exact Q'.le_of_eqv (Q'.eqv_refl _)
  | cons x rest ih =>
      intro h
      exact Q'.add_le_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem ofNat_succ_forward (k : Nat) :
    Q'.ofNat (k+1) ≈ Q'.ofNat k+1 :=
  Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv k 1)
    (Q'.add_eqv_congr_left _ _ _ (by decide))

private theorem qsum_const {I : Type} (xs : List I) (v : Q') :
    qListSum (xs.map fun _ => v) ≈ Q'.ofNat xs.length*v := by
  induction xs with
  | nil => exact Q'.eqv_symm (Q'.zero_mul_eqv v)
  | cons x rest ih =>
      change v + qListSum (rest.map fun _ => v) ≈
        Q'.ofNat (rest.length+1)*v
      have hring : v + Q'.ofNat rest.length*v ≈
          (Q'.ofNat rest.length+1)*v :=
        poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.var 1) (.var 0)))
          (.mul (.add (.var 1) (.const 1)) (.var 0))
          (by decide) (fun | 0 => v | _ => Q'.ofNat rest.length)
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (Q'.eqv_trans _ _ _ hring
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm
            (ofNat_succ_forward rest.length))))

/-- An arbitrary original block list, including repetitions.  No head
linearity is needed; every listed block supplies its own in-range and
six-plane relative certificate. -/
theorem active_residual_lower (n : Nat) (J : List Nat)
    (hJ : ∀ b, b ∈ J → b < n)
    {W f : RatPoly} {C : Q'} (hC : (0 : Q') < C)
    (R : ∀ b, b ∈ J → ∀ i j, i < 4 → j < 4 →
      RelativeBound n (4*b+i) (4*b+j) W C)
    (hf : SupportedQuaternionBlocks n f) (c : Q') :
    -(2*qListSum (J.map fun b => blockResidual n b W f c)) ≤
      (6*Q'.ofNat J.length*C*C)*
        H n (polyMul W
          (polyMul (polyAdd f (polySmul (-c) polyOne))
            (polyAdd f (polySmul (-c) polyOne)))) +
        qListSum (J.map fun b => blockEnergy n b W f) := by
  let A := H n (polyMul W
    (polyMul (polyAdd f (polySmul (-c) polyOne))
      (polyAdd f (polySmul (-c) polyOne))))
  let residual := fun b => blockResidual n b W f c
  let energy := fun b => blockEnergy n b W f
  have hpoint : qListSum (J.map fun b => -(2*residual b)) ≤
      qListSum (J.map fun b => 6*(C*C)*A + energy b) := by
    apply qsum_mono
    intro b hb
    exact block_residual_lower n b (hJ b hb) hC (R b hb) hf c
  have hleft : -(2*qListSum (J.map residual)) ≈
      qListSum (J.map fun b => -(2*residual b)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv 2 _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (qListSum_scale J residual (-2)))
        (qListSum_congr J (fun b => (-2)*residual b)
          (fun b => -(2*residual b))
          (fun b _ => Q'.neg_mul_eqv 2 (residual b))))
  have hright : qListSum (J.map fun b => 6*(C*C)*A + energy b) ≈
      (6*Q'.ofNat J.length*C*C)*A + qListSum (J.map energy) := by
    have hconst := qsum_const J (6*(C*C)*A)
    have hcoef : Q'.ofNat J.length*(6*(C*C)*A) ≈
        (6*Q'.ofNat J.length*C*C)*A :=
      poly_identity_of_normal_eq
        (.mul (.var 0)
          (.mul (.mul (.const 6) (.mul (.var 1) (.var 1))) (.var 2)))
        (.mul (.mul (.mul (.mul (.const 6) (.var 0)) (.var 1)) (.var 1)) (.var 2))
        (by decide) (fun | 0 => Q'.ofNat J.length | 1 => C | _ => A)
    exact Q'.eqv_trans _ _ _ (qListSum_add J (fun _ => 6*(C*C)*A) energy)
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hconst hcoef)
        (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hpoint (Q'.le_of_eqv hright))

end YMGap.Continuum.QuaternionHaarLocalRelativeWard

#print axioms YMGap.Continuum.QuaternionHaarLocalRelativeWard.block_residual_lower
#print axioms YMGap.Continuum.QuaternionHaarLocalRelativeWard.active_residual_lower
