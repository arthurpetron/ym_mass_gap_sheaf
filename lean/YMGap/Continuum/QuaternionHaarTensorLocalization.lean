/-
# Separable localization test for the ORIGINAL finite product Haar

The literal one-link polynomial ((1+x0)/2)^m is placed in EACH actual
quaternion block. Ordered-head Fubini computes its original product-Haar
moment exactly, and the existing one-link moment floor gives a computable
tensor floor. Evaluation uses the SAME explicit unit-assignment environment
as original finite-action localization. Empty tensors and exponent zero are
included. No interacting partition, typical raw-link concentration, entropy,
relative response, physical scaling or survival claim is made here.
-/

import YMGap.Continuum.SU2QuaternionKernelMomentLower
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
import YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization

namespace YMGap.Continuum.QuaternionHaarTensorLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base base_bounds)
open YMGap.Continuum.RingNormaliser (evalMono evalMonoFrom)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul quaternionHaar_polySmul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_one evalRatPoly_var evalRatPoly_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)
open YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration
open YMGap.Continuum.SU2QuaternionKernelMomentLower
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (partialHaarHeads_supported_constant)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment environment_coordinate)
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization (scalarProduct scalarProduct_nonnegative)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Append the literal one-link kernel in the NEXT original quaternion block.
No coordinate identification or Haar-carrier equivalence defines this test. -/
def tensorKernel : Nat → Nat → RatPoly
  | 0, _ => polyOne
  | blocks+1, m => polyMul (tensorKernel blocks m) (liftBoundary blocks (kernelPower m))

/-- The test uses exactly the first `blocks` original quaternion blocks. -/
theorem tensorKernel_supported : ∀ (blocks m : Nat),
    SupportedQuaternionBlocks blocks (tensorKernel blocks m)
  | 0, _ => supported_one 0
  | blocks+1, m => by
      apply supported_polyMul
      · intro term ht
        exact Nat.le_trans (tensorKernel_supported blocks m term ht)
          (Nat.mul_le_mul_left 4 (by omega))
      · simpa only [Nat.add_comm] using lift_supported (kernelPower_supported m) blocks

private theorem mono_shift (rho : Nat → Q') (s : Nat) : ∀ (mon : List Nat) (i : Nat),
    evalMonoFrom rho (s+i) mon = evalMonoFrom (fun j => rho (s+j)) i mon
  | [], _ => rfl
  | _::mon, i => by
      simp only [evalMonoFrom]
      rw [show s+i+1=s+(i+1) from Nat.add_assoc _ _ _, mono_shift rho s mon (i+1)]

private theorem mono_lift (rho : Nat → Q') (mon : List Nat) :
    evalMono rho (0::0::0::0::mon) ≈ evalMono (fun i => rho (4+i)) mon := by
  have ht : evalMonoFrom rho 4 mon = evalMono (fun i => rho (4+i)) mon := by
    simpa only [evalMono, Nat.add_zero] using mono_shift rho 4 mon 0
  change 1*(1*(1*(1*evalMonoFrom rho 4 mon))) ≈ _
  rw [ht]
  exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)))

private theorem eval_liftHead (rho : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly rho (liftHead p) ≈ evalRatPoly (fun i => rho (4+i)) p
  | [] => Q'.eqv_refl _
  | term::p => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (mono_lift rho term.1)) (eval_liftHead rho p)

private theorem eval_liftBoundary (rho : Nat → Q') : ∀ (blocks : Nat) (p : RatPoly),
    evalRatPoly rho (liftBoundary blocks p) ≈ evalRatPoly (fun i => rho (4*blocks+i)) p
  | 0, p => by
      simp only [liftBoundary, Nat.mul_zero, Nat.zero_add]
      exact Q'.eqv_refl _
  | blocks+1, p => by
      refine Q'.eqv_trans _ _ _ (eval_liftHead rho (liftBoundary blocks p)) ?_
      have he := eval_liftBoundary (fun i => rho (4+i)) blocks p
      have henv : (fun i => rho (4+(4*blocks+i))) = (fun i => rho (4*(blocks+1)+i)) := by
        funext i
        congr 1
        omega
      rw [henv] at he
      exact he

private theorem kernelBase_eval (rho : Nat → Q') :
    evalRatPoly rho kernelBase ≈ half*(1+rho 0) := by
  change evalRatPoly rho (polySmul half (polyAdd polyOne (polyVar 0))) ≈ _
  exact Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr' (evalRatPoly_one rho) (evalRatPoly_var rho 0))))

private theorem kernelPower_eval (rho : Nat → Q') : ∀ m,
    evalRatPoly rho (kernelPower m) ≈ qpow (half*(1+rho 0)) m
  | 0 => evalRatPoly_one rho
  | m+1 => Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc (kernelPower_eval rho m) (kernelBase_eval rho))

private theorem shifted_kernel_eval (qs : Nat → UnitNorm) (blocks m : Nat) :
    evalRatPoly (environment qs) (liftBoundary blocks (kernelPower m)) ≈ qpow (base (qs blocks)) m := by
  refine Q'.eqv_trans _ _ _ (eval_liftBoundary (environment qs) blocks _) ?_
  have he := kernelPower_eval (fun i => environment qs (4*blocks+i)) m
  have hs : half*(1+environment qs (4*blocks+0)) = base (qs blocks) := by
    have hc : environment qs (4*blocks+0) = (qs blocks).val.r :=
      environment_coordinate qs blocks (0 : Fin 4)
    rw [hc]
    rfl
  rw [hs] at he
  exact he

private theorem scalarProduct_append {A : Type} (f : A → Q') : ∀ xs ys,
    scalarProduct f (xs++ys) ≈ scalarProduct f xs*scalarProduct f ys
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv _)
  | _::xs, ys => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (scalarProduct_append f xs ys))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem scalarProduct_range_succ (f : Nat → Q') (blocks : Nat) :
    scalarProduct f (List.range (blocks+1)) ≈ scalarProduct f (List.range blocks)*f blocks := by
  rw [List.range_succ]
  exact Q'.eqv_trans _ _ _ (scalarProduct_append f _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))

/-- Exact evaluation in the SAME original assignment used by the action:
one base power per actual block, in ascending `List.range` order. -/
theorem tensorKernel_eval : ∀ (blocks m : Nat) (qs : Nat → UnitNorm),
    evalRatPoly (environment qs) (tensorKernel blocks m) ≈
      scalarProduct (fun b => qpow (base (qs b)) m) (List.range blocks)
  | 0, _, qs => evalRatPoly_one (environment qs)
  | blocks+1, m, qs => Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
      (Q'.eqv_trans _ _ _ (mc (tensorKernel_eval blocks m qs) (shifted_kernel_eval qs blocks m))
        (Q'.eqv_symm (scalarProduct_range_succ _ blocks)))

private theorem power_bounds (x : Q') (hx : (0 : Q') ≤ x ∧ x ≤ 1) : ∀ m,
    (0 : Q') ≤ qpow x m ∧ qpow x m ≤ 1
  | 0 => ⟨by change (0 : Q') ≤ 1; decide, Q'.le_refl' _⟩
  | m+1 => ⟨Q'.mul_nonneg _ _ (power_bounds x hx m).1 hx.1,
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg (power_bounds x hx m).2 hx.2 (by decide) hx.1)
        (Q'.le_of_eqv (by decide : (1 : Q')*1 ≈ 1))⟩

private theorem scalarProduct_upper {A : Type} (f : A → Q')
    (hf : ∀ a, (0 : Q') ≤ f a ∧ f a ≤ 1) : ∀ xs, scalarProduct f xs ≤ 1
  | [] => Q'.le_refl' _
  | a::xs => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (hf a).2 (scalarProduct_upper f hf xs) (by decide)
        (scalarProduct_nonnegative f (fun b => (hf b).1) xs))
      (Q'.le_of_eqv (by decide : (1 : Q')*1 ≈ 1))

/-- Pointwise unit interval for every explicit original unit assignment.
No probability law, positive action, or assigned-point restriction is assumed. -/
theorem tensorKernel_bounds (blocks m : Nat) (qs : Nat → UnitNorm) :
    (0 : Q') ≤ evalRatPoly (environment qs) (tensorKernel blocks m) ∧
      evalRatPoly (environment qs) (tensorKernel blocks m) ≤ 1 := by
  have hb (b : Nat) := power_bounds (base (qs b)) (base_bounds (qs b)) m
  have he := tensorKernel_eval blocks m qs
  exact ⟨Q'.le_trans' _ _ _ (scalarProduct_nonnegative _ (fun b => (hb b).1) _)
      (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (scalarProduct_upper _ hb _)⟩

/-- Exact ORIGINAL Haar factorization, derived by ordered-head Fubini and
the already proved supported-polynomial constant pin. Exponent zero allowed. -/
theorem tensorKernel_haar : ∀ (blocks m : Nat),
    quaternionHaar blocks (tensorKernel blocks m) ≈ (kernelMoment m)^blocks
  | 0, _ => by change (1 : Q') ≈ 1; decide
  | blocks+1, m => by
      have hhead := head_pairing 1 blocks (tensorKernel blocks m) (kernelPower m)
      have hc := partialHaarHeads_supported_constant blocks (tensorKernel_supported blocks m)
      have hfactor : quaternionHaar 1
          (polyMul (partialHaarHeads blocks (tensorKernel blocks m)) (kernelPower m)) ≈
          quaternionHaar blocks (tensorKernel blocks m)*kernelMoment m :=
        Q'.eqv_trans _ _ _ (haar_of_coeff
          ((hc.mul_right (kernelPower m)).trans (cap_mul_left _ _)))
          (quaternionHaar_polySmul _ _ _)
      have hh : quaternionHaar (blocks+1) (tensorKernel (blocks+1) m) ≈
          quaternionHaar blocks (tensorKernel blocks m)*kernelMoment m := by
        simpa only [Nat.add_comm] using Q'.eqv_trans _ _ _ hhead hfactor
      exact Q'.eqv_trans _ _ _ hh
        (Q'.eqv_trans _ _ _ (mc (tensorKernel_haar blocks m) (Q'.eqv_refl _))
          (Q'.mul_comm_eqv _ _))

private theorem pow_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ blocks : Nat, a^blocks ≤ b^blocks
  | 0 => Q'.le_refl' _
  | blocks+1 => Q'.mul_le_mul_of_nonneg hab (pow_mono ha hab blocks)
      (Q'.le_trans' _ _ _ ha hab) (Q'.pow_nonneg a ha blocks)

/-- Computed localization mass `(1/(m+1)^2)^blocks` below the actual original
Haar moment. Both zero blocks and exponent zero are retained. -/
theorem tensorKernel_haar_lower (blocks m : Nat) :
    (localizationFloor m)^blocks ≤ quaternionHaar blocks (tensorKernel blocks m) :=
  Q'.le_trans' _ _ _
    (pow_mono (Q'.le_of_lt (localizationFloor_positive m)) (localizationFloor_le_kernelMoment m) blocks)
    (Q'.ge_of_eqv (tensorKernel_haar blocks m))

end YMGap.Continuum.QuaternionHaarTensorLocalization

#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel
#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel_supported
#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel_eval
#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel_bounds
#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel_haar
#print axioms YMGap.Continuum.QuaternionHaarTensorLocalization.tensorKernel_haar_lower
