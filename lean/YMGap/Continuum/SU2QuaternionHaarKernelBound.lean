/-
# An ordinary-Haar L2 bound for an actual polynomial kernel map

Integrate the lower N coordinates of W(x,y)f(x), retaining the upper N
coordinates as the output polynomial. A positive certificate for W and
its certificate interval of cap C prove the explicit squared-norm bound
C*C on this SAME map. Weighted Cauchy--Schwarz, ordered-head Fubini and
normalized unused coordinates supply the proof; no kernel estimate is
assumed beyond the stated algebraic certificates.

This is an ordinary product-Haar bound on supported polynomials. It is
not an OS quotient identification, a stationary normalization, a strict
contraction, a thermodynamic estimate or a physical spectral gap.
-/

import YMGap.Continuum.SU2QuaternionHeadChainComposition
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SU2QuaternionHaarKernelBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- The actual lower-coordinate integration map, with no normalization. -/
def kernelMap (blocks : Nat) (W f : RatPoly) : RatPoly :=
  partialHaarHeads blocks (polyMul W f)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

theorem kernelMap_supported {blocks : Nat} {W f : RatPoly}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (kernelMap blocks W f) :=
  partialHaarHeads_supported blocks blocks _
    (supported_polyMul hW (support_mono hf (by omega)))

theorem kernelMap_congr (blocks : Nat) (W : RatPoly) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (kernelMap blocks W f) (kernelMap blocks W g) :=
  partialHaarHeads_congr blocks (h.mul_left W)

private theorem head_add (p q : RatPoly) :
    partialHaarHead (polyAdd p q) = polyAdd (partialHaarHead p) (partialHaarHead q) :=
  List.map_append

private theorem heads_add : ∀ (blocks : Nat) (p q : RatPoly),
    partialHaarHeads blocks (polyAdd p q) =
      polyAdd (partialHaarHeads blocks p) (partialHaarHeads blocks q)
  | 0, _, _ => rfl
  | blocks+1, p, q => by
      simp only [partialHaarHeads, head_add, heads_add blocks]

private theorem head_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polySmul c p)) (polySmul c (partialHaarHead p)) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (polySmul c p))
      (polySmul c (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem heads_smul : ∀ (blocks : Nat) (c : Q') (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads blocks (polySmul c p))
      (polySmul c (partialHaarHeads blocks p))
  | 0, _, _ => .refl _
  | blocks+1, c, p =>
      (partialHaarHeads_congr blocks (head_smul c p)).trans
        (heads_smul blocks c (partialHaarHead p))

theorem kernelMap_add (blocks : Nat) (W f g : RatPoly) :
    RatPolyCoeffEqv (kernelMap blocks W (polyAdd f g))
      (polyAdd (kernelMap blocks W f) (kernelMap blocks W g)) := by
  unfold kernelMap
  rw [← heads_add]
  exact partialHaarHeads_congr blocks (RatPolyCoeffEqv.mul_add_right W f g)

theorem kernelMap_smul (blocks : Nat) (W : RatPoly) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (kernelMap blocks W (polySmul c f))
      (polySmul c (kernelMap blocks W f)) :=
  (partialHaarHeads_congr blocks (RatPolyCoeffEqv.polyMul_smul_right c W f)).trans
    (heads_smul blocks c (polyMul W f))

private theorem partial_lift (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (liftHead p)) p := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (liftHead p)) p := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        refine ⟨rfl, ?_, ih⟩
        have h : headQuaternionMoment (0::0::0::0::t.1) ≈ 1 := by
          change sphereMoment4 0 0 0 0 ≈ 1
          decide +kernel
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left t.2 _ _ h) (Q'.mul_one_eqv t.2)
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- Integrating the freshly adjoined normalized heads leaves the literal tail. -/
theorem partialHaarHeads_liftBoundary : ∀ (blocks : Nat) (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads blocks (liftBoundary blocks p)) p
  | 0, _ => .refl _
  | blocks+1, p =>
      (partialHaarHeads_congr blocks (partial_lift (liftBoundary blocks p))).trans
        (partialHaarHeads_liftBoundary blocks p)

theorem haar_liftBoundary (headBlocks tailBlocks : Nat) (p : RatPoly) :
    quaternionHaar (tailBlocks+headBlocks) (liftBoundary headBlocks p) ≈
      quaternionHaar tailBlocks p :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_partialHaarHeads tailBlocks headBlocks (liftBoundary headBlocks p)))
    (haar_of_coeff (partialHaarHeads_liftBoundary headBlocks p))

/-- Exact bilinear pairing of the computed output against an arbitrary tail probe. -/
theorem kernelMap_pairing (blocks : Nat) (W f g : RatPoly) :
    weightedPair (blocks+blocks) W f (liftBoundary blocks g) ≈
      quaternionHaar blocks (polyMul (kernelMap blocks W f) g) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ W).trans (RatPolyCoeffEqv.mul_assoc W f _).symm))
    (head_pairing blocks blocks (polyMul W f) g)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- The same explicit cap controls every supported bilinear pairing. -/
theorem kernelMap_bilinear_bound {blocks : Nat} {W f g : RatPoly} {C : Q'}
    (HW : Certificate (blocks+blocks) W) (IW : Interval (blocks+blocks) W C)
    (hf : SupportedQuaternionBlocks blocks f) (hg : SupportedQuaternionBlocks blocks g) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) g) *
        quaternionHaar blocks (polyMul (kernelMap blocks W f) g) ≤
      (C*C) * (quaternionHaar blocks (polyMul f f) * quaternionHaar blocks (polyMul g g)) := by
  have hf' : SupportedQuaternionBlocks (blocks+blocks) f := support_mono hf (by omega)
  have hg' := lift_supported hg blocks
  have hcs := weighted_cauchySchwarz (blocks+blocks) W f (liftBoundary blocks g) HW hf' hg'
  have hp := kernelMap_pairing blocks W f g
  have hfirst : weightedPair (blocks+blocks) W f f ≤
      C * quaternionHaar blocks (polyMul f f) :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (IW.weighted_haar_bound (.square f hf'))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _
          (quaternionHaar_extend_supported_endpoint (by omega) _ (supported_polyMul hf hf)))))
  have hlift : quaternionHaar (blocks+blocks)
      (polyMul (liftBoundary blocks g) (liftBoundary blocks g)) ≈
      quaternionHaar blocks (polyMul g g) := by
    rw [← lift_product]
    exact haar_liftBoundary blocks blocks (polyMul g g)
  have hsecond : weightedPair (blocks+blocks) W (liftBoundary blocks g) (liftBoundary blocks g) ≤
      C * quaternionHaar blocks (polyMul g g) :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (IW.weighted_haar_bound (.square (liftBoundary blocks g) hg'))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _ hlift)))
  have hnonnegative : (0 : Q') ≤ C * quaternionHaar blocks (polyMul f f) :=
    Q'.mul_nonneg _ _ IW.nonnegative (Certificate.haar_nonnegative (.square f hf))
  have hsecond_nonnegative : (0 : Q') ≤
      weightedPair (blocks+blocks) W (liftBoundary blocks g) (liftBoundary blocks g) :=
    HW.square_insertion_nonnegative _ hg'
  have hproduct := Q'.mul_le_mul_of_nonneg hfirst hsecond hnonnegative hsecond_nonnegative
  have hreorder :
      (C * quaternionHaar blocks (polyMul f f)) * (C * quaternionHaar blocks (polyMul g g)) ≈
        (C*C) * (quaternionHaar blocks (polyMul f f) * quaternionHaar blocks (polyMul g g)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun
        | 0 => C
        | 1 => quaternionHaar blocks (polyMul f f)
        | _ => quaternionHaar blocks (polyMul g g))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_congr hp hp))
    (Q'.le_trans' _ _ _ hcs (Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hreorder)))

/-- Ordinary-Haar squared norm bound for the actual partial-integration map.
The output norm is cancelled only when rationally positive; zero is handled separately. -/
theorem kernelMap_square_bound {blocks : Nat} {W f : RatPoly} {C : Q'}
    (HW : Certificate (blocks+blocks) W) (IW : Interval (blocks+blocks) W C)
    (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks
        (polyMul (kernelMap blocks W f) (kernelMap blocks W f)) ≤
      (C*C) * quaternionHaar blocks (polyMul f f) := by
  let A := quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f))
  let F := quaternionHaar blocks (polyMul f f)
  have h := kernelMap_bilinear_bound HW IW hf (kernelMap_supported IW.support hf)
  change A*A ≤ (C*C)*(F*A) at h
  change A ≤ (C*C)*F
  by_cases hpos : (0 : Q') < A
  · have hreorder : (C*C)*(F*A) ≈ A*((C*C)*F) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)
    exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hreorder)) hpos
  · have hzero : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn
    exact Q'.le_trans' _ _ _ hzero
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ IW.nonnegative IW.nonnegative)
        (Certificate.haar_nonnegative (.square f hf)))

end YMGap.Continuum.SU2QuaternionHaarKernelBound

#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_congr
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_add
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_smul
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.partialHaarHeads_liftBoundary
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.haar_liftBoundary
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_pairing
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_bilinear_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarKernelBound.kernelMap_square_bound
