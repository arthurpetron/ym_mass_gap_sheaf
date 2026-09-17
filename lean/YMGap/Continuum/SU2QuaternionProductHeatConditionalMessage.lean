/-
# One-coordinate normalizers for the entire selected product heat message

Integrating one OUTPUT coordinate of the full product message gives the
message with just its matching heat factor erased, in supported Haar
pairings. That erased message is literally independent of the coordinate
by `productMap_independent_of_not_mem`.

For any supported certified input, the original one-factor heat floor and
cap give positive certificates comparing the full message to this same
erased message. Every other heat factor and the complete input remain.
The constants depend on the nome but not the number of selected blocks,
the input, or any depth used to construct it; the cutoff guard is explicit.

These are conditional NORMALIZATION bounds. They do not establish small
cross-coordinate influence, weighted martingale orthogonality, an
interacting OS gap, or a spacing/continuum limit. In particular the
conditional pin is not a false free-polynomial normalization identity.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (heatInterval)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv

/-- The actual output conditional marginal is the erased-factor message.
Arbitrary supported output spectators are retained. -/
theorem productMap_conditional_pin (n : Nat) (w : Q') (K i : Nat)
    (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    SupportedHaarEqv n
      (project i (productMap n w K (i::ids) f))
      (productMap n w K ids f) := by
  intro r hr
  have hfixed := project_fixed i (productMap n w K ids f)
    (productMap_independent_of_not_mem n w K ids hids i hi hnot f hf)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (project_selfAdjoint n i hi r (productMap n w K (i::ids) f)))
    (Q'.eqv_trans _ _ _
      (productMap_cons_test_independent n w K i ids hi hnot hids
        f (project i r) hf (project_supported i hr) (project_independent i r))
      (Q'.eqv_trans _ _ _
        (project_selfAdjoint n i hi r (productMap n w K ids f))
        (haar_of_coeff (hfixed.mul_left r))))

private theorem heads_add : ∀ (n : Nat) (p q : RatPoly),
    partialHaarHeads n (polyAdd p q) =
      polyAdd (partialHaarHeads n p) (partialHaarHeads n q)
  | 0, _, _ => rfl
  | n+1, p, q => by
      simp only [partialHaarHeads, partialHaarHead_add, heads_add n]

private theorem head_neg (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyNeg p)) (polyNeg (partialHaarHead p)) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (polyNeg p))
      (polyNeg (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.neg_mul_eqv _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem heads_neg : ∀ (n : Nat) (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads n (polyNeg p)) (polyNeg (partialHaarHeads n p))
  | 0, _ => .refl _
  | n+1, p =>
      (partialHaarHeads_congr n (head_neg p)).trans (heads_neg n (partialHaarHead p))

private theorem heads_sub (n : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads n (polyAdd p (polyNeg q)))
      (polyAdd (partialHaarHeads n p) (polyNeg (partialHaarHeads n q))) := by
  rw [heads_add]
  exact (RatPolyCoeffEqv.refl _).add (heads_neg n q)

private theorem heads_smul : ∀ (n : Nat) (c : Q') (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads n (polySmul c p))
      (polySmul c (partialHaarHeads n p))
  | 0, _, _ => .refl _
  | n+1, c, p =>
      (partialHaarHeads_congr n (partialHaarHead_smul c p)).trans
        (heads_smul n c (partialHaarHead p))

private theorem floor_algebra (u r f : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (polyMul (polyAdd u (polyNeg (cap c))) (polyMul r f))
      (polyAdd (polyMul (polyMul u r) f) (polyNeg (polySmul c (polyMul r f)))) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 3))) (.mul (.var 1) (.var 2)))
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.neg (.mul (.var 3) (.mul (.var 1) (.var 2)))))
    (by decide) (fun | 0 => u | 1 => r | 2 => f | _ => cap c)).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left c _)))

private theorem cap_algebra (u r f : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (polyMul (polyAdd (cap c) (polyNeg u)) (polyMul r f))
      (polyAdd (polySmul c (polyMul r f)) (polyNeg (polyMul (polyMul u r) f))) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 3) (.neg (.var 0))) (.mul (.var 1) (.var 2)))
    (.add (.mul (.var 3) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
    (by decide) (fun | 0 => u | 1 => r | 2 => f | _ => cap c)).trans
    ((cap_mul_left c _).add (RatPolyCoeffEqv.refl _))

/-- One-factor lower certificate. All remaining factors and the whole
certified input are kept inside the original partial Haar integral. -/
def productMap_floorCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (i : Nat) (ids : List Nat) (hi : i < n)
    (hids : ∀ j, j ∈ ids → j < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (polyAdd (productMap n w K (i::ids) f)
      (polyNeg (polySmul (headFloor w) (productMap n w K ids f)))) := by
  let R := productHeat n w K ids
  let u := heatAt i (n+i) w K
  have hraw : Certificate (n+n)
      (polyMul (polyAdd u (polyNeg (cap (headFloor w)))) (polyMul R f)) :=
    (heatAt_floorCertificate (show i < n+n by omega)
      (show n+i < n+n by omega) hw0 hw1 K hK).mul
      ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
        (certificate_extend n hf F))
  have hp := (partialHaarHeads_congr n (floor_algebra u R f (headFloor w))).trans
    ((heads_sub n (polyMul (polyMul u R) f) (polySmul (headFloor w) (polyMul R f))).trans
      ((RatPolyCoeffEqv.refl _).add
        (RatPolyCoeffEqv.neg (heads_smul n (headFloor w) (polyMul R f)))))
  exact .ofCoeff hp.symm (partialHaarHeads_certificate n n hraw)

/-- One-factor upper certificate with the same erased normalizer as the
lower certificate; no product cap or volume factor is introduced. -/
def productMap_capCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (i : Nat) (ids : List Nat) (hi : i < n)
    (hids : ∀ j, j ∈ ids → j < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (polyAdd (polySmul (prefixCap w) (productMap n w K ids f))
      (polyNeg (productMap n w K (i::ids) f))) := by
  let R := productHeat n w K ids
  let u := heatAt i (n+i) w K
  have hraw : Certificate (n+n)
      (polyMul (polyAdd (cap (prefixCap w)) (polyNeg u)) (polyMul R f)) :=
    (heatInterval (show i < n+n by omega)
      (show n+i < n+n by omega) hw0 hw1 K).upper.mul
      ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
        (certificate_extend n hf F))
  have hp := (partialHaarHeads_congr n (cap_algebra u R f (prefixCap w))).trans
    ((heads_sub n (polySmul (prefixCap w) (polyMul R f)) (polyMul (polyMul u R) f)).trans
      ((heads_smul n (prefixCap w) (polyMul R f)).add (RatPolyCoeffEqv.refl _)))
  exact .ofCoeff hp.symm (partialHaarHeads_certificate n n hraw)

end YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage

#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage.productMap_conditional_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage.productMap_floorCertificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage.productMap_capCertificate
