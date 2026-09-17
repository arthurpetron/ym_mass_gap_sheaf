/-
# Positive semidefiniteness of the ACTUAL product heat operator

Each original character kernel is its proved positive-weighted sum of
representation-column pairings. A lower channel and its literal upper
coordinate lift multiply the SAME signed input. Induction over the selected
link pairs therefore reduces the quadratic to ordinary Haar squares.
Repeated pairs are allowed; no Nodup premise or pointwise density floor is
needed. The nome is merely nonnegative, and every retained cutoff is covered.

This is an actual finite kinetic-operator theorem, not a strict contraction
or an OS identification. Interacting transfer and current Wilson completion
consumers must retain the full spatial weight and prove their own pins.
-/

import YMGap.Continuum.SU2QuaternionCoordinateColumnLift
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.SU2QuaternionProductHeatPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial (polynomialSum)
open YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

private def pairSource (blocks : Nat) (f : RatPoly) : RatPoly :=
  polyMul f (liftBoundary blocks f)

/-- The original two-slice kernel quadratic with an arbitrary signed input. -/
def haarQuadratic (blocks : Nat) (W f : RatPoly) : Q' :=
  quaternionHaar (blocks+blocks) (polyMul W (pairSource blocks f))

private def insertion (blocks : Nat) (W f p : RatPoly) : Q' :=
  quaternionHaar (blocks+blocks) (polyMul (polyMul W (pairSource blocks f)) p)

private theorem support_twice {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))

private theorem pairSource_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+blocks) (pairSource blocks p) :=
  supported_polyMul (support_twice hp) (lift_supported hp blocks)

private theorem insertion_coeff (blocks : Nat) (W f : RatPoly) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : insertion blocks W f p ≈ insertion blocks W f q :=
  haar_of_coeff (h.mul_left _)

private theorem insertion_add (blocks : Nat) (W f p q : RatPoly) :
    insertion blocks W f (polyAdd p q) ≈ insertion blocks W f p + insertion blocks W f q :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ p q))
    (quaternionHaar_append _ _ _)

private theorem insertion_smul (blocks : Nat) (W f p : RatPoly) (c : Q') :
    insertion blocks W f (polySmul c p) ≈ c * insertion blocks W f p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c _ p))
    (quaternionHaar_polySmul _ _ _)

private theorem channel_pairing {blocks : Nat} {W f a b : RatPoly}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hf : SupportedQuaternionBlocks blocks f) (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks (blocks+blocks) b)
    (hab : PaddedPolynomialCoeffEqv (blocks+blocks) (liftBoundary blocks a) b) :
    insertion blocks W f (polyMul a b) ≈ haarQuadratic blocks W (polyMul f a) := by
  have hpin : PaddedPolynomialCoeffEqv (blocks+blocks)
      (polyMul (polyMul W (pairSource blocks f)) (polyMul a b))
      (polyMul W (pairSource blocks (polyMul f a))) := by
    refine ((PaddedPolynomialCoeffEqv.refl _ _).mul
      ((PaddedPolynomialCoeffEqv.refl _ a).mul hab.symm)).trans ?_
    apply PaddedPolynomialCoeffEqv.of_coeff
    unfold pairSource
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4))))
      (by decide) (fun
        | 0 => W | 1 => f | 2 => liftBoundary blocks f | 3 => a | _ => liftBoundary blocks a)
  exact hpin.haar
    (supported_polyMul (supported_polyMul hW (pairSource_supported hf))
      (supported_polyMul (support_twice ha) hb))
    (supported_polyMul hW (pairSource_supported (supported_polyMul hf ha)))

private theorem tensor_insertion_nonnegative {blocks : Nat} {W f : RatPoly}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hpositive : ∀ g, SupportedQuaternionBlocks blocks g → (0 : Q') ≤ haarQuadratic blocks W g)
    (hf : SupportedQuaternionBlocks blocks f) :
    ∀ (degree : Nat) (x y : PolyTensor degree),
      PolyTensorSupported blocks degree x → PolyTensorSupported (blocks+blocks) degree y →
      TensorLiftImage blocks degree x y →
      (0 : Q') ≤ insertion blocks W f (polyTensorInner degree x y).1
  | 0, x, y, hx, hy, hxy => by
      have h1 := Q'.le_trans' _ _ _ (hpositive _ (supported_polyMul hf hx.1))
        (Q'.ge_of_eqv (channel_pairing hW hf hx.1 hy.1 hxy.1))
      have h2 := Q'.le_trans' _ _ _ (hpositive _ (supported_polyMul hf hx.2))
        (Q'.ge_of_eqv (channel_pairing hW hf hx.2 hy.2 hxy.2))
      have he : RatPolyCoeffEqv (polyTensorInner 0 x y).1
          (polyAdd (polyMul x.1 y.1) (polyMul x.2 y.2)) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.neg (.var 1)) (.var 3))))
          (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun | 0 => x.1 | 1 => x.2 | 2 => y.1 | _ => y.2)
      exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ h1 h2)
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (insertion_coeff blocks W f he)
          (insertion_add blocks W f _ _)))
  | degree+1, x, y, hx, hy, hxy =>
      Q'.le_trans' _ _ _ (Q'.zero_le_add _ _
        (tensor_insertion_nonnegative hW hpositive hf degree (x false) (y false)
          (hx false) (hy false) (hxy false))
        (tensor_insertion_nonnegative hW hpositive hf degree (x true) (y true)
          (hx true) (hy true) (hxy true)))
        (Q'.ge_of_eqv (insertion_add blocks W f _ _))

private theorem prefix_insertion_nonnegative (blocks : Nat) (W f : RatPoly)
    (p : Nat → ComplexRatPoly) (hp : ∀ k, (0 : Q') ≤ insertion blocks W f (p k).1) :
    ∀ count, (0 : Q') ≤ insertion blocks W f (polynomialSum count p).1
  | 0 => by change (0 : Q') ≤ quaternionHaar _ (polyMul _ polyZero)
            exact Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right _))
  | count+1 => Q'.le_trans' _ _ _ (Q'.zero_le_add _ _
      (prefix_insertion_nonnegative blocks W f p hp count) (hp count))
      (Q'.ge_of_eqv (insertion_add blocks W f _ _))

private theorem gram_insertion_nonnegative {blocks slot : Nat} (hslot : slot < blocks)
    {W f : RatPoly} (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hpositive : ∀ g, SupportedQuaternionBlocks blocks g → (0 : Q') ≤ haarQuadratic blocks W g)
    (hf : SupportedQuaternionBlocks blocks f) (degree : Nat) :
    (0 : Q') ≤ insertion blocks W f
      (polynomialGramKernel (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot))
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (blocks+slot))) degree).1 := by
  apply prefix_insertion_nonnegative
  intro k
  exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.le_of_lt (basisInverseWeight_pos degree k))
    (tensor_insertion_nonnegative hW hpositive hf degree _ _
      (coordinateColumn_supported hslot degree k)
      (coordinateColumn_supported (by omega : blocks+slot < blocks+blocks) degree k)
      (coordinateColumn_lift blocks slot degree k)))
    (Q'.ge_of_eqv (insertion_smul blocks W f _ _))

private theorem character_insertion_nonnegative {blocks slot : Nat} (hslot : slot < blocks)
    {W f : RatPoly} (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hpositive : ∀ g, SupportedQuaternionBlocks blocks g → (0 : Q') ≤ haarQuadratic blocks W g)
    (hf : SupportedQuaternionBlocks blocks f) (degree : Nat) :
    (0 : Q') ≤ insertion blocks W f (characterPolynomial (scalarAt (blocks+slot) slot) degree) := by
  have hg := (character_haar_gram_of_unit_radii
    (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot))
    (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (blocks+slot)))
    (haarNorm_coordinate (by omega : slot < blocks+blocks))
    (haarNorm_coordinate (by omega : blocks+slot < blocks+blocks)) degree).1
  have hs := characterPolynomial_coeffEqv
    (pathProduct_scalar (PolyQuaternion.coordinateVariable slot)
      (PolyQuaternion.coordinateVariable (blocks+slot))) degree
  have he := Q'.eqv_trans _ _ _ (insertion_coeff blocks W f hs)
    (hg (polyMul W (pairSource blocks f)))
  exact Q'.le_trans' _ _ _ (gram_insertion_nonnegative hslot hW hpositive hf degree)
    (Q'.ge_of_eqv he)

private theorem sum_insertion_nonnegative {A : Type} (blocks : Nat) (W f : RatPoly)
    (p : A → RatPoly) : ∀ (xs : List A),
      (∀ a, a ∈ xs → (0 : Q') ≤ insertion blocks W f (p a)) →
      (0 : Q') ≤ insertion blocks W f (finitePolySum p xs)
  | [], _ => by change (0 : Q') ≤ quaternionHaar _ (polyMul _ polyZero)
                exact Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right _))
  | a::xs, hp => Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ (hp a List.mem_cons_self)
      (sum_insertion_nonnegative blocks W f p xs (fun b hb => hp b (List.mem_cons_of_mem a hb))))
      (Q'.ge_of_eqv (insertion_add blocks W f _ _))

/-- Multiplying by an ACTUAL heat factor preserves the proved quadratic
positivity. This is the induction step, not an assumed heat-kernel estimate. -/
theorem heat_preserves_quadratic {blocks slot : Nat} (hslot : slot < blocks)
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {W : RatPoly}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hpositive : ∀ g, SupportedQuaternionBlocks blocks g → (0 : Q') ≤ haarQuadratic blocks W g)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    (0 : Q') ≤ haarQuadratic blocks (polyMul (heatAt slot (blocks+slot) w K) W) f := by
  have hheat : (0 : Q') ≤ insertion blocks W f (heatAt (blocks+slot) slot w K) := by
    apply sum_insertion_nonnegative
    intro degree hdegree
    have hc : (0 : Q') ≤ coeffAt (heatKernelPacket K w) degree := by
      rw [coeffAt_heatKernelPacket (List.mem_range.mp hdegree)]
      exact coeffW_nonneg hw degree
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hc
      (character_insertion_nonnegative hslot hW hpositive hf degree))
      (Q'.ge_of_eqv (insertion_smul blocks W f _ _))
  have he : haarQuadratic blocks (polyMul (heatAt slot (blocks+slot) w K) W) f ≈
      insertion blocks W f (heatAt (blocks+slot) slot w K) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      (((heatAt_symm slot (blocks+slot) w K).mul_right W).mul_right _))
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
        (fun | 0 => heatAt (blocks+slot) slot w K | 1 => W | _ => pairSource blocks f)))
  exact Q'.le_trans' _ _ _ hheat (Q'.ge_of_eqv he)

/-- Every cutoff, every nonnegative nome and any list of valid link pairs.
Repeated indices are permitted because PSD products do not need normalized marginals. -/
theorem productHeat_quadratic_nonnegative (blocks : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) : ∀ (ids : List Nat), (∀ i, i ∈ ids → i < blocks) →
      ∀ f, SupportedQuaternionBlocks blocks f → (0 : Q') ≤ haarQuadratic blocks (productHeat blocks w K ids) f
  | [], _, f, hf =>
      Q'.le_trans' _ _ _ (SumOfSquares.q_mul_self_nonneg (quaternionHaar blocks f))
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
          (haar_split_pairing hf f)))
  | i::ids, hi, f, hf =>
      heat_preserves_quadratic (hi i List.mem_cons_self) w hw K
        (productHeat_supported blocks w K ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))
        (productHeat_quadratic_nonnegative blocks w hw K ids
          (fun j hj => hi j (List.mem_cons_of_mem i hj))) f hf

/-- PSD of the literal original kernelMap, including its output-coordinate convention. -/
theorem productMap_nonnegative (blocks : Nat) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hi : ∀ i, i ∈ ids → i < blocks)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul f (productMap blocks w K ids f)) :=
  Q'.le_trans' _ _ _ (productHeat_quadratic_nonnegative blocks w hw K ids hi f hf)
    (Q'.ge_of_eqv (productMap_pairing blocks w K ids f f))

end YMGap.Continuum.SU2QuaternionProductHeatPositive

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositive.haarQuadratic
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositive.heat_preserves_quadratic
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositive.productHeat_quadratic_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositive.productMap_nonnegative
