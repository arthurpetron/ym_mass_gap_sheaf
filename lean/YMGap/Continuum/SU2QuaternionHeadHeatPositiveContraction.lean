/-
# Symmetry and positive contraction of the actual head heat map

Exchange the two head coordinates, retaining every spectator, to prove
bilinear symmetry. The computed harmonic weights then give 0 <= H <= I
at EVERY finite cutoff for 0 <= w <= 1. Rational form Cauchy--Schwarz
upgrades this to the actual image norm bound, without a pointwise heat
floor, a spectral theorem, or an assumed operator realization.

These are ingredients for product composition, not a product-defect theorem
or an interacting/OS/continuum gap.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
import YMGap.Continuum.PositiveContractionOneStepForm

namespace YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem heat_swap_carrier (tail : Nat) (w : Q') (K : Nat) :
    HaarCarrierEqv (tail+2)
      (reindexQuaternionPolynomial (spareSwap (tail+1) (by omega)) (relativeHeat w K))
      (relativeHeat w K) := by
  let s := spareSwap (tail+1) (by omega)
  have hp : QuaternionPrefixPolyQuaternionEqv (tail+2)
      (reindexPolyQuaternion s
        (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
          (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))))
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 1)
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))) := by
    rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
    exact (reindex_coordinateVariable_prefix s (by omega)
      (by simp [s, spareSwap, blockSwapInvolution, blockSwapMap])).mul
      (reindex_coordinateVariable_prefix s (by omega)
        (by simp [s, spareSwap, blockSwapInvolution, blockSwapMap])).conj
  have hc (d : Nat) : QuaternionPrefixPolynomialEqv (tail+2)
      (reindexQuaternionPolynomial s (characterPolynomial (scalarAt 0 1) d))
      (characterPolynomial (scalarAt 1 0) d) :=
    (reindexQuaternionPolynomial_character_prefix s _ d).trans (hp.scalar.character d)
  have he : QuaternionPrefixPolynomialEqv (tail+2)
      (reindexQuaternionPolynomial s (heatAt 0 1 w K)) (heatAt 1 0 w K) := by
    unfold heatAt
    induction List.range (K+1) with
    | nil => exact .nil
    | cons d ds ih =>
        simp only [finitePolySum, reindexQuaternionPolynomial_add,
          reindexQuaternionPolynomial_smul]
        exact ((hc d).smul _).append ih
  exact HaarCarrierEqv.trans
    (carrierOfPrefix (reindex_supported s _)
      (heat_supported (by omega : 1 < tail+2) (by omega : 0 < tail+2) w K) he)
    (RatPolyCoeffEqv.haarCarrier (heatAt_symm 1 0 w K))

/-- Source/output exchange proves symmetry of the actual local kernel form. -/
theorem heatPair_symm (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    heatPair tail w K p q ≈ heatPair tail w K q p := by
  let s := spareSwap (tail+1) (by omega)
  have cp := carrierOfPrefix (reindex_supported s (liftHead p))
    (copy_supported (by omega) hp) (copy_reindex_prefix (tail+1) (by omega) p)
  have cq := carrierOfPrefix (reindex_supported s (liftHead q))
    (copy_supported (by omega) hq) (copy_reindex_prefix (tail+1) (by omega) q)
  have sp := reindex_carrier s (reindex_supported s _) (copy_supported (by omega) hp) cp
  have ip := carrierOfPrefix (reindex_supported s _) (lift_supported hp 1)
    (reindex_twice_prefix s (liftHead p))
  have pc := HaarCarrierEqv.trans (HaarCarrierEqv.symm sp) ip
  have hs := quaternionHaar_reindex s
    (polyMul (polyMul (relativeHeat w K) (copy p)) (liftHead q))
    (supported_polyMul
      (supported_polyMul
        (heat_supported (by omega : 0 < tail+2) (by omega : 1 < tail+2) w K)
        (copy_supported (by omega) hp)) (lift_supported hq 1))
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul] at hs
  have ht := HaarCarrierEqv.mul (HaarCarrierEqv.mul (heat_swap_carrier tail w K) pc) cq
  have hc : RatPolyCoeffEqv
      (polyMul (polyMul (relativeHeat w K) (liftHead p)) (copy q))
      (polyMul (polyMul (relativeHeat w K) (copy q)) (liftHead p)) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).trans
      (((RatPolyCoeffEqv.mul_comm _ _).mul_left _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (Q'.eqv_trans _ _ _ (haar_of_carrier ht) (haar_of_coeff hc))

/-- Self-adjointness refers to the computed head map on the same Haar carrier. -/
theorem headMap_symmetric (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    quaternionHaar (tail+1) (polyMul p (headMap w K q)) ≈
      quaternionHaar (tail+1) (polyMul (headMap w K p) q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (headMap_pairing tail w K q p)
      (Q'.eqv_trans _ _ _ (heatPair_symm tail w K q p hq hp)
        (Q'.eqv_symm (headMap_pairing tail w K p q))))

private theorem head_diagonal (tail : Nat) (w : Q') (K : Nat) (p : RatPoly) :
    quaternionHaar (tail+1) (polyMul p (headMap w K p)) ≈ heatPair tail w K p p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (headMap_pairing tail w K p p)

theorem headMap_positive (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ quaternionHaar (tail+1) (polyMul p (headMap w K p)) :=
  Q'.le_trans' _ _ _ (polynomial_pair_nonnegative tail hw0 K p hp)
    (Q'.ge_of_eqv (head_diagonal tail w K p))

theorem headMap_form_le_norm (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p (headMap w K p)) ≤
      quaternionHaar (tail+1) (polyMul p p) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (head_diagonal tail w K p))
    (Q'.le_of_sub_nonneg (polynomial_defect_nonnegative tail hw0 hw1 K p hp))

/-- Actual image norm bounded by the same-input pairing, at every cutoff.
The rational Cauchy--Schwarz proof does not require a pointwise heat floor. -/
theorem headMap_square_le_pair (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul (headMap w K p) (headMap w K p)) ≤
      quaternionHaar (tail+1) (polyMul p (headMap w K p)) := by
  let D := finiteHaarGNSData (tail+1)
  let P : D.V → D.V := fun a => ⟨headMap w K a.val, headMap_supported tail w K a.property⟩
  have hs : ∀ a b, D.B a (P b) ≈ D.B (P a) b :=
    fun a b => headMap_symmetric tail w K a.val b.val a.property b.property
  have hpos : ∀ a, (0 : Q') ≤ D.B a (P a) :=
    fun a => headMap_positive tail hw0 K a.val a.property
  have hu : ∀ a, D.B a (P a) ≤ (1 : Q') * D.B a a :=
    fun a => Q'.le_trans' _ _ _ (headMap_form_le_norm tail hw0 hw1 K a.val a.property)
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have h := PositiveContractionOneStepForm.square_form_bound D P hs hpos
    (by decide : (0 : Q') ≤ 1) hu ⟨p, hp⟩
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- The literal local update is a Haar norm contraction for 0<=w<=1, any K. -/
theorem headMap_square_contraction (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul (headMap w K p) (headMap w K p)) ≤
      quaternionHaar (tail+1) (polyMul p p) :=
  Q'.le_trans' _ _ _ (headMap_square_le_pair tail hw0 hw1 K p hp)
    (headMap_form_le_norm tail hw0 hw1 K p hp)

end YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.heatPair_symm
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.headMap_symmetric
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.headMap_positive
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.headMap_form_le_norm
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.headMap_square_le_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction.headMap_square_contraction
