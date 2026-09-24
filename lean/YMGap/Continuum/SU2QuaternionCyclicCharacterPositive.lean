/-
# Positive full cycles of actual character kernels

Each fresh-output step uses the dimension-normalized relative character at
its chosen degree. Ordered finite Haar integration identifies a complete
cycle with the product of the original lower/upper character kernels.
Their already constructed Gram positivity proves the diagonal endpoint
pairing nonnegative. No positivity of an intermediate rotating step, no
commutation of Fischer projections, and no continuum assertion is used.
-/

import YMGap.Continuum.SU2QuaternionCyclicCharacterSelection
import YMGap.Continuum.SU2QuaternionProductHeatPrefix

namespace YMGap.Continuum.SU2QuaternionCyclicCharacterPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionCyclicCharacterSelection
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The chosen degrees are attached to consecutive original source slots. -/
def pathSlots : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | start, d::ds => (start,d)::pathSlots (start+1) ds

private theorem pathSlots_lt (start : Nat) : ∀ ds : List Nat,
    ∀ a, a ∈ pathSlots start ds → a.1 < start+ds.length
  | [], _, h => by contradiction
  | d::ds, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.length_cons]; omega
      · have ht := pathSlots_lt (start+1) ds a h
        simp only [List.length_cons]; omega

private theorem prefix_supported (n m : Nat) : ∀ (ds : List Nat) (start : Nat),
    start+ds.length ≤ m → SupportedQuaternionBlocks (n+m)
      (characterProduct n (pathSlots start ds))
  | [], _, _ => supported_one _
  | d::ds, start, h => by
      have hs : start < n+m := by simp only [List.length_cons] at h; omega
      have ht : n+start < n+m := by simp only [List.length_cons] at h; omega
      exact supported_polyMul (normalizedCharacterAt_supported (degree := d) hs ht)
        (prefix_supported n m ds (start+1) (by simp only [List.length_cons] at h; omega))

private theorem lift_scalarAt (a b : Nat) :
    liftHead (scalarAt a b) = scalarAt (a+1) (b+1) := by
  change (liftQuaternion 1 (PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b)))).scalar = _
  simp only [liftQuaternion_mul, liftQuaternion_conj, liftQuaternion_coordinateVariable]
  change scalarAt (1+a) (1+b) = scalarAt (a+1) (b+1)
  rw [Nat.add_comm 1 a, Nat.add_comm 1 b]

private theorem lift_characterAt (blocks a b d : Nat) :
    PaddedPolynomialCoeffEqv blocks (liftHead (normalizedCharacterAt a b d))
      (normalizedCharacterAt (a+1) (b+1) d) := by
  unfold normalizedCharacterAt
  change PaddedPolynomialCoeffEqv blocks (liftBoundary 1 (polySmul _ _)) _
  rw [lift_smul]
  have h := lift_character blocks 1 (scalarAt a b) d
  change PaddedPolynomialCoeffEqv blocks
    (liftHead (characterPolynomial (scalarAt a b) d))
    (characterPolynomial (liftHead (scalarAt a b)) d) at h
  rw [lift_scalarAt] at h
  exact h.smul _

private theorem lift_prefix (blocks n : Nat) : ∀ (ds : List Nat) (start : Nat),
    PaddedPolynomialCoeffEqv blocks
      (liftHead (characterProduct n (pathSlots start ds)))
      (characterProduct n (pathSlots (start+1) ds))
  | [], _ => lift_one blocks 1
  | d::ds, start => by
      change PaddedPolynomialCoeffEqv blocks
        (liftHead (polyMul (normalizedCharacterAt start (n+start) d)
          (characterProduct n (pathSlots (start+1) ds)))) _
      rw [liftHead_mul]
      have h := (lift_characterAt blocks start (n+start) d).mul
        (lift_prefix blocks n ds (start+1))
      simpa only [Nat.add_assoc] using h

private theorem prefix_cons_carrier (n d : Nat) (ds : List Nat) :
    HaarCarrierEqv (n+(ds.length+1))
      (characterProduct n (pathSlots 0 (d::ds)))
      (polyMul (normalizedCharacterAt 0 n d)
        (liftHead (characterProduct n (pathSlots 0 ds)))) := by
  have hc := (PaddedPolynomialCoeffEqv.refl (n+(ds.length+1))
    (normalizedCharacterAt 0 n d)).mul (lift_prefix (n+(ds.length+1)) n ds 0).symm
  have hs := prefix_supported n (ds.length+1) (d::ds) 0 (by simp)
  have ht : SupportedQuaternionBlocks (n+(ds.length+1))
      (polyMul (normalizedCharacterAt 0 n d)
        (liftHead (characterProduct n (pathSlots 0 ds)))) := by
    apply supported_polyMul (normalizedCharacterAt_supported (degree := d) (by omega) (by omega))
    simpa only [Nat.add_assoc] using
      (lift_supported (prefix_supported n ds.length ds 0 (by simp)) 1)
  apply carrier_of_supported hs ht
  exact SupportedHaarEqv.of_padded (by simpa only [pathSlots, Nat.add_zero] using hc) hs ht

/-- Fresh-output character steps in the same order as the computed degree path. -/
def characterIterate (n : Nat) : List Nat → RatPoly → RatPoly
  | [], p => p
  | d::ds, p => characterIterate n ds (characterCycleStep n d p)

theorem characterIterate_supported (n : Nat) : ∀ (ds : List Nat) {p : RatPoly},
    SupportedQuaternionBlocks n p → SupportedQuaternionBlocks n (characterIterate n ds p)
  | [], _, hp => hp
  | d::ds, _, hp => characterIterate_supported n ds (characterCycleStep_supported n d hp)

theorem characterIterate_carrier (n : Nat) : ∀ (ds : List Nat) {p q : RatPoly},
    SupportedQuaternionBlocks n p → SupportedQuaternionBlocks n q → HaarCarrierEqv n p q →
    HaarCarrierEqv n (characterIterate n ds p) (characterIterate n ds q)
  | [], _, _, _, _, h => h
  | d::ds, _, _, hp, hq, h => by
      apply characterIterate_carrier n ds
        (characterCycleStep_supported n d hp) (characterCycleStep_supported n d hq)
      apply partialHaarHead_carrier
      exact HaarCarrierEqv.mul_left (normalizedCharacterAt 0 n d) (carrier_extend 1 hp hq h)

private theorem prefix_step (n d : Nat) (ds : List Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (ds.length+1)
        (polyMul (polyMul (normalizedCharacterAt 0 n d)
          (liftHead (characterProduct n (pathSlots 0 ds)))) p))
      (partialHaarHeads ds.length
        (polyMul (characterProduct n (pathSlots 0 ds)) (characterCycleStep n d p))) := by
  let A := normalizedCharacterAt 0 n d
  let B := characterProduct n (pathSlots 0 ds)
  have hr : RatPolyCoeffEqv (polyMul (polyMul A (liftHead B)) p)
      (polyMul (polyMul A p) (liftHead B)) :=
    (RatPolyCoeffEqv.mul_assoc A (liftHead B) p).trans
      (((RatPolyCoeffEqv.mul_comm (liftHead B) p).mul_left A).trans
        (RatPolyCoeffEqv.mul_assoc A p (liftHead B)).symm)
  exact partialHaarHeads_congr ds.length
    ((partialHaarHead_congr hr).trans
      ((partialHaarHead_mul_lift (polyMul A p) B).trans (RatPolyCoeffEqv.mul_comm _ B)))

/-- Exact finite Fubini identity, with every character factor retained. -/
theorem character_prefix_fold_carrier (n : Nat) : ∀ (ds : List Nat) (p : RatPoly),
    HaarCarrierEqv n
      (partialHaarHeads ds.length (polyMul (characterProduct n (pathSlots 0 ds)) p))
      (characterIterate n ds p)
  | [], p => RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul p)
  | d::ds, p => by
      have hk := HaarCarrierEqv.mul_right p (prefix_cons_carrier n d ds)
      have hh := partialHaarHeads_carrier (tailBlocks := n) (headBlocks := ds.length+1) hk
      exact hh.trans ((RatPolyCoeffEqv.haarCarrier (prefix_step n d ds p)).trans
        (character_prefix_fold_carrier n ds (characterCycleStep n d p)))

/-- At a full cycle the endpoint quadratic is the original product-character
Gram quadratic. It need not be positive at an incomplete rotating prefix. -/
theorem characterIterate_diagonal_nonnegative (n : Nat) (ds : List Nat)
    (hlen : ds.length = n) (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    (0 : Q') ≤ quaternionHaar n (polyMul p (characterIterate n ds p)) := by
  have hpos := characterProduct_quadratic_nonnegative n (pathSlots 0 ds)
    (fun a ha => by have h := pathSlots_lt 0 ds a ha; simpa [hlen] using h) p hp
  have hf := character_prefix_fold_carrier n ds p p
  rw [hlen] at hf
  have hpair := head_pairing n n (polyMul (characterProduct n (pathSlots 0 ds)) p) p
  have he : haarQuadratic n (characterProduct n (pathSlots 0 ds)) p ≈
      quaternionHaar n (polyMul p (characterIterate n ds p)) := by
    apply Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
    exact Q'.eqv_trans _ _ _ hpair
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) hf)
  exact Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he)

end YMGap.Continuum.SU2QuaternionCyclicCharacterPositive

#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterPositive.characterIterate_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterPositive.characterIterate_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterPositive.character_prefix_fold_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterPositive.characterIterate_diagonal_nonnegative
