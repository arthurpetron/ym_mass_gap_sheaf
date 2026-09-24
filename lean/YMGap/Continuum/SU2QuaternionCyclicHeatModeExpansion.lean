/-
# Computed degree-path expansion of the ORIGINAL full product heat

At each actual cyclic step, compute the complete head harmonic groups and
rotate their polynomials. The finite tree depends on the input, not on nome
or cutoff. A leaf receives the product of its actual cutoff attenuations.
The resulting polynomial represents the original product map under EVERY
Haar insertion. No joint-mode orthogonality is asserted here; in particular
signed leaf pairings must not be replaced by nonnegative spectral masses.
-/

import YMGap.Continuum.SU2QuaternionCyclicHeatLinear
import YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction
import YMGap.Continuum.SU2HeatProductTaylorRemainder

namespace YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

def branchDegrees (tail : Nat) (p : RatPoly) : List Nat :=
  headDegrees (sumHarmonics (modes (tail+1) (by omega) p))

def branchPiece (tail : Nat) (p : RatPoly) (d : Nat) : RatPoly :=
  grouped d (modes (tail+1) (by omega) p)

def nextPiece (tail : Nat) (p : RatPoly) (d : Nat) : RatPoly :=
  cycleRotation (tail+1) (branchPiece tail p d)

theorem nextPiece_supported (tail : Nat) (p : RatPoly) (d : Nat) :
    SupportedQuaternionBlocks (tail+1) (nextPiece tail p d) :=
  reindex_supported _ _

private theorem sum_supported {A : Type} (n : Nat) (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks n (f a)) : ∀ ids : List A,
    SupportedQuaternionBlocks n (polySum (ids.map f))
  | [] => by intro t ht; contradiction
  | a::ids => polyAdd_supported (hf a) (sum_supported n f hf ids)

private theorem sum_carrier {A : Type} (n : Nat) (f g : A → RatPoly)
    (h : ∀ a, HaarCarrierEqv n (f a) (g a)) : ∀ ids : List A,
    HaarCarrierEqv n (polySum (ids.map f)) (polySum (ids.map g))
  | [] => .refl _ _
  | a::ids => HaarCarrierEqv.add (h a) (sum_carrier n f g h ids)

private theorem sum_coeff {A : Type} (f g : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) : ∀ ids : List A,
    RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [] => .refl _
  | a::ids => (h a).add (sum_coeff f g h ids)

private theorem sum_smul {A : Type} (c : Q') (f : A → RatPoly) : ∀ ids : List A,
    RatPolyCoeffEqv (polySum (ids.map fun a => polySmul c (f a)))
      (polySmul c (polySum (ids.map f)))
  | [] => RatPolyCoeffEqv.refl _
  | a::ids => by
      exact ((RatPolyCoeffEqv.refl _).add (sum_smul c f ids)).trans
        (RatPolyCoeffEqv.smul_add c (f a) (polySum (ids.map f))).symm

private theorem rotation_sum {A : Type} (n : Nat) (f : A → RatPoly) : ∀ ids : List A,
    cycleRotation n (polySum (ids.map f)) =
      polySum (ids.map fun a => cycleRotation n (f a))
  | [] => rfl
  | a::ids => by
      simp only [List.map_cons, polySum, cycleRotation_add, rotation_sum n f ids]

private theorem pairing_sum {A : Type} (n : Nat) (test : RatPoly)
    (f : A → RatPoly) (c : A → Q') : ∀ ids : List A,
    quaternionHaar n (polyMul test (polySum (ids.map fun a => polySmul (c a) (f a)))) ≈
      qListSum (ids.map fun a => c a * quaternionHaar n (polyMul (f a) test))
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
  | a::ids => by
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (c a) test (f a))
              (Q'.mul_eqv_congr_left _ _ _
                (haar_of_coeff (RatPolyCoeffEqv.mul_comm test (f a)))))
            (pairing_sum n test f c ids)))

/-- One step uses complete computed groups, including those above K. -/
theorem cycleStep_grouped (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (cycleStep (tail+1) w K p)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (attenuation w K d) (nextPiece tail p d))) := by
  have hh : HaarCarrierEqv (tail+1) (headMap w K p)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (attenuation w K d) (branchPiece tail p d))) := by
    intro test
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm test _))
      (Q'.eqv_trans _ _ _ (headMap_pairing tail w K p test)
        (Q'.eqv_trans _ _ _ (polynomial_pair tail w K p test hp)
          (pairing_sum (tail+1) test (branchPiece tail p) (attenuation w K) _).symm))
  have hr := cycleRotation_carrier (tail+1) (headMap_supported tail w K hp)
    (sum_supported (tail+1) _ (fun d => polySmul_supported (grouped_supported d _) _) _) hh
  have he : cycleRotation (tail+1)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (attenuation w K d) (branchPiece tail p d))) =
      polySum ((branchDegrees tail p).map fun d =>
        polySmul (attenuation w K d) (nextPiece tail p d)) := by
    rw [rotation_sum]
    simp only [cycleRotation_smul, nextPiece]
  exact (cycleStep_headMap_carrier tail w K p hp).trans (he ▸ hr)

/-- Finite computed degree tree with an arbitrary weight on each leaf path.
Its branches and leaf polynomials do not use nome or heat cutoff. -/
def modeFold (tail : Nat) : Nat → RatPoly → (List Nat → Q') → RatPoly
  | 0, p, weight => polySmul (weight []) p
  | m+1, p, weight => polySum ((branchDegrees tail p).map fun d =>
      modeFold tail m (nextPiece tail p d) (fun ds => weight (d::ds)))

theorem modeFold_supported (tail : Nat) : ∀ (m : Nat) (p : RatPoly)
    (weight : List Nat → Q'), SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) (modeFold tail m p weight)
  | 0, _, _, hp => polySmul_supported hp _
  | m+1, p, _weight, _ => sum_supported (tail+1) _
      (fun d => modeFold_supported tail m _ _ (nextPiece_supported tail p d)) _

theorem modeFold_smul (tail : Nat) : ∀ (m : Nat) (p : RatPoly)
    (weight : List Nat → Q') (c : Q'),
    RatPolyCoeffEqv (modeFold tail m p (fun ds => c * weight ds))
      (polySmul c (modeFold tail m p weight))
  | 0, p, weight, c => (RatPolyCoeffEqv.smul_assoc c (weight []) p).symm
  | m+1, p, weight, c =>
      (sum_coeff _ _ (fun d => modeFold_smul tail m (nextPiece tail p d)
        (fun ds => weight (d::ds)) c) _).trans (sum_smul c _ _)

private theorem cycleIterate_sum {A : Type} (n : Nat) (w : Q') (K m : Nat)
    (f : A → RatPoly) (hf : ∀ a, SupportedQuaternionBlocks n (f a)) :
    ∀ ids : List A, HaarCarrierEqv n (cycleIterate n w K m (polySum (ids.map f)))
      (polySum (ids.map fun a => cycleIterate n w K m (f a)))
  | [] => cycleIterate_zero n w K m
  | a::ids => (cycleIterate_add n w K m _ _ (hf a) (sum_supported n f hf ids)).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (cycleIterate_sum n w K m f hf ids))

/-- Each actual cyclic prefix equals its computed attenuation-weighted tree. -/
theorem cycleIterate_modeFold (tail : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p : RatPoly), SupportedQuaternionBlocks (tail+1) p →
      HaarCarrierEqv (tail+1) (cycleIterate (tail+1) w K m p)
        (modeFold tail m p (productAttenuation w K))
  | 0, p, _ => by
      intro test
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
        (quaternionHaar_polyMul_smul_right (tail+1) 1 test p).symm
  | m+1, p, hp => by
      let f := fun d => polySmul (attenuation w K d) (nextPiece tail p d)
      have hf : ∀ d, SupportedQuaternionBlocks (tail+1) (f d) :=
        fun d => polySmul_supported (nextPiece_supported tail p d) _
      have hs := cycleIterate_carrier (tail+1) w K m
        (cycleStep_supported _ _ _ hp) (sum_supported (tail+1) f hf _)
        (cycleStep_grouped tail w K p hp)
      have hl := cycleIterate_sum (tail+1) w K m f hf (branchDegrees tail p)
      have ht (d : Nat) : HaarCarrierEqv (tail+1)
          (cycleIterate (tail+1) w K m (f d))
          (modeFold tail m (nextPiece tail p d)
            (fun ds => productAttenuation w K (d::ds))) :=
        (cycleIterate_smul (tail+1) w K m _ _ (nextPiece_supported tail p d)).trans
          ((HaarCarrierEqv.smul _
            (cycleIterate_modeFold tail w K m _ (nextPiece_supported tail p d))).trans
            (RatPolyCoeffEqv.haarCarrier (modeFold_smul tail m _ _ _).symm))
      exact hs.trans (hl.trans (sum_carrier (tail+1) _ _ ht _))

/-- Original full product, original output ordering, every signed insertion.
This is a computed expansion, not a supplied spectral certificate. -/
theorem productMap_modeFold (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (productMap (tail+1) w K (List.range (tail+1)) p)
      (modeFold tail (tail+1) p (productAttenuation w K)) :=
  (productMap_range_cycle_carrier (tail+1) w K p).trans
    (cycleIterate_modeFold tail w K (tail+1) p hp)

end YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion

#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.nextPiece_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.cycleStep_grouped
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.modeFold_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.modeFold_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.cycleIterate_modeFold
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion.productMap_modeFold
