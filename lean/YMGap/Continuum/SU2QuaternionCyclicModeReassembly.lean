/-
# Unweighted reassembly of the computed cyclic mode tree

Giving every computed degree path weight one reassembles the underlying
coordinate rotation at every round. After a full cycle the rotation period
therefore returns the original supported polynomial. This is an exact
Haar-carrier identity and uses the computed harmonic decomposition itself,
not a supplied reassembly premise.
-/

import YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion

namespace YMGap.Continuum.SU2QuaternionCyclicModeReassembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularSupport (polyAdd_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (reindex_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion

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

private theorem rotateIterate_sum {A : Type} (n m : Nat) (f : A → RatPoly) :
    ∀ ids : List A, rotateIterate n m (polySum (ids.map f)) =
      polySum (ids.map fun a => rotateIterate n m (f a))
  | [] => by
      induction m with
      | zero => rfl
      | succ m ih =>
          change cycleRotation n (rotateIterate n m polyZero) = polyZero
          have ih' : rotateIterate n m polyZero = polyZero := by
            simpa only [List.map_nil, polySum] using ih
          rw [ih']
          rfl
  | a::ids => by
      simp only [List.map_cons, polySum, rotateIterate_add,
        rotateIterate_sum n m f ids]

private theorem cycleRotation_sum {A : Type} (n : Nat) (f : A → RatPoly) :
    ∀ ids : List A, cycleRotation n (polySum (ids.map f)) =
      polySum (ids.map fun a => cycleRotation n (f a))
  | [] => rfl
  | a::ids => by
      simp only [List.map_cons, polySum, cycleRotation_add,
        cycleRotation_sum n f ids]

private theorem rotateIterate_succ_right (n : Nat) :
    ∀ (m : Nat) (p : RatPoly),
      rotateIterate n m (cycleRotation n p) = rotateIterate n (m+1) p
  | 0, _ => rfl
  | m+1, p => by
      change cycleRotation n (rotateIterate n m (cycleRotation n p)) =
        cycleRotation n (rotateIterate n (m+1) p)
      rw [rotateIterate_succ_right n m p]

/-- The complete computed head groups, after coordinate rotation, reassemble
the rotated supported input. -/
theorem branchPieces_one_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (polySum ((branchDegrees tail p).map fun d => nextPiece tail p d))
      (cycleRotation (tail+1) p) := by
  let ms := modes (tail+1) (by omega) p
  let s := sumHarmonics ms
  let pieces := polySum ((headDegrees s).map fun d => grouped d ms)
  have hpieces : SupportedQuaternionBlocks (tail+1) pieces :=
    sum_supported (tail+1) _ (fun d => grouped_supported d ms) _
  have hreassemble : HaarCarrierEqv (tail+1) pieces p :=
    (RatPolyCoeffEqv.haarCarrier (blocks := tail+1)
      (headComponent_reassembly s)).trans
      (polynomial_harmonic_carrier (by omega) p hp).symm
  have hr := cycleRotation_carrier (tail+1) hpieces hp hreassemble
  have he : cycleRotation (tail+1) pieces =
      polySum ((branchDegrees tail p).map fun d => nextPiece tail p d) := by
    dsimp [pieces, s, ms, branchDegrees, nextPiece, branchPiece]
    exact cycleRotation_sum (tail+1) _ _
  exact he ▸ hr

/-- At every depth, the unweighted computed mode tree is exactly the same
carrier element as the corresponding iterate of cyclic coordinate rotation. -/
theorem modeFold_one_carrier (tail : Nat) : ∀ (m : Nat) (p : RatPoly),
    SupportedQuaternionBlocks (tail+1) p →
    HaarCarrierEqv (tail+1) (modeFold tail m p (fun _ => (1 : Q')))
      (rotateIterate (tail+1) m p)
  | 0, p, _ => RatPolyCoeffEqv.haarCarrier (blocks := tail+1)
      (RatPolyCoeffEqv.one_smul p)
  | m+1, p, hp => by
      let ids := branchDegrees tail p
      let f := fun d => modeFold tail m (nextPiece tail p d) (fun _ => (1 : Q'))
      let g := fun d => rotateIterate (tail+1) m (nextPiece tail p d)
      have hf (d : Nat) : SupportedQuaternionBlocks (tail+1) (nextPiece tail p d) :=
        nextPiece_supported tail p d
      have hs : HaarCarrierEqv (tail+1) (polySum (ids.map f)) (polySum (ids.map g)) :=
        sum_carrier (tail+1) f g
          (fun d => modeFold_one_carrier tail m _ (hf d)) ids
      have hsum : HaarCarrierEqv (tail+1) (polySum (ids.map g))
          (rotateIterate (tail+1) m
            (polySum (ids.map fun d => nextPiece tail p d))) :=
        by
          rw [rotateIterate_sum (tail+1) m (nextPiece tail p) ids]
          exact HaarCarrierEqv.refl (tail+1) _
      have hrot : SupportedQuaternionBlocks (tail+1) (cycleRotation (tail+1) p) := by
        unfold cycleRotation
        exact reindex_supported _ _
      have hi := rotateIterate_carrier (tail+1) m
        (sum_supported (tail+1) (nextPiece tail p) hf ids)
        hrot
        (branchPieces_one_carrier tail p hp)
      exact hs.trans (hsum.trans
        ((rotateIterate_succ_right (tail+1) m p) ▸ hi))

/-- A full unweighted degree-path tree returns the original supported input,
because the actual cyclic coordinate rotation has period `tail+1`. -/
theorem full_modeFold_one_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (modeFold tail (tail+1) p (fun _ => (1 : Q'))) p :=
  (modeFold_one_carrier tail (tail+1) p hp).trans
    (rotateIterate_period_carrier (tail+1) p hp)

end YMGap.Continuum.SU2QuaternionCyclicModeReassembly

#print axioms YMGap.Continuum.SU2QuaternionCyclicModeReassembly.branchPieces_one_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeReassembly.modeFold_one_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicModeReassembly.full_modeFold_one_carrier
