/-
# Full heat tubes preserve the same retained boundary mass

The unit-mass identity is transported by the actual whole-carrier swaps and
composed through all tube links. No non-vacuum factor is silently selected.
This supplies the vacuum term for connected, rather than raw, transmission.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
import YMGap.Continuum.SU2QuaternionFullHeatTubeComposition

namespace YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionFullHeatTubeLayer
open YMGap.Continuum.SU2QuaternionFullHeatTubeComposition

local infix:50 " ≈ " => Q'.eqv

theorem pair_vacuum (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val) (w : Q') (K : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r) (hd : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (heatAt a.val b.val w K) r) ≈ quaternionHaar (tailBlocks+1) r := by
  let steps := pairSteps (show 1 < tailBlocks+1 by omega) a b
  let tr := applyQuaternionBlockSwapChain steps r
  have htr : SupportedQuaternionBlocks (tailBlocks+1) tr := applyQuaternionBlockSwapChain_supported steps r hr
  have hk := heat_supported a.isLt b.isLt w K
  have hkh := heat_supported (show 0 < tailBlocks+1 by omega) (show 1 < tailBlocks+1 by omega) w K
  have hd0 : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hd
  have hleft := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul hk hr)
  rw [chain_mul] at hleft
  have hpin := ((heat_exposed (by omega) a b hab w K).mul (PaddedPolynomialCoeffEqv.refl (tailBlocks+1) tr)).haar
    (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hk) htr) (supported_polyMul hkh htr)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) (Q'.eqv_trans _ _ _ hpin
    (Q'.eqv_trans _ _ _ (heat_vacuum tailBlocks hb w K tr hd0) (quaternionHaar_applyQuaternionBlockSwapChain steps r hr)))

theorem stage_vacuum (tailBlocks offset : Nat) (hb : offset+7 < tailBlocks+1) (w : Q') (K : Nat)
    (i : Fin 4) (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : HasQuaternionBlockDegree (offset+i.val) 0 r) :
    quaternionHaar (tailBlocks+1) (pending offset w K i.val r) ≈
      quaternionHaar (tailBlocks+1) (pending offset w K (i.val+1) r) := by
  rw [pending_step]
  exact pair_vacuum tailBlocks (by omega) ⟨offset+i.val,by omega⟩ ⟨offset+(i.val+4),by omega⟩
    (by change offset+i.val ≠ offset+(i.val+4); omega) w K _ (pending_supported hb w K (i.val+1) r hr)
    (pending_independent offset (offset+i.val) w K (i.val+1) r hd (by omega) (by omega))

theorem layer_vacuum (tailBlocks offset : Nat) (hb : offset+7 < tailBlocks+1) (w : Q') (K : Nat)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ i : Fin 4, HasQuaternionBlockDegree (offset+i.val) 0 r) :
    quaternionHaar (tailBlocks+1) (pending offset w K 0 r) ≈ quaternionHaar (tailBlocks+1) r :=
  Q'.eqv_trans _ _ _ (stage_vacuum tailBlocks offset hb w K 0 r hr (hd 0))
    (Q'.eqv_trans _ _ _ (stage_vacuum tailBlocks offset hb w K 1 r hr (hd 1))
      (Q'.eqv_trans _ _ _ (stage_vacuum tailBlocks offset hb w K 2 r hr (hd 2))
        (stage_vacuum tailBlocks offset hb w K 3 r hr (hd 3))))

/-- No restriction K>=1: vacuum normalization also holds at cutoff zero. -/
theorem chain_vacuum (tailBlocks offset K : Nat) (ws : List Q')
    (hb : offset+4*ws.length+3 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+4*ws.length → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (tailBlocks+1) (chain offset K ws r) ≈ quaternionHaar (tailBlocks+1) r := by
  induction ws generalizing offset with
  | nil => exact Q'.eqv_refl _
  | cons w ws ih =>
    have ht : offset+4+4*ws.length+3 < tailBlocks+1 := by simp only [List.length_cons] at hb; omega
    have hs := chain_supported (offset+4) K ws ht r hr
    have hi (i : Fin 4) : HasQuaternionBlockDegree (offset+i.val) 0 (chain (offset+4) K ws r) :=
      chain_independent (offset+4) (offset+i.val) K ws r
        (hd (offset+i.val) (by omega) (by simp only [List.length_cons]; omega)) (by omega)
    exact Q'.eqv_trans _ _ _ (layer_vacuum tailBlocks offset (by simp only [List.length_cons] at hb; omega) w K _ hs hi)
      (ih (offset+4) ht (fun slot hl hu => hd slot (by omega) (by simp only [List.length_cons]; omega)))

end YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum

#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum.pair_vacuum
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum.stage_vacuum
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum.layer_vacuum
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum.chain_vacuum
