/-
# Saturation and endpoint reproduction of the ORIGINAL local head heat map

The actual headMap introduces a spare heat coordinate and keeps every other
coordinate shared. A computed cutoff of the complete harmonic reassembly
contains all its degree groups. Above it the map has its exact finite Casimir
formula, independent of the inclusive prefix cutoff, and nome one reproduces
the original input under EVERY Haar insertion.

This supplies finite-flow endpoint data, not positivity of the finite kernel
at nome one, a conditional Poincare inequality, or a changing-family budget.
The cutoff belongs to this fixed polynomial; it need not be uniform for a
cutoff-dependent original weighted source.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatSmoothing

namespace YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal (headMap)
open YMGap.Continuum.SU2QuaternionHeadHeatSmoothing (headMap_grouped)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (attenuation)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit inclusive degree bound of the computed harmonic polynomial.
All unheated spectator coordinates remain in its actual coefficients. -/
def inputCutoff (tail : Nat) (p : RatPoly) : Nat :=
  headDegreeBound (sumHarmonics (modes (tail+1) (Nat.zero_lt_succ tail) p))

private theorem degree_le_inputCutoff (tail : Nat) (p : RatPoly) {d : Nat}
    (hd : d ∈ headDegrees (sumHarmonics (modes (tail+1) (Nat.zero_lt_succ tail) p))) :
    d ≤ inputCutoff tail p := by
  have h := List.mem_range.mp hd
  exact Nat.le_of_lt_succ h

/-- Exact original map above the FIXED input's computed degree bound.
No positivity, strict nome or independent-spectator hypothesis is supplied. -/
theorem headMap_saturated (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : inputCutoff tail p ≤ K) :
    HaarCarrierEqv (tail+1) (headMap w K p)
      (polySum ((headDegrees (sumHarmonics
        (modes (tail+1) (Nat.zero_lt_succ tail) p))).map fun d =>
          polySmul (RGTransport.qpow w (d*(d+2)))
            (grouped d (modes (tail+1) (Nat.zero_lt_succ tail) p)))) := by
  have H := headMap_grouped tail w K p hp
  have he :
      (headDegrees (sumHarmonics (modes (tail+1) (Nat.zero_lt_succ tail) p))).map
        (fun d => polySmul (attenuation w K d)
          (grouped d (modes (tail+1) (Nat.zero_lt_succ tail) p))) =
      (headDegrees (sumHarmonics (modes (tail+1) (Nat.zero_lt_succ tail) p))).map
        (fun d => polySmul (RGTransport.qpow w (d*(d+2)))
          (grouped d (modes (tail+1) (Nat.zero_lt_succ tail) p))) := by
    apply List.map_congr_left
    intro d hd
    rw [attenuation, if_pos (Nat.le_trans (degree_le_inputCutoff tail p hd) hK)]
  rw [he] at H
  exact H

/-- Both arbitrary later inclusive cutoffs give the SAME conditional map
on this input, with equality tested by every surviving Haar insertion. -/
theorem headMap_cutoff_stable (tail : Nat) (w : Q') (K L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : inputCutoff tail p ≤ K) (hL : inputCutoff tail p ≤ L) :
    HaarCarrierEqv (tail+1) (headMap w K p) (headMap w L p) :=
  (headMap_saturated tail w K p hp hK).trans
    (headMap_saturated tail w L p hp hL).symm

private theorem qpow_one : ∀ k : Nat, RGTransport.qpow (1 : Q') k ≈ 1
  | 0 => Q'.eqv_refl _
  | k+1 =>
      Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (RGTransport.qpow 1 k)) (qpow_one k)

private theorem sum_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ d, d ∈ ids → RatPolyCoeffEqv (f d) (g d)) →
      RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | d::ds, h => by
      simp only [List.map_cons, polySum]
      exact (h d List.mem_cons_self).add
        (sum_congr f g ds (fun e he => h e (List.mem_cons_of_mem d he)))

/-- Nome one reproduces the literal original input once all of its computed
modes are retained. It is a carrier identity, NOT kernel positivity at one. -/
theorem headMap_one_reproduction (tail : Nat) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : inputCutoff tail p ≤ K) :
    HaarCarrierEqv (tail+1) (headMap 1 K p) p := by
  let ms := modes (tail+1) (Nat.zero_lt_succ tail) p
  let ids := headDegrees (sumHarmonics ms)
  have hs : RatPolyCoeffEqv
      (polySum (ids.map fun d => polySmul (RGTransport.qpow 1 (d*(d+2))) (grouped d ms)))
      (polySum (ids.map fun d => grouped d ms)) :=
    sum_congr _ _ ids (fun d _ =>
      (RatPolyCoeffEqv.smul_coefficient (qpow_one _) _).trans (RatPolyCoeffEqv.one_smul _))
  have hr : RatPolyCoeffEqv (polySum (ids.map fun d => grouped d ms)) (sumHarmonics ms) :=
    headComponent_reassembly (sumHarmonics ms)
  exact (headMap_saturated tail 1 K p hp hK).trans
    ((RatPolyCoeffEqv.haarCarrier (hs.trans hr)).trans
      (polynomial_harmonic_carrier (Nat.zero_lt_succ tail) p hp).symm)

end YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow.inputCutoff
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow.headMap_saturated
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow.headMap_cutoff_stable
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow.headMap_one_reproduction
