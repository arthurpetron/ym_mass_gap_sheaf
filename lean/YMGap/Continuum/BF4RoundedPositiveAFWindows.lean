/-
# Actual positive heat windows with a proved AF bit budget

The Euler lower estimate and the Gaussian-in-label upper estimate give
`upper <= 4^(5*N+5)*lower`, where N is the rounded actual-nome cutoff.
All local windows are constructed, uniformly on the rational class box.
The SAME bit schedule costs at most 180 heat units under the existing AF
margin. Thus no local window or spread premise is supplied to the existing
generic `PointwiseHeatAFWindowFamily` below.

This deliberately uses a sufficient larger bit budget, not the unproved
sharper cap 4^N. No existing field or old theorem statement is changed.
The matched specialization still requires the cubic law and physical
spacing envelope. Identification of these local factors with the original
interacting transfer and its nonlinear spectral rate remains independent.
No physical gap, continuum QFT, or all-group result is asserted.
-/

import YMGap.Continuum.SU2RoundedHeatLower
import YMGap.Continuum.SU2RoundedHeatUpper
import YMGap.Continuum.BF4RoundedNomeAFGrowth

namespace YMGap.Continuum.BF4RoundedPositiveAFWindows

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4RoundedNomeAFGrowth
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow

set_option autoImplicit false
local infix:50 " ≈ " => Q'.eqv

/-- The actual window cost, distinct from the power-tail cutoff. -/
def bits (w : Q') : Nat := 5 * HeatRoundedCutoff.cutoff w + 5

private theorem one_le_four_pow : ∀ n : Nat, (1 : Q') ≤ (4 : Q') ^ n
  | 0 => Q'.le_refl' _
  | n + 1 => Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 4)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 4))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_four_pow n) (by decide)))

/-- Proved spread for the actual computed endpoints, at every nome. -/
theorem window_spread {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SU2PointwiseHeatPositiveWindow.upper w ≤
      (4 : Q') ^ bits w * SU2PointwiseHeatPositiveWindow.lower w := by
  let N := HeatRoundedCutoff.cutoff w
  let L := SU2PointwiseHeatPositiveWindow.lower w
  have hL : (0 : Q') ≤ L := Q'.le_of_lt (SU2PointwiseHeatPositiveWindow.lower_pos hw0 hw1)
  have hC : BF4ExactSlabAllNomeTailInterval.prefixCap w ≤ (4 : Q') ^ (5*N+4) * L := by
    have hpaid := Q'.mul_le_mul_of_nonneg_left _ _ ((4 : Q') ^ (N+1))
      (SU2RoundedHeatLower.lower_paid hw0 hw1) (Q'.pow_nonneg _ (by decide) _)
    have he : (4 : Q') ^ (N+1) * ((4 : Q') ^ (4*N+3) * L) ≈
        (4 : Q') ^ (5*N+4) * L := by
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (by
          have h := Q'.pow_add_eqv (4 : Q') (N+1) (4*N+3)
          rw [show (N+1)+(4*N+3)=5*N+4 by omega] at h
          exact Q'.eqv_symm h))
    exact Q'.le_trans' _ _ _ (SU2RoundedHeatUpper.prefixCap_le_rounded_pow hw0 hw1)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
        (Q'.le_trans' _ _ _ hpaid (Q'.le_of_eqv he)))
  have hsmall : L ≤ (4 : Q') ^ (5*N+4) * L := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (one_le_four_pow _) hL)
  have hsum := Q'.add_le_add hC hsmall
  have hdouble : ((4 : Q') ^ (5*N+4) * L) + ((4 : Q') ^ (5*N+4) * L) ≈
      (2 : Q') * ((4 : Q') ^ (5*N+4) * L) :=
    Q'.eqv_trans _ _ _
      (Cheb.add_eqv_congr _ _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
        (Q'.eqv_symm (Q'.one_mul_eqv _))) (Q'.eqv_symm (Q'.add_mul_eqv 1 1 _))
  have htwo := Q'.mul_le_mul_of_nonneg_right (2 : Q') 4
    ((4 : Q') ^ (5*N+4) * L) (by decide)
    (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _) hL)
  have hend : (4 : Q') * ((4 : Q') ^ (5*N+4) * L) ≈
      (4 : Q') ^ bits w * L := by
    have hindex : bits w = (5*N+4)+1 := by rfl
    rw [hindex]
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdouble)
    (Q'.le_trans' _ _ _ htwo (Q'.le_of_eqv hend)))

/-- The larger ACTUAL bit budget remains O(1/t) in the AF envelope. -/
theorem bit_heat_cost (E : AFEnvelope) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ E.g₁) (hw : (0 : Q') < E.w g) :
    Q'.ofNat (bits (E.w g)) * (BF4AFHeatSpacing.quarter * E.t g) ≤ (180 : Q') := by
  let N := HeatRoundedCutoff.cutoff (E.w g)
  have hN : 0 < N := HeatRoundedCutoff.cutoff_positive _
  have hn : bits (E.w g) ≤ 10*N := by unfold bits; change 5*N+5 ≤ 10*N; omega
  have hq : Q'.ofNat (bits (E.w g)) ≤ Q'.ofNat (10*N) := by
    change ((bits (E.w g) : Nat) : Int) * 1 ≤ ((10*N : Nat) : Int) * 1
    simpa only [Int.mul_one] using (Int.ofNat_le.mpr hn)
  have hcost := Q'.mul_le_mul_of_nonneg_left _ _ (10 : Q')
    (rounded_heat_cost E g hg hgle hw) (by decide)
  have he : Q'.ofNat (10*N) * (BF4AFHeatSpacing.quarter * E.t g) ≈
      (10 : Q') * (Q'.ofNat N * (BF4AFHeatSpacing.quarter * E.t g)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (SU3CharFactor.ofNat_mul_eqv 10 N))
      (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hq
      (Q'.le_of_lt (Q'.mul_pos BF4AFHeatSpacing.quarter_pos (envelope_time_pos E g hg hgle))))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ hcost (by decide)))

/-- Existing growth structure at exactly the constructed window schedule. -/
def growth (E : AFEnvelope) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s) (hle : ∀ s, coupling s ≤ E.g₁)
    (hw : ∀ s, (0 : Q') < E.w (coupling s)) :
    FarautAFBitGrowth E coupling (fun s => bits (E.w (coupling s))) where
  costCeiling := 180
  costCeiling_nonnegative := by decide
  coupling_pos := hpos
  coupling_le := hle
  bit_heat_cost := fun s => bit_heat_cost E _ (hpos s) (hle s) (hw s)

/-- No window, positivity, spread or growth premise: all are constructed
from the named AF envelope, positive nomes and actual class coordinates. -/
def windowFamily (E : AFEnvelope) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s) (hle : ∀ s, coupling s ≤ E.g₁)
    (hw : ∀ s, (0 : Q') < E.w (coupling s))
    (Local : Type) (x : Nat → Local → Q')
    (hxLower : ∀ s l, (-(1 : Q')) ≤ x s l) (hxUpper : ∀ s l, x s l ≤ (1 : Q')) :
    PointwiseHeatAFWindowFamily E coupling Local (fun s _ => E.w (coupling s)) x
      (fun s => SU2PointwiseHeatPositiveWindow.lower (E.w (coupling s)))
      (fun s => SU2PointwiseHeatPositiveWindow.upper (E.w (coupling s))) where
  bits := fun s => bits (E.w (coupling s))
  growth := growth E coupling hpos hle hw
  lower_pos := fun s => SU2PointwiseHeatPositiveWindow.lower_pos (hw s)
    (envelope_weight_lt_one E _ (hpos s) (hle s))
  upper_nonnegative := fun s => SU2PointwiseHeatPositiveWindow.upper_nonnegative (hw s)
    (envelope_weight_lt_one E _ (hpos s) (hle s))
  upper_le_bit_cap := fun s => window_spread (hw s) (envelope_weight_lt_one E _ (hpos s) (hle s))
  local_window := fun s l => SU2PointwiseHeatPositiveWindow.window (hw s)
    (envelope_weight_lt_one E _ (hpos s) (hle s)) (hxLower s l) (hxUpper s l)

/-- Direct specialization to the literal finite matched BF4 output. The
existing physical cubic and spacing laws are still explicit hypotheses. -/
def matchedWindowFamily (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s) (hle : ∀ s, coupling s ≤ law.g₁)
    (Local : Type) (x : Nat → Local → Q')
    (hxLower : ∀ s l, (-(1 : Q')) ≤ x s l) (hxUpper : ∀ s l, x s l ≤ (1 : Q')) :
    PointwiseHeatAFWindowFamily (physicalAFEnvelope family law spacing) coupling Local
      (fun s _ => blockedWeight family (coupling s)) x
      (fun s => SU2PointwiseHeatPositiveWindow.lower (blockedWeight family (coupling s)))
      (fun s => SU2PointwiseHeatPositiveWindow.upper (blockedWeight family (coupling s))) :=
  windowFamily (physicalAFEnvelope family law spacing) coupling hpos hle
    (fun s => blockedWeight_pos family (coupling s)) Local x hxLower hxUpper

/-- A genuine analytic consumer: twenty-three actual completed heat
factors have the existing projective comparison, with all local windows
and their spread proved here. This does not identify the supplied class
coordinates/product with the original interacting transfer. -/
def retainedHarnack {Source Target State Factor : Type}
    (paths : List (List State)) (factors : List Factor)
    (factor_count : factors.length = BF4GroupedFeynmanKacHarnack.bf4SpatialCycleCount)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (x : Source → Target → List State → Factor → Q')
    (hxLower : ∀ s t p f, (-(1 : Q')) ≤ x s t p f)
    (hxUpper : ∀ s t p f, x s t p f ≤ (1 : Q'))
    (sources : List Source) (targets : List Target) :
    DynamicCompletedRetainedHarnackData paths
      (fun s t p => BF4CompletedHeatRetainedConsumer.completedFactorProduct
        (dynamicPointwiseLocalHeat (fun _ _ _ _ => w) x
          (fun _ _ _ _ => hw0) (fun _ _ _ _ => hw1) hxLower hxUpper s t p) factors)
      sources targets :=
  dynamicPointwiseRetainedHarnack paths factors factor_count
    (fun _ _ _ _ => w) x (fun _ _ _ _ => hw0) (fun _ _ _ _ => hw1) hxLower hxUpper
    sources targets (SU2PointwiseHeatPositiveWindow.lower w)
    (SU2PointwiseHeatPositiveWindow.upper w) (bits w)
    (SU2PointwiseHeatPositiveWindow.lower_pos hw0 hw1)
    (SU2PointwiseHeatPositiveWindow.upper_nonnegative hw0 hw1)
    (window_spread hw0 hw1)
    (fun s _ t _ p _ f _ => SU2PointwiseHeatPositiveWindow.window hw0 hw1
      (hxLower s t p f) (hxUpper s t p f))

#print axioms bits
#print axioms window_spread
#print axioms bit_heat_cost
#print axioms growth
#print axioms windowFamily
#print axioms matchedWindowFamily
#print axioms retainedHarnack

end YMGap.Continuum.BF4RoundedPositiveAFWindows
