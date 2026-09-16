/-
# Rounded cutoff growth at the actual AF nome

For an AF envelope and a positive nome, the existing margin inequality
`t/8 <= 1-w` and the computed cutoff `N(w)` imply `N(w)*(t/4) <= 18`.
This directly supplies the existing `FarautAFBitGrowth` interface. There
is no exact dyadic-time equation and no identification with a Pade nome.

The window constructor below consumes the existing generic interface:
its local character windows and `upper <= 4^N * lower` remain explicit
inputs. The proved power-tail cutoff does NOT prove that spread bound.
The physical specialization still assumes the existing cubic law and
spacing envelope; neither is constructed here. No spatial estimate,
physical transfer identification, continuum theory, or gap is supplied.
-/

import YMGap.Continuum.HeatRoundedCutoff
import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.SU2PointwiseHeatDynamicWindow

namespace YMGap.Continuum.BF4RoundedNomeAFGrowth

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow

local infix:50 " ≈ " => Q'.eqv

/-- Positivity of heat time follows from the existing lower AF bound. -/
theorem envelope_time_pos (E : AFEnvelope)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ E.g₁) :
    (0 : Q') < E.t g :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos E.α_pos (Q'.mul_pos hg hg)) (E.t_lower g hg hgle)

private theorem lt_one_of_margin_pos {x : Q'}
    (h : (0 : Q') < (1 : Q') + (-x)) : x < (1 : Q') := by
  have hnum : (0 : Int) < ((1 : Q') + (-x)).num := Q'.num_pos_of_pos h
  show x.num * ((1 : Q').den : Int) < (1 : Q').num * (x.den : Int)
  change (0 : Int) < (1 : Q').num * (x.den : Int) +
    (-x.num) * ((1 : Q').den : Int) at hnum
  rw [Int.neg_mul] at hnum
  omega

/-- Subunity is a consequence of the envelope, not an additional field. -/
theorem envelope_weight_lt_one (E : AFEnvelope)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ E.g₁) :
    E.w g < (1 : Q') :=
  lt_one_of_margin_pos (Q'.pos_of_lt_of_le
    (Q'.mul_pos oneEighth_pos (envelope_time_pos E g hg hgle))
    (E.w_floor g hg hgle))

/-- Direct quantitative growth: the rounded actual-nome cutoff costs at
most 18 heat units throughout the stated AF chart. -/
theorem rounded_heat_cost (E : AFEnvelope)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ E.g₁)
    (hw : (0 : Q') < E.w g) :
    Q'.ofNat (HeatRoundedCutoff.cutoff (E.w g)) *
        (BF4AFHeatSpacing.quarter * E.t g) ≤ (18 : Q') := by
  let N := Q'.ofNat (HeatRoundedCutoff.cutoff (E.w g))
  let δ := (1 : Q') + -(E.w g)
  have ht : BF4AFHeatSpacing.quarter * E.t g ≈
      (2 : Q') * (oneEighth * E.t g) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide))
      (Q'.mul_assoc_eqv (2 : Q') oneEighth (E.t g))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (E.w_floor g hg hgle) (by decide)
  have htime : BF4AFHeatSpacing.quarter * E.t g ≤ (2 : Q') * δ :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv ht) hscaled
  have hcost := Q'.mul_le_mul_of_nonneg_left _ _ N htime
    (HeatKernelRGStep.zero_le_ofNat _)
  have hswap : N * ((2 : Q') * δ) ≈ (2 : Q') * (N * δ) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv N (2 : Q')))
        (Q'.mul_assoc_eqv _ _ _))
  have hbound := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (HeatRoundedCutoff.cutoff_gap_upper hw (envelope_weight_lt_one E g hg hgle))
    (by decide)
  exact Q'.le_trans' _ _ _ hcost
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap)
      (Q'.le_trans' _ _ _ hbound (by decide)))

/-- A computed witness of the existing growth interface, without a
dyadic bridge or an externally supplied heat-cost hypothesis. -/
def roundedAFBitGrowth (E : AFEnvelope) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s)
    (hle : ∀ s, coupling s ≤ E.g₁)
    (hw : ∀ s, (0 : Q') < E.w (coupling s)) :
    FarautAFBitGrowth E coupling
      (fun s => HeatRoundedCutoff.cutoff (E.w (coupling s))) where
  costCeiling := 18
  costCeiling_nonnegative := by decide
  coupling_pos := hpos
  coupling_le := hle
  bit_heat_cost := fun s => rounded_heat_cost E _ (hpos s) (hle s) (hw s)

/-- The existing scalar core-length consumer now uses the actual nome's
rounded schedule. This is not an identification of a physical transfer. -/
theorem rounded_core_length_uniform (E : AFEnvelope) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s)
    (hle : ∀ s, coupling s ≤ E.g₁)
    (hw : ∀ s, (0 : Q') < E.w (coupling s)) :
    ∀ s, BF4AFHeatSpacing.heatSpacingRate E *
      (Q'.ofNat (46 * HeatRoundedCutoff.cutoff (E.w (coupling s))) *
        E.a (coupling s)) ≤ Q'.ofNat 46 * (18 : Q') :=
  faraut_af_family_core_length_uniform (roundedAFBitGrowth E coupling hpos hle hw)

/-- Assemble the EXISTING generic window family at the actual envelope
nome. Its window-spread estimate is still supplied, not inferred from a
tail bound. The local windows' own truncation indices are unchanged. -/
def roundedPointwiseHeatAFWindowFamily
    (E : AFEnvelope) (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s)
    (hle : ∀ s, coupling s ≤ E.g₁)
    (hw : ∀ s, (0 : Q') < E.w (coupling s))
    (Local : Type) (x : Nat → Local → Q') (lower upper : Nat → Q')
    (hlower : ∀ s, (0 : Q') < lower s)
    (hupper : ∀ s, (0 : Q') ≤ upper s)
    (hcap : ∀ s, upper s ≤ FiveHolonomyPerronCutoff.four ^
      HeatRoundedCutoff.cutoff (E.w (coupling s)) * lower s)
    (windows : ∀ s location, PointwiseHeatTailWindow
      (E.w (coupling s)) (x s location) (lower s) (upper s)) :
    PointwiseHeatAFWindowFamily E coupling Local
      (fun s _ => E.w (coupling s)) x lower upper where
  bits := fun s => HeatRoundedCutoff.cutoff (E.w (coupling s))
  growth := roundedAFBitGrowth E coupling hpos hle hw
  lower_pos := hlower
  upper_nonnegative := hupper
  upper_le_bit_cap := hcap
  local_window := windows

/-- Specialization to the exact finite matched block output, given the
unchanged cubic-law and spacing inputs. No impossible schedule is assumed. -/
def matchedRoundedAFBitGrowth (family : MatchedBlockFamily)
    (law : CubicMarginLaw family) (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (hpos : ∀ s, (0 : Q') < coupling s)
    (hle : ∀ s, coupling s ≤ law.g₁) :
    FarautAFBitGrowth (physicalAFEnvelope family law spacing) coupling
      (fun s => HeatRoundedCutoff.cutoff (blockedWeight family (coupling s))) :=
  roundedAFBitGrowth (physicalAFEnvelope family law spacing) coupling hpos hle
    (fun s => blockedWeight_pos family (coupling s))

#print axioms envelope_time_pos
#print axioms envelope_weight_lt_one
#print axioms rounded_heat_cost
#print axioms roundedAFBitGrowth
#print axioms rounded_core_length_uniform
#print axioms roundedPointwiseHeatAFWindowFamily
#print axioms matchedRoundedAFBitGrowth

end YMGap.Continuum.BF4RoundedNomeAFGrowth
