/-
# Explicit moving Faraut cutoffs on a dyadic heat-time schedule

The abstract `FarautAFBitGrowth` record asks for a bit schedule whose product
with the BF4 heat argument stays bounded.  This module constructs such a
schedule for an explicit dyadic heat trajectory instead of postulating the
growth estimate.

At scale `s`, set

    x_s = (t_s / 4) = 1 / 2^s,
    w_s = 1 / (1 + x_s),
    B_s = spacingLabelCutoff w_s.

Because the project's constructive `powBaseCutoff` uses the Archimedean
cutoff `1 / ((1-w) delta)` with `delta = 1/8`, its raw rational arithmetic is
exact on this schedule:

    B_s = 8 (2^s + 1).

Consequently `B_s x_s <= 16` uniformly.  This is the requested moving-cutoff
versus heat-time estimate.  A final interface records the two exact
identifications needed to transport the result to a physical nome; no
logarithm or exponential inversion is assumed.

## Axiom gate

Constructive rational and natural-number arithmetic only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4FarautJointCarrierAFBudget
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.BF4FarautAFCutoffGrowth

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFHeatSpacing
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Explicit dyadic heat and Padé-nome schedule -/

def dyadicHeatDenominator (scale : Nat) : Nat := 2 ^ scale

theorem dyadicHeatDenominator_pos (scale : Nat) :
    0 < dyadicHeatDenominator scale := by
  unfold dyadicHeatDenominator
  exact Nat.pow_pos (by decide)

/-- The BF4 heat argument `x=t/4`, chosen dyadically. -/
def dyadicHeatArgument (scale : Nat) : Q' :=
  Q'.mkPos 1 (dyadicHeatDenominator scale)
    (dyadicHeatDenominator_pos scale)

/-- Heat time whose quarter is the dyadic heat argument. -/
def dyadicHeatTime (scale : Nat) : Q' :=
  Q'.ofNat 4 * dyadicHeatArgument scale

/-- The proved rational Padé upper nome `1/(1+t/4)`. -/
def dyadicPadeNome (scale : Nat) : Q' :=
  ExpUBInstance.oneOver1p (dyadicHeatArgument scale)

/-- The existing spacing-dependent label cutoff, now evaluated on the
explicit dyadic Padé nome. -/
def dyadicSpacingBits (scale : Nat) : Nat :=
  spacingLabelCutoff (dyadicPadeNome scale)

theorem dyadicHeatArgument_num (scale : Nat) :
    (dyadicHeatArgument scale).num = 1 := rfl

theorem dyadicHeatArgument_den (scale : Nat) :
    (dyadicHeatArgument scale).den =
      dyadicHeatDenominator scale := by
  unfold dyadicHeatArgument
  exact Q'.mkPos_den _ _ _

theorem dyadicPadeNome_num (scale : Nat) :
    (dyadicPadeNome scale).num =
      Int.ofNat (dyadicHeatDenominator scale) := by
  unfold dyadicPadeNome
  rw [ExpUBInstance.oneOver1p_num,
    dyadicHeatArgument_den]
  rfl

theorem dyadicPadeNome_den (scale : Nat) :
    (dyadicPadeNome scale).den =
      dyadicHeatDenominator scale + 1 := by
  unfold dyadicPadeNome
  rw [ExpUBInstance.oneOver1p_den,
    dyadicHeatArgument_num, dyadicHeatArgument_den]
  omega

/-! ## 2. Exact cutoff evaluation and the uniform heat cost -/

/-- On the dyadic Padé nome, the raw `powBaseCutoff` representation evaluates
exactly to `8(2^s+1)`. -/
theorem dyadicSpacingBits_eq (scale : Nat) :
    dyadicSpacingBits scale =
      8 * (dyadicHeatDenominator scale + 1) := by
  let nome := dyadicPadeNome scale
  let gap : Q' := 1 + (-nome)
  let denominator : Q' :=
    gap * SU2PointwiseHeatSpacingCompletion.eighth
  have hnomeDen :
      ((nome.den : Nat) : Int) =
        Int.ofNat (dyadicHeatDenominator scale + 1) := by
    change ((dyadicPadeNome scale).den : Int) =
      Int.ofNat (dyadicHeatDenominator scale + 1)
    rw [dyadicPadeNome_den]
    rfl
  have hgapDen :
      (gap.den : Int) =
        Int.ofNat (dyadicHeatDenominator scale + 1) := by
    unfold gap
    rw [Q'.add_den_cast, Q'.neg_den]
    change (1 : Int) * (nome.den : Int) =
      Int.ofNat (dyadicHeatDenominator scale + 1)
    rw [Int.one_mul, hnomeDen]
  have heighthDen :
      ((SU2PointwiseHeatSpacingCompletion.eighth).den : Int) = 8 := by
    decide
  have hdenominatorDenCast :
      (denominator.den : Int) =
        Int.ofNat (8 * (dyadicHeatDenominator scale + 1)) := by
    calc
      (denominator.den : Int) =
          (gap.den : Int) *
            (SU2PointwiseHeatSpacingCompletion.eighth.den : Int) := by
        unfold denominator
        exact Q'.mul_den_cast _ _
      _ = Int.ofNat (dyadicHeatDenominator scale + 1) * 8 := by
        rw [hgapDen, heighthDen]
      _ = Int.ofNat
          (8 * (dyadicHeatDenominator scale + 1)) := by
        change
          Int.ofNat (dyadicHeatDenominator scale + 1) *
              Int.ofNat 8 =
            Int.ofNat
              (8 * (dyadicHeatDenominator scale + 1))
        simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
        rw [Int.mul_comm]
  have hdenominatorDen :
      denominator.den =
        8 * (dyadicHeatDenominator scale + 1) := by
    exact Int.ofNat.inj hdenominatorDenCast
  unfold dyadicSpacingBits spacingLabelCutoff powBaseCutoff
  change
    (HKConv.divPos 1 denominator).num.toNat =
      8 * (dyadicHeatDenominator scale + 1)
  rw [HKConv.divPos_num, hdenominatorDen]
  rw [show (1 : Q').num = 1 by rfl, Int.one_mul]
  change
    (Int.ofNat (8 *
      (dyadicHeatDenominator scale + 1))).toNat =
      8 * (dyadicHeatDenominator scale + 1)
  omega

/-- The chosen heat time really has dyadic quarter argument. -/
theorem quarter_mul_dyadicHeatTime (scale : Nat) :
    quarter * dyadicHeatTime scale ≈
      dyadicHeatArgument scale := by
  unfold dyadicHeatTime
  calc
    quarter * (Q'.ofNat 4 * dyadicHeatArgument scale) ≈
        (quarter * Q'.ofNat 4) * dyadicHeatArgument scale :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ 1 * dyadicHeatArgument scale := by
      exact Q'.mul_eqv_congr_right _ _ _
        (by decide)
    _ ≈ dyadicHeatArgument scale :=
      Q'.one_mul_eqv _

/-- The exact all-scale moving-cutoff bound:

`dyadicSpacingBits(s) * (t_s/4) <= 16`.
-/
theorem dyadicSpacingBits_mul_heatArgument_le (scale : Nat) :
    Q'.ofNat (dyadicSpacingBits scale) *
        dyadicHeatArgument scale ≤
      Q'.ofNat 16 := by
  rw [dyadicSpacingBits_eq]
  show
    (Q'.ofNat (8 * (dyadicHeatDenominator scale + 1)) *
      Q'.mkPos 1 (dyadicHeatDenominator scale)
        (dyadicHeatDenominator_pos scale)) ≤
      Q'.ofNat 16
  show
    ((Q'.ofNat (8 * (dyadicHeatDenominator scale + 1)) *
      Q'.mkPos 1 (dyadicHeatDenominator scale)
        (dyadicHeatDenominator_pos scale)).num *
        (Q'.ofNat 16).den : Int) ≤
      (Q'.ofNat 16).num *
        ((Q'.ofNat (8 * (dyadicHeatDenominator scale + 1)) *
          Q'.mkPos 1 (dyadicHeatDenominator scale)
            (dyadicHeatDenominator_pos scale)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  have hden : 1 ≤ dyadicHeatDenominator scale :=
    dyadicHeatDenominator_pos scale
  omega

/-- The same estimate in the BF4 form `B_s * (t_s/4) <= 16`. -/
theorem dyadicSpacingBits_mul_quarter_time_le (scale : Nat) :
    Q'.ofNat (dyadicSpacingBits scale) *
        (quarter * dyadicHeatTime scale) ≤
      Q'.ofNat 16 := by
  have htransport :
      Q'.ofNat (dyadicSpacingBits scale) *
          (quarter * dyadicHeatTime scale) ≈
        Q'.ofNat (dyadicSpacingBits scale) *
          dyadicHeatArgument scale :=
    Q'.mul_eqv_congr_left _ _ _
      (quarter_mul_dyadicHeatTime scale)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport)
    (dyadicSpacingBits_mul_heatArgument_le scale)

/-! ## 3. An explicit `FarautAFBitGrowth` inhabitant -/

/-- The exact scalar identification needed to place an `AFEnvelope` heat
trajectory on the dyadic schedule.  Positivity and the small-coupling window
are included because they are fields of `FarautAFBitGrowth`. -/
structure DyadicAFHeatBridge
    (E : BareAFDiagnostic.AFEnvelope)
    (coupling : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le :
    ∀ scale, coupling scale ≤ E.g₁
  heat_time :
    ∀ scale,
      quarter * E.t (coupling scale) ≈
        dyadicHeatArgument scale

/-- The existing abstract bit-growth hypothesis is constructively inhabited
by the explicit spacing cutoff on every dyadically identified AF heat
trajectory. -/
def dyadicSpacingFarautAFBitGrowth
    {E : BareAFDiagnostic.AFEnvelope}
    {coupling : Nat → Q'}
    (bridge : DyadicAFHeatBridge E coupling) :
    FarautAFBitGrowth E coupling dyadicSpacingBits where
  costCeiling := Q'.ofNat 16
  costCeiling_nonnegative := by decide
  coupling_pos := bridge.coupling_pos
  coupling_le := bridge.coupling_le
  bit_heat_cost := by
    intro scale
    have htransport :
        Q'.ofNat (dyadicSpacingBits scale) *
            (quarter * E.t (coupling scale)) ≈
          Q'.ofNat (dyadicSpacingBits scale) *
            dyadicHeatArgument scale :=
      Q'.mul_eqv_congr_left _ _ _
        (bridge.heat_time scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv htransport)
      (dyadicSpacingBits_mul_heatArgument_le scale)

/-- Therefore the already-proved AF/Faraut cancellation theorem gives a
uniform physical length for the explicit moving cutoff. -/
theorem dyadic_faraut_core_length_uniform
    {E : BareAFDiagnostic.AFEnvelope}
    {coupling : Nat → Q'}
    (bridge : DyadicAFHeatBridge E coupling) :
    ∀ scale,
      heatSpacingRate E *
          (Q'.ofNat (46 * dyadicSpacingBits scale) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 * Q'.ofNat 16 :=
  faraut_af_family_core_length_uniform
    (dyadicSpacingFarautAFBitGrowth bridge)

/-! ## 4. Minimal bridge to a physical nome -/

/-- Exact data needed to identify a physical rational heat trajectory with
the explicit schedule.  The nome identity is deliberately semantic (`≈`):
the project rational type is unnormalised. -/
structure DyadicPhysicalNomeBridge
    (heatTime physicalNome : Nat → Q') : Type where
  heat_time :
    ∀ scale, quarter * heatTime scale ≈ dyadicHeatArgument scale
  nome :
    ∀ scale, physicalNome scale ≈ dyadicPadeNome scale
  cutoff :
    ∀ scale,
      spacingLabelCutoff (physicalNome scale) =
        spacingLabelCutoff (dyadicPadeNome scale)

/-- Once the physical nome supplies the exact cutoff identification, the
uniform bit/heat bound transports without any logarithmic inversion. -/
theorem physical_spacingBits_mul_quarter_time_le
    {heatTime physicalNome : Nat → Q'}
    (bridge : DyadicPhysicalNomeBridge heatTime physicalNome)
    (scale : Nat) :
    Q'.ofNat (spacingLabelCutoff (physicalNome scale)) *
        (quarter * heatTime scale) ≤
      Q'.ofNat 16 := by
  rw [bridge.cutoff scale]
  have htransport :
      Q'.ofNat
          (spacingLabelCutoff (dyadicPadeNome scale)) *
          (quarter * heatTime scale) ≈
        Q'.ofNat
          (spacingLabelCutoff (dyadicPadeNome scale)) *
          dyadicHeatArgument scale :=
    Q'.mul_eqv_congr_left _ _ _
      (bridge.heat_time scale)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport)
    (dyadicSpacingBits_mul_heatArgument_le scale)

/-! ## 5. Same-action AF cutoff

The preceding physical bridge accepted free `heatTime` and `physicalNome`
families.  The Perron application must not pay for a local kernel using an
unrelated cheap nome.  The following interface fixes both families to the
same `AFEnvelope` action, evaluated at the same coupling trajectory. -/

/-- The exact label budget of the actual AF-envelope weight. -/
def sameActionSpacingBits
    (E : BareAFDiagnostic.AFEnvelope)
    (coupling : Nat → Q') (scale : Nat) : Nat :=
  spacingLabelCutoff (E.w (coupling scale))

/-- A dyadic identification of one AF action.  The heat time and nome are
both read from `E` at `coupling scale`; `cutoff` is retained explicitly
because `Q'` is intentionally unnormalised and the executable cutoff depends
on its representation. -/
structure DyadicSameActionAFBridge
    (E : BareAFDiagnostic.AFEnvelope)
    (coupling : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le :
    ∀ scale, coupling scale ≤ E.g₁
  heat_time :
    ∀ scale,
      quarter * E.t (coupling scale) ≈
        dyadicHeatArgument scale
  nome :
    ∀ scale,
      E.w (coupling scale) ≈
        dyadicPadeNome scale
  cutoff :
    ∀ scale,
      sameActionSpacingBits E coupling scale =
        dyadicSpacingBits scale

/-- The same physical AF weight used by the local character kernel now owns
its spacing cutoff and the resulting uniform heat cost. -/
def sameActionFarautAFBitGrowth
    {E : BareAFDiagnostic.AFEnvelope}
    {coupling : Nat → Q'}
    (bridge : DyadicSameActionAFBridge E coupling) :
    FarautAFBitGrowth E coupling
      (sameActionSpacingBits E coupling) where
  costCeiling := Q'.ofNat 16
  costCeiling_nonnegative := by decide
  coupling_pos := bridge.coupling_pos
  coupling_le := bridge.coupling_le
  bit_heat_cost := by
    intro scale
    rw [bridge.cutoff scale]
    have htransport :
        Q'.ofNat (dyadicSpacingBits scale) *
            (quarter * E.t (coupling scale)) ≈
          Q'.ofNat (dyadicSpacingBits scale) *
            dyadicHeatArgument scale :=
      Q'.mul_eqv_congr_left _ _ _
        (bridge.heat_time scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv htransport)
      (dyadicSpacingBits_mul_heatArgument_le scale)

/-- The same-action cutoff therefore occupies a uniformly bounded physical
core length. -/
theorem sameAction_faraut_core_length_uniform
    {E : BareAFDiagnostic.AFEnvelope}
    {coupling : Nat → Q'}
    (bridge : DyadicSameActionAFBridge E coupling) :
    ∀ scale,
      heatSpacingRate E *
          (Q'.ofNat
              (46 * sameActionSpacingBits E coupling scale) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 * Q'.ofNat 16 :=
  faraut_af_family_core_length_uniform
    (sameActionFarautAFBitGrowth bridge)

#print axioms dyadicSpacingBits_eq
#print axioms quarter_mul_dyadicHeatTime
#print axioms dyadicSpacingBits_mul_heatArgument_le
#print axioms dyadicSpacingBits_mul_quarter_time_le
#print axioms DyadicAFHeatBridge
#print axioms dyadicSpacingFarautAFBitGrowth
#print axioms dyadic_faraut_core_length_uniform
#print axioms DyadicPhysicalNomeBridge
#print axioms physical_spacingBits_mul_quarter_time_le
#print axioms sameActionSpacingBits
#print axioms DyadicSameActionAFBridge
#print axioms sameActionFarautAFBitGrowth
#print axioms sameAction_faraut_core_length_uniform

end YMGap.Continuum.BF4FarautAFCutoffGrowth
