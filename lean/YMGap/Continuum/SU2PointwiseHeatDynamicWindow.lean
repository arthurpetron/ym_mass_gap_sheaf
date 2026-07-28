/-
# Dynamic arbitrary-nome SU(2) heat windows from one finite prefix

`SU2PointwiseHeatSpacingTailBound` constructs the completed pointwise SU(2)
heat kernel at every rational nome `0 < w < 1` and proves the exact corridor

    prefix(M) - tail(M) <= K_w(x) <= prefix(M) + tail(M).

This module turns one finite rational verification at the spacing-dependent
cutoff `M` into the dynamic local window needed by the BF4 Perron argument.
In particular, the completed kernel and its positivity are not fields of the
certificate: they are the already-constructed all-label character series.

For common rational `lower`, `upper`, the local finite certificate contains
only

    lower <= prefix(M) - tail(M),
    prefix(M) + tail(M) <= upper.

The first two inequalities imply semantic constructive-real bounds on the
completed heat kernel.  Supplying the single common bit cap
`upper <= 4^bits * lower`, literal products of twenty-three such factors
then give a `DynamicCompletedRetainedHarnackData` with spread
`4^(23*bits)`.
Thus either a Faraut image estimate or a direct finite character-prefix
estimate may feed the same AF/Perron layer.

## Honest scope

This file does not manufacture the finite prefix inequalities, identify the
class coordinates with the physical BF4 joint carrier, or prove the
nonlinear Perron ratio.  It removes the completed-series and tensorization
parts from that obligation.

## Constructivity

Exact `Q'` arithmetic, explicit all-label tails, finite lists, and
approximation-wise `CReal` order only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
import YMGap.Continuum.BF4FarautJointCarrierAFBudget
import YMGap.Continuum.BF4FarautAFCutoffGrowth

namespace YMGap.Continuum.SU2PointwiseHeatDynamicWindow

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4FarautAFCutoffGrowth
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One finite prefix certifies the completed heat window -/

/-- A finite rational certificate for one arbitrary-nome completed pointwise
SU(2) heat kernel.  The cutoff `M` may depend on the nome and class
coordinate; the common floor and ceiling are parameters so a finite BF4
carrier can share one projective window. -/
structure PointwiseHeatTailWindow
    (w x lower upper : Q') : Type where
  M : Nat
  lower_le_prefix_sub_tail :
    lower ≤
      spacingPointwiseHeatPartial w x M +
        -spacingClosedTail w M
  prefix_add_tail_le_upper :
    spacingPointwiseHeatPartial w x M +
        spacingClosedTail w M ≤ upper

namespace PointwiseHeatTailWindow

variable {w x lower upper : Q'}
    (window :
      PointwiseHeatTailWindow
        w x lower upper)

include window

/-- The finite lower-prefix calculation gives a genuine semantic lower bound
on the completed all-label heat kernel. -/
theorem completed_ge_lower
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x)
    (hxUpper : x ≤ (1 : Q')) :
    ExpPos.geRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      lower := by
  exact ExpPos.geRat_mono
    (prefix_sub_tail_le_pointwiseHeatCReal
      hw0 hw1 hxLower hxUpper window.M)
    window.lower_le_prefix_sub_tail

/-- The finite upper-prefix calculation gives a genuine semantic upper bound
on the completed all-label heat kernel. -/
theorem completed_le_upper
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x)
    (hxUpper : x ≤ (1 : Q')) :
    CReal.leRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      upper := by
  exact CReal.leRat_mono
    (pointwiseHeatCReal_le_prefix_add_tail
      hw0 hw1 hxLower hxUpper window.M)
    window.prefix_add_tail_le_upper

/-- The completed kernel is nonnegative, derived from its strict certified
floor. -/
theorem completed_ge_zero
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x)
    (hxUpper : x ≤ (1 : Q'))
    (lower_pos : (0 : Q') < lower) :
    ExpPos.geRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      0 :=
  ExpPos.geRat_mono
    (window.completed_ge_lower
      hw0 hw1 hxLower hxUpper)
    (Q'.le_of_lt lower_pos)

end PointwiseHeatTailWindow

/-! ### A closed non-vacuity instance -/

/-- At `w = 1/2`, `x = 0`, the computed spacing cutoff already certifies
the concrete window `1/2 <= K <= 2` at shifted prefix index zero. -/
def halfZeroTailWindow :
    PointwiseHeatTailWindow
      half 0 half 2 where
  M := 0
  lower_le_prefix_sub_tail := by decide
  prefix_add_tail_le_upper := by decide

/-- The preceding finite calculation gives a genuine positive lower bound
on the completed all-label kernel. -/
theorem half_le_completed_half_zero :
    ExpPos.geRat
      (pointwiseHeatCReal
        (w := half) (x := 0)
        (by decide) (by decide)
        (by decide) (by decide))
      half :=
  halfZeroTailWindow.completed_ge_lower
    (by decide) (by decide)
    (by decide) (by decide)

/-- The same finite calculation gives the matching coarse upper window. -/
theorem completed_half_zero_le_two :
    CReal.leRat
      (pointwiseHeatCReal
        (w := half) (x := 0)
        (by decide) (by decide)
        (by decide) (by decide))
      2 :=
  halfZeroTailWindow.completed_le_upper
    (by decide) (by decide)
    (by decide) (by decide)

/-- One bit pays the concrete `1/2 <= K <= 2` window exactly. -/
theorem half_zero_one_bit_cap :
    (2 : Q') ≤ four ^ 1 * half := by decide

/-! ## 2. A common dynamic local window tensorizes over 23 factors -/

private theorem pow_pos_local {value : Q'}
    (value_pos : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      show (0 : Q') < (1 : Q')
      decide
  | exponent + 1 =>
      Q'.mul_pos value_pos
        (pow_pos_local value_pos exponent)

private theorem one_le_pow_local {value : Q'}
    (one_le_value : (1 : Q') ≤ value) :
    ∀ exponent : Nat, (1 : Q') ≤ value ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hvalue_nonnegative : (0 : Q') ≤ value :=
        Q'.le_trans' _ _ _ Q'.zero_le_one one_le_value
      have hscaled :
          (1 : Q') * 1 ≤
            value * value ^ exponent :=
        Q'.mul_le_mul_of_nonneg
          one_le_value
          (one_le_pow_local one_le_value exponent)
          hvalue_nonnegative Q'.zero_le_one
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.one_mul_eqv 1))
        hscaled

private theorem mul_pow_eqv_local (left right : Q') :
    ∀ exponent : Nat,
      (left * right) ^ exponent ≈
        left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive :=
        mul_pow_eqv_local left right exponent
      show
        (left * right) * (left * right) ^ exponent ≈
          (left * left ^ exponent) *
            (right * right ^ exponent)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (left * right) _ _ hinductive) ?_
      calc
        (left * right) *
              (left ^ exponent * right ^ exponent) ≈
            left *
              (right *
                (left ^ exponent * right ^ exponent)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ left *
              ((right * left ^ exponent) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                right (left ^ exponent)
                (right ^ exponent)))
        _ ≈ left *
              ((left ^ exponent * right) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _
              (right ^ exponent)
              (Q'.mul_comm_eqv
                right (left ^ exponent)))
        _ ≈ left *
              (left ^ exponent *
                (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv
              (left ^ exponent) right
              (right ^ exponent))
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm
            (Q'.mul_assoc_eqv _ _ _)

/-- A one-factor dynamic bit cap tensorizes to the exact retained BF4
spread, independently of how the one-factor bounds were proved. -/
theorem dynamic_local_product_window_cap
    {lower upper : Q'} {bits : Nat}
    (upper_nonnegative : (0 : Q') ≤ upper)
    (upper_le_bit_cap :
      upper ≤ four ^ bits * lower) :
    upper ^ bf4SpatialCycleCount ≤
      farautRetainedSpread bits *
        lower ^ bf4SpatialCycleCount := by
  have hpowered :=
    FiveHolonomyPerronCutoff.pow_base_mono
      upper (four ^ bits * lower)
      upper_nonnegative upper_le_bit_cap
      bf4SpatialCycleCount
  have hfactor :
      (four ^ bits * lower) ^
          bf4SpatialCycleCount ≈
        farautRetainedSpread bits *
          lower ^ bf4SpatialCycleCount := by
    refine Q'.eqv_trans _ _ _
      (mul_pow_eqv_local
        (four ^ bits) lower
        bf4SpatialCycleCount) ?_
    unfold farautRetainedSpread
    exact Q'.mul_eqv_congr_right _ _
      (lower ^ bf4SpatialCycleCount)
      (FiveHolonomyPerronCutoff.pow_mul_eqv
        four bits bf4SpatialCycleCount)
  exact Q'.le_trans' _ _ _ hpowered
    (Q'.le_of_eqv hfactor)

private theorem leEv_of_leRat_local
    {value : CReal} {upper : Q'}
    (h : CReal.leRat value upper) :
    CReal.leEv value (CReal.ofQ' upper) := by
  intro ε hε
  exact h ε hε

private theorem leEv_of_geRat_local
    {value : CReal} {lower : Q'}
    (h : ExpPos.geRat value lower) :
    CReal.leEv (CReal.ofQ' lower) value := by
  intro ε hε
  exact h ε hε

private theorem rationalWindow_leEv
    {lower upper spread : Q'}
    {first second : CReal}
    (spread_nonnegative : (0 : Q') ≤ spread)
    (window_order : upper ≤ spread * lower)
    (first_upper : CReal.leRat first upper)
    (second_lower : ExpPos.geRat second lower) :
    CReal.leEv first
      (CReal.mul (CReal.ofQ' spread) second) := by
  have hconstant :
      CReal.leEv
        (CReal.ofQ' upper)
        (CReal.ofQ' (spread * lower)) := by
    intro ε hε
    refine ⟨0, fun _ _ => ?_⟩
    exact Q'.le_trans' _ _ _ window_order
      (Q'.add_le_self_of_nonneg
        (spread * lower) ε (Q'.le_of_lt hε))
  have hscaled :
      ExpPos.geRat
        (CReal.mul (CReal.ofQ' spread) second)
        (spread * lower) :=
    YMGap.Constructive.SU3CharFactor.geRat_smul_nonneg
      spread_nonnegative second_lower
  exact CReal.leEv_trans
    (CReal.leEv_trans
      (leEv_of_leRat_local first_upper)
      hconstant)
    (leEv_of_geRat_local hscaled)

/-- Generic dynamic completed retained Harnack construction from common
one-factor semantic bounds.  Unlike `farautCompletedRetainedHarnack`, this
consumer does not require an image representation; it is therefore also
available to the direct character-prefix route. -/
def dynamicCompletedRetainedHarnackOfLocalWindow
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (kernel :
      Source → Target → List State → Factor → CReal)
    (sources : List Source) (targets : List Target)
    (lower upper : Q') (bits : Nat)
    (lower_pos : (0 : Q') < lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (local_lower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              ExpPos.geRat
                (kernel source target path factor)
                lower)
    (local_upper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              CReal.leRat
                (kernel source target path factor)
                upper)
    (upper_le_bit_cap :
      upper ≤ four ^ bits * lower) :
    DynamicCompletedRetainedHarnackData
      paths
      (fun source target path =>
        completedFactorProduct
          (kernel source target path) factors)
      sources targets := by
  let spread := farautRetainedSpread bits
  exact {
    lower := lower ^ bf4SpatialCycleCount
    upper := upper ^ bf4SpatialCycleCount
    spread := spread
    lower_pos :=
      pow_pos_local lower_pos bf4SpatialCycleCount
    one_le_spread := by
      unfold spread farautRetainedSpread
      exact one_le_pow_local
        (by decide)
        (bits * bf4SpatialCycleCount)
    kinetic_nonnegative := by
      intro source hsource target htarget path hpath
      have hlower :=
        completedFactorProduct_lower_on
          (kernel source target path)
          lower (Q'.le_of_lt lower_pos)
          factors
          (fun factor hfactor =>
            local_lower source hsource
              target htarget path hpath
              factor hfactor)
      exact ExpPos.geRat_mono hlower
        (Q'.pow_nonneg lower
          (Q'.le_of_lt lower_pos)
          factors.length)
    lower_bound := by
      intro source hsource target htarget path hpath
      have hlower :=
        completedFactorProduct_lower_on
          (kernel source target path)
          lower (Q'.le_of_lt lower_pos)
          factors
          (fun factor hfactor =>
            local_lower source hsource
              target htarget path hpath
              factor hfactor)
      rw [factor_count] at hlower
      exact hlower
    upper_bound := by
      intro source hsource target htarget path hpath
      have hupper :=
        completedFactorProduct_upper_on
          (kernel source target path)
          lower upper
          (Q'.le_of_lt lower_pos)
          upper_nonnegative
          factors
          (fun factor hfactor =>
            local_lower source hsource
              target htarget path hpath
              factor hfactor)
          (fun factor hfactor =>
            local_upper source hsource
              target htarget path hpath
              factor hfactor)
      rw [factor_count] at hupper
      exact hupper
    pathwiseDomination := by
      intro first hfirst second hsecond
        target htarget path hpath
      have hfirstUpper :=
        completedFactorProduct_upper_on
          (kernel first target path)
          lower upper
          (Q'.le_of_lt lower_pos)
          upper_nonnegative
          factors
          (fun factor hfactor =>
            local_lower first hfirst target htarget
              path hpath factor hfactor)
          (fun factor hfactor =>
            local_upper first hfirst target htarget
              path hpath factor hfactor)
      have hsecondLower :=
        completedFactorProduct_lower_on
          (kernel second target path)
          lower (Q'.le_of_lt lower_pos)
          factors
          (fun factor hfactor =>
            local_lower second hsecond target htarget
              path hpath factor hfactor)
      rw [factor_count] at hfirstUpper hsecondLower
      exact rationalWindow_leEv
        (Q'.pow_nonneg four (by decide)
          (bits * bf4SpatialCycleCount))
        (dynamic_local_product_window_cap
          upper_nonnegative upper_le_bit_cap)
        hfirstUpper hsecondLower
  }

/-! ## 3. Specialization to the actual completed pointwise heat series -/

/-- The actual arbitrary-nome pointwise SU(2) character kernel on every
literal retained factor, with no abstract completed kernel argument. -/
def dynamicPointwiseLocalHeat
    {Source Target State Factor : Type}
    (w x : Source → Target → List State → Factor → Q')
    (w_pos :
      ∀ source target path factor,
        (0 : Q') <
          w source target path factor)
    (w_lt_one :
      ∀ source target path factor,
        w source target path factor < (1 : Q'))
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤
          x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (source : Source) (target : Target)
    (path : List State) (factor : Factor) : CReal :=
  pointwiseHeatCReal
    (w_pos source target path factor)
    (w_lt_one source target path factor)
    (x_lower source target path factor)
    (x_upper source target path factor)

/-- Literal products of twenty-three actual arbitrary-nome completed heat
kernels inherit the dynamic Harnack datum from finite prefix/tail
certificates. -/
def dynamicPointwiseRetainedHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x : Source → Target → List State → Factor → Q')
    (w_pos :
      ∀ source target path factor,
        (0 : Q') <
          w source target path factor)
    (w_lt_one :
      ∀ source target path factor,
        w source target path factor < (1 : Q'))
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤
          x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (sources : List Source) (targets : List Target)
    (lower upper : Q') (bits : Nat)
    (lower_pos : (0 : Q') < lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (upper_le_bit_cap :
      upper ≤ four ^ bits * lower)
    (windows :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              PointwiseHeatTailWindow
                (w source target path factor)
                (x source target path factor)
                lower upper) :
    DynamicCompletedRetainedHarnackData
      paths
      (fun source target path =>
        completedFactorProduct
          (dynamicPointwiseLocalHeat
            w x w_pos w_lt_one x_lower x_upper
            source target path)
          factors)
      sources targets := by
  exact dynamicCompletedRetainedHarnackOfLocalWindow
    paths factors factor_count
    (dynamicPointwiseLocalHeat
      w x w_pos w_lt_one x_lower x_upper)
    sources targets lower upper bits
    lower_pos upper_nonnegative
    (fun source hsource target htarget
      path hpath factor hfactor =>
        (windows source hsource target htarget
          path hpath factor hfactor).completed_ge_lower
            (w_pos source target path factor)
            (w_lt_one source target path factor)
            (x_lower source target path factor)
            (x_upper source target path factor))
    (fun source hsource target htarget
      path hpath factor hfactor =>
        (windows source hsource target htarget
          path hpath factor hfactor).completed_le_upper
            (w_pos source target path factor)
            (w_lt_one source target path factor)
            (x_lower source target path factor)
            (x_upper source target path factor))
    upper_le_bit_cap

/-! ## 4. The full joint BF4 carrier and conditional pushforward -/

/-- The direct character-prefix window on the literal full joint carrier.
Every retained state still contains its complete face-channel field and
shared-link fusion witness. -/
def wholeSlabDynamicPointwiseRetainedHarnack
    {Source Target Factor : Type}
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          Factor → Q')
    (w_pos :
      ∀ source target path factor,
        (0 : Q') <
          w source target path factor)
    (w_lt_one :
      ∀ source target path factor,
        w source target path factor < (1 : Q'))
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤
          x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (sources : List Source) (targets : List Target)
    (lower upper : Q') (bits : Nat)
    (lower_pos : (0 : Q') < lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (upper_le_bit_cap :
      upper ≤ four ^ bits * lower)
    (windows :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path,
            path ∈ wholeSlabJointCarrierPaths S fineState →
            ∀ factor, factor ∈ factors →
              PointwiseHeatTailWindow
                (w source target path factor)
                (x source target path factor)
                lower upper) :
    DynamicCompletedRetainedHarnackData
      (wholeSlabJointCarrierPaths S fineState)
      (fun source target path =>
        completedFactorProduct
          (dynamicPointwiseLocalHeat
            w x w_pos w_lt_one x_lower x_upper
            source target path)
          factors)
      sources targets :=
  dynamicPointwiseRetainedHarnack
    (wholeSlabJointCarrierPaths S fineState)
    factors factor_count
    w x w_pos w_lt_one x_lower x_upper
    sources targets lower upper bits
    lower_pos upper_nonnegative upper_le_bit_cap
    windows

/-- Arbitrary common nonnegative interior spatial weights and summation over
the full joint carrier preserve the direct character-prefix projective
spread exactly. -/
theorem wholeSlabDynamicPointwiseConditionalPushforward_domination
    {Source Target Factor : Type}
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          Factor → Q')
    (w_pos :
      ∀ source target path factor,
        (0 : Q') <
          w source target path factor)
    (w_lt_one :
      ∀ source target path factor,
        w source target path factor < (1 : Q'))
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤
          x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential :
      WholeSlabJointCarrierCode S fineState → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (lower upper : Q') (bits : Nat)
    (lower_pos : (0 : Q') < lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (upper_le_bit_cap :
      upper ≤ four ^ bits * lower)
    (windows :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path,
            path ∈ wholeSlabJointCarrierPaths S fineState →
            ∀ factor, factor ∈ factors →
              PointwiseHeatTailWindow
                (w source target path factor)
                (x source target path factor)
                lower upper)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    CReal.leEv
      (completedConditionalPathPushforward
        (wholeSlabJointCarrierPaths S fineState)
        (fun source target path =>
          completedFactorProduct
            (dynamicPointwiseLocalHeat
              w x w_pos w_lt_one x_lower x_upper
              source target path)
            factors)
        potential first target)
      (CReal.mul
        (CReal.ofQ'
          (farautRetainedSpread bits))
        (completedConditionalPathPushforward
          (wholeSlabJointCarrierPaths S fineState)
          (fun source target path =>
            completedFactorProduct
              (dynamicPointwiseLocalHeat
                w x w_pos w_lt_one x_lower x_upper
                source target path)
              factors)
          potential second target)) := by
  let harnack :=
    wholeSlabDynamicPointwiseRetainedHarnack
      factors factor_count
      w x w_pos w_lt_one x_lower x_upper
      sources targets lower upper bits
      lower_pos upper_nonnegative upper_le_bit_cap
      windows
  exact dynamicCompletedConditionalPushforward_domination
    (wholeSlabJointCarrierPaths S fineState)
    (fun source target path =>
      completedFactorProduct
        (dynamicPointwiseLocalHeat
          w x w_pos w_lt_one x_lower x_upper
          source target path)
        factors)
    potential potential_nonnegative
    sources targets harnack
    first hfirst second hsecond target htarget

/-! ### Non-vacuous conditional integration

The projective domination above is valid for an empty carrier, as every
finite-sum identity must be.  A positive physical row needs more: an explicit
joint carrier member and a strictly positive interior weight.  The next two
theorems make those hypotheses visible and retain a quantitative lower bound
after conditional integration. -/

/-- A genuine joint-carrier witness produces a literal singleton retained
path, so the path list has positive length. -/
theorem wholeSlabJointCarrierPaths_length_pos
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (nonempty :
      WholeSlabJointCarrierNonempty S fineState) :
    0 < (wholeSlabJointCarrierPaths S fineState).length := by
  let carrier := nonempty.toEnumeratedCarrier
  exact List.length_pos_of_mem
    (singleton_mem_wholeSlabJointCarrierPaths
      carrier.code_mem)

/-- On a witnessed joint carrier, a common positive potential floor and the
dynamic kinetic floor survive the conditional sum.  In particular the
positive lower bound cannot be discharged by an empty enumeration. -/
theorem wholeSlabDynamicConditionalPushforward_ge_witnessed_floor
    {Source Target : Type}
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (nonempty :
      WholeSlabJointCarrierNonempty S fineState)
    (kineticWeight :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          CReal)
    (potential :
      WholeSlabJointCarrierCode S fineState → Q')
    (potentialFloor : Q')
    (potential_floor_pos :
      (0 : Q') < potentialFloor)
    (potential_lower :
      ∀ state, potentialFloor ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      DynamicCompletedRetainedHarnackData
        (wholeSlabJointCarrierPaths S fineState)
        kineticWeight sources targets)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    ExpPos.geRat
      (completedConditionalPathPushforward
        (wholeSlabJointCarrierPaths S fineState)
        kineticWeight potential source target)
      (potentialFloor ^ 1 * harnack.lower) := by
  let carrier := nonempty.toEnumeratedCarrier
  let selected : List
      (WholeSlabJointCarrierCode S fineState) :=
    [carrier.code]
  have hselected :
      selected ∈
        wholeSlabJointCarrierPaths S fineState :=
    singleton_mem_wholeSlabJointCarrierPaths
      carrier.code_mem
  have hpotential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state := by
    intro state
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt potential_floor_pos)
      (potential_lower state)
  have hsum_nonnegative :
      ∀ path,
        path ∈ wholeSlabJointCarrierPaths S fineState →
        ExpPos.geRat
          (completedRetainedFeynmanKacWeight
            kineticWeight potential source target path)
          0 := by
    intro path hpath
    exact completedRetainedFeynmanKacWeight_nonnegative
      kineticWeight potential hpotential_nonnegative
      (harnack.kinetic_nonnegative
        source hsource target htarget path hpath)
  have hpotential_product :
      potentialFloor ^ selected.length ≤
        pathPotentialProduct potential selected :=
    potentialProduct_lower
      potential potentialFloor
      (Q'.le_of_lt potential_floor_pos)
      potential_lower selected
  have hkinetic_lower :
      ExpPos.geRat
        (kineticWeight source target selected)
        harnack.lower :=
    harnack.lower_bound
      source hsource target htarget selected hselected
  have hscaled :
      ExpPos.geRat
        (completedRetainedFeynmanKacWeight
          kineticWeight potential source target selected)
        (pathPotentialProduct potential selected *
          harnack.lower) :=
    YMGap.Constructive.SU3CharFactor.geRat_smul_nonneg
      (pathPotentialProduct_nonnegative
        hpotential_nonnegative selected)
      hkinetic_lower
  have hlower_nonnegative :
      (0 : Q') ≤ harnack.lower :=
    Q'.le_of_lt harnack.lower_pos
  have hselected_floor :
      ExpPos.geRat
        (completedRetainedFeynmanKacWeight
          kineticWeight potential source target selected)
        (potentialFloor ^ 1 * harnack.lower) := by
    exact ExpPos.geRat_mono hscaled
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (by
          change
            potentialFloor ^ selected.length ≤
              pathPotentialProduct potential selected
          exact hpotential_product)
        hlower_nonnegative)
  exact completedPathSum_ge_selected
    (completedRetainedFeynmanKacWeight
      kineticWeight potential source target)
    (wholeSlabJointCarrierPaths S fineState)
    hsum_nonnegative selected hselected
    (potentialFloor ^ 1 * harnack.lower)
    hselected_floor

/-! ## 5. The direct character windows tied to the AF bit schedule -/

/-- A family of actual arbitrary-nome character-prefix windows tied to the
same bit schedule whose heat cost is controlled by the AF trajectory.
`Local` may be the complete source/target/path/factor tuple; keeping it
explicit prevents a cheap unrelated bit schedule from paying for a more
expensive local window. -/
structure PointwiseHeatAFWindowFamily
    (E : AFEnvelope)
    (coupling : Nat → Q')
    (Local : Type)
    (w x : Nat → Local → Q')
    (lower upper : Nat → Q') : Type where
  bits : Nat → Nat
  growth :
    FarautAFBitGrowth E coupling bits
  lower_pos :
    ∀ scale, (0 : Q') < lower scale
  upper_nonnegative :
    ∀ scale, (0 : Q') ≤ upper scale
  upper_le_bit_cap :
    ∀ scale,
      upper scale ≤
        four ^ bits scale * lower scale
  local_window :
    ∀ scale location,
      PointwiseHeatTailWindow
        (w scale location) (x scale location)
        (lower scale) (upper scale)

/-- Every local member of a direct AF character-window family gives the
semantic lower bound on the actual completed all-label kernel. -/
theorem pointwise_af_window_completed_ge_lower
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {Local : Type}
    {w x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (family :
      PointwiseHeatAFWindowFamily
        E coupling Local w x lower upper)
    (w_pos :
      ∀ scale location,
        (0 : Q') < w scale location)
    (w_lt_one :
      ∀ scale location,
        w scale location < (1 : Q'))
    (x_lower :
      ∀ scale location,
        (-(1 : Q')) ≤ x scale location)
    (x_upper :
      ∀ scale location,
        x scale location ≤ (1 : Q'))
    (scale : Nat) (location : Local) :
    ExpPos.geRat
      (pointwiseHeatCReal
        (w_pos scale location)
        (w_lt_one scale location)
        (x_lower scale location)
        (x_upper scale location))
      (lower scale) :=
  (family.local_window scale location).completed_ge_lower
    (w_pos scale location)
    (w_lt_one scale location)
    (x_lower scale location)
    (x_upper scale location)

/-- Every local member also gives the semantic upper bound on the same
completed kernel. -/
theorem pointwise_af_window_completed_le_upper
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {Local : Type}
    {w x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (family :
      PointwiseHeatAFWindowFamily
        E coupling Local w x lower upper)
    (w_pos :
      ∀ scale location,
        (0 : Q') < w scale location)
    (w_lt_one :
      ∀ scale location,
        w scale location < (1 : Q'))
    (x_lower :
      ∀ scale location,
        (-(1 : Q')) ≤ x scale location)
    (x_upper :
      ∀ scale location,
        x scale location ≤ (1 : Q'))
    (scale : Nat) (location : Local) :
    CReal.leRat
      (pointwiseHeatCReal
        (w_pos scale location)
        (w_lt_one scale location)
        (x_lower scale location)
        (x_upper scale location))
      (upper scale) :=
  (family.local_window scale location).completed_le_upper
    (w_pos scale location)
    (w_lt_one scale location)
    (x_lower scale location)
    (x_upper scale location)

/-- The tied direct character-window family pays the strict Perron
inequality at every scale once the physical depth contains its own bit
cost. -/
theorem pointwise_af_window_family_perron_strict
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {Local : Type}
    {w x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (family :
      PointwiseHeatAFWindowFamily
        E coupling Local w x lower upper)
    (qS : Nat → Q') (m : Nat → Nat)
    (qS_nonnegative :
      ∀ scale, (0 : Q') ≤ qS scale)
    (qS_le_quarter :
      ∀ scale, qS scale ≤ quarter)
    (depth_available :
      ∀ scale,
        farautRequiredDepth
            (family.bits scale) ≤
          m scale) :
    ∀ scale,
      farautPerronSquare
          (family.bits scale) *
        qS scale ^ (m scale - 2) < 1 :=
  fun scale =>
    faraut_perron_of_available_depth
      (family.bits scale)
      (qS scale) (m scale)
      (qS_nonnegative scale)
      (qS_le_quarter scale)
      (depth_available scale)

/-- The tied direct character-window family occupies one uniformly bounded
AF-scaled physical core length. -/
theorem pointwise_af_window_family_core_length_uniform
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {Local : Type}
    {w x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (family :
      PointwiseHeatAFWindowFamily
        E coupling Local w x lower upper) :
    ∀ scale,
      BF4AFHeatSpacing.heatSpacingRate E *
          (Q'.ofNat
              (46 * family.bits scale) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 *
          family.growth.costCeiling :=
  faraut_af_family_core_length_uniform
    family.growth

/-! ## 6. Same-action direct character windows -/

/-- Direct character windows evaluated at the literal AF-envelope weight.
The bit budget is definitionally the spacing cutoff of that same weight.
This rules out paying for the physical kernel with an unrelated nome or bit
schedule. -/
structure SameActionPointwiseHeatWindows
    (E : AFEnvelope)
    (coupling : Nat → Q')
    (Local : Type)
    (x : Nat → Local → Q')
    (lower upper : Nat → Q') : Type where
  bridge :
    DyadicSameActionAFBridge E coupling
  weight_pos :
    ∀ scale, (0 : Q') < E.w (coupling scale)
  weight_lt_one :
    ∀ scale, E.w (coupling scale) < (1 : Q')
  lower_pos :
    ∀ scale, (0 : Q') < lower scale
  upper_nonnegative :
    ∀ scale, (0 : Q') ≤ upper scale
  upper_le_cutoff_cap :
    ∀ scale,
      upper scale ≤
        four ^
            sameActionSpacingBits E coupling scale *
          lower scale
  local_window :
    ∀ scale location,
      PointwiseHeatTailWindow
        (E.w (coupling scale))
        (x scale location)
        (lower scale) (upper scale)

namespace SameActionPointwiseHeatWindows

variable
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {Local : Type}
    {x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (windows :
      SameActionPointwiseHeatWindows
        E coupling Local x lower upper)

/-- Forgetting the definitional same-action refinement gives the generic AF
window family, with no change to its nome or bit schedule. -/
def toAFWindowFamily :
    PointwiseHeatAFWindowFamily
      E coupling Local
      (fun scale _ => E.w (coupling scale))
      x lower upper where
  bits := sameActionSpacingBits E coupling
  growth := sameActionFarautAFBitGrowth windows.bridge
  lower_pos := windows.lower_pos
  upper_nonnegative := windows.upper_nonnegative
  upper_le_bit_cap := windows.upper_le_cutoff_cap
  local_window := windows.local_window

include windows

/-- The same-action family inherits the uniform physical core-length bound
with the explicit constant `46*16`. -/
theorem core_length_uniform :
    ∀ scale,
      BF4AFHeatSpacing.heatSpacingRate E *
          (Q'.ofNat
              (46 *
                sameActionSpacingBits E coupling scale) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 * Q'.ofNat 16 :=
  sameAction_faraut_core_length_uniform windows.bridge

end SameActionPointwiseHeatWindows

end YMGap.Continuum.SU2PointwiseHeatDynamicWindow

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.PointwiseHeatTailWindow.completed_ge_lower
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.PointwiseHeatTailWindow.completed_le_upper
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.PointwiseHeatTailWindow.completed_ge_zero
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.halfZeroTailWindow
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.half_le_completed_half_zero
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.completed_half_zero_le_two
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.half_zero_one_bit_cap
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.dynamic_local_product_window_cap
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.dynamicCompletedRetainedHarnackOfLocalWindow
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.dynamicPointwiseLocalHeat
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.dynamicPointwiseRetainedHarnack
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.wholeSlabDynamicPointwiseRetainedHarnack
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.wholeSlabDynamicPointwiseConditionalPushforward_domination
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.wholeSlabJointCarrierPaths_length_pos
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.wholeSlabDynamicConditionalPushforward_ge_witnessed_floor
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.pointwise_af_window_completed_ge_lower
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.pointwise_af_window_completed_le_upper
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.pointwise_af_window_family_perron_strict
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.pointwise_af_window_family_core_length_uniform
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.SameActionPointwiseHeatWindows
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.SameActionPointwiseHeatWindows.toAFWindowFamily
#print axioms YMGap.Continuum.SU2PointwiseHeatDynamicWindow.SameActionPointwiseHeatWindows.core_length_uniform
