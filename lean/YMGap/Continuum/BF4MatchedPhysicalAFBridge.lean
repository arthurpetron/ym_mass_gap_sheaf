/-
# Physical BF4 matching to the bare AF diagnostic

`BareAFDiagnostic.AFEnvelope` is indexed by a rational weak-coupling
coordinate `g`, whereas `BF4ObservableMatchedTrajectory` is a discrete
trajectory of rational heat nomes.  A discrete trajectory alone therefore
cannot inhabit `AFEnvelope`: the latter asks for bounds at every rational
`0 < g <= g₁`.

This module supplies the smallest honest local chart currently supported by
the exact finite BF4 block kernels.  A `MatchedBlockFamily` is, by
construction, one of:

* the exact observable-matched cutoff-one block output; or
* the exact exponent-Gram-matched cutoff-one block output.

Thus `blockedWeight F g` is definitionally obtained by a finite matching
argmin and is not definitionally the Padé weight.  The geometry, atlas,
coordinates, and observable in the parameterized family are still supplied
data; this module does not prove that they form the nonperturbative continuum
trajectory.  The AF input is split into precisely two named, Type-valued
certificates:

1. `CubicMarginLaw F`: on a small rational chart, the current physical
   heat-nome margin is `g²`, and the blocked physical margin obeys the cubic
   AF recurrence with an explicit one-sided smallness window.
2. `PhysicalSpacingEnvelope g₁`: a positive physical spacing family with the
   collapsed spacing estimate `a(g) Λ <= C g²`.

The cubic recurrence plus its window proves the two-sided comparison

    (1/2) g² <= 1 - blockedWeight(F,g).
    1 - blockedWeight(F,g) <= 2 g².

With `t(g) = 4 g²`, this is exactly the `AFEnvelope.w_floor` field.  The
spacing certificate supplies the logically independent `spacing_quad` field.
Consequently `physicalAFEnvelope` has

    w(g) = blockedWeight(F,g)

definitionally and can be passed to `BareAFImpliesLinearFloor` without
conflating the physical block output with the pre-existing Padé model.

Honest frontier:

* no inhabitant of `CubicMarginLaw` is constructed here for four-dimensional
  Yang--Mills; that is the separator/identifiability plus cubic-remainder
  theorem still to prove;
* no physical `PhysicalSpacingEnvelope` is constructed here; the cubic
  recurrence does not imply dimensional-transmutation spacing;
* the finite atlases and finite exponent-coordinate lists remain explicit.

All data are constructive and Type-valued.  No `Classical.*`,
`native_decide`, custom axiom, `noncomputable`, or placeholder is used.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep
import YMGap.Continuum.BF4ExponentGramMatchedOneStep
import YMGap.Continuum.BF4AFHeatSpacing

namespace YMGap.Continuum.BF4MatchedPhysicalAFBridge

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4AFHeatSpacing
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4ExponentGramMatchedOneStep

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact physical one-step families -/

/-- A rationally parameterized family of exact observable-matching problems.
The fine heat nome is required to be nonnegative for every rational parameter
so the family is total; the AF chart below constrains it only on
`0 < g <= g₁`. -/
structure ObservableBlockFamily : Type where
  geometry : Q' → CutoffOneGeometry
  fineWeight : Q' → Q'
  fineWeight_nonnegative : ∀ g, (0 : Q') ≤ fineWeight g
  atlas : Q' → PositiveCouplingAtlas
  observable :
    Q' → BF4ObservableMatchedOneStep.SlabLabelling → Q'

/-- A rationally parameterized family of exact exponent-Gram matching
problems.  Every blocked weight is selected by the complete supplied finite
coordinate list and finite positive atlas. -/
structure ExponentGramBlockFamily : Type where
  geometry : Q' → CutoffOneGeometry
  fineWeight : Q' → Q'
  fineWeight_nonnegative : ∀ g, (0 : Q') ≤ fineWeight g
  atlas : Q' → PositiveCouplingAtlas
  coordinates : Q' → List ExponentGramCoordinate

/-- The two finite BF4 selector forms presently available in the library.
The inductive carrier records which literal argmin construction is used.  It
does not by itself certify that the freely supplied parameterized matching
data are the Yang--Mills continuum trajectory. -/
inductive MatchedBlockFamily : Type
  | observable : ObservableBlockFamily → MatchedBlockFamily
  | exponentGram : ExponentGramBlockFamily → MatchedBlockFamily

/-- The fine physical heat nome supplied to the exact block kernel. -/
def fineWeight : MatchedBlockFamily → Q' → Q'
  | .observable family => family.fineWeight
  | .exponentGram family => family.fineWeight

/-- Every fine physical heat nome in a matched family is nonnegative. -/
theorem fineWeight_nonnegative (family : MatchedBlockFamily) (g : Q') :
    (0 : Q') ≤ fineWeight family g := by
  cases family with
  | observable family => exact family.fineWeight_nonnegative g
  | exponentGram family => exact family.fineWeight_nonnegative g

/-- The exact finite physical blocked heat nome.  Both branches are
definitionally the corresponding constructive finite argmin. -/
def blockedWeight : MatchedBlockFamily → Q' → Q'
  | .observable family, g =>
      observableMatchedCoupling
        (family.geometry g)
        (family.fineWeight g)
        (family.fineWeight_nonnegative g)
        (family.atlas g)
        (family.observable g)
  | .exponentGram family, g =>
      exponentGramMatchedCoupling
        (family.geometry g)
        (family.fineWeight g)
        (family.fineWeight_nonnegative g)
        (family.atlas g)
        (family.coordinates g)

/-- The exact physical blocked heat nome is strictly positive because the
selected candidate belongs to the supplied positive atlas. -/
theorem blockedWeight_pos (family : MatchedBlockFamily) (g : Q') :
    (0 : Q') < blockedWeight family g := by
  cases family with
  | observable family =>
      exact observableMatchedCoupling_pos
        (family.geometry g)
        (family.fineWeight g)
        (family.fineWeight_nonnegative g)
        (family.atlas g)
        (family.observable g)
  | exponentGram family =>
      exact exponentGramMatchedCoupling_pos
        (family.geometry g)
        (family.fineWeight g)
        (family.fineWeight_nonnegative g)
        (family.atlas g)
        (family.coordinates g)

/-- The current heat-nome margin `1-w`. -/
def fineMargin (family : MatchedBlockFamily) (g : Q') : Q' :=
  1 + -(fineWeight family g)

/-- The blocked heat-nome margin `1-w'`. -/
def blockedMargin (family : MatchedBlockFamily) (g : Q') : Q' :=
  1 + -(blockedWeight family g)

/-! ## 2. The genuine cubic AF input on the physical block output -/

/-- The Yang--Mills-specific local AF law for an exact matched block family.

`current_margin` pins the rational chart to the physical fine heat nome:
`1-w = g²`.  `cubic_remainder` is then a recurrence for the exact blocked
margin, not for a supplied scalar model.  `cubic_window` is the explicit
smallness condition ensuring that, after the full cubic error is subtracted,
at least half of the incoming margin remains.

The window is stated in its minimal one-sided form because that is exactly
what the downstream `w_floor` proof consumes.  A conventional estimate such
as `β g² + E g⁴ <= 1/2` implies it by elementary multiplication and
reassociation. -/
structure CubicMarginLaw (family : MatchedBlockFamily) : Type where
  β : Q'
  E : Q'
  g₁ : Q'
  β_pos : (0 : Q') < β
  E_nonnegative : (0 : Q') ≤ E
  g₁_pos : (0 : Q') < g₁
  current_margin :
    ∀ g : Q', (0 : Q') < g → g ≤ g₁ →
      fineMargin family g ≈ g * g
  cubic_remainder :
    ∀ g : Q', (0 : Q') < g → g ≤ g₁ →
      Q'.abs
        (blockedMargin family g -
          ((g * g) - β * ((g * g) * (g * g)))) ≤
        E * ((g * g) * ((g * g) * (g * g)))
  cubic_window :
    ∀ g : Q', (0 : Q') < g → g ≤ g₁ →
      half * fineMargin family g +
          E * ((g * g) * ((g * g) * (g * g))) ≤
        (g * g) - β * ((g * g) * (g * g))

/-! ## 3. Cubic recurrence implies the physical margin floor -/

/-- The lower half of an absolute-value remainder estimate. -/
private theorem neg_error_le_difference
    {difference error : Q'}
    (habs : Q'.abs difference ≤ error) :
    -error ≤ difference := by
  have hneg_error : -error ≤ -(Q'.abs difference) :=
    Q'.neg_le_neg habs
  have hneg_abs : -(Q'.abs difference) ≤ difference := by
    have hnegated :
        -(Q'.abs difference) ≤ -(-difference) :=
      Q'.neg_le_neg (Q'.neg_le_abs difference)
    exact Q'.le_trans' _ _ _ hnegated
      (Q'.le_of_eqv (Q'.neg_neg_eqv difference))
  exact Q'.le_trans' _ _ _ hneg_error hneg_abs

/-- A two-sided remainder and a one-sided retained-window estimate imply the
desired lower bound on the next value. -/
theorem lower_of_abs_remainder
    {next model error lower : Q'}
    (habs : Q'.abs (next - model) ≤ error)
    (hwindow : lower + error ≤ model) :
    lower ≤ next := by
  have hdiff : -error ≤ next - model :=
    neg_error_le_difference habs
  have hadd :
      (-error) + model ≤ (next - model) + model :=
    Q'.add_le_add_right (-error) (next - model) model hdiff
  have hleft : ((-error) + model).eqv (model + (-error)) :=
    Q'.add_comm_eqv (-error) model
  have hright : ((next - model) + model).eqv next := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv next (-model) model) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left next ((-model) + model) 0
        (Q'.neg_add_self_eqv model)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' next)
  have hmodel_sub_error : lower ≤ model + (-error) :=
    le_sub_of_add_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_comm_eqv error lower))
        hwindow)
  exact Q'.le_trans' _ _ _ hmodel_sub_error
    (Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)))

/-- The exact physically blocked heat-nome margin retains at least half of
the incoming `g²` margin throughout the AF chart. -/
theorem blockedMargin_ge_half_square
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) :
    half * (g * g) ≤ blockedMargin family g := by
  have hcurrent := law.current_margin g hg hgle
  have hchart :
      half * (g * g) ≈
        half * fineMargin family g :=
    Q'.mul_eqv_congr_left
      half (g * g) (fineMargin family g)
      (Q'.eqv_symm hcurrent)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hchart)
    (lower_of_abs_remainder
      (law.cubic_remainder g hg hgle)
      (law.cubic_window g hg hgle))

/-- The same cubic remainder and one-sided window also give a constructive
upper comparison for the physical blocked margin.  The constant `2` is
deliberately coarse: the purpose is to expose an explicit volume-independent
`O(g²)` factor for downstream physical perturbation estimates. -/
theorem blockedMargin_le_two_square
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) :
    blockedMargin family g ≤ Q'.ofNat 2 * (g * g) := by
  have hg0 : (0 : Q') ≤ g := Q'.le_of_lt hg
  have hsquare0 : (0 : Q') ≤ g * g :=
    Q'.mul_nonneg g g hg0 hg0
  have hfine0 : (0 : Q') ≤ fineMargin family g :=
    Q'.le_trans' _ (g * g) _ hsquare0
      (Q'.ge_of_eqv (law.current_margin g hg hgle))
  have hhalfFine0 :
      (0 : Q') ≤ half * fineMargin family g :=
    Q'.mul_nonneg half (fineMargin family g) (by decide) hfine0
  have herror_le_model :
      law.E * ((g * g) * ((g * g) * (g * g))) ≤
        (g * g) - law.β * ((g * g) * (g * g)) := by
    refine Q'.le_trans' _
      (half * fineMargin family g +
        law.E * ((g * g) * ((g * g) * (g * g)))) _ ?_ ?_
    · exact Q'.le_trans' _
        (law.E * ((g * g) * ((g * g) * (g * g))) +
          half * fineMargin family g) _
        (Q'.add_le_self_of_nonneg _ _ hhalfFine0)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
    · exact law.cubic_window g hg hgle
  have hbetaFourth0 :
      (0 : Q') ≤ law.β * ((g * g) * (g * g)) :=
    Q'.mul_nonneg law.β ((g * g) * (g * g))
      (Q'.le_of_lt law.β_pos)
      (Q'.mul_nonneg (g * g) (g * g) hsquare0 hsquare0)
  have hmodel_le_square :
      (g * g) - law.β * ((g * g) * (g * g)) ≤ g * g := by
    refine Q'.le_trans' _ ((g * g) + 0) _ ?_ ?_
    · change (g * g) + (-(law.β * ((g * g) * (g * g)))) ≤
        (g * g) + 0
      exact Q'.add_le_add_left (g * g) _ _
        (Q'.neg_le_neg hbetaFourth0)
    · exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (g * g)))
  have hupper :
      blockedMargin family g ≤
        ((g * g) - law.β * ((g * g) * (g * g))) +
          law.E * ((g * g) * ((g * g) * (g * g))) :=
    YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
      (law.cubic_remainder g hg hgle)
  refine Q'.le_trans' _ _ _ hupper
    (Q'.le_trans' _
      ((g * g) +
        ((g * g) - law.β * ((g * g) * (g * g)))) _
      (Q'.add_le_add hmodel_le_square herror_le_model)
      ?_)
  refine Q'.le_trans' _ ((g * g) + (g * g)) _
    (Q'.add_le_add_left (g * g) _ _ hmodel_le_square) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm (YMGap.Constructive.ExpNeg.two_mul_eqv (g * g)))

/-! ## 4. The independent physical spacing input -/

/-- Positive physical spacing data on the same rational AF chart.

The `spacing_quad` field is deliberately separate from `CubicMarginLaw`.
A coupling recurrence controls the flow of the heat nome; it does not by
itself identify the geometric lattice spacing or prove dimensional
transmutation. -/
structure PhysicalSpacingEnvelope (g₁ : Q') : Type where
  C : Q'
  Λ : Q'
  a : Q' → Q'
  C_pos : (0 : Q') < C
  Λ_pos : (0 : Q') < Λ
  a_pos : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → (0 : Q') < a g
  spacing_quad :
    ∀ g : Q', (0 : Q') < g → g ≤ g₁ →
      a g * Λ ≤ C * (g * g)

/-! ## 5. The physical `AFEnvelope` and bare-floor consumer -/

/-- The canonical heat time on the margin chart: `t(g)=4g²`. -/
def physicalTime (g : Q') : Q' :=
  Q'.ofNat 4 * (g * g)

/-- `t(g)/8` is exactly `(1/2)g²`. -/
theorem oneEighth_physicalTime (g : Q') :
    (oneEighth * physicalTime g).eqv (half * (g * g)) := by
  unfold physicalTime
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv oneEighth (Q'.ofNat 4) (g * g))) ?_
  exact Q'.mul_eqv_congr_right
    (oneEighth * Q'.ofNat 4) half (g * g) (by decide)

/-- The genuine cubic physical law supplies `AFEnvelope.w_floor`. -/
theorem physicalWeight_floor
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) :
    oneEighth * physicalTime g ≤
      1 + (-(blockedWeight family g)) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (oneEighth_physicalTime g))
    (blockedMargin_ge_half_square family law g hg hgle)

/-- Construct an `AFEnvelope` whose weight is definitionally the exact
observable- or exponent-Gram-matched physical block output.

Unlike `padeAFEnvelope`, this constructor does not define `w` using
`oneOver1p`.  The Padé model is not imported into the physical identification:
the cubic law proves the required margin estimate directly. -/
def physicalAFEnvelope
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁) :
    AFEnvelope where
  α := Q'.ofNat 4
  ᾱ := Q'.ofNat 4
  C := spacing.C
  Λ := spacing.Λ
  g₁ := law.g₁
  t := physicalTime
  a := spacing.a
  w := blockedWeight family
  α_pos := by decide
  ᾱ_pos := by decide
  C_pos := spacing.C_pos
  Λ_pos := spacing.Λ_pos
  g₁_pos := law.g₁_pos
  t_lower := by
    intro g _ _
    exact Q'.le_refl' _
  t_upper := by
    intro g _ _
    exact Q'.le_refl' _
  w_floor := physicalWeight_floor family law
  spacing_quad := spacing.spacing_quad

/-- The pre-existing bare diagnostic can now be applied to a physically
matched envelope without replacing its block output by a Padé surrogate. -/
def physicalBareLinearFloor
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁) :
    Σ' c₀ : Q', (0 : Q') < c₀ ∧
      ∀ g : Q', (0 : Q') < g →
        g ≤ (physicalAFEnvelope family law spacing).g₁ →
        c₀ *
            ((physicalAFEnvelope family law spacing).a g *
              (physicalAFEnvelope family law spacing).Λ) ≤
          1 + (-((physicalAFEnvelope family law spacing).w g)) :=
  BareAFImpliesLinearFloor
    (physicalAFEnvelope family law spacing)

/-- The constructed envelope's weight is literally the exact physical
matched output. -/
theorem physicalAFEnvelope_weight
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (g : Q') :
    (physicalAFEnvelope family law spacing).w g =
      blockedWeight family g :=
  rfl

/-- The constructed envelope's spacing is literally the supplied positive
physical spacing family. -/
theorem physicalAFEnvelope_spacing
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (g : Q') :
    (physicalAFEnvelope family law spacing).a g = spacing.a g :=
  rfl

end YMGap.Continuum.BF4MatchedPhysicalAFBridge

#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.fineWeight_nonnegative
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.blockedWeight_pos
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.lower_of_abs_remainder
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.blockedMargin_ge_half_square
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.blockedMargin_le_two_square
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.oneEighth_physicalTime
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.physicalWeight_floor
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.physicalAFEnvelope
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.physicalBareLinearFloor
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.physicalAFEnvelope_weight
#print axioms YMGap.Continuum.BF4MatchedPhysicalAFBridge.physicalAFEnvelope_spacing
