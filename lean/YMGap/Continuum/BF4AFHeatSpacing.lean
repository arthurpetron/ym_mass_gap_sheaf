/-
BF4 / AF handoff — derive the heat-time/spacing inequality used by the
five-holonomy Perron budget from the existing `AFEnvelope`.

The physical BF4 estimate needs

    τ(g) = t(g) / 4  ≥  κ · a(g),
    κ = α Λ / (4 C).

`BareAFDiagnostic.AFEnvelope` already carries exactly the two inequalities
needed for this implication:

    α g² ≤ t(g),       a(g) Λ ≤ C g².

This module proves the displayed BF4 estimate.  It does not construct an
`AFEnvelope` for the physical four-dimensional block map: that remains the
first open trajectory-identification input.  In particular, it does not identify
the rational envelope surrogate `E.w` with the heat coordinate of the exact
all-label grouped Haar operator.

The proof is pure constructive `Q'` arithmetic.  Every load-bearing declaration
is axiom-gated below; permitted output is `propext` / `Quot.sound` only.
-/

import YMGap.Continuum.BareAFDiagnostic

namespace YMGap.Continuum.BF4AFHeatSpacing

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic

/-! ## 1. The explicit BF4 heat-time coefficient -/

/-- The rational quarter appearing in `τ = t/4`. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

theorem quarter_pos : (0 : Q') < quarter := by decide

/-- The BF4 heat-time/spacing rate

    `κ = α Λ / (4 C)`.

The reciprocal is the constructive positive reciprocal from
`BareAFDiagnostic`. -/
def heatSpacingRate (E : AFEnvelope) : Q' :=
  (quarter * E.α * E.Λ) * recip E.C E.C_pos

/-- `κ = α Λ/(4C)` is strictly positive. -/
theorem heatSpacingRate_pos (E : AFEnvelope) :
    (0 : Q') < heatSpacingRate E := by
  exact mul_pos
    (mul_pos (mul_pos quarter_pos E.α_pos) E.Λ_pos)
    (by
      have hn : (0 : Int) < (recip E.C E.C_pos).num := by
        show (0 : Int) < (E.C.den : Int)
        exact_mod_cast E.C.den_pos
      show (0 : Int) * ((recip E.C E.C_pos).den : Int)
          < (recip E.C E.C_pos).num * ((0 : Q').den : Int)
      rw [Int.zero_mul]
      have h0d : ((0 : Q').den : Int) = 1 := rfl
      rw [h0d, Int.mul_one]
      exact hn)

/-! ## 2. AF envelope implies the BF4 heat-time/spacing bound -/

/-- **The BF4 heat-time/spacing theorem.**  On the small-coupling window of an
`AFEnvelope`,

    `heatSpacingRate E · a(g) ≤ quarter · t(g)`.

Equivalently, with `τ(g) := t(g)/4`,

    `τ(g) ≥ (α Λ/(4C)) a(g)`.

Thus the scalar trajectory hypothesis used by the five-holonomy Perron budget is
not an additional field once an `AFEnvelope` for the physical trajectory has
been constructed.  The still-open input is that construction/identification,
not this inequality. -/
theorem heat_time_ge_rate_mul_spacing (E : AFEnvelope) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ E.g₁) :
    heatSpacingRate E * E.a g ≤ quarter * E.t g := by
  have hgg_nn : (0 : Q') ≤ g * g :=
    Q'.mul_nonneg g g (Q'.le_of_lt hg) (Q'.le_of_lt hg)
  have hqα_nn : (0 : Q') ≤ quarter * E.α :=
    Q'.le_of_lt (mul_pos quarter_pos E.α_pos)
  have hr_nn : (0 : Q') ≤ recip E.C E.C_pos :=
    recip_nonneg E.C E.C_pos
  have hqαr_nn : (0 : Q') ≤ (quarter * E.α) * recip E.C E.C_pos :=
    Q'.mul_nonneg _ _ hqα_nn hr_nn

  -- Reassociate κ·a as ((1/4)α/C)·(aΛ), so `spacing_quad` applies.
  have hκa :
      (heatSpacingRate E * E.a g).eqv
        (((quarter * E.α) * recip E.C E.C_pos) * (E.a g * E.Λ)) := by
    show ((((quarter * E.α) * E.Λ) * recip E.C E.C_pos) * E.a g).eqv
      (((quarter * E.α) * recip E.C E.C_pos) * (E.a g * E.Λ))
    -- Both sides are the same four factors; move `Λ` to the far right.
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv ((quarter * E.α) * E.Λ)
        (recip E.C E.C_pos) (E.a g)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (quarter * E.α) E.Λ
        (recip E.C E.C_pos * E.a g)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (quarter * E.α)
        (E.Λ * (recip E.C E.C_pos * E.a g))
        ((recip E.C E.C_pos * E.a g) * E.Λ)
        (Q'.mul_comm_eqv E.Λ (recip E.C E.C_pos * E.a g))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (quarter * E.α)
        ((recip E.C E.C_pos * E.a g) * E.Λ)
        (recip E.C E.C_pos * (E.a g * E.Λ))
        (Q'.mul_assoc_eqv (recip E.C E.C_pos) (E.a g) E.Λ)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (quarter * E.α) (recip E.C E.C_pos) (E.a g * E.Λ))

  have hspacing :
      ((quarter * E.α) * recip E.C E.C_pos) * (E.a g * E.Λ)
        ≤ ((quarter * E.α) * recip E.C E.C_pos) * (E.C * (g * g)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (E.spacing_quad g hg hgle) hqαr_nn

  -- Cancel `(1/C)·C` in the upper bound.
  have hcancel :
      (((quarter * E.α) * recip E.C E.C_pos) * (E.C * (g * g))).eqv
        ((quarter * E.α) * (g * g)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (quarter * E.α) (recip E.C E.C_pos)
        (E.C * (g * g))) ?_
    refine Q'.mul_eqv_congr_left (quarter * E.α) _ (g * g) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (recip E.C E.C_pos) E.C (g * g))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (recip E.C E.C_pos * E.C) 1 (g * g)
        (recip_mul_self E.C E.C_pos)) ?_
    exact Q'.one_mul_eqv (g * g)

  -- The heat-time lower envelope gives `(1/4) α g² ≤ (1/4) t(g)`.
  have htime : (quarter * E.α) * (g * g) ≤ quarter * E.t g := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv quarter E.α (g * g))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (E.t_lower g hg hgle) (Q'.le_of_lt quarter_pos)

  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hκa)
    (Q'.le_trans' _ _ _ hspacing
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel) htime))

/-! ## 3. A proved rational heat-weight constructor

The exact physical heat weight `exp(−t/4)` is a `CReal`, whereas `AFEnvelope.w`
is deliberately a rational upper-envelope surrogate.  The project's proved Padé
bound supplies such a surrogate without identifying the two types:

    `exp(−x) ≤ 1/(1+x)`,  `x = t/4`.

The following reduced data record omits both `w` and `w_floor`.  Its constructor
defines `w := 1/(1+t/4)` and derives `w_floor` from
`half_mul_add_oneOver1p_le_one`.  The genuinely physical spacing comparison
`spacing_quad` remains explicit.
-/

/-- AF data sufficient to construct the rational Padé heat-weight envelope.

Compared with `AFEnvelope`, this record removes the arbitrary rational function
`w` and its lower-margin field `w_floor`.  The closed threshold condition says
that the whole declared coupling window lies in `t/4 ≤ 1`; it is enough, together
with `t_upper`, to fire the proved scalar exponential estimate. -/
structure PadeEnvelopeData where
  α : Q'
  ᾱ : Q'
  C : Q'
  Λ : Q'
  g₁ : Q'
  t : Q' → Q'
  a : Q' → Q'
  α_pos : (0 : Q') < α
  ᾱ_pos : (0 : Q') < ᾱ
  C_pos : (0 : Q') < C
  Λ_pos : (0 : Q') < Λ
  g₁_pos : (0 : Q') < g₁
  t_lower : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → α * (g * g) ≤ t g
  t_upper : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → t g ≤ ᾱ * (g * g)
  /-- The declared coupling window is small enough that
  `(1/4)·ᾱ·g₁² ≤ 1`. -/
  heat_window : quarter * (ᾱ * (g₁ * g₁)) ≤ 1
  spacing_quad : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → a g * Λ ≤ C * (g * g)

/-- The heat argument `x(g)=t(g)/4`. -/
def heatArgument (D : PadeEnvelopeData) (g : Q') : Q' :=
  quarter * D.t g

/-- The rational Padé upper envelope for the exact heat weight:
`w_P(g)=1/(1+t(g)/4)`. -/
def padeWeight (D : PadeEnvelopeData) (g : Q') : Q' :=
  ExpUBInstance.oneOver1p (heatArgument D g)

/-- On the small-coupling window, `t(g)/4` is nonnegative. -/
theorem heatArgument_nonneg (D : PadeEnvelopeData) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ D.g₁) :
    (0 : Q') ≤ heatArgument D g := by
  have hgg_nn : (0 : Q') ≤ g * g :=
    Q'.mul_nonneg g g (Q'.le_of_lt hg) (Q'.le_of_lt hg)
  have hαgg_nn : (0 : Q') ≤ D.α * (g * g) :=
    Q'.mul_nonneg D.α (g * g) (Q'.le_of_lt D.α_pos) hgg_nn
  have ht_nn : (0 : Q') ≤ D.t g :=
    Q'.le_trans' _ _ _ hαgg_nn (D.t_lower g hg hgle)
  exact Q'.mul_nonneg quarter (D.t g) (Q'.le_of_lt quarter_pos) ht_nn

/-- On the declared coupling window, `t(g)/4 ≤ 1`. -/
theorem heatArgument_le_one (D : PadeEnvelopeData) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ D.g₁) :
    heatArgument D g ≤ 1 := by
  have hg_nn : (0 : Q') ≤ g := Q'.le_of_lt hg
  have hg1_nn : (0 : Q') ≤ D.g₁ := Q'.le_of_lt D.g₁_pos
  have hgg_le_left : g * g ≤ D.g₁ * g :=
    Q'.mul_le_mul_of_nonneg_right g D.g₁ g hgle hg_nn
  have hgg_le_right : D.g₁ * g ≤ D.g₁ * D.g₁ :=
    Q'.mul_le_mul_of_nonneg_left g D.g₁ D.g₁ hgle hg1_nn
  have hgg_le : g * g ≤ D.g₁ * D.g₁ :=
    Q'.le_trans' _ _ _ hgg_le_left hgg_le_right
  have hbar_nn : (0 : Q') ≤ D.ᾱ := Q'.le_of_lt D.ᾱ_pos
  have hbar :
      D.ᾱ * (g * g) ≤ D.ᾱ * (D.g₁ * D.g₁) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgg_le hbar_nn
  have ht : D.t g ≤ D.ᾱ * (D.g₁ * D.g₁) :=
    Q'.le_trans' _ _ _ (D.t_upper g hg hgle) hbar
  have hquarter_nn : (0 : Q') ≤ quarter := Q'.le_of_lt quarter_pos
  have hscaled :
      quarter * D.t g ≤ quarter * (D.ᾱ * (D.g₁ * D.g₁)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ ht hquarter_nn
  exact Q'.le_trans' _ _ _ hscaled D.heat_window

/-- `1/8·t ≃ 1/2·(1/4·t)`. -/
theorem oneEighth_time_eq_half_argument (t : Q') :
    (oneEighth * t).eqv (half * (quarter * t)) := by
  have hcoeff : oneEighth.eqv (half * quarter) := by decide
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right oneEighth (half * quarter) t hcoeff) ?_
  exact Q'.mul_assoc_eqv half quarter t

/-- The Padé surrogate has the required AF numerator floor:
`t(g)/8 ≤ 1 − padeWeight(g)`.  This is derived, not a field. -/
theorem padeWeight_floor (D : PadeEnvelopeData) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ D.g₁) :
    oneEighth * D.t g ≤ 1 + (-(padeWeight D g)) := by
  let x := heatArgument D g
  have hx0 : (0 : Q') ≤ x := heatArgument_nonneg D g hg hgle
  have hx1 : x ≤ 1 := heatArgument_le_one D g hg hgle
  have hbase : half * x + ExpUBInstance.oneOver1p x ≤ 1 :=
    half_mul_add_oneOver1p_le_one x hx0 hx1
  have hcomm :
      ExpUBInstance.oneOver1p x + half * x ≤ 1 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_comm_eqv (ExpUBInstance.oneOver1p x) (half * x)))
      hbase
  have hfloor : half * x ≤ 1 + (-(ExpUBInstance.oneOver1p x)) :=
    le_sub_of_add_le hcomm
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (oneEighth_time_eq_half_argument (D.t g))) hfloor

/-- The exact constructive exponential is below the rational Padé weight.
This is the sound typed bridge: no equality between the `CReal` exponential and
the `Q'` envelope is asserted. -/
theorem physical_exp_le_padeWeight (D : PadeEnvelopeData) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ D.g₁) :
    CReal.leRat
      (ExpNeg.expNeg (heatArgument D g) (heatArgument_nonneg D g hg hgle))
      (padeWeight D g) :=
  expNeg_le_oneOver1p (heatArgument D g) (heatArgument_nonneg D g hg hgle)

/-- **Reduced constructor.**  Build an `AFEnvelope` whose rational heat weight is
the proved Padé upper envelope.  Both `w` and `w_floor` are discharged from
constructive exponential arithmetic; `spacing_quad` remains the physical
trajectory input. -/
def padeAFEnvelope (D : PadeEnvelopeData) : AFEnvelope where
  α := D.α
  ᾱ := D.ᾱ
  C := D.C
  Λ := D.Λ
  g₁ := D.g₁
  t := D.t
  a := D.a
  w := padeWeight D
  α_pos := D.α_pos
  ᾱ_pos := D.ᾱ_pos
  C_pos := D.C_pos
  Λ_pos := D.Λ_pos
  g₁_pos := D.g₁_pos
  t_lower := D.t_lower
  t_upper := D.t_upper
  w_floor := padeWeight_floor D
  spacing_quad := D.spacing_quad

/-! ## 4. Honest frontier statement

PROVED: an `AFEnvelope` implies the exact scalar BF4 heat-time/spacing hypothesis
with the positive coefficient `αΛ/(4C)`.

PROVED: the rational heat-weight surrogate and its `w_floor` field can be removed:
`padeAFEnvelope` constructs both from the Padé envelope of the exact constructive
exponential.

OPEN: the `PadeEnvelopeData` heat-time and, first irreducibly, spacing fields on
the nonperturbative physical BF4 trajectory, including identification with the
exact all-label grouped Haar block map.  Neither
`AFTrajectoryCertificate` nor `AFExpLift` supplies that operator-level
identification: they provide a scalar reciprocal trajectory and a derived
spacing schedule, respectively.
-/

end YMGap.Continuum.BF4AFHeatSpacing

#print axioms YMGap.Continuum.BF4AFHeatSpacing.quarter_pos
#print axioms YMGap.Continuum.BF4AFHeatSpacing.heatSpacingRate_pos
#print axioms YMGap.Continuum.BF4AFHeatSpacing.heat_time_ge_rate_mul_spacing
#print axioms YMGap.Continuum.BF4AFHeatSpacing.heatArgument_nonneg
#print axioms YMGap.Continuum.BF4AFHeatSpacing.heatArgument_le_one
#print axioms YMGap.Continuum.BF4AFHeatSpacing.oneEighth_time_eq_half_argument
#print axioms YMGap.Continuum.BF4AFHeatSpacing.padeWeight_floor
#print axioms YMGap.Continuum.BF4AFHeatSpacing.physical_exp_le_padeWeight
#print axioms YMGap.Continuum.BF4AFHeatSpacing.padeAFEnvelope
