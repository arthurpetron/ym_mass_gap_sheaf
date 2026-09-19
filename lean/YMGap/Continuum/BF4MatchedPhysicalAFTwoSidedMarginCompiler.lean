/-
# Two-sided physical margin calibration on the matched AF chart

The matched cubic law already gives

  (1/2) g^2 <= 1 - blockedWeight(g) <= 2 g^2.

The existing physical-spacing envelope supplies only the upper estimate
`a(g) Λ <= C g^2`.  This module isolates the missing dimensional input as a
positive lower quadratic spacing envelope
`c g^2 <= a(g) Λ`.  From that one additional Type-valued certificate, the
literal matched blocked margin receives an explicit two-sided physical band.

The result is intentionally scalar and remains tied to `blockedWeight` on the
matched AF chart.  It does not identify that blocked margin with the rate of a
separately produced completed transfer, and therefore does not claim a
dynamic-family rate band, a continuum limit, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler

namespace YMGap.Continuum.BF4MatchedPhysicalAFTwoSidedMarginCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The missing physical input -/

/-- A lower quadratic dimensional-transmutation envelope on the same spacing
chart used by `CubicMarginLaw`. -/
structure PhysicalSpacingLowerQuadraticEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    (spacing : PhysicalSpacingEnvelope law.g₁) : Type 1 where
  c : Q'
  c_pos : (0 : Q') < c
  lower : ∀ g : Q', (0 : Q') < g → g ≤ law.g₁ →
    c * (g * g) ≤ spacing.a g * spacing.Λ

/-! ## 2. A scalar two-sided margin band -/

/-- The scalar rate band deliberately names the exact matched blocked margin,
not the rate of an unrelated completed carrier. -/
structure MatchedBlockedMarginBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerRate : ∀ scale,
    floor * spacing.a (trajectory.coupling scale) ≤
      blockedMargin family (trajectory.coupling scale)
  upperRate : ∀ scale,
    blockedMargin family (trajectory.coupling scale) ≤
      ceiling * spacing.a (trajectory.coupling scale)

private theorem half_mul_two_right (x : Q') :
    (half * (Q'.ofNat 2 * x)).eqv x := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (half * Q'.ofNat 2) 1 x (by decide)) ?_
  exact Q'.one_mul_eqv x

private theorem floor_mul_spacing_le_half_square
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) :
    Q'.divPos spacing.Λ (Q'.ofNat 2 * spacing.C)
        (Q'.mul_pos (by decide) spacing.C_pos) * spacing.a g ≤
      half * (g * g) := by
  let denominator := Q'.ofNat 2 * spacing.C
  have hdenominator : (0 : Q') < denominator :=
    Q'.mul_pos (by decide) spacing.C_pos
  have hspacing := spacing.spacing_quad g hg hgle
  have hfloor_mul_denominator :
      (Q'.divPos spacing.Λ denominator hdenominator) * denominator ≈
        spacing.Λ :=
    Q'.divPos_mul_eqv spacing.Λ denominator hdenominator
  have hcross :
      (Q'.divPos spacing.Λ denominator hdenominator * spacing.a g) *
          denominator ≤ spacing.C * (g * g) := by
    have hleft :
        (Q'.divPos spacing.Λ denominator hdenominator * spacing.a g) *
            denominator ≈ spacing.a g * spacing.Λ := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv
        (Q'.divPos spacing.Λ denominator hdenominator)
        (spacing.a g) denominator) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left
        (Q'.divPos spacing.Λ denominator hdenominator) _ _
        (Q'.mul_comm_eqv (spacing.a g) denominator)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv
        (Q'.divPos spacing.Λ denominator hdenominator)
        denominator (spacing.a g))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right
        (Q'.divPos spacing.Λ denominator hdenominator * denominator)
        spacing.Λ (spacing.a g) hfloor_mul_denominator) ?_
      · exact Q'.mul_comm_eqv spacing.Λ (spacing.a g)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleft) hspacing
  have hquotient := Q'.le_divPos_of_mul_le
    (spacing.C * (g * g)) denominator hdenominator hcross
  have hhalf_denominator :
      (half * (g * g)) * denominator ≈ spacing.C * (g * g) := by
    change (half * (g * g)) * (Q'.ofNat 2 * spacing.C) ≈
      spacing.C * (g * g)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv half (g * g)
        (Q'.ofNat 2 * spacing.C)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (g * g)
          (Q'.ofNat 2) spacing.C))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (Q'.mul_eqv_congr_right ((g * g) * Q'.ofNat 2)
          (Q'.ofNat 2 * (g * g)) spacing.C
          (Q'.mul_comm_eqv (g * g) (Q'.ofNat 2)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (Q'.mul_assoc_eqv (Q'.ofNat 2) (g * g) spacing.C)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_comm_eqv (g * g) spacing.C))) ?_
    exact half_mul_two_right (spacing.C * (g * g))
  have hupper :
      Q'.divPos (spacing.C * (g * g)) denominator hdenominator ≤
        half * (g * g) :=
    Q'.divPos_le_of_le_mul (spacing.C * (g * g)) denominator hdenominator
      (Q'.le_of_eqv (Q'.eqv_symm hhalf_denominator))
  exact Q'.le_trans' _ _ _ hquotient hupper

private theorem two_square_le_ceiling_mul_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (lower : PhysicalSpacingLowerQuadraticEnvelope spacing)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) :
    Q'.ofNat 2 * (g * g) ≤
      Q'.divPos (Q'.ofNat 2 * spacing.Λ) lower.c lower.c_pos *
        spacing.a g := by
  let ceiling := Q'.divPos (Q'.ofNat 2 * spacing.Λ)
    lower.c lower.c_pos
  have hspacing := lower.lower g hg hgle
  have hceiling_mul_floor : ceiling * lower.c ≈
      Q'.ofNat 2 * spacing.Λ :=
    Q'.divPos_mul_eqv (Q'.ofNat 2 * spacing.Λ) lower.c lower.c_pos
  have hcross :
      (Q'.ofNat 2 * (g * g)) * lower.c ≤
        (ceiling * spacing.a g) * lower.c := by
    have hleft :
        (Q'.ofNat 2 * (g * g)) * lower.c ≤
          Q'.ofNat 2 * (spacing.a g * spacing.Λ) := by
      have hleft_eqv :
          (Q'.ofNat 2 * (g * g)) * lower.c ≈
            Q'.ofNat 2 * (lower.c * (g * g)) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv
          (Q'.ofNat 2) (g * g) lower.c) ?_
        exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_comm_eqv (g * g) lower.c)
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hspacing
        (by decide : (0 : Q') ≤ Q'.ofNat 2)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft_eqv) hscaled
    have hright :
        Q'.ofNat 2 * (spacing.a g * spacing.Λ) ≈
          (ceiling * spacing.a g) * lower.c := by
      have hright_rev :
          (ceiling * spacing.a g) * lower.c ≈
            Q'.ofNat 2 * (spacing.a g * spacing.Λ) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ceiling
          (spacing.a g) lower.c) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left ceiling _ _
            (Q'.mul_comm_eqv (spacing.a g) lower.c)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv ceiling lower.c
            (spacing.a g))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (ceiling * lower.c) _ _
            hceiling_mul_floor) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv
          (Q'.ofNat 2) spacing.Λ (spacing.a g)) ?_
        exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_comm_eqv spacing.Λ (spacing.a g))
      exact Q'.eqv_symm hright_rev
    exact Q'.le_trans' _ _ _ hleft
      (Q'.le_of_eqv hright)
  have hquotient := Q'.le_divPos_of_mul_le
    ((ceiling * spacing.a g) * lower.c) lower.c lower.c_pos hcross
  have hupper :
      Q'.divPos ((ceiling * spacing.a g) * lower.c)
          lower.c lower.c_pos ≤ ceiling * spacing.a g :=
    Q'.divPos_le_of_le_mul ((ceiling * spacing.a g) * lower.c)
      lower.c lower.c_pos (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _ hquotient hupper

/-! ## 3. Construct the scalar band -/

/-- A positive lower spacing envelope supplies explicit two-sided bounds for
the literal matched blocked margin. -/
def MatchedPhysicalDynamicScalarTrajectory.toBlockedMarginBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (lower : PhysicalSpacingLowerQuadraticEnvelope spacing) :
    MatchedBlockedMarginBand trajectory where
  floor := Q'.divPos spacing.Λ
    (Q'.ofNat 2 * spacing.C)
    (Q'.mul_pos (by decide) spacing.C_pos)
  floor_pos := Q'.divPos_pos spacing.Λ
    (Q'.ofNat 2 * spacing.C)
    (Q'.mul_pos (by decide) spacing.C_pos)
    spacing.Λ_pos
  ceiling := Q'.divPos (Q'.ofNat 2 * spacing.Λ)
    lower.c lower.c_pos
  ceiling_pos := Q'.divPos_pos (Q'.ofNat 2 * spacing.Λ)
    lower.c lower.c_pos
    (Q'.mul_pos (by decide) spacing.Λ_pos)
  lowerRate := by
    intro scale
    exact Q'.le_trans' _ _ _
      (floor_mul_spacing_le_half_square
        (trajectory.coupling scale)
        (trajectory.coupling_pos scale)
        (trajectory.coupling_le_window scale))
      (blockedMargin_ge_half_square family law
        (trajectory.coupling scale)
        (trajectory.coupling_pos scale)
        (trajectory.coupling_le_window scale))
  upperRate := by
    intro scale
    exact Q'.le_trans' _ _ _
      (blockedMargin_le_two_square family law
        (trajectory.coupling scale)
        (trajectory.coupling_pos scale)
        (trajectory.coupling_le_window scale))
      (two_square_le_ceiling_mul_spacing lower
        (trajectory.coupling scale)
        (trajectory.coupling_pos scale)
        (trajectory.coupling_le_window scale))

end YMGap.Continuum.BF4MatchedPhysicalAFTwoSidedMarginCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4MatchedPhysicalAFTwoSidedMarginCompiler.MatchedPhysicalDynamicScalarTrajectory.toBlockedMarginBand
