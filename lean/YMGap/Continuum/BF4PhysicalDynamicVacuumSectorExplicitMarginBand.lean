/-
# Explicit denominator-level physical calibration

The completed-family interface already consumes a two-sided physical-rate band.
This file factors that input one step further: a finite analytic route may
provide an explicit positive denominator for the lattice margin, an exact
margin-to-reciprocal identity, and two rational product inequalities.  The
compiler below turns those data into the existing physical-rate band on the
definitionally same completed family.

This is a named scale-law certificate, not an inhabitant of the changing-nome
SU(2) calibration.  It exposes the remaining comparison with the spacing and
does not assert a continuum limit, an OS/GNS identification, or the Clay
theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.WindowedSpacingFloor

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The refined named input -/

/-- An explicit positive denominator presentation of the dimensionless lattice
margin of one completed family.  The `margin_eqv_inverse` field is the exact
algebraic bridge from the actual completed rate to the presented denominator;
it prevents a later compiler from silently replacing the rate by unrelated
data. -/
structure ExplicitMarginInverseLaw
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  denominator : Nat → Q'
  denominator_pos : ∀ scale, (0 : Q') < denominator scale
  margin_eqv_inverse : ∀ scale,
    family.latticeMargin scale ≈
      Q'.divPos 1 (denominator scale) (denominator_pos scale)

/-- A two-sided scale law written before division by the explicit denominator.
The inequalities are the exact raw obligations needed by the rate-band
compiler, with no hidden asymptotic or uniformity claim. -/
structure ExplicitMarginDenominatorBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : ExplicitMarginInverseLaw family) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerDenominator : ∀ scale,
    (floor * family.transferSpacing.spacing scale) * law.denominator scale ≤
      (1 : Q')
  upperDenominator : ∀ scale,
    (1 : Q') ≤
      (ceiling * family.transferSpacing.spacing scale) * law.denominator scale

namespace ExplicitMarginDenominatorBand

/-! ## 2. Necessary scale growth -/

/- A denominator band over a spacing stream that vanishes cannot have a
bounded denominator.  The proof is deliberately stated before the compiler:
it uses only the upper raw product inequality and the explicit spacing
modulus, so it cannot smuggle in the physical-rate conclusion. -/

/-- Every positive rational ceiling is eventually exceeded by the explicit
denominator of an inhabited denominator band.  Thus an eventual or global
bounded-denominator route cannot supply the missing physical calibration over
a spacing-to-zero family. -/
theorem denominator_unbounded
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (band : ExplicitMarginDenominatorBand law)
    (bound : Q') (hbound : (0 : Q') < bound) :
    ∃ scale, bound ≤ law.denominator scale := by
  let target : Q' := (1 : Q') + bound
  have htarget : (0 : Q') < target := by
    exact Q'.add_pos (by decide) hbound
  have hbound_target : bound ≤ target := by
    refine Q'.le_trans' bound (bound + 1) target ?_ ?_
    · exact Q'.add_le_self_of_nonneg bound 1 (by decide)
    · exact Q'.le_of_eqv (Q'.add_comm_eqv bound 1)
  let denominatorScale : Q' := band.ceiling * target
  have hdenominatorScale : (0 : Q') < denominatorScale := by
    exact Q'.mul_pos band.ceiling_pos htarget
  let threshold : Q' :=
    Q'.divPos (YMGap.Constructive.HalfPow.half) denominatorScale
      hdenominatorScale
  have hthreshold : (0 : Q') < threshold := by
    exact Q'.divPos_pos (YMGap.Constructive.HalfPow.half)
      denominatorScale hdenominatorScale (by decide)
  let scale : Nat := family.transferSpacingToZero.modulus threshold
  have hspacing : family.transferSpacing.spacing scale ≤ threshold :=
    family.transferSpacingToZero.spacing_le threshold hthreshold
      scale (Nat.le_refl _)
  have hscaled :
      band.ceiling * family.transferSpacing.spacing scale ≤
        band.ceiling * threshold :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hspacing
      (Q'.le_of_lt band.ceiling_pos)
  by_cases htarget_le : target ≤ law.denominator scale
  · exact ⟨scale, Q'.le_trans' bound target (law.denominator scale)
      hbound_target htarget_le⟩
  · have hdenominator_le : law.denominator scale ≤ target :=
      Q'.le_of_not_le' htarget_le
    have hproduct :
        (band.ceiling * family.transferSpacing.spacing scale) *
            law.denominator scale ≤
          (band.ceiling * threshold) * target :=
      Q'.mul_le_mul_of_nonneg hscaled hdenominator_le
        (Q'.le_of_lt (Q'.mul_pos band.ceiling_pos hthreshold))
        (Q'.le_of_lt (law.denominator_pos scale))
    have hcollapse :
        ((band.ceiling * threshold) * target).eqv
          (YMGap.Constructive.HalfPow.half) := by
      refine Q'.eqv_trans _ ((threshold * band.ceiling) * target) _
        (Q'.mul_eqv_congr_right (band.ceiling * threshold)
          (threshold * band.ceiling) target
          (Q'.mul_comm_eqv band.ceiling threshold)) ?_
      refine Q'.eqv_trans _ (threshold * (band.ceiling * target)) _
        (Q'.mul_assoc_eqv threshold band.ceiling target) ?_
      exact Q'.divPos_mul_eqv (YMGap.Constructive.HalfPow.half)
        denominatorScale hdenominatorScale
    have hupper :
        (1 : Q') ≤
          (band.ceiling * family.transferSpacing.spacing scale) *
            law.denominator scale :=
      band.upperDenominator scale
    have hone_half : (1 : Q') ≤ YMGap.Constructive.HalfPow.half :=
      Q'.le_trans' _ _ _ hupper
        (Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hcollapse))
    have hfalse : False := (by decide : ¬ ((1 : Q') ≤
      YMGap.Constructive.HalfPow.half)) hone_half
    exact hfalse.elim

/-! ## 2a. Every finite prefix has a computed denominator band -/

/- A finite regulator does not need the missing all-scale comparison.  The
   exact same-family physical-gap stream itself supplies a positive minimum
   and a finite maximum on every prefix.  This is deliberately a windowed
   certificate: passing from these prefix extrema to one positive floor and
   one finite ceiling for all scales is the still-open B04 join. -/

theorem physicalGap_pos
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale : Nat) :
    (0 : Q') < family.physicalGap scale := by
  unfold DynamicVacuumSectorCompletedFamily.physicalGap
  exact Q'.divPos_pos _ _ _ (family.latticeMargin_pos scale)

def finitePrefixGapFloor
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (bound : Nat) : Q' :=
  YMGap.Continuum.WindowedSpacingFloor.finMin
    family.physicalGap bound

def finitePrefixGapCeiling
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (bound : Nat) : Q' :=
  Q'.runningMax family.physicalGap bound

theorem finitePrefixGapFloor_pos
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (bound : Nat) :
    (0 : Q') < finitePrefixGapFloor family bound := by
  unfold finitePrefixGapFloor
  exact YMGap.Continuum.WindowedSpacingFloor.finMin_pos
    family.physicalGap (physicalGap_pos family) bound

theorem finitePrefixGapCeiling_pos
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (bound : Nat) :
    (0 : Q') < finitePrefixGapCeiling family bound := by
  unfold finitePrefixGapCeiling
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (physicalGap_pos family bound)
    (Q'.le_runningMax family.physicalGap bound)

theorem physicalGap_mul_spacing_mul_den_eqv_one
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (scale : Nat) :
    (family.physicalGap scale * family.transferSpacing.spacing scale) *
        law.denominator scale ≈ (1 : Q') := by
  have hgapSpacing :
      family.physicalGap scale * family.transferSpacing.spacing scale ≈
        family.latticeMargin scale := by
    unfold DynamicVacuumSectorCompletedFamily.physicalGap
    exact Q'.divPos_mul_eqv
      (family.latticeMargin scale)
      (family.transferSpacing.spacing scale)
      (family.transferSpacing.spacing_pos scale)
  have hmarginDen :
      family.latticeMargin scale * law.denominator scale ≈ (1 : Q') := by
    refine Q'.eqv_trans _
      (Q'.divPos 1 (law.denominator scale)
        (law.denominator_pos scale) * law.denominator scale) _
      (Q'.mul_eqv_congr_right _ _ _
        (law.margin_eqv_inverse scale)) ?_
    exact Q'.divPos_mul_eqv 1 (law.denominator scale)
      (law.denominator_pos scale)
  refine Q'.eqv_trans _
    (family.latticeMargin scale * law.denominator scale) _
    (Q'.mul_eqv_congr_right _ _ _ hgapSpacing) hmarginDen

private theorem le_runningMax_of_le
    (f : Nat → Q') :
    ∀ bound scale, scale ≤ bound → f scale ≤ Q'.runningMax f bound
  | 0, scale, hscale => by
      have hzero : scale = 0 := by omega
      subst hzero
      exact Q'.le_refl' _
  | bound + 1, scale, hscale => by
      have hcases : scale < bound + 1 ∨ scale = bound + 1 := by omega
      rcases hcases with hlt | heq
      · exact Q'.le_trans' _ _ _
          (le_runningMax_of_le f bound scale (by omega))
          (Q'.le_runningMax_succ f bound)
      · subst heq
        exact Q'.le_runningMax f (bound + 1)

structure FinitePrefixExplicitMarginDenominatorBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : ExplicitMarginInverseLaw family)
    (bound : Nat) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerDenominator : ∀ scale, scale ≤ bound →
    (floor * family.transferSpacing.spacing scale) *
        law.denominator scale ≤ (1 : Q')
  upperDenominator : ∀ scale, scale ≤ bound →
    (1 : Q') ≤
      (ceiling * family.transferSpacing.spacing scale) *
        law.denominator scale

def finitePrefixExplicitMarginDenominatorBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (bound : Nat) :
    FinitePrefixExplicitMarginDenominatorBand law bound where
  floor := finitePrefixGapFloor family bound
  floor_pos := finitePrefixGapFloor_pos family bound
  ceiling := finitePrefixGapCeiling family bound
  ceiling_pos := finitePrefixGapCeiling_pos family bound
  lowerDenominator := by
    intro scale hscale
    have hfloor :=
      YMGap.Continuum.WindowedSpacingFloor.finMin_le
        family.physicalGap bound scale hscale
    have hnonneg :
        (0 : Q') ≤
          family.transferSpacing.spacing scale * law.denominator scale :=
      Q'.mul_nonneg
        (family.transferSpacing.spacing scale)
        (law.denominator scale)
        (Q'.le_of_lt (family.transferSpacing.spacing_pos scale))
        (Q'.le_of_lt (law.denominator_pos scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (finitePrefixGapFloor family bound)
      (family.physicalGap scale)
      (family.transferSpacing.spacing scale * law.denominator scale)
      hfloor hnonneg
    have htargetAssoc := Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_assoc_eqv
        (family.physicalGap scale)
        (family.transferSpacing.spacing scale)
        (law.denominator scale)))
    have htarget := Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ htargetAssoc
        (Q'.le_of_eqv
          (physicalGap_mul_spacing_mul_den_eqv_one (law := law) scale)))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv
        (finitePrefixGapFloor family bound)
        (family.transferSpacing.spacing scale)
        (law.denominator scale)))
      htarget
  upperDenominator := by
    intro scale hscale
    have hceiling :=
      le_runningMax_of_le family.physicalGap bound scale hscale
    have hgapCeiling : family.physicalGap scale ≤
        finitePrefixGapCeiling family bound := by
      exact hceiling
    have hnonneg :
        (0 : Q') ≤
          family.transferSpacing.spacing scale * law.denominator scale :=
      Q'.mul_nonneg
        (family.transferSpacing.spacing scale)
        (law.denominator scale)
        (Q'.le_of_lt (family.transferSpacing.spacing_pos scale))
        (Q'.le_of_lt (law.denominator_pos scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (family.physicalGap scale)
      (finitePrefixGapCeiling family bound)
      (family.transferSpacing.spacing scale * law.denominator scale)
      hgapCeiling
      hnonneg
    have honeEqv : (1 : Q') ≈
        family.physicalGap scale *
          (family.transferSpacing.spacing scale * law.denominator scale) :=
      Q'.eqv_trans _
        ((family.physicalGap scale * family.transferSpacing.spacing scale) *
          law.denominator scale) _
        (Q'.eqv_symm
          (physicalGap_mul_spacing_mul_den_eqv_one (law := law) scale))
        (Q'.mul_assoc_eqv
          (family.physicalGap scale)
          (family.transferSpacing.spacing scale)
          (law.denominator scale))
    have hone : (1 : Q') ≤
        family.physicalGap scale *
          (family.transferSpacing.spacing scale * law.denominator scale) :=
      Q'.le_of_eqv honeEqv
    exact Q'.le_trans' _ _ _ hone
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv
          (finitePrefixGapCeiling family bound)
          (family.transferSpacing.spacing scale)
          (law.denominator scale)))))

/-! ## 2b. The finite prefix reaches the rate-level interface -/

/-- A physical-rate band restricted to one finite scale prefix.  This is the
    windowed analogue of `DynamicVacuumSectorPhysicalRateBand`; it does not
    assert one floor or ceiling for all scales. -/
structure FinitePrefixPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : ExplicitMarginInverseLaw family)
    (bound : Nat) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerRate : ∀ scale, scale ≤ bound →
    floor * family.transferSpacing.spacing scale ≤
      family.latticeMargin scale
  upperRate : ∀ scale, scale ≤ bound →
    family.latticeMargin scale ≤
      ceiling * family.transferSpacing.spacing scale

/-- Divide the finite-prefix denominator inequalities by the same positive
    denominator to obtain the corresponding finite-prefix rate inequalities. -/
def FinitePrefixExplicitMarginDenominatorBand.toFinitePrefixPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    {bound : Nat}
    (band : FinitePrefixExplicitMarginDenominatorBand law bound) :
    FinitePrefixPhysicalRateBand law bound where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerRate := by
    intro scale hscale
    have hquotient := Q'.le_divPos_of_mul_le
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.lowerDenominator scale hscale)
    exact Q'.le_trans' _ _ _ hquotient
      (Q'.le_of_eqv
        (Q'.eqv_symm (law.margin_eqv_inverse scale)))
  upperRate := by
    intro scale hscale
    have hquotient := Q'.divPos_le_of_le_mul
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.upperDenominator scale hscale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (law.margin_eqv_inverse scale)) hquotient

/-! ## 3. The causal compiler -/

/-- Compile the explicit denominator inequalities into the existing physical
rate band for the same completed family. -/
def toPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (band : ExplicitMarginDenominatorBand law) :
    DynamicVacuumSectorPhysicalRateBand family where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerRate := fun scale => by
    have hquotient := Q'.le_divPos_of_mul_le
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.lowerDenominator scale)
    exact Q'.le_trans' _ _ _ hquotient
      (Q'.le_of_eqv
        (Q'.eqv_symm (law.margin_eqv_inverse scale)))
  upperRate := fun scale => by
    have hquotient := Q'.divPos_le_of_le_mul
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.upperDenominator scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (law.margin_eqv_inverse scale)) hquotient

/-- The refined certificate reaches the existing constructive continuum-gap
interface without changing the family or its physical spacing. -/
def toContinuumGapTheorem
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (band : ExplicitMarginDenominatorBand law) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  band.toPhysicalRateBand.toContinuumGapTheorem

end ExplicitMarginDenominatorBand

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.finitePrefixExplicitMarginDenominatorBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.physicalGap_mul_spacing_mul_den_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.FinitePrefixExplicitMarginDenominatorBand.toFinitePrefixPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.denominator_unbounded
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.toContinuumGapTheorem
