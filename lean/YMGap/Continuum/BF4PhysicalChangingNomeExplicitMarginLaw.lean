/-
# Explicit margin law for the changing-nome completed family

This module specializes the scale-free rational margin algebra to the actual
dependent `changingNomeDynamicFamily`.  It proves only the exact denominator
presentation of the lattice margin; comparison of that denominator with the
vanishing spacing is deliberately left as a separate typed certificate.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
import YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

namespace YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

local infix:50 " ≈ " => Q'.eqv

/-- The explicit denominator inherited from the finite BF4 rate at the
scheduled nome. -/
def changingNomeMarginDenominator (scale : Nat) : Q' :=
  gapDenominator (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

theorem changingNomeMarginDenominator_pos (scale : Nat) :
    (0 : Q') < changingNomeMarginDenominator scale :=
  gapDenominator_pos (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

/-- The changing family has an exact same-object reciprocal presentation of
its lattice margin.  No spacing comparison is included. -/
def changingNomeExplicitMarginInverseLaw :
    ExplicitMarginInverseLaw changingNomeDynamicFamily where
  denominator := changingNomeMarginDenominator
  denominator_pos := changingNomeMarginDenominator_pos
  margin_eqv_inverse := by
    intro scale
    change
      (1 - (changingNomeDynamicFamily.completedGap scale).rate) ≈
        Q'.divPos 1 (changingNomeMarginDenominator scale)
          (changingNomeMarginDenominator_pos scale)
    rw [changingNomeDynamicFamily_rate]
    let w := changingNome scale
    let hw : (0 : Q') ≤ w := Q'.le_of_lt (changingNome_pos scale)
    let numerator := gapNumerator w hw
    let denominator := gapDenominator w hw
    have hdenominator : (0 : Q') < denominator := gapDenominator_pos w hw
    have hmargin := one_sub_divPos_eqv_inverse numerator denominator hdenominator
    have hsub : (denominator - numerator) ≈ (1 : Q') := by
      show ((1 + numerator) + -numerator) ≈ (1 : Q')
      exact one_add_sub_self_eqv numerator
    refine Q'.eqv_trans _ (Q'.divPos (denominator - numerator) denominator hdenominator)
      _ hmargin ?_
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _ hsub

#print axioms changingNomeMarginDenominator
#print axioms changingNomeMarginDenominator_pos
#print axioms changingNomeExplicitMarginInverseLaw

end YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
