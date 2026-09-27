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
open YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
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

/-! The finite anchor budget now gives a concrete one-sided denominator
    lower bound.  This remains pointwise in the schedule; it does not compare
    the denominator to the vanishing spacing. -/

theorem changingNomeMarginDenominator_ge_two_add_twelve_scale (scale : Nat) :
    Q'.ofNat 2 + Q'.ofNat 12 *
        centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          (changingNome scale)
          (Q'.le_of_lt (changingNome_pos scale)) 1404 0 ≤
      changingNomeMarginDenominator scale := by
  let w := changingNome scale
  let hw : (0 : Q') ≤ w := Q'.le_of_lt (changingNome_pos scale)
  let scaleValue :=
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw 1404 0
  have hbudget : Q'.ofNat 2 * scaleValue ≤ headEnergyConstant w hw :=
    YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headEnergyConstant_ge_two_carrierSquareScale
      w hw
  have hscaled :
      Q'.ofNat 6 * (Q'.ofNat 2 * scaleValue) ≤
        Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbudget (by decide)
  have hcoeff : Q'.ofNat 12 ≈ Q'.ofNat 6 * Q'.ofNat 2 := by decide
  have hscale_eqv :
      Q'.ofNat 12 * scaleValue ≈
        Q'.ofNat 6 * (Q'.ofNat 2 * scaleValue) := by
    refine Q'.eqv_trans _ ((Q'.ofNat 6 * Q'.ofNat 2) * scaleValue) _
      (Q'.mul_eqv_congr_right _ _ _ hcoeff) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hscaled' :
      Q'.ofNat 12 * scaleValue ≤
        Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale_eqv) hscaled
  have hadded :
      Q'.ofNat 2 + Q'.ofNat 12 * scaleValue ≤
        Q'.ofNat 2 + Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.add_le_add_left _ _ _ hscaled'
  let x : Q' := Q'.ofNat 6 * headEnergyConstant w hw
  have htwo : Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide
  have hden : Q'.ofNat 2 + x ≈ 1 + (1 + x) := by
    have hfirst : Q'.ofNat 2 + x ≈ (1 + 1) + x :=
      Q'.add_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) x htwo
    exact Q'.eqv_trans _ ((1 + 1) + x) _ hfirst
      (Q'.add_assoc_eqv 1 1 x)
  change Q'.ofNat 2 + Q'.ofNat 12 * scaleValue ≤
    1 + (1 + Q'.ofNat 6 * headEnergyConstant w hw)
  exact Q'.le_trans' _ _ _ hadded (Q'.le_of_eqv hden)

/-- The exact denominator expression needed by the changing-nome asymptotic
    reduction.  This is an algebraic presentation only; it does not compare
    the expression with the vanishing spacing. -/
theorem changingNomeMarginDenominator_eqv_two_add_six_headEnergy
    (scale : Nat) :
    changingNomeMarginDenominator scale ≈
      Q'.ofNat 2 + Q'.ofNat 6 *
        headEnergyConstant
          (changingNome scale)
          (Q'.le_of_lt (changingNome_pos scale)) := by
  unfold changingNomeMarginDenominator gapDenominator gapNumerator
  let x : Q' := Q'.ofNat 6 *
    headEnergyConstant (changingNome scale)
      (Q'.le_of_lt (changingNome_pos scale))
  change 1 + (1 + x) ≈ Q'.ofNat 2 + x
  refine Q'.eqv_trans _ ((1 + 1) + x) _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 1 x)) ?_
  exact Q'.add_eqv_congr_right (1 + 1) (Q'.ofNat 2) x (by decide)

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

/-- The remaining physical-calibration fields specialized to the concrete
changing family.  This type is intentionally not inhabited here: its fields
are exactly the two uniform denominator-versus-spacing inequalities. -/
abbrev changingNomeExplicitMarginDenominatorBand : Type 1 :=
  ExplicitMarginDenominatorBand changingNomeExplicitMarginInverseLaw

/-! The remaining B04 input can now be stated directly at the anchored
    head-energy level.  This is the smallest honest certificate below the
    generic denominator band: it asks only for two uniform product bounds on
    `2 + 6 * H(w_scale)`, with `H = S/F` the already-defined head quotient. -/

structure ChangingNomeHeadEnergyProductBand : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerHeadEnergy : ∀ scale,
    (floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale))) ≤
      (1 : Q')
  upperHeadEnergy : ∀ scale,
    (1 : Q') ≤
      (ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale)))

/-! The lower product inequality is not merely a quotient-side condition.  By
    multiplying it by the positive finite floor and using the exact identity
    `F * (S / F) = S`, it forces the floor itself to be at least of the
    spacing-times-carrier-square order.  This generic scalar kernel keeps the
    expensive algebra independent of the dependent finite-sector expressions
    used by the changing-nome theorem below. -/

theorem ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
    {A H S F : Q'}
    (hA0 : (0 : Q') ≤ A)
    (hF0 : (0 : Q') ≤ F)
    (hband : A * (Q'.ofNat 2 + Q'.ofNat 6 * H) ≤ (1 : Q'))
    (hFS : F * H ≈ S) :
    Q'.ofNat 6 * (A * S) ≤ F := by
  have hsixH_le : Q'.ofNat 6 * H ≤
      Q'.ofNat 2 + Q'.ofNat 6 * H := by
    exact Q'.le_trans' _ (Q'.ofNat 6 * H + Q'.ofNat 2) _
      (Q'.add_le_self_of_nonneg _ _ (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hsixH_scaled : A * (Q'.ofNat 6 * H) ≤
      A * (Q'.ofNat 2 + Q'.ofNat 6 * H) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ A hsixH_le hA0
  have hsixH_le_one : A * (Q'.ofNat 6 * H) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hsixH_scaled hband
  have hscaled : F * (A * (Q'.ofNat 6 * H)) ≤ F := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ F hsixH_le_one hF0)
      (Q'.le_of_eqv (Q'.mul_one_eqv F))
  have hleft :
      Q'.ofNat 6 * (A * S) ≈ F * (A * (Q'.ofNat 6 * H)) := by
    refine Q'.eqv_trans _ (Q'.ofNat 6 * (A * (F * H))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _
        (Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm hFS))
    · refine Q'.eqv_trans _ ((Q'.ofNat 6 * A) * (F * H)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) A (F * H))) ?_
      refine Q'.eqv_trans _ (((Q'.ofNat 6 * A) * F) * H) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6 * A) F H)) ?_
      refine Q'.eqv_trans _ ((F * (Q'.ofNat 6 * A)) * H) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (Q'.ofNat 6 * A) F)) ?_
      refine Q'.eqv_trans _ ((F * (A * Q'.ofNat 6)) * H) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left F _ _ (Q'.mul_comm_eqv (Q'.ofNat 6) A))) ?_
      refine Q'.eqv_trans _ (F * ((A * Q'.ofNat 6) * H)) _
        (Q'.mul_assoc_eqv F (A * Q'.ofNat 6) H) ?_
      exact Q'.mul_eqv_congr_left F _ _
        (Q'.mul_assoc_eqv A (Q'.ofNat 6) H)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hscaled

/-! The dependent specialization is kept behind four small names.  This
    avoids asking elaboration to repeatedly normalize the changing-nome
    carrier, its positive floor, and the scheduled spacing in one large
    theorem term. -/

def changingNomeBandSpacing (scale : Nat) : Q' :=
  changingNomeDynamicFamily.transferSpacing.spacing scale

def changingNomeBandFloor (scale : Nat) : Q' :=
  fixedBasePulledPositiveEdgeFloorValue
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale)) 1404 0

def changingNomeBandScale (scale : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale)) 1404 0

def changingNomeBandHeadEnergy (scale : Nat) : Q' :=
  headEnergyConstant
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

theorem ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
    (band : ChangingNomeHeadEnergyProductBand) (scale : Nat) :
    Q'.ofNat 6 *
        ((band.floor * changingNomeBandSpacing scale) *
          changingNomeBandScale scale) ≤
      changingNomeBandFloor scale := by
  let A : Q' := band.floor * changingNomeBandSpacing scale
  let H : Q' := changingNomeBandHeadEnergy scale
  let S : Q' := changingNomeBandScale scale
  let F : Q' := changingNomeBandFloor scale
  have hA0 : (0 : Q') ≤ A := by
    dsimp [A, changingNomeBandSpacing]
    exact Q'.mul_nonneg band.floor
      (changingNomeDynamicFamily.transferSpacing.spacing scale)
      (Q'.le_of_lt band.floor_pos)
      (Q'.le_of_lt (changingNomeDynamicFamily.transferSpacing.spacing_pos scale))
  have hF0 : (0 : Q') ≤ F := by
    dsimp [F, changingNomeBandFloor]
    exact Q'.le_of_lt
      (fixedBasePulledPositiveEdgeFloorValue_pos
        (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
  have hband : A * (Q'.ofNat 2 + Q'.ofNat 6 * H) ≤ (1 : Q') := by
    dsimp [A, H, changingNomeBandSpacing, changingNomeBandHeadEnergy]
    exact band.lowerHeadEnergy scale
  have hFS : F * H ≈ S := by
    dsimp [F, H, S, changingNomeBandFloor, changingNomeBandHeadEnergy,
      changingNomeBandScale]
    exact fixedBasePulledPositiveEdgeFloorValue_mul_headEnergyConstant_eqv_scale
      (changingNome scale) (Q'.le_of_lt (changingNome_pos scale))
  have hresult :=
    ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
      (A := A) (H := H) (S := S) (F := F) hA0 hF0 hband hFS
  simpa [A, S, F, changingNomeBandSpacing, changingNomeBandScale,
    changingNomeBandFloor] using hresult

private theorem floor_mul_six_spacing_scale_eqv
    (floor spacing scale : Q') :
    Q'.ofNat 6 * ((floor * spacing) * scale) ≈
      floor * (Q'.ofNat 6 * (spacing * scale)) := by
  refine Q'.eqv_trans _ ((Q'.ofNat 6 * (floor * spacing)) * scale) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) (floor * spacing) scale)) ?_
  refine Q'.eqv_trans _ (((Q'.ofNat 6 * floor) * spacing) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) floor spacing))) ?_
  refine Q'.eqv_trans _ (((floor * Q'.ofNat 6) * spacing) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.mul_eqv_congr_right _ _ spacing
        (Q'.mul_comm_eqv (Q'.ofNat 6) floor))) ?_
  refine Q'.eqv_trans _ ((floor * (Q'.ofNat 6 * spacing)) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.mul_assoc_eqv floor (Q'.ofNat 6) spacing)) ?_
  refine Q'.eqv_trans _ (floor * ((Q'.ofNat 6 * spacing) * scale)) _
    (Q'.mul_assoc_eqv floor (Q'.ofNat 6 * spacing) scale) ?_
  exact Q'.mul_eqv_congr_left floor _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 6) spacing scale)

private theorem cancel_floor_of_spacing_scale
    {floor spacing scale : Q'}
    (hfloor : (0 : Q') < floor)
    (hbound : Q'.ofNat 6 * ((floor * spacing) * scale) ≤ floor) :
    Q'.ofNat 6 * (spacing * scale) ≤ (1 : Q') := by
  have htransport :
      Q'.ofNat 6 * ((floor * spacing) * scale) ≈
        floor * (Q'.ofNat 6 * (spacing * scale)) := by
    exact floor_mul_six_spacing_scale_eqv floor spacing scale
  have hright : floor ≈ floor * (1 : Q') :=
    Q'.eqv_symm (Q'.mul_one_eqv floor)
  have hcancel :
      floor * (Q'.ofNat 6 * (spacing * scale)) ≤ floor * (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm htransport))
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hcancel hfloor

/-- Cancelling the positive finite floor from the specialized necessary
    condition leaves a floor-independent carrier/spacing ceiling.  This is a
    necessary consequence of an inhabited product band, not an assertion that
    the product band itself exists. -/
theorem ChangingNomeHeadEnergyProductBand.spacing_mul_scale_le_of_lower_bound
    (scale : Nat)
    (hbound :
      Q'.ofNat 6 *
          ((changingNomeBandFloor scale * changingNomeBandSpacing scale) *
            changingNomeBandScale scale) ≤
        changingNomeBandFloor scale) :
    Q'.ofNat 6 *
        (changingNomeBandSpacing scale * changingNomeBandScale scale) ≤
      (1 : Q') := by
  exact cancel_floor_of_spacing_scale
    (floor := changingNomeBandFloor scale)
    (spacing := changingNomeBandSpacing scale)
    (scale := changingNomeBandScale scale)
    (by
      exact fixedBasePulledPositiveEdgeFloorValue_pos
        (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
    hbound

/-- Compile the minimal head-energy product certificate into the existing
    same-family denominator band without changing the spacing or denominator.
    The certificate remains uninhabited until the cofinal floor-order estimate
    for `F(w_scale)` is proved. -/
def ChangingNomeHeadEnergyProductBand.toExplicitMarginDenominatorBand
    (band : ChangingNomeHeadEnergyProductBand) :
    changingNomeExplicitMarginDenominatorBand where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerDenominator := by
    intro scale
    have htransport :
        (band.floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport)
      (band.lowerHeadEnergy scale)
  upperDenominator := by
    intro scale
    have htransport :
        (band.ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (band.upperHeadEnergy scale)
      (Q'.le_of_eqv (Q'.eqv_symm htransport))

/-- Once the two specialized inequalities are supplied, the generic compiler
produces the physical-rate band for the same changing family. -/
def changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand
    (band : changingNomeExplicitMarginDenominatorBand) :
    DynamicVacuumSectorPhysicalRateBand changingNomeDynamicFamily :=
  band.toPhysicalRateBand

/-- The specialized product certificate contracts all the way to the sharp
continuum-gap interface.  This is only a conditional compiler: the product
band remains an explicit, currently uninhabited input, and the resulting
`ContinuumGapTheorem` still carries the same changing-family physical gap. -/
def ChangingNomeHeadEnergyProductBand.toContinuumGapTheorem
    (band : ChangingNomeHeadEnergyProductBand) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  (band.toExplicitMarginDenominatorBand).toContinuumGapTheorem

#print axioms changingNomeMarginDenominator
#print axioms changingNomeMarginDenominator_pos
#print axioms changingNomeMarginDenominator_ge_two_add_twelve_scale
#print axioms changingNomeMarginDenominator_eqv_two_add_six_headEnergy
#print axioms ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
#print axioms changingNomeBandSpacing
#print axioms changingNomeBandFloor
#print axioms changingNomeBandScale
#print axioms changingNomeBandHeadEnergy
#print axioms ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
#print axioms ChangingNomeHeadEnergyProductBand.spacing_mul_scale_le_of_lower_bound
#print axioms ChangingNomeHeadEnergyProductBand.toExplicitMarginDenominatorBand
#print axioms ChangingNomeHeadEnergyProductBand.toContinuumGapTheorem
#print axioms changingNomeExplicitMarginInverseLaw
#print axioms changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand

end YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
